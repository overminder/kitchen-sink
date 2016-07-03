package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.backend.{MachineSpec, PReg, RegProvider}
import com.github.overmind.seaofnodes.hir.Lsra.LiveRangeBag.ItemOrdering
import com.github.overmind.seaofnodes.hir.Lsra._
import com.github.overmind.seaofnodes.hir.Trace.{TBlock, TGraph}
import com.github.overmind.seaofnodes.hir.nodes._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

object Lsra {
  type IntervalMap = mutable.Map[ValueNode, LiveRangeBag]

  import LiveRangeBag._

  object LiveRangeBag {
    def empty(v: ValueNode) = LiveRangeBag(v, ArrayBuffer.empty)

    object ItemOrdering extends Ordering[Item] {
      override def compare(x: Item, y: Item): Int = {
        Ordering.Tuple2[Int, Int].compare((x.from, x.to), (y.from, y.to))
      }
    }

    case class Item(from: Int, to: Int, var usePositions: Set[Int]) {
      usePositions.foreach(checkPos)

      def checkPos(p: Int): Unit = {
        assert(from <= p && p <= to)
      }

      def addUsePosition(pos: Int): Unit = {
        checkPos(pos)
        usePositions += pos
      }

      override def toString = {
        s"($from:$to @ {${usePositions.toSeq.sorted.mkString(", ")}})"
      }
      protected def createUnion(newFrom: Int, newTo: Int, other: Item): Item = {
        Item(newFrom, newTo, usePositions ++ other.usePositions)
      }

      protected def createIntersection(newFrom: Int, newTo: Int, other: Item): Item = {
        def contained(x: Int) = {
          newFrom <= x && x <= newTo
        }
        Item(newFrom, newTo, (usePositions ++ other.usePositions).filter(contained))
      }

      def mergeAll(oldRs: ArrayBuffer[Item]): Unit = {
        val canMergeAt = oldRs.indexWhere(this.intersects)
        if (canMergeAt >= 0) {
          val toMerge = oldRs.remove(canMergeAt)
          unionOf(toMerge).mergeAll(oldRs)
        } else {
          oldRs += this
          val sorted = oldRs.sorted(ItemOrdering)
          oldRs.clear()
          oldRs ++= sorted
        }
      }

      def intersects(other: Item): Boolean = {
        if (to < other.from || other.to < from) {
          false
        } else {
          true
        }
      }

      def unionOf(other: Item): Item = {
        createUnion(from.min(other.from), to.max(other.to), other)
      }

      def intersectionOf(other: Item): Item = {
        val (newFrom, newTo) = (from.max(other.from), to.min(other.to))
        assert(newFrom < newTo)
        createIntersection(newFrom, newTo, other)
      }
    }
  }

  case class LiveRangeBag(definedBy: ValueNode, ranges: ArrayBuffer[LiveRangeBag.Item]) {

    def nextUseAfter(currentFrom: Int): Option[Int] = {
      val first = ranges.find(r => {
        r.usePositions.exists(_ > currentFrom)
      })
      first.flatMap(_.usePositions.toSeq.sorted.find(_ > currentFrom))
    }

    def endsBefore(position: Int): Boolean = {
      // Last range ends before this position. XXX: < or <=?
      ranges.last.to <= position
    }

    def doesNotCover(position: Int): Boolean = !covers(position)
    def covers(position: Int): Boolean = {
      // XXX: Same question: < or <=?
      ranges.exists({ case r =>
        r.from <= position || position <= r.to
      })
    }

    def intersects(other: LiveRangeBag): Boolean = {
      // O(N^2)...
      val product = for {
        x <- ranges
        y <- other.ranges
      } yield (x, y)
      product.exists { case (x, y) => x.intersects(y) }
    }

    def firstIntersection(other: LiveRangeBag): Option[Item] = {
      val product = for {
        x <- ranges
        y <- other.ranges
      } yield (x, y)
      product
        .find({ case (x, y) => x.intersects(y) })
        .map({ case (x, y) => x.intersectionOf(y) })
    }

    def firstRange = ranges.head

    def firstRangeThatContains(pos: Int): Option[Item] = {
      ranges.find(r => {
        r.from <= pos && pos <= r.to
      })
    }

    def add(newFrom: Int, newTo: Int): Unit = {
      sanityCheck(newFrom, newTo)
      Item(newFrom, newTo, Set.empty).mergeAll(ranges)
    }

    def setFrom(newFrom: Int): Unit = {
      // Must always set the first one?
      assert(newFrom < ranges(0).to)
      val r0 = ranges(0)
      ranges(0) = r0.copy(from = newFrom, usePositions = r0.usePositions + newFrom)
    }

    protected def sanityCheck(f: Int, t: Int) = {
      assert(f < t)
    }

    override def toString = {
      val body = ranges.map(_.toString).mkString(", ")
      s"LiveRanges[$body]"
    }
  }

  def buildLiveness(g: TGraph, log: String => Unit) = {
    val preorder = ArrayBuffer.empty[TBlock]
    g.dfsIdom(preorder += _)
    val rpre = preorder.reverse

    // Block -> VReg
    val liveIns = mutable.Map.empty[Int, mutable.Set[ValueNode]]
    def liveIn(b: TBlock): mutable.Set[ValueNode] = {
      liveIns.getOrElseUpdate(b.id, Graph.emptyIdentitySet[ValueNode])
    }

    // VReg -> LiveRange
    val intervals = Graph.emptyIdentityMap[ValueNode, LiveRangeBag]
    def ensureInterval(v: ValueNode) = {
      intervals.getOrElseUpdate(v, LiveRangeBag.empty(v))
    }

    rpre.foreach(b => {
      log(s"Scanning Block ${b.id}")
      // Combine successor's liveIn as this block's liveOut.
      val live = b.cfgSuccessors.map(liveIn).foldRight(Graph.emptyIdentitySet[ValueNode])({ case (x, y) =>
        // Can't use union as the created HashSet is not an identity set.
        x.foreach(y += _)
        y
      })
      log(s"Live = $live")
      log(s"Intervals = $intervals")

      // Also add each successor's phi input.
      b.cfgSuccessors.foreach(s => {
        s.valuePhis.foreach(phi => {
          val nthBlock = phi.anchor.comingFrom.indexWhere(_ eq b.last)
          val phiUse = phi.composedInputs(nthBlock)
          live += phiUse
          log(s"Add phiUse $phiUse to live")
        })
      })

      // For each liveOut pessimistically assume it's not defined in this block.
      val (bFrom, bTo) = b.range
      live.foreach(opr => ensureInterval(opr).add(bFrom, bTo))

      // For each mid and last instruction, calculate their kill/gen.
      b.numberedInstrs.reverse.foreach({ case (ix, instr) =>
        outputs(instr).foreach(o => {
          log(s"$instr.output: $o, setFrom($ix)")
          // Def: kill the live range here.
          intervals(o).setFrom(ix)
          live -= o
        })
        instr.valueInputs.foreach(i => {
          // Use: gen a live range.
          ensureInterval(i).add(bFrom, ix)
          live += i
        })
      })

      // For each phi def in the block entry: kill the live range.
      b.valuePhis.foreach(phi => {
        live -= phi
      })

      // Special case: add loop begin's live in to loop end's live out.
      // Without this, a value that's defined before
      // the loop and only used after the loop will not be live in the loop body.
      if (b.isLoopBegin) {
        val loopEnd = b.first.asInstanceOf[LoopBeginNode].loopEnd
        val loopEndTo = g.blocks(loopEnd.belongsToBlock).instrIxEnd
        live.foreach(ensureInterval(_).add(bFrom, loopEndTo))
      }

      liveIns += (b.id -> live)
    })

    intervals
  }

  // It's also possible to build useposes together with the live ranges.
  // I choose to write this in a separate way for clarity.
  def buildUsePositions(g: TGraph, intervals: IntervalMap) = {
    // val vreg2Instr = mutable.Map.empty[Int, ValueNode]
    // val instr2Ix = Graph.emptyIdentityMap[ValueNode, Int]
    g.dfsIdom(b => {
      b.numberedInstrs.foreach({ case (ix, instr) =>
        outputs(instr).foreach(o => {
          intervals(o).firstRange.addUsePosition(ix)
        })
        instr.valueInputs.foreach(i => {
          intervals(i).firstRangeThatContains(ix).get.addUsePosition(ix)
        })
      })
      val (bFrom, _) = b.range
      b.valuePhis.foreach(phi => {
        intervals(phi).firstRange.addUsePosition(bFrom)
        // Phi inputs are used in the coming from block.
        phi.composedInputs.zip(phi.anchor.comingFrom).foreach({ case (v, end) =>
          val comingFrom = g.blocks(end.belongsToBlock)
          val (_, comingFromLast) = comingFrom.range
          intervals(v).firstRangeThatContains(comingFromLast).get.addUsePosition(comingFromLast)
        })
      })
    })
  }

  def outputs(n0: Node): Seq[ValueNode] = {
    n0 match {
      case n: ValueNode =>
        Seq(n)
      case exit: BaseBlockExitNode =>
        Seq()
      case begin: BaseBeginNode =>
        Seq()
      case _ =>
        sys.error(s"Unknown node: $n0")
    }
  }
}

case class Lsra(g: TGraph, mspec: MachineSpec, verbose: Boolean = false) extends RegProvider {
  // For now.
  var intervals: IntervalMap = _

  var unhandled: mutable.Queue[LiveRangeBag] = _
  val active = Graph.emptyIdentityMap[PReg, LiveRangeBag]
  val inactive = Graph.emptyIdentityMap[LiveRangeBag, PReg]
  val handled = Graph.emptyIdentityMap[LiveRangeBag, PReg]

  def log(s: String) = {
    if (verbose) {
      println(s)
    }
  }

  def pRegs = mspec.gpRegs

  def run() = {
    buildLiveness()
    lsraInternal()
  }

  def buildLiveness() = {
    intervals = Lsra.buildLiveness(g, log)
    Lsra.buildUsePositions(g, intervals)
    intervals
  }

  def printLiveness(): Unit = {
    println("Lsra.liveInterval:")
    intervals.toSeq.sortBy(_._1.id).foreach({ case (vreg, ranges) =>
      val moar = handled.get(ranges).map(r => s" ;; %${r.toString}").getOrElse("")
      println(s"  v${vreg.id}: $ranges$moar")
    })
  }

  override def pregFor(v: ValueNode): PReg = {
    handled(intervals(v))
  }

  def splitBefore(current: LiveRangeBag, regFreeUntil: Int) = {
    sys.error("Not implemented")
  }

  def spillAt(bag: LiveRangeBag, pos: Int): PReg = {
    sys.error("Not implemented")
  }

  def tryAllocateFreeReg(current: LiveRangeBag): Option[PReg] = {
    val freeUntilPos = mutable.Map(pRegs.zip(Stream.continually(Int.MaxValue)) : _*)

    active.foreach(act => {
      // Active intervals: can't allocate them.
      freeUntilPos += (act._1 -> 0)
    })

    inactive.foreach(ina => {
      // Inactive intervals might intersect with the current allocation.
      ina._1.firstIntersection(current).foreach(sect => {
        freeUntilPos += (ina._2 -> sect.from)
      })
    })

    // Selection heuristic: the most free reg.
    // We also use register hint when possible.
    if (current.definedBy.isInstanceOf[ValuePhiNode]) {

    }
    val (reg, regFreeUntil) = freeUntilPos.maxBy(_._2)
    if (regFreeUntil == 0) {
      // Failed.
      None
    } else if (current.endsBefore(regFreeUntil)) {
      // Available for the entire interval.
      Some(reg)
    } else {
      splitBefore(current, regFreeUntil)
      // Available for the first part.
      Some(reg)
    }
  }

  def allocateBlockedReg(current: LiveRangeBag): PReg = {
    val nextUsePos = mutable.Map(pRegs.zip(Stream.continually(Int.MaxValue)) : _*)
    val currentFrom = current.firstRange.from

    active.foreach(act => {
      nextUsePos += (act._1 -> act._2.nextUseAfter(currentFrom).get)
    })

    inactive.filter(_._1.intersects(current)).foreach(ina => {
      val newPos = ina._1.nextUseAfter(currentFrom).get
      val pos = nextUsePos.get(ina._2) match {
        case Some(oldPos) => newPos.min(oldPos)
        case None => newPos
      }
      nextUsePos += (ina._2 -> pos)
    })

    // The farthest use will be chosen as the victim.
    val (reg, usePos) = nextUsePos.maxBy(_._2)
    val currentFirstUse = current.firstRange.usePositions.min

    if (currentFirstUse > usePos) {
      // Current's first use is even farther - spill this instead.
      sys.error("Spill current: not implemented yet")
    } else {
      // Spill `reg`
      spillAt(active(reg), usePos)
    }
  }

  def lsraInternal(): Unit = {
    unhandled = intervals.values.toSeq.sortBy(_.firstRange)(ItemOrdering).to[mutable.Queue]

    // var nextSpillSlot = 1

    while (unhandled.nonEmpty) {
      val current = unhandled.dequeue()
      val position = current.firstRange.from

      log(s"Lsra: Handling $current")

      // Demote active intervals that are expired or temporarily inactive.
      active.toSeq.foreach(act => {
        if (act._2.endsBefore(position)) {
          log(s"Lsra: Done handling active $act")
          active -= act._1
          handled += act.swap
        } else if (act._2.doesNotCover(position)) {
          log(s"Lsra: Hole on $act")
          active -= act._1
          inactive += act.swap
        }
      })

      // Promote or demote inactive intervals.
      inactive.toSeq.foreach(ina => {
        if (ina._1.endsBefore(position)) {
          log(s"Lsra: Done handling inactive $ina")
          inactive -= ina._1
          handled += ina
        } else if (ina._1.covers(position)) {
          log(s"Lsra: Hole ends on $ina")
          inactive -= ina._1
          active += ina.swap
        }
      })

      // Done housekeeping intervals.
      tryAllocateFreeReg(current) match {
        case Some(r) =>
          log(s"Lsra: tryAlloc($current) gives $r")
          active += (r -> current)
        case None =>
          val r = allocateBlockedReg(current)
          log(s"Lsra: allocBlocked($current) gives $r")
          active += (r -> current)
      }
    }

    // All are handled. We might not have the chance to move some of the intervals to handled in the above loop
    // so we clear them here.
    active.foreach(handled += _.swap)
    active.clear()
    inactive.foreach(handled += _)
    inactive.clear()
  }
}
