package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.hir.Trace.{TBlock, TGraph}
import com.github.overmind.seaofnodes.hir.nodes._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

import Lsra._
import LiveRangeBag.ItemOrdering

object Lsra {
  type IntervalMap = mutable.Map[Int, LiveRangeBag]

  import LiveRangeBag._

  object LiveRangeBag {
    def empty = LiveRangeBag(ArrayBuffer.empty)

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

  case class LiveRangeBag(ranges: ArrayBuffer[LiveRangeBag.Item]) {

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
      product
        .find({ case (x, y) => x.intersects(y) })
        .isDefined
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
    val liveIns = mutable.Map.empty[Int, Set[Int]]
    def liveIn(b: TBlock): Set[Int] = {
      liveIns.getOrElseUpdate(b.id, Set.empty)
    }

    // VReg -> LiveRange
    val intervals = mutable.Map.empty[Int, LiveRangeBag]
    def ensureInterval(vreg: Int) = {
      intervals.getOrElseUpdate(vreg, LiveRangeBag.empty)
    }

    rpre.foreach(b => {
      log(s"Scanning Block ${b.id}")
      // Calculate live out
      var live = b.cfgSuccessors.map(liveIn).foldRight(Set.empty[Int])(_ union _)
      log(s"Live = $live")
      log(s"Intervals = $intervals")

      // Also add each successor's phi input
      b.cfgSuccessors.foreach(s => {
        s.valuePhis.foreach(phi => {
          val nthBlock = phi.anchor.comingFrom.indexWhere(_ eq b.last)
          val phiUse = phi.composedInputs(nthBlock).id
          live += phiUse
          log(s"Add phiUse $phiUse to live")
        })
      })

      // Build initial live range for each operand.
      val (bFrom, bTo) = b.range
      live.foreach(opr => ensureInterval(opr).add(bFrom, bTo))

      b.numberedInstrs.reverse.foreach({ case (ix, instr) =>
        outputs(instr).foreach(o => {
          log(s"$instr.output: $o, setFrom($ix)")
          // Def: cut the live range here.
          intervals(o.id).setFrom(ix)
          live -= o.id
        })
        instr.valueInputs.foreach(i => {
          // Use: extend the live range.
          ensureInterval(i.id).add(bFrom, ix)
          live += i.id
        })
      })

      // Phi def: kill the live in
      b.valuePhis.foreach(phi => {
        live -= phi.id
      })

      // Special case: add loop begin's live in to loop end's live out?
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
          intervals(o.id).firstRange.addUsePosition(ix)
        })
        instr.valueInputs.foreach(i => {
          intervals(i.id).firstRangeThatContains(ix).get.addUsePosition(ix)
        })
      })
      val (bFrom, bTo) = b.range
      b.valuePhis.foreach(phi => {
        intervals(phi.id).firstRange.addUsePosition(bFrom)
        // Phi inputs are used in the coming from block.
        phi.composedInputs.zip(phi.anchor.comingFrom).foreach({ case (v, end) =>
          val comingFrom = g.blocks(end.belongsToBlock)
          val (_, comingFromLast) = comingFrom.range
          intervals(v.id).firstRangeThatContains(comingFromLast).get.addUsePosition(comingFromLast)
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

case class Lsra(g: TGraph, verbose: Boolean = false) {
  // For now.
  type PReg = String

  var intervals: IntervalMap = _

  val pRegs = Seq("rax", "rbx", "rcx", "rdx", "rdi", "rsi", "r8", "r9")

  def log(s: String) = {
    if (verbose) {
      println(s)
    }
  }

  def buildLiveness() = {
    intervals = Lsra.buildLiveness(g, log)
    Lsra.buildUsePositions(g, intervals)
    intervals
  }

  def splitBefore(current: LiveRangeBag, regFreeUntil: Int) = {

  }

  def lsra() = {
    val unhandled = intervals.values.toSeq.sortBy(_.firstRange)(ItemOrdering).to[mutable.Queue]
    val active = Graph.emptyIdentityMap[LiveRangeBag, PReg]
    val inactive = Graph.emptyIdentityMap[LiveRangeBag, PReg]
    val handled = Graph.emptyIdentityMap[LiveRangeBag, PReg]

    var nextSpillSlot = 1
    val spills =

    def tryAllocateFreeReg(current: LiveRangeBag): Option[String] = {
      val freeUntilPos = mutable.Map(pRegs.zip(Stream.continually(Int.MaxValue)) : _*)

      active.foreach(act => {
        // Active intervals: can't allocate them.
        freeUntilPos += (act._2 -> 0)
      })

      inactive.foreach(ina => {
        // Inactive intervals might intersect with the current allocation.
        ina._1.firstIntersection(current).foreach(sect => {
          freeUntilPos += (ina._2 -> sect.from)
        })
      })

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

    def allocateBlockedReg(current: LiveRangeBag) = {
      val nextUsePos = mutable.Map(pRegs.zip(Stream.continually(Int.MaxValue)) : _*)
      val currentFrom = current.firstRange.from

      active.foreach(act => {
        nextUsePos += (act._2 -> act._1.nextUseAfter(currentFrom).get)
      })

      inactive.filter(_._1.intersects(current)).foreach(ina => {
        nextUsePos += (ina._2 -> ina._1.nextUseAfter(currentFrom).get)
      })

      // The farthest use will be chosen as the victim.
      val (reg, usePos) = nextUsePos.maxBy(_._2)
      val currentFirstUse = current.firstRange.usePositions.min

      if (currentFirstUse > usePos) {
        // Current's first use is even farther - spill this instead.
        nextSpillSlot
      } else {
        // Spill `reg`
      }
    }

    while (unhandled.nonEmpty) {
      val current = unhandled.dequeue()
      val position = current.firstRange.from

      // Demote active intervals that are expired or temporarily inactive.
      active.toSeq.foreach(act => {
        if (act._1.endsBefore(position)) {
          active -= act._1
          handled += act
        } else if (act._1.doesNotCover(position)) {
          active -= act._1
          inactive += act
        }
      })

      // Promote or demote inactive intervals.
      inactive.toSeq.foreach(ina => {
        if (ina._1.endsBefore(position)) {
          inactive -= ina._1
          handled += ina
        } else if (ina._1.covers(position)) {
          inactive -= ina._1
          active += ina
        }
      })

      // Done housekeeping intervals.
      tryAllocateFreeReg(current)
    }
  }
}
