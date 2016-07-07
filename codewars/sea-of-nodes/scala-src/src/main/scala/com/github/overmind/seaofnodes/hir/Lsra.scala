package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.backend.{MachineSpec, PReg, RegProvider}
import com.github.overmind.seaofnodes.hir.Lsra._
import com.github.overmind.seaofnodes.hir.Linearize.{TBlock, TGraph}
import com.github.overmind.seaofnodes.hir.nodes._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

object Lsra {
  type IntervalMap = mutable.Map[ValueNode, Interval]

  case class Interval(definedBy: ValueNode,
                      ranges: mutable.SortedSet[RangePair], usePositions: mutable.SortedSet[UsePosition],
                      children: ArrayBuffer[Interval], parent: Option[Interval]) extends Ordered[Interval] {

    var reg: Option[PReg] = None
    var spillSlot: Option[Int] = None
    var spillInstr: Option[SpillNode] = None

    def spillRestoreInstrs = {
      val res = ArrayBuffer.empty[(Int, RegAllocNode)]
      definedBy match {
        case r: RestoreNode =>
          res += (firstRange.from -> r)
        case _ =>
          ()
      }
      spillInstr.foreach(s => {
        res += (lastRange.to -> s)
      })
      res
    }

    def toplevel = parent.getOrElse(this)

    def firstRange = ranges.head
    def lastRange = ranges.last

    def firstRangeThatContains(pos: Int): Option[RangePair] = {
      ranges.find(_.contains(pos))
    }

    def covers(pos: Int): Boolean = {
      firstRangeThatContains(pos).isDefined
    }

    def endsBefore(pos: Int): Boolean = {
      // Last range ends before this position.
      range.endsBefore(pos)
    }

    def nextUseAfter(pos: Int): Option[UsePosition] = {
      usePositions.iteratorFrom(UsePosition(pos + 1)).toStream.headOption
    }

    def prevUseBefore(pos: Int): Option[UsePosition] = {
      usePositions.range(usePositions.head, UsePosition(pos)).lastOption
    }

    def intersects(other: Interval): Boolean = {
      firstIntersection(other).nonEmpty
    }

    def firstIntersection(other: Interval): Option[RangePair] = {
      ranges.flatMap(_.firstIntersection(other.ranges)).headOption
    }

    def range: RangePair = {
      RangePair(ranges.head.from, ranges.last.to)
    }

    def addUsePosition(pos: UsePosition): Unit = {
      usePositions += pos
    }

    def addUsePosition(ix: Int): Unit = {
      addUsePosition(UsePosition(ix))
    }

    def add(from: Int, to: Int): Unit = {
      RangePair(from, to).mergeAll(ranges)
    }

    def setFrom(newFrom: Int): Unit = {
      // Must always set the first one?
      val r0 = firstRange
      assert(newFrom < r0.to)
      ranges.remove(r0)
      ranges += r0.copy(from = newFrom)
    }

    def spillAt(pos: Int, spillInstr: SpillNode, restoreInstr: RestoreNode): Interval = {
      val prevUse = prevUseBefore(pos).get.ix
      val nextUse = nextUseAfter(pos).get.ix
      this.spillInstr = Some(spillInstr)
      spiltBetween(prevUse + 1, nextUse - 1, restoreInstr)
    }

    def spiltBetween(from: Int, to: Int, restoreInstr: RestoreNode): Interval = {
      val spill = ranges.find(_.adjoins(from)).get
      val restore = ranges.find(_.adjoins(to)).get
      assert(spill eq restore)

      // Split ranges
      val rhsRanges = ranges.iteratorFrom(spill).to[mutable.SortedSet]
      ranges --= rhsRanges
      ranges ++= RangePair.mightBeEmpty(spill.from, from)
      rhsRanges -= spill
      rhsRanges ++= RangePair.mightBeEmpty(to, spill.to)

      // Split usePoses
      val rhsPoses = usePositions.iteratorFrom(UsePosition(from)).to[mutable.SortedSet]
      usePositions --= rhsPoses

      // Link tree
      val child = Interval(restoreInstr, rhsRanges, usePositions, ArrayBuffer.empty, Some(toplevel))
      toplevel.children += child
      child
    }

    override def toString = {
      val rgs = ranges.map(p => s"${p.from}:${p.to}").mkString(", ")
      s"Interval[($rgs) @ {${usePositions.map(_.ix).mkString(", ")}})"
    }

    override def compare(that: Interval): Int = {
      firstRange.compare(that.firstRange)
    }
  }

  object Interval {
    def empty(v: ValueNode) = Interval(definedBy = v,
      ranges = mutable.SortedSet.empty[RangePair],
      usePositions = mutable.SortedSet.empty[UsePosition],
      children = ArrayBuffer.empty, parent = None)
  }

  object RangePair {
    def mightBeEmpty(from: Int, to: Int): Option[RangePair] = {
      if (from == to) {
        None
      } else {
        Some(RangePair(from, to))
      }
    }
  }

  // [from, to)
  case class RangePair(from: Int, to: Int) extends Ordered[RangePair] {
    assert(from < to, s"RangePair($from, $to)")

    def contains(p: Int): Boolean = {
      from <= p && p < to
    }

    def startsAfter(pos: Int): Boolean = {
      pos < from
    }

    def endsBefore(pos: Int): Boolean = {
      to <= pos
    }

    def adjoins(pos: Int): Boolean = {
      if (pos < from || to < pos) {
        false
      } else {
        true
      }
    }

    def adjoins(other: RangePair): Boolean = {
      if (to < other.from || other.to < from) {
        false
      } else {
        true
      }
    }

    def intersects(other: RangePair): Boolean = {
      if (to <= other.from || other.to <= from) {
        false
      } else {
        true
      }
    }

    def firstIntersection(other: Iterable[RangePair]): Option[RangePair] =
      other.find(intersects).map(intersectionWith)

    def unionWith(other: RangePair): RangePair = {
      RangePair(from.min(other.from), to.max(other.to))
    }

    def intersectionWith(other: RangePair): RangePair = {
      RangePair(from.max(other.from), to.min(other.to))
    }

    def mergeAll(rs: mutable.SortedSet[RangePair]): Unit = {
      rs.find(adjoins) match {
        case Some(toMerge) =>
          rs.remove(toMerge)
          unionWith(toMerge).mergeAll(rs)
        case None =>
          rs += this
      }
    }

    override def compare(that: RangePair): Int = {
      Ordering.Tuple2[Int, Int].compare((from, to), (that.from, that.to))
    }
  }

  case class UsePosition(ix: Int, mustBeInReg: Boolean = true) extends Ordered[UsePosition] {
    override def compare(that: UsePosition): Int = {
      ix.compare(that.ix)
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
    val intervals = Graph.emptyIdentityMap[ValueNode, Interval]
    def ensureInterval(v: ValueNode) = {
      intervals.getOrElseUpdate(v, Interval.empty(v))
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
          intervals(o).addUsePosition(ix)
        })
        instr.valueInputs.foreach(i => {
          intervals(i).addUsePosition(ix)
        })
      })
      val (bFrom, _) = b.range
      b.valuePhis.foreach(phi => {
        intervals(phi).addUsePosition(bFrom)
        // Phi inputs are used in the coming from block.
        phi.composedInputs.zip(phi.anchor.comingFrom).foreach({ case (v, end) =>
          val comingFrom = g.blocks(end.belongsToBlock)
          val (_, comingFromLast) = comingFrom.range
          intervals(v).addUsePosition(comingFromLast)
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

case class Lsra(g: TGraph, arch: MachineSpec, verbose: Boolean = false) extends RegProvider {
  // For now.
  var intervals: IntervalMap = _

  var unhandled: mutable.SortedSet[Interval] = _
  val active = Graph.emptyIdentityMap[PReg, Interval]
  val inactive = Graph.emptyIdentitySet[Interval]
  val handled = Graph.emptyIdentitySet[Interval]
  var nextSpillSlot = 1

  def log(s: String) = {
    if (verbose) {
      println(s)
    }
  }

  def spillRestorePair(i: Interval): (SpillNode, RestoreNode) = {
    val v = i.definedBy
    val slot = i.toplevel.spillSlot.getOrElse({
      val ix = nextSpillSlot
      nextSpillSlot += 1
      ix
    })
    (SpillNode(slot, v), RestoreNode(slot))
  }

  def pRegs = arch.gpRegs

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
    def go(itv: Interval): Unit = {
      val vreg = itv.definedBy
      val moar = itv.reg.map(r => s" ;; ${arch.showReg(r)}").getOrElse("")
      println(s"  v${vreg.id}: $itv$moar")
      itv.spillRestoreInstrs.foreach({
        case (ix, v: SpillNode) =>
          println(s"  * $ix: Spill v${arch.showReg(itv.reg.get)} -> Stack[${v.ix}]")
        case (ix, v: RestoreNode) =>
          println(s"  * $ix: Restore v${arch.showReg(itv.reg.get)} <- Stack[${v.ix}]")
      })
    }
    intervals.toSeq.sortBy(_._1.id).foreach({ case (_, itv) => go(itv) })
  }

  override def pregFor(v: ValueNode): PReg = {
    // log(s"pregFor($v) -> ${intervals(v)}")
    intervals(v).reg.get
  }

  override def spillRestoreInstrs: Seq[(Int, RegAllocNode)] = {
    intervals.values.flatMap(_.spillRestoreInstrs).to
  }

  def splitBefore(interval: Interval, regFreeUntil: Int) = {
    sys.error("Not implemented")
  }

  def tryAllocateFreeReg(current: Interval): Option[PReg] = {
    val freeUntilPos = mutable.Map(pRegs.zip(Stream.continually(Int.MaxValue)) : _*)

    active.foreach(act => {
      // Active intervals: can't allocate them.
      freeUntilPos += (act._1 -> 0)
    })

    inactive.foreach(ina => {
      // Inactive intervals might intersect with the current allocation.
      ina.firstIntersection(current).foreach(sect => {
        freeUntilPos += (ina.reg.get -> sect.from)
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
      current.reg = Some(reg)
      // Available for the entire interval.
      Some(reg)
    } else {
      splitBefore(current, regFreeUntil)
      // Available for the first part.
      current.reg = Some(reg)
      Some(reg)
    }
  }

  def allocateBlockedReg(current: Interval): PReg = {
    val nextUsePos = mutable.Map(pRegs.zip(Stream.continually(Int.MaxValue)) : _*)
    val currentFrom = current.firstRange.from

    active.foreach(act => {
      nextUsePos += (act._1 -> act._2.nextUseAfter(currentFrom).get.ix)
    })

    inactive.filter(_.intersects(current)).foreach(ina => {
      val newPos = ina.nextUseAfter(currentFrom).get
      val pos = nextUsePos.get(ina.reg.get) match {
        case Some(oldPos) => newPos.ix.min(oldPos)
        case None => newPos.ix
      }
      nextUsePos += (ina.reg.get -> pos)
    })

    // The farthest use will be chosen as the victim.
    val (reg, usePos) = nextUsePos.maxBy(_._2)
    val currentFirstUse = current.usePositions.head

    if (currentFirstUse.ix > usePos) {
      // Current's first use is even farther - spill this instead.
      sys.error("Spill current: not implemented yet")
    } else {
      // Spill `reg`
      val victim = active.remove(reg).get
      val spillPos = currentFirstUse
      log(s"SpillAt($spillPos): victim = $victim")
      val (spillInstr, restoreInstr) = spillRestorePair(victim)
      val laterPart = victim.spillAt(spillPos.ix, spillInstr, restoreInstr)
      log(s"Spilling: become $victim + $laterPart")
      handled += victim
      unhandled += laterPart
      intervals += (laterPart.definedBy -> laterPart)
      current.reg = Some(reg)
      reg
    }
  }

  def lsraInternal(): Unit = {
    unhandled = intervals.values.to

    while (unhandled.nonEmpty) {
      val current = unhandled.head
      unhandled.remove(current)
      val position = current.firstRange.from

      log(s"Lsra: Handling $current")

      // Demote active intervals that are expired or temporarily inactive.
      active.toSeq.foreach(act => {
        if (act._2.endsBefore(position)) {
          log(s"Lsra: Done handling active $act")
          active -= act._1
          handled += act._2
        } else if (!act._2.covers(position)) {
          log(s"Lsra: Hole on $act")
          active -= act._1
          inactive += act._2
        }
      })

      // Promote or demote inactive intervals.
      inactive.toSeq.foreach(ina => {
        if (ina.endsBefore(position)) {
          log(s"Lsra: Done handling inactive $ina")
          inactive -= ina
          handled += ina
        } else if (ina.covers(position)) {
          log(s"Lsra: Hole ends on $ina")
          inactive -= ina
          active += (ina.reg.get -> ina)
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
    active.foreach(handled += _._2)
    active.clear()
    inactive.foreach(handled += _)
    inactive.clear()
  }
}
