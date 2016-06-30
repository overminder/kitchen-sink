package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.hir.Lsra.{IntervalMap, LiveRange}
import com.github.overmind.seaofnodes.hir.Trace.{TBlock, TGraph}
import com.github.overmind.seaofnodes.hir.nodes._

import scala.collection.{GenIterable, mutable}
import scala.collection.mutable.ArrayBuffer

object Lsra {
  type IntervalMap = mutable.Map[Int, LiveRange]

  object LiveRange {
    def empty = LiveRange(ArrayBuffer.empty)

    // Unfortunately O(N^2)..
    def mergeAll(newR: (Int, Int), oldRs: ArrayBuffer[(Int, Int)]): Unit = {
      val canMergeAt = oldRs.indexWhere(intersects(newR, _))
      if (canMergeAt >= 0) {
        val toMerge = oldRs.remove(canMergeAt)
        mergeAll(unionOf(newR, toMerge), oldRs)
      } else {
        oldRs += newR
        val sorted = oldRs.sorted
        oldRs.clear()
        oldRs ++= sorted
      }
    }

    def intersects(lhs: (Int, Int), rhs: (Int, Int)): Boolean = {
      if (lhs._2 < rhs._1 || rhs._2 < lhs._1) {
        false
      } else {
        true
      }
    }

    def unionOf(lhs: (Int, Int), rhs: (Int, Int)): (Int, Int) = {
      (lhs._1.min(rhs._1), lhs._2.max(rhs._2))
    }

    def intersectionOf(lhs: (Int, Int), rhs: (Int, Int)): (Int, Int) = {
      val res = (lhs._1.max(rhs._1), lhs._2.min(rhs._2))
      assert(res._1 < res._2)
      res
    }
  }

  case class LiveRange(ranges: ArrayBuffer[(Int, Int)]) {

    def endsBefore(position: Int): Boolean = {
      // Last range ends before this position. XXX: < or <=?
      ranges.last._2 <= position
    }

    def doesNotCover(position: Int): Boolean = !covers(position)
    def covers(position: Int): Boolean = {
      // XXX: Same question: < or <=?
      ranges.exists({ case (from, to) =>
        from <= position || position <= to
      })
    }

    def firstIntersection(other: LiveRange) = {
      // O(N^2) again!
      val product = for {
        x <- ranges
        y <- other.ranges
      } yield (x, y)
      product.find({ case (x, y) =>
        LiveRange.intersects(x, y)
      }).map((LiveRange.intersectionOf _).tupled)
    }

    def firstRange = ranges.head

    def add(newFrom: Int, newTo: Int, usePositions: Seq[Int] = Seq()): Unit = {
      sanityCheck(newFrom, newTo)
      LiveRange.mergeAll((newFrom, newTo), ranges)
    }

    def setFrom(newFrom: Int): Unit = {
      // Must always set the first one?
      assert(newFrom < ranges(0)._2)
      ranges(0) = ranges(0).copy(_1 = newFrom)
    }

    protected def sanityCheck(f: Int, t: Int) = {
      assert(f < t)
    }

    override def toString = {
      val body = ranges.map(_.toString).mkString(", ")
      s"LiveRange[$body]"
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
    val intervals = mutable.Map.empty[Int, LiveRange]
    def ensureInterval(id: Int) = {
      intervals.getOrElseUpdate(id, LiveRange.empty)
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
          ensureInterval(i.id).add(bFrom, ix, Seq(ix))
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
    intervals
  }

  def splitBefore(current: LiveRange, regFreeUntil: Int) = {

  }

  def lsra() = {
    val unhandled = intervals.values.toSeq.sortBy(_.firstRange).to[mutable.Queue]
    val active = Graph.emptyIdentityMap[LiveRange, PReg]
    val inactive = Graph.emptyIdentityMap[LiveRange, PReg]
    val handled = Graph.emptyIdentityMap[LiveRange, PReg]

    def tryAllocateFreeReg(current: LiveRange): Option[String] = {
      val freeUntilPos = mutable.Map(pRegs.zip(Stream.continually(Int.MaxValue)) : _*)

      active.foreach(act => {
        // Active intervals: can't allocate them.
        freeUntilPos += (act._2 -> 0)
      })

      inactive.foreach(ina => {
        // Inactive intervals might intersect with the current allocation.
        ina._1.firstIntersection(current).foreach(sect => {
          freeUntilPos += (ina._2 -> sect._1)
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

    def allocateBlockedReg(current: LiveRange) = {
      val nextUsePos = mutable.Map(pRegs.zip(Stream.continually(Int.MaxValue)) : _*)

      active.foreach(act => {
        // Active intervals: can't allocate them.
        nextUsePos += (act._2 -> 0)
      })
    }

    while (unhandled.nonEmpty) {
      val current = unhandled.dequeue()
      val position = current.firstRange._1

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
