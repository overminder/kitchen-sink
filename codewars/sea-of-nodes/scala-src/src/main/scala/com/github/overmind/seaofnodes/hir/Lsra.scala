package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.hir.Trace.{TBlock, TGraph}
import com.github.overmind.seaofnodes.hir.nodes._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

object Lsra {
  object LiveRange {
    // Unfortunately O(N^2)..
    def mergeAll(newR: (Int, Int), oldRs: ArrayBuffer[(Int, Int)]): Unit = {
      val canMergeAt = oldRs.indexWhere(canMerge(newR, _))
      if (canMergeAt >= 0) {
        val toMerge = oldRs.remove(canMergeAt)
        mergeAll(merge(newR, toMerge), oldRs)
      } else {
        oldRs += newR
      }
    }

    def canMerge(lhs: (Int, Int), rhs: (Int, Int)): Boolean = {
      if (lhs._2 < rhs._1 || rhs._2 < lhs._1) {
        false
      } else {
        true
      }
    }

    def merge(lhs: (Int, Int), rhs: (Int, Int)): (Int, Int) = {
      (lhs._1.min(rhs._1), lhs._2.max(rhs._2))
    }
  }

  case class LiveRange(var from: Int, var to: Int) {
    sanityCheck(from, to)

    def add(newFrom: Int, newTo: Int): Unit = {
      sanityCheck(newFrom, newTo)
      // Must be mergable?
      val merged = LiveRange.merge((from, to), (newFrom, newTo))
      from = merged._1
      to = merged._2
    }

    protected def sanityCheck(f: Int, t: Int) = {
      assert(f < t)
    }
  }

  object Liveness {
    def build(g: TGraph) = {
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
      def ensureInterval(id: Int, from: Int, to: Int) = {
        intervals.get(id) match {
          case Some(i) =>
            println(s"Add ($id -> $from, $to) to $i")
            i.add(from, to)
          case None =>
            intervals += (id -> LiveRange(from, to))
        }
      }

      rpre.foreach(b => {
        println(s"Scanning Block ${b.id}")
        // Calculate live out
        var live = b.cfgSuccessors.map(liveIn).foldRight(Set.empty[Int])(_ union _)
        println(s"Live = $live")
        println(s"Intervals = $intervals")

        // Also add each successor's phi input
        b.cfgSuccessors.foreach(s => {
          s.valuePhis.foreach(phi => {
            val nthBlock = phi.anchor.comingFrom.indexWhere(_ eq b.last)
            val phiUse = phi.composedInputs(nthBlock).id
            live += phiUse
            println(s"Add phiUse $phiUse to live")
          })
        })

        // Build initial live range for each operand.
        val (bFrom, bTo) = b.range
        live.foreach(opr => ensureInterval(opr, bFrom, bTo))

        b.numberedInstrs.reverse.foreach({ case (ix, instr) =>
          outputs(instr).foreach(o => {
            // Def: cut the live range here.
            intervals(o.id).from = ix
            live -= o.id
          })
          instr.valueInputs.foreach(i => {
            // Use: extend the live range.
            ensureInterval(i.id, bFrom, ix)
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
          live.foreach(ensureInterval(_, bFrom, loopEndTo))
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
}
