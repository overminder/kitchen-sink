package com.github.overmind.seaofnodes.backend.x64

import com.github.overmind.seaofnodes.backend.{MachineSpec, PReg, RegProvider}
import com.github.overmind.seaofnodes.hir.Trace.{TBlock, TGraph}
import com.github.overmind.seaofnodes.hir.nodes._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

case object X64Arch extends MachineSpec {
  val regNames = "rax rcx rbx rdx rdi rsi rbp rsp r8 r9 r10 r11 r12 r13 r14 r15".split(' ')
  override val gpRegs: IndexedSeq[PReg] = ((0 to 5) ++ (8 +: (10 to 15))).map(PReg(_))
  override val scratch = PReg(10)

  override def showReg(r: PReg): String = {
    regNames(r.id)
  }
}

// Let's do it in a simple way for now.
case class ISel(rp: RegProvider, mspec: MachineSpec) {
  def emitBlock(b: TBlock): Seq[Instr] = {
    emitNodes(b.instrs.reverse.toList).reverse
  }

  def emitGraph(g: TGraph): Seq[Instr] = {
    val xs = ArrayBuffer.empty[Instr]
    g.dfsIdom(xs ++= emitBlock(_))
    xs
  }

  def emitNodes(ns: List[Node]): Seq[Instr] = {
    ns match {
      case List() =>
        Seq()
      case (n: BaseBeginNode) :: rest =>
        BlockStart.of(n.id) +: emitNodes(rest)
      case (n: IfNode) :: LessThanNode(v1, v2) :: rest =>
        Seq(Jnz(b(n.t), b(n.f)), Cmp(r(v1), r(v2))) ++ emitNodes(rest)
      case (n: BaseEndNode) :: rest =>
        val succ = n.cfgSuccessor
        val phiMoves = succ match {
          case m: BaseMergeNode =>
            val endIx = m.comingFrom.indexWhere(_ eq n)
            val srcDsts = m.valuePhis.map(phi => {
              (r(phi.composedInputs(endIx)), r(phi))
            })
            // Parallel move.
            val orderedDstSrcs = orderWindmill(srcDsts, mspec.scratch)
            orderedDstSrcs.map(Mov.tupled)
          case _ =>
            Seq()
        }
        Jmp(b(n.cfgSuccessor)) +: (phiMoves ++ emitNodes(rest))
      case (n: RetNode) :: rest =>
        Seq(Ret, Mov(PReg(0), r(n.value))) ++ emitNodes(rest)
      case (v: ValueNode) :: rest =>
        emitNode(v).reverse ++ emitNodes(rest)
      case _ =>
        sys.error(s"Unhandled nodes: ${ns.take(3)}")
    }
  }

  // See http://gallium.inria.fr/~xleroy/publi/parallel-move.pdf.
  def orderWindmill(srcDsts: Seq[(PReg, PReg)], scratch: PReg): Seq[(PReg, PReg)] = {
    // Basically a toposort followed by a SCC elimination.
    val moves = mutable.Map(srcDsts: _*)
    val out = ArrayBuffer.empty[(PReg, PReg)]
    var done = false
    while (!done) {
      val blades = moves.filter({ case (src, dst) =>
        !moves.contains(dst)
      })
      if (blades.nonEmpty) {
        out ++= blades
        moves --= blades.keys
      } else {
        // Axles (SCC) residue.
        def sccChain(start: PReg): Seq[(PReg, PReg)] = {
          var iter = start
          val chain = ArrayBuffer.empty[(PReg, PReg)]
          do {
            val dst = moves(iter)
            chain += (iter -> dst)
            iter = dst
          } while (iter ne start)
          println(s"sccChain = $chain")
          chain
        }

        val (fstSrc, fstDst) = moves.head
        out += (fstDst -> scratch)
        out ++= sccChain(fstDst).tail
        out += (scratch -> fstSrc)
        done = true
      }
    }
    out
  }

  // In the correct order.
  def emitNode(v: ValueNode): Seq[Instr] = {
    v match {
      case AddNode(v1, v2) =>
        Seq(Lea(r(v), Mem.addReg(r(v1), r(v2))))
      case SubNode(v1, v2) =>
        Seq(Mov(r(v), r(v1)), Sub(r(v), r(v2)))
      case LitLongNode(imm) =>
        Seq(Mov(r(v), Imm(imm.toInt)))
      case _ =>
        sys.error(s"Unhandled node: $v")
    }
  }

  def r(v: ValueNode): PReg = {
    PReg(rp.pregFor(v).id)
  }

  def b(n: BaseBeginNode): BlockLabel = {
    BlockLabel(n.id)
  }
}
