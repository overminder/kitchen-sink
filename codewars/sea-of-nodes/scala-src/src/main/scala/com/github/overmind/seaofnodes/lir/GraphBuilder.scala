package com.github.overmind.seaofnodes.lir

import scala.collection.mutable

import com.github.overmind.seaofnodes.hir
import com.github.overmind.seaofnodes.hir.nodes._

// HIR -> LIR: move out of sea-of-nodes form (read: SSA destruction and trivial scheduling)
// and do instruction selection.
// TODO: Better scheduling using dominator tree.
case class GraphBuilder(start: StartNode) {
  var nextVReg = 1
  val phi2Reg = hir.Graph.emptyIdentityMap[BasePhiNode, Reg]
  var currentBlock: Option[Block] = None
  val blocks = mutable.Map.empty[Int, Block]

  var entryBlock: Option[Int] = None
  val rax = PReg("rax")

  def build(): Graph = {
    go(start)
    Graph(blocks, entryBlock.get)
  }

  def go(n0: Node): Unit = {
    n0 match {
      case n: StartNode =>
        go(n.successor)
      case n: EndNode =>
        ()
      case n: RegionNode =>
        entryBlock = entryBlock.orElse(Some(n.id))
        hir.Graph.dfsRegion(n) { r =>
          currentBlock = Some(newBlock(r.id))
          r.composes.foreach(c => {
            // Compose the outgoing values.
            emitMov(c.phi, c.value)
          })
          goControl(r.exit)
        }

      case n =>
        sys.error(s"Shouldn't reach here: $n")
    }
  }

  def asReg(op: Op): Reg = {
    op match {
      case r: Reg => r
      case _ =>
        val r = newReg
        emit(Mov(r, op))
        r
    }
  }

  // Still this can generate multiple calculations for shared nodes... Need a way to lift this kind
  // of nodes to the dominator (am I right?).
  def goV(n0: ValueNode): Op = {
    n0 match {
      case LitNode(lval) =>
        Imm(lval.toInt)
      case AddNode(lhs, rhs) =>
        val r = newReg
        emit(Lea(r, Mem.addReg(asReg(goV(lhs)), asReg(goV(rhs)))))
        r
      case SubNode(lhs, rhs) =>
        val r = newReg
        emit(Mov(r, goV(lhs)))
        emit(Sub(r, goV(rhs)))
        r
      case phi: BasePhiNode =>
        regForPhi(phi)
      case _ =>
        sys.error(s"${n0.getClass.getName} should never be directly evaluated: $n0")
    }
  }

  def goCond(n0: LogicNode): Unit = {
    n0 match {
      case n: IsTruthyNode =>
        val v = goV(n.v)
        emit(Cmp(asReg(v), Imm(0)))
      case n: LessThanNode =>
        // Could also get some optimization when rhs is a reg.
        // Or we can also do this kind of canonicalization in HIR.
        emit(Cmp(asReg(goV(n.lhs)), goV(n.rhs)))
      case _ =>
        sys.error(s"${n0.getClass.getName} should never be directly evaluated: $n0")
    }
  }


  def goControl(c: ControlNode) {
    c match {
      case n: IfNode =>
        goCond(n.cond)
        emitBranch(Jnz(BlockLabel(n.t.id), BlockLabel(n.f.id)))

      case n: RetNode =>
        emit(Mov(rax, goV(n.value)))
        emitBranch(Ret)

      case r: RegionNode =>
        emitBranch(Jmp(BlockLabel(r.id)))

      case e: EndNode => ()

      case n =>
        sys.error(s"Shouldn't reach here: $n")
    }
  }

  def newBlock(id: Int): Block = {
    val b = Block(id)
    blocks += (id -> b)
    b
  }

  def newReg: Reg = {
    val r = VReg(nextVReg)
    nextVReg += 1
    r
  }

  def emitImm(i: Int): Reg = {
    val r = newReg
    emit(Mov(r, Imm(i)))
    r
  }

  def emit(i: Instr): Unit = {
    currentBlock.get.body += i
  }

  def emitBranch(value: Branch): Unit = {
    currentBlock.get.exit = value
  }

  def regForPhi(phi: BasePhiNode): Reg = {
    phi2Reg.getOrElseUpdate(phi, newReg)
  }

  // Special instruction selection cases for x86.
  def emitMov(dst: BasePhiNode, src: ValueNode): Unit = {
    src match {
      case AddNode(lhs, rhs) if lhs eq dst =>
        emit(Add(regForPhi(dst), goV(rhs)))

      case AddNode(lhs, rhs) if rhs eq dst =>
        emit(Add(regForPhi(dst), goV(lhs)))

      case SubNode(lhs, rhs) if lhs eq dst =>
        emit(Sub(regForPhi(dst), goV(rhs)))

      case _ =>
        emit(Mov(regForPhi(dst), goV(src)))
    }
  }
}
