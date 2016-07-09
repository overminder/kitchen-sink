package com.github.overmind.seaofnodes.backend.x64

import com.github.overmind.seaofnodes.backend.{Operand, Reg}

case class Mem(base: Reg, index: Option[Reg], scale: Option[Scale], disp: Int) extends Operand

object Mem {
  def addReg(lhs: Reg, rhs: Reg): Mem = {
    Mem(lhs, Some(rhs), Some(Scale1), 0)
  }

  def constIx(base: Reg, index: Int): Mem = {
    Mem(base, None, None, index)
  }
}

case class Imm(v: Int) extends Operand

sealed trait Scale {
  def asInt: Int = {
    this match {
      case Scale1 => 1
      case Scale2 => 2
      case Scale4 => 4
      case Scale8 => 8
    }
  }
}
case object Scale1 extends Scale
case object Scale2 extends Scale
case object Scale4 extends Scale
case object Scale8 extends Scale

sealed trait Label extends Operand
case class BlockLabel(i: Int) extends Label
case class SymbolLabel(s: String) extends Label

sealed trait Instr

sealed trait FirstInstr extends Instr
case class BlockStart(label: BlockLabel) extends FirstInstr
object BlockStart {
  def of(id: Int) = BlockStart(BlockLabel(id))
}

sealed trait MidInstr extends Instr

sealed trait SimpleOp {
  def shortName = getClass.getSimpleName.replace("$", "").toLowerCase
}
object SimpleOp {
  case object Add extends SimpleOp
  case object Lea extends SimpleOp
  case object Mov extends SimpleOp
  case object Sub extends SimpleOp
  case object Cmp extends SimpleOp
  case object Xchg extends SimpleOp
}

case class SimpleInstr(op: SimpleOp, dst: Operand, src: Operand) extends MidInstr

object Instr {
  import SimpleOp._

  def mov(dst: Mem, src: Reg) = SimpleInstr(Mov, dst, src)
  def mov(dst: Reg, src: Operand) = SimpleInstr(Mov, dst, src)

  def add(dst: Reg, src: Operand) = SimpleInstr(Add, dst, src)
  def add(dst: Mem, src: Reg) = SimpleInstr(Add, dst, src)

  def sub(dst: Mem, src: Reg) = SimpleInstr(Sub, dst, src)
  def sub(dst: Reg, src: Operand) = SimpleInstr(Sub, dst, src)

  def lea(dst: Reg, src: Mem) = SimpleInstr(Lea, dst, src)

  def cmp(dst: Mem, src: Reg) = SimpleInstr(Cmp, dst, src)
  def cmp(dst: Reg, src: Operand) = SimpleInstr(Cmp, dst, src)

  def xchg(dst: Reg, src: Reg) = SimpleInstr(Xchg, dst, src)
}

sealed trait Cond
object Cond {
  case object LT extends Cond
  case object GE extends Cond
}

sealed trait LastInstr extends Instr
case class Jcc(cond: Cond, t: BlockLabel, f: BlockLabel) extends LastInstr
case class Jmp(t: BlockLabel) extends LastInstr
case object Ret extends LastInstr
