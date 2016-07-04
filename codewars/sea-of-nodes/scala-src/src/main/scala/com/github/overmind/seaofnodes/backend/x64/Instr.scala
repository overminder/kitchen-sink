package com.github.overmind.seaofnodes.backend.x64

import com.github.overmind.seaofnodes.backend.{Op, Reg}

case class Mem(base: Reg, index: Reg, scale: Scale, disp: Int) extends Op

object Mem {
  def addReg(lhs: Reg, rhs: Reg): Mem = {
    Mem(lhs, rhs, Scale1, 0)
  }
}

case class Imm(v: Int) extends Op

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

sealed trait Label extends Op
case class BlockLabel(i: Int) extends Label
case class SymbolLabel(s: String) extends Label

sealed trait Instr

sealed trait FirstInstr extends Instr
case class BlockStart(label: BlockLabel) extends FirstInstr
object BlockStart {
  def of(id: Int) = BlockStart(BlockLabel(id))
}

sealed trait MidInstr extends Instr
sealed trait SimpleInstr extends Instr {
  def shortName = getClass.getSimpleName.toLowerCase
  def dst: Reg
  def src: Op
}
case class Add(dst: Reg, src: Op) extends MidInstr with SimpleInstr
case class Lea(dst: Reg, src: Mem) extends MidInstr with SimpleInstr
case class Mov(dst: Reg, src: Op) extends MidInstr with SimpleInstr
case class Sub(dst: Reg, src: Op) extends MidInstr with SimpleInstr
case class Cmp(dst: Reg, src: Op) extends MidInstr with SimpleInstr

sealed trait Cond
object Cond {
  case object LT extends Cond
  case object GE extends Cond
}

sealed trait LastInstr extends Instr
case class Jcc(cond: Cond, t: BlockLabel, f: BlockLabel) extends LastInstr
case class Jmp(t: BlockLabel) extends LastInstr
case object Ret extends LastInstr
