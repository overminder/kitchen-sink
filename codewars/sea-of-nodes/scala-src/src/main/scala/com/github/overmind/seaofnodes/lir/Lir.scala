package com.github.overmind.seaofnodes.lir

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable

case class Graph(blocks: mutable.Map[Int, Block], entry: Int)
case class Block(id: Int, body: ArrayBuffer[Instr] = ArrayBuffer.empty, var exit: Branch = null)
// ^ Null is bad - will fix that later.

sealed trait Op

sealed trait Reg extends Op
case class VReg(id: Int) extends Reg
case class PReg(name: String) extends Reg

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

sealed trait Instr
case class Add(dst: Reg, src: Op) extends Instr
case class Lea(dst: Reg, src: Mem) extends Instr
case class Mov(dst: Reg, src: Op) extends Instr
case class Sub(dst: Reg, src: Op) extends Instr
case class Cmp(dst: Reg, src: Op) extends Instr

sealed trait Label extends Op
case class BlockLabel(i: Int) extends Label

sealed trait Branch
case class Jnz(t: Label, f: Label) extends Branch
case class Jmp(t: Label) extends Branch
case object Ret extends Branch
