package com.github.overmind.seaofnodes.backend.x64

import com.github.overmind.seaofnodes.backend.{MachineSpec, Operand, PReg}

case class Gas(arch: MachineSpec) {
  def instrs(is: Seq[Instr]): String = {
    is.map(instr).mkString("\n")
  }
  def instr(i: Instr): String = {
    i match {
      case BlockStart(label) =>
        s"${blockLabel(label)}:"
      case mid: MidInstr =>
        s"\t${midInstr(mid)}"
      case last: LastInstr =>
        s"\t${lastInstr(last)}"
    }
  }

  def midInstr(m: MidInstr): String = {
    m match {
      case s: SimpleInstr =>
        s"${s.op.shortName} ${op(s.src)}, ${op(s.dst)}"
    }
  }

  def lastInstr(i: LastInstr): String = {
    i match {
      case Jcc(c, t, f) =>
        s"j${cond(c)} ${blockLabel(f)}"
      case Jmp(to) =>
        s"jmp ${blockLabel(to)}"
      case Ret =>
        "ret"
    }
  }

  def blockLabel(label: BlockLabel): String = {
    s".LB_${label.i}"
  }

  def opWithComma(o: Option[Operand]): String = {
    o.map("," + op(_)).getOrElse("")
  }

  def scale(o: Option[Scale]): String = {
    o.map("," + _.asInt.toString).getOrElse("")
  }

  def op(o: Operand): String = {
    o match {
      case r: PReg =>
        arch.showReg(r)
      case m: Mem =>
        s"${m.disp}(${op(m.base)}${opWithComma(m.index)}${scale(m.scale)})"
      case i: Imm =>
        s"$$${i.v}"
      case label: BlockLabel =>
        s"$$${blockLabel(label)}"
    }
  }

  def cond(c: Cond): String = {
    c match {
      case Cond.GE =>
        "ge"
      case Cond.LT =>
        "l"
    }
  }
}
