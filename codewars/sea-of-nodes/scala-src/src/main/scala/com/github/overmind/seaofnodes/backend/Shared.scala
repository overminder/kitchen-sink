package com.github.overmind.seaofnodes.backend

import com.github.overmind.seaofnodes.hir.nodes.{RegAllocNode, ValueNode}

trait Operand
trait Reg extends Operand
case class PReg(id: Int) extends Reg

trait MachineSpec {
  def scratch: PReg
  def gpRegs: Seq[PReg]
  def showReg(r: PReg): String
}

object MachineSpec {
}

trait RegProvider {
  def pregFor(v: ValueNode): PReg
  def spillRestoreInstrs: Seq[(Int, RegAllocNode)]
}
