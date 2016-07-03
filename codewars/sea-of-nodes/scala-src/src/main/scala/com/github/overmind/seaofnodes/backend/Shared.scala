package com.github.overmind.seaofnodes.backend

import com.github.overmind.seaofnodes.hir.nodes.ValueNode

trait Op
trait Reg extends Op
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
}
