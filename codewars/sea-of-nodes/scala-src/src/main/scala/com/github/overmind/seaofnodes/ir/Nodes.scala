package com.github.overmind.seaofnodes.ir

import scala.collection.mutable.ArrayBuffer

sealed trait Node {
  type Edges[A] = ArrayBuffer[A]
  val uses: Edges[Node] = ArrayBuffer.empty
  val inputs: Edges[Node] = ArrayBuffer.empty

  def toShallowString: String
  override def toString: String = toShallowString

  def adaptInput[N <: Node](input: N): N = {
    adaptEdgeTo(inputs, input)
    input.adaptEdgeTo(input.uses, this)
    input
  }

  def removeInput(input: Node): Unit = {
    removeEdgeTo(inputs, input)
    input.removeEdgeTo(input.uses, this)
  }

  def replaceInput[N <: Node](oldInput: N, newInput: N): N = {
    removeInput(oldInput)
    adaptInput(newInput)
  }

  def replaceOrAdaptInput[N <: Node](oldInput: Option[N], newInput: Option[N]): Option[N] = {
    oldInput.foreach(removeInput)
    newInput.foreach(adaptInput)
    newInput
  }

  protected def adaptEdgeTo[A <: AnyRef](edges: Edges[A], to: A): Unit = {
    val ix = indexOfByRef(edges, to)
    if (ix < 0) {
      // Doesn't exist
      edges += to
    }
  }

  protected def removeEdgeTo[A <: AnyRef](edges: Edges[A], to: A): Unit = {
    val ix = indexOfByRef(edges, to)
    if (ix < 0) {
      // Doesn't exist
      edges.remove(ix)
    }
  }

  protected def indexOfByRef[A <: AnyRef](xs: Seq[A], to: A): Int = {
    xs.indexWhere(to.eq)
  }
}

sealed trait ValueNode extends Node
sealed trait LogicNode extends ValueNode
sealed trait ControlNode extends Node {
  val predecessors: Edges[ControlNode] = ArrayBuffer.empty
  val successors: Edges[ControlNode] = ArrayBuffer.empty

  def adaptSuccessor[N <: ControlNode](successor: N): N = {
    successor.adaptEdgeTo(successor.predecessors, this)
    adaptEdgeTo(successors, successor)
    successor
  }

  def removeSuccessor(successor: ControlNode): Unit = {
    removeEdgeTo(successors, successor)
    successor.removeEdgeTo(successor.predecessors, this)
  }

  def replaceOrAdaptSuccessor[N <: ControlNode](oldSucc: Option[N], newSucc: Option[N]): Option[N] = {
    oldSucc.foreach(removeSuccessor)
    newSucc.foreach(adaptSuccessor)
    newSucc
  }

  def replaceSuccessor[N <: ControlNode](oldSucc: N, newSucc: N): N = {
    removeSuccessor(oldSucc)
    adaptSuccessor(newSucc)
  }
}

case class StartNode(protected var _successor: ControlNode) extends ControlNode {
  adaptSuccessor(_successor)

  def successor = _successor
  def successor_=(newSucc: ControlNode) = {
    _successor = replaceSuccessor(_successor, newSucc)
  }

  override def toShallowString: String = "Start"
}

case class EndNode() extends ControlNode {
  override def toShallowString: String = "End"
}

object RegionNode {
  type Id = Int
}
case class RegionNode(id: RegionNode.Id) extends ControlNode {
  var _exit: Option[ControlNode] = None

  override def toShallowString: String = s"RegionNode $id"

  override def toString: String =
    s"$toShallowString succs: ${ShallowRegionBuilder.exits(this).map(_.toShallowString)}" +
      s" preds: ${ShallowRegionBuilder.preds(this).map(_.toShallowString)}"

  def exit: ControlNode = _exit.get  // Unsafe
  def exit_=(newExit: ControlNode): Unit = {
    _exit = replaceOrAdaptSuccessor(_exit, Some(newExit))
  }
}

case class RetNode() extends ControlNode {
  private var _value: Option[ValueNode] = None

  override def toShallowString: String = s"Ret"

  def value: ValueNode = _value.get  // Unsafe
  def value_=(newValue: ValueNode): Unit = {
    _value = replaceOrAdaptInput(_value, Some(newValue))
  }
}

case class IfNode(private var _t: RegionNode, private var _f: RegionNode) extends ControlNode {
  private var _cond: Option[LogicNode] = None

  adaptSuccessor(_t)
  adaptSuccessor(_f)

  override def toShallowString: String = s"If"

  def region = predecessors(0).asInstanceOf[RegionNode]

  def cond = _cond.get
  def cond_=(newCond: LogicNode) = {
    _cond = replaceOrAdaptInput(_cond, Some(newCond))
  }
  def t = _t
  def t_=(newT: RegionNode) = _t = replaceSuccessor(_t, newT)
  def f = _f
  def f_=(newF: RegionNode) = _f = replaceSuccessor(_f, newF)
}

case class LitNode(v: Long) extends ValueNode {
  def toShallowString: String = s"Lit $v"
}

sealed trait UnaryNode extends ValueNode {
  protected var _v: ValueNode
  adaptInput(_v)
}
sealed trait BinaryNode extends ValueNode {
  protected var _lhs: ValueNode
  protected var _rhs: ValueNode
  adaptInput(_lhs)
  adaptInput(_rhs)

  def lhs = _lhs
  def lhs_=(newLhs: ValueNode): Unit = {
    _lhs = replaceInput(_lhs, newLhs)
  }

  def rhs = _rhs
  def rhs_=(newRhs: ValueNode): Unit = {
    _rhs = replaceInput(_rhs, newRhs)
  }
}

sealed trait BinaryArithNode extends BinaryNode
case class AddNode(var _lhs: ValueNode, var _rhs: ValueNode) extends BinaryArithNode {
  def toShallowString: String = s"+"
}

case class SubNode(var _lhs: ValueNode, var _rhs: ValueNode) extends BinaryArithNode {
  def toShallowString: String = s"-"
}

sealed trait UnaryLogicNode extends UnaryNode with LogicNode
sealed trait BinaryLogicNode extends BinaryNode with LogicNode
case class LessThanNode(var _lhs: ValueNode, var _rhs: ValueNode) extends BinaryLogicNode {
  def toShallowString: String = s"<"
}
case class IsTruthyNode(var _v: ValueNode) extends UnaryLogicNode {
  def toShallowString: String = s"isTruthy"
}

case class ComposeNode(private var _value: ValueNode, private var _ctrl: ControlNode) extends ValueNode {
  adaptInput(_value)
  adaptInput(_ctrl)

  def toShallowString: String = s"Compose"
}

sealed trait FixedNode extends ValueNode {
  protected var _region: RegionNode
  adaptInput(_region)

  def region = _region
  def region_=(newRegion: RegionNode): Unit = {
    _region = replaceInput(_region, newRegion)
  }
}

case class PhiNode(protected var _region: RegionNode) extends FixedNode {
  val composeInputs = ArrayBuffer.empty[ComposeNode]
  def addInput(v: ComposeNode): Unit = {
    val ix = indexOfByRef(composeInputs, v)
    if (ix < 0) {
      inputs += adaptInput(v)
    }
  }

  def toShallowString: String = s"Phi"
}
