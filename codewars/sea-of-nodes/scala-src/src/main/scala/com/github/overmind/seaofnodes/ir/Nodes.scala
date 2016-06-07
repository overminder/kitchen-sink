package com.github.overmind.seaofnodes.ir

import com.github.overmind.seaofnodes.DotGen
import com.github.overmind.seaofnodes.ir.Graph.GraphBuilder

import scala.collection.mutable.ArrayBuffer

sealed trait Node {
  type Edges[A] = ArrayBuffer[A]
  val uses: Edges[Node] = ArrayBuffer.empty
  val inputs: Edges[Node] = ArrayBuffer.empty

  def toShallowString: String
  override def toString: String = toShallowString

  protected def remove(): Unit = {
    inputs.toArray.foreach(removeInput)
  }

  // Call this after uses / preds is shrinked.
  protected def tryRemove(): Unit = {
    if (uses.isEmpty) {
      remove()
    }
  }

  def adaptInput[N <: Node](input: N): N = {
    adaptEdgeTo(inputs, input)
    input.adaptEdgeTo(input.uses, this)
    input
  }

  def removeInput(input: Node): Unit = {
    removeEdgeTo(inputs, input)
    input.removeEdgeTo(input.uses, this)
    // input.tryRemove()
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
    if (ix >= 0) {
      // Exists
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

  protected override def remove(): Unit = {
    super.remove()
    successors.toArray.foreach(removeSuccessor)
  }

  override def tryRemove(): Unit = {
    if (uses.isEmpty && predecessors.isEmpty) {
      remove()
    }
  }

  def adaptSuccessor[N <: ControlNode](successor: N): N = {
    successor.adaptEdgeTo(successor.predecessors, this)
    adaptEdgeTo(successors, successor)
    successor
  }

  def removeSuccessor(successor: ControlNode): Unit = {
    removeEdgeTo(successors, successor)
    successor.removeEdgeTo(successor.predecessors, this)
    // successor.tryRemove()
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
    s"$toShallowString succs: ${Graph.exits(this).map(_.toShallowString)}" +
      s" preds: ${Graph.preds(this).map(_.toShallowString)}"

  def exit: ControlNode = _exit.get  // Unsafe
  def exit_=(newExit: ControlNode): Unit = {
    _exit = replaceOrAdaptSuccessor(_exit, Some(newExit))
  }
}

case class RetNode(private var _endNode: EndNode) extends ControlNode {
  adaptSuccessor(_endNode)

  def endNode = _endNode

  private var _value: Option[ValueNode] = None

  override def toShallowString: String = s"Ret"

  def value: ValueNode = _value.get  // Unsafe
  def value_=(newValue: ValueNode): Unit = {
    _value = replaceOrAdaptInput(_value, Some(newValue))
  }
}

case class IfNode(private var _t: RegionNode, private var _f: RegionNode) extends ControlNode with Simplifiable[ControlNode] {
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

  override def simplified(builder: GraphBuilder): ControlNode = {
    cond match {
      case TrueNode =>
        f.tryRemove()
        tryRemove()
        t
      case FalseNode =>
        t.tryRemove()
        tryRemove()
        f
      case _ => this
    }
  }
}

case class LitNode(v: Long) extends ValueNode {
  def toShallowString: String = s"Lit $v"
}

sealed trait UnaryNode extends ValueNode {
  protected var _v: ValueNode
  adaptInput(_v)

  def v = _v
  def v_=(newV: ValueNode): Unit = {
    _v = replaceInput(_v, newV)
  }
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

sealed trait Simplifiable[Into] {
  def simplified(builder: GraphBuilder): Into
}

object Simplifiable {
  def binaryLitOp(op: (Long, Long) => Long)(lhs: ValueNode, rhs: ValueNode): Option[ValueNode] = {
    (lhs, rhs) match {
      case (LitNode(a), LitNode(b)) =>
        Some(LitNode(op(a, b)))
      case _ =>
        None
    }
  }

  def ADD(a: Long, b: Long) = a + b
  def SUB(a: Long, b: Long) = a - b
  def LT(a: Long, b: Long) = if (a < b) 1 else 0
}

sealed trait BinaryArithNode extends BinaryNode with Simplifiable[ValueNode]
case class AddNode(var _lhs: ValueNode, var _rhs: ValueNode) extends BinaryArithNode {
  def toShallowString: String = s"+"

  override def simplified(builder: GraphBuilder): ValueNode = {
    Simplifiable.binaryLitOp(_ + _)(lhs, rhs).map(builder.unique).getOrElse(this)
  }
}

case class SubNode(var _lhs: ValueNode, var _rhs: ValueNode) extends BinaryArithNode {
  def toShallowString: String = s"-"

  override def simplified(builder: GraphBuilder): ValueNode = {
    Simplifiable.binaryLitOp(_ - _)(lhs, rhs).map(builder.unique).getOrElse(this)
  }
}

sealed trait UnaryLogicNode extends UnaryNode with LogicNode with Simplifiable[LogicNode]
sealed trait BinaryLogicNode extends BinaryNode with LogicNode with Simplifiable[LogicNode]
case class LessThanNode(var _lhs: ValueNode, var _rhs: ValueNode) extends BinaryLogicNode {
  def toShallowString: String = s"<"

  override def simplified(builder: GraphBuilder): LogicNode = {
    Simplifiable.binaryLitOp(Simplifiable.LT)(lhs, rhs)
      .map(IsTruthyNode(_).simplified(builder))
      .map(builder.unique)
      .getOrElse(this)
  }
}
case class IsTruthyNode(var _v: ValueNode) extends UnaryLogicNode {
  def toShallowString: String = s"isTruthy"

  override def simplified(builder: GraphBuilder): LogicNode = {
    v match {
      case LitNode(i) =>
        if (i == 0) {
          FalseNode
        } else {
          TrueNode
        }
      case _ => this
    }
  }
}
case object TrueNode extends LogicNode {
  override def toShallowString: String = "True"
}
case object FalseNode extends LogicNode {
  override def toShallowString: String = "False"
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
    adaptEdgeTo(composeInputs, adaptInput(v))
  }

  def toShallowString: String = s"Phi"
}

case class DotContext(name: String) {
  val g = DotGen.Graph(name)

  def addNode(n: Node): DotContext = {
    val visited = Graph.emptyIdentityMap[Node, DotGen.NodeId]

    def putText(n: Node): DotGen.NodeId = {
      visited.getOrElseUpdate(n, {
        val id = g.addText(n.toShallowString)
        visited += (n -> id)
        id
      })
    }

    def go(n: Node): DotGen.NodeId = {
      visited.getOrElse(n, {
        val id = putText(n)
        n.inputs.map(go).foreach(i => {
          g.addEdge(i, id, ("color", "blue"))
        })
        n.uses.map(go).foreach(u => {
          g.addEdge(id, u, ("color", "blue"), ("style", "dotted"))
        })
        n match {
          case c: ControlNode =>
            c.successors.map(go).foreach(s => {
              g.addEdge(id, s)
            })
            c.predecessors.map(go).foreach(p => {
              g.addEdge(p, id, ("style", "dotted"))
            })
          case _ => ()
        }
        id
      })
    }
    go(n)
    this
  }

  def render = g.toDot
}
