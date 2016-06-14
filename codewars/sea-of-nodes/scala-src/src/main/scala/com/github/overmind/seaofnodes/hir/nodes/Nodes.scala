package com.github.overmind.seaofnodes.hir.nodes

import com.github.overmind.seaofnodes.DotGen
import com.github.overmind.seaofnodes.hir.Graph
import com.github.overmind.seaofnodes.hir.Graph.GraphBuilder

import scala.collection.mutable.ArrayBuffer

// NOTE: We deliberately allow null inputs. This makes partial nodes easier at the cost
// of maintainability.
sealed trait Node {

  type Edges[A] = ArrayBuffer[A]
  protected val _uses: Edges[Node] = ArrayBuffer.empty
  protected var _predecessor: Node = _

  def uses = _uses.toArray
  final def inputs: Array[Node] = inputsInternal.flatMap(Option(_))
  def inputsInternal: Array[Node]

  def predecessor = _predecessor

  final def successors: Array[Node] = successorsInternal.flatMap(Option(_))
  def successorsInternal: Array[Node]

  def toShallowString: String
  override def toString: String = toShallowString

  protected def remove(): Unit = {
    inputs.foreach(removeInput)
    successors.foreach(removeSuccessor)
  }

  // Call this after uses / preds is shrinked.
  def tryRemove(): Unit = {
    if (uses.isEmpty && predecessor == null) {
      remove()
    }
  }

  def addSuccessor[N <: Node](successor: N): N = {
    if (successor != null) {
      assert(successor.predecessor == null)
      successor._predecessor = this
    }
    successor
  }

  def removeSuccessor(successor: Node): Unit = {
    if (successor != null) {
      assert(successor.predecessor == this)
      successor._predecessor = null
    }
    // successor.tryRemove()
  }

  def replaceSuccessor[N <: Node](oldSucc: N, newSucc: N): N = {
    removeSuccessor(oldSucc)
    addSuccessor(newSucc)
  }

  protected def addInput[N <: Node](input: N): N = {
    if (input != null) {
      input.addEdgeTo(this, input._uses)
    }
    input
  }

  protected def removeInput(input: Node): Unit = {
    if (input != null) {
      input.removeEdgeTo(this, input._uses)
    }
    // input.tryRemove()
  }

  protected def replaceInput[N <: Node](oldInput: N, newInput: N): N = {
    removeInput(oldInput)
    addInput(newInput)
  }

  protected def addEdgeTo[A <: AnyRef](to: A, onEdges: Edges[A]): Unit = {
    val ix = indexOfByRef(onEdges, to)
    assert(ix < 0, s"Node $to already exist on $this at $ix")
    onEdges += to
  }

  protected def removeEdgeTo[A <: AnyRef](to: A, onEdges: Edges[A]): Unit = {
    val ix = indexOfByRef(onEdges, to)
    assert(ix >= 0, s"Node $to doesn't exist on $this")
    onEdges.remove(ix)
  }

  protected def indexOfByRef[A <: AnyRef](xs: Seq[A], to: A): Int = {
    xs.indexWhere(to.eq)
  }
}

// Graal attaches lattices on ValueNodes - I current don't have such thing.
sealed trait ValueNode extends Node

sealed trait LogicNode extends ValueNode with NoSuccessor

sealed trait NoInput extends Node {
  final override def inputsInternal: Array[Node] = Array()
}

sealed trait NoSuccessor extends Node {
  final override def successorsInternal: Array[Node] = Array()
}

sealed trait SingleNext[N <: Node] extends Node {
  protected var _next: N

  addSuccessor(_next)

  override def successorsInternal: Array[Node] = Array(_next)

  def next = _next
  def next_=(newSucc: N) = {
    _next = replaceSuccessor(_next, newSucc)
  }
}

sealed trait UseSingleValue[N <: ValueNode] extends Node {
  protected var _value: N

  addInput(_value)

  def value = _value
  def value_=(newV: N) = {
    _value = replaceInput(_value, newV)
  }
}

case class GraphEntryNode(protected var _next: Node) extends SingleNext with NoInput {
  override def toShallowString: String = "Start"
}

case class GraphExitNode(protected var _returns: ArrayBuffer[RetNode] = ArrayBuffer.empty)
  extends Node with NoSuccessor {
  override def toShallowString: String = "End"

  override def inputsInternal: Array[Node] = _returns.toArray
  def addReturn(r: RetNode): RetNode = {
    _returns += addInput(r)
    r
  }
}

// Marks the begin of a basic block
sealed trait BaseBeginNode extends SingleNext[Node] {
  def id: Int
  def anchored = uses
}

case class MergeNode(id: Int,
                      protected val _comingFrom: ArrayBuffer[BaseEndNode] = ArrayBuffer.empty,
                     protected var _next: BaseEndNode = null) extends BaseBeginNode {
  _comingFrom.foreach(addInput)

  override def inputsInternal: Array[Node] = _comingFrom.toArray
  override def toShallowString: String = "Merge"

  def addComingFrom[N <: BaseEndNode](n: N): N = {
    _comingFrom += addInput(n)
    n
  }

  def valuePhis: Array[ValuePhiNode] = uses.flatMap({
    case n: ValuePhiNode => Some(n)
    case _ => None
  })
}

case class BeginNode(id: Int, protected var _next: BaseEndNode = null) extends BaseBeginNode with NoInput {
  override def toShallowString: String = "Begin"
}

sealed trait BaseEndNode extends Node

// Just a marker.
sealed trait BaseBlockExitNode extends Node

// Ends the current basic block.
case class EndNode() extends BaseEndNode with NoInput with NoSuccessor with BaseBlockExitNode {
  override def toShallowString: String = "BlockEnd"

  def cfgSuccessor = {
    assert(uses.length == 1)
    uses.head.asInstanceOf[BaseBeginNode]
  }
}

sealed trait ControlSplitNode extends BaseBlockExitNode {
  def cfgSuccessors: Array[BaseBeginNode]
}

case class RetNode(protected var _value: ValueNode = null)
  extends Node with UseSingleValue[ValueNode] with NoSuccessor with BaseBlockExitNode {

  override def toShallowString: String = s"Ret"

  override def inputsInternal: Array[Node] = Array(_value)
}

case class IfNode(protected var _value: LogicNode,
                  protected var _t: BaseBeginNode,
                  protected var _f: BaseBeginNode)
  extends ControlSplitNode with Simplifiable[Node] with UseSingleValue[LogicNode] {

  override def toShallowString: String = s"If"

  def t = _t
  def f = _f

  override def simplified(builder: GraphBuilder): Node = {
    _value match {
      case TrueNode =>
        t
      case FalseNode =>
        f
      case _ => this
    }
  }

  override def successorsInternal: Array[Node] = Array(_t, _f)

  override def inputsInternal: Array[Node] = Array(_value)

  override def cfgSuccessors: Array[BaseBeginNode] = Array(_t, _f)
}

case class LitNode(v: Long) extends ValueNode with NoInput with NoSuccessor {
  def toShallowString: String = s"Lit $v"
}

sealed trait UnaryNode extends ValueNode with UseSingleValue {
  override def inputsInternal: Array[Node] = Array(_value)
}

sealed trait BinaryNode extends ValueNode {
  protected var _lhs: ValueNode
  protected var _rhs: ValueNode

  addInput(_lhs)
  addInput(_rhs)

  def lhs = _lhs
  def lhs_=(newLhs: ValueNode): Unit = {
    _lhs = replaceInput(_lhs, newLhs)
  }

  def rhs = _rhs
  def rhs_=(newRhs: ValueNode): Unit = {
    _rhs = replaceInput(_rhs, newRhs)
  }

  override def inputsInternal: Array[Node] = Array(_lhs, _rhs)
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

sealed trait BinaryArithNode extends BinaryNode with Simplifiable[ValueNode] with NoSuccessor
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
case class IsTruthyNode(var _value: ValueNode) extends UnaryLogicNode {
  def toShallowString: String = s"isTruthy"

  override def simplified(builder: GraphBuilder): LogicNode = {
    _value match {
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

case object TrueNode extends LogicNode with NoInput {
  override def toShallowString: String = "True"
}
case object FalseNode extends LogicNode with NoInput {
  override def toShallowString: String = "False"
}

// High-level array ops. All the high-level memory-related ops are treated pessimistically:
// they are simply threaded between the containing block's begin and end node. We will do
// floating on later phases.

case class AllocFixedArrayNode(length: Int,
                               protected var _next: SingleNext = null)
  extends ValueNode with SingleNext with NoInput {
  override def toShallowString: String = s"AllocFixedArray(length = $length)"
}

sealed trait ArrayIndexNode extends ValueNode with SingleNext {
  protected var _base: ValueNode
  protected var _index: ValueNode

  addInput(_base)
  addInput(_index)

  def base = _base
  def index = _index
}

case class ReadArrayNode(protected var _base: ValueNode,
                         protected var _index: ValueNode,
                         protected var _next: SingleNext = null) extends ArrayIndexNode {
  override def toShallowString: String = "ReadArray"

  override def inputsInternal: Array[Node] = Array(_base, _index)
}

case class WriteArrayNode(protected var _base: ValueNode,
                          protected var _index: ValueNode,
                          protected var _value: ValueNode,
                          protected var _next: SingleNext = null) extends ArrayIndexNode {
  addInput(_value)
  def value = _value
  override def toShallowString: String = "WriteArray"
  override def inputsInternal: Array[Node] = Array(_base, _index, _value)
}

sealed trait AnchoredNode extends ValueNode {
  protected var _anchor: BaseBeginNode
  addInput(_anchor)

  def anchor = _anchor
  def anchor_=(newAnchor: BaseBeginNode): Unit = {
    _anchor = replaceInput(_anchor, newAnchor)
  }
}

sealed trait BasePhiNode[N <: ValueNode] extends AnchoredNode with NoSuccessor {
  protected val _composedInputs: ArrayBuffer[N]

  def composedInput = _composedInputs
  def addComposedInput(n: N): N = {
    super.addInput(n)
  }
}

case class ValuePhiNode(protected var _anchor: BaseBeginNode,
                        protected val _composedInputs: ArrayBuffer[ValueNode] = ArrayBuffer.empty)
  extends BasePhiNode {
  def toShallowString: String = s"ValuePhi"

  override def inputsInternal: Array[Node] = (composedInput :+ anchor).toArray
}

// Lowered nodes
// Memory-related nodes are added into the graph on later phases (on Graal: FloatingReadPhase etc)

case class MemoryPhiNode(protected var _anchor: BaseBeginNode,
                         protected val _composedInputs: ArrayBuffer[MemoryStateNode] = ArrayBuffer.empty)
  extends BasePhiNode[MemoryStateNode] {
  def toShallowString: String = s"MemoryPhi"

  override def inputsInternal: Array[Node] = (composedInput :+ anchor).toArray
}

sealed trait UseMemoryNode extends Node {
  protected var _memory: MemoryStateNode

  addInput(_memory)

  def memory = _memory
  def memory_=(newMemory: MemoryStateNode) = {
    _memory = replaceInput(_memory, newMemory)
  }
}

sealed trait MemoryStateNode extends ValueNode

case class DotContext(name: String, showBackedges: Boolean = false) {
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
        if (showBackedges) {
          n.uses.map(go).foreach(u => {
            g.addEdge(id, u, ("color", "blue"), ("style", "dotted"))
          })
        }
        n match {
          case c: Node =>
            c.successors.map(go).foreach(s => {
              g.addEdge(id, s)
            })
            if (showBackedges) {
              val p = go(c.predecessor)
              g.addEdge(p, id, ("style", "dotted"))
            }
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
