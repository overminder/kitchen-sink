package com.github.overmind.seaofnodes.hir.nodes

import com.github.overmind.seaofnodes.DotGen
import com.github.overmind.seaofnodes.hir.Graph
import com.github.overmind.seaofnodes.hir.Graph.GraphBuilder

import scala.collection.mutable.ArrayBuffer

// NOTE: We deliberately allow null inputs. This makes partial nodes easier at the cost
// of maintainability.
sealed trait Node {

  type Edges[A] = ArrayBuffer[A]
  val _uses: Edges[Node] = ArrayBuffer.empty

  def uses = _uses.toArray
  final def inputs: Array[Node] = inputsInternal.flatMap(Option(_))
  def inputsInternal: Array[Node]

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

sealed trait ValueNode extends Node
sealed trait LogicNode extends ValueNode
sealed trait ControlNode extends Node {
  var predecessor: ControlNode = _

  final def successors: Array[ControlNode] = successorsInternal.flatMap(Option(_))
  def successorsInternal: Array[ControlNode]

  protected override def remove(): Unit = {
    super.remove()
    successors.foreach(removeSuccessor)
  }

  override def tryRemove(): Unit = {
    if (uses.isEmpty && predecessor == null) {
      remove()
    }
  }

  def addSuccessor[N <: ControlNode](successor: N): N = {
    if (successor != null) {
      assert(successor.predecessor == null)
      successor.predecessor = this
    }
    successor
  }

  def removeSuccessor(successor: ControlNode): Unit = {
    if (successor != null) {
      assert(successor.predecessor == this)
      successor.predecessor = null
    }
    // successor.tryRemove()
  }

  def replaceSuccessor[N <: ControlNode](oldSucc: N, newSucc: N): N = {
    removeSuccessor(oldSucc)
    addSuccessor(newSucc)
  }
}

sealed trait NoInput extends Node {
  final override def inputsInternal: Array[Node] = Array()
}

sealed trait NoSuccessor extends ControlNode {
  final override def successorsInternal: Array[ControlNode] = Array()
}

sealed trait SingleNext[N <: ControlNode] extends ControlNode {
  protected var _next: N

  addSuccessor(_next)

  override def successorsInternal: Array[ControlNode] = Array(_next)

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

case class StartNode(protected var _next: ControlNode) extends SingleNext with NoInput {
  override def toShallowString: String = "Start"
}

case class EndNode() extends ControlNode with NoInput with NoSuccessor {
  override def toShallowString: String = "End"
}

sealed trait JProjNode

case class TrueProjNode() extends NoInput with NoSuccessor {
  override def toShallowString: String = "TrueProj"
}

case class FalseProjNode() extends NoInput with NoSuccessor {
  override def toShallowString: String = "FalseProj"
}

case class MergeNode(protected var _next: ControlNode,
                     protected val _comingFrom: Seq[ControlNode]) extends SingleNext {
  _comingFrom.foreach(addInput)

  override def inputsInternal: Array[Node] = _comingFrom.toArray

  override def toShallowString: String = "Merge"
}

object RegionNode {
  type Id = Int
}
case class RegionNode(id: RegionNode.Id,
                      protected var _next: ControlNode = null) extends SingleNext with NoInput {
  override def toShallowString: String = s"RegionNode $id"

  override def toString: String =
    s"$toShallowString succs: ${Graph.exits(this).map(_.toShallowString)}" +
      s" preds: ${Graph.preds(this).map(_.toShallowString)}"

  def phis: Seq[BasePhiNode] = {
    uses.flatMap({
      case phi: BasePhiNode => Some(phi)
      case _: ComposeNode => None
      case n => sys.error(s"Unknown RegionNode input $n")
    })
  }

  def composes: Seq[ComposeNode] = {
    uses.flatMap({
      case n: ComposeNode => Some(n)
      case _: BasePhiNode => None
      case n => sys.error(s"Unknown RegionNode input $n")
    })
  }
}

case class RetNode(protected var _next: EndNode,
                   protected var _value: ValueNode = null,
                   protected var _memory: MemoryStateNode = null)
  extends SingleNext[EndNode] with UseMemoryNode with UseSingleValue {

  override def toShallowString: String = s"Ret"

  override def inputsInternal: Array[Node] = Array(_value, _memory)
}

case class IfNode(protected var _value: ValueNode,
                  protected var _t: TrueProjNode,
                  protected var _f: FalseProjNode)
  extends ControlNode with Simplifiable[ControlNode] with UseSingleValue {

  override def toShallowString: String = s"If"

  def region = predecessor.asInstanceOf[RegionNode]

  def t = _t
  def f = _f

  override def simplified(builder: GraphBuilder): ControlNode = {
    _value match {
      case TrueNode =>
        t
      case FalseNode =>
        f
      case _ => this
    }
  }

  override def successorsInternal: Array[ControlNode] = Array(_t, _f)

  override def inputsInternal: Array[Node] = Array(_value)
}

case class LitNode(v: Long) extends ValueNode with NoInput {
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

// Arrays

sealed trait UseMemoryNode extends Node {
  protected var _memory: MemoryStateNode

  addInput(_memory)

  def memory = _memory
  def memory_=(newMemory: MemoryStateNode) = {
    _memory = replaceInput(_memory, newMemory)
  }
}

case class AllocFixedArrayNode(length: Int,
                               protected var _memory: MemoryStateNode)
  extends ValueNode with UseMemoryNode {
  override def toShallowString: String = s"AllocFixedArray(length = $length)"

  override def inputsInternal: Array[Node] = Array(_memory)
}

sealed trait ArrayIndexNode extends ValueNode with UseMemoryNode {
  protected var _base: ValueNode
  protected var _index: ValueNode

  addInput(_base)
  addInput(_index)

  def base = _base
  def index = _index
}

case class ReadArrayNode(protected var _base: ValueNode,
                         protected var _index: ValueNode,
                         protected var _memory: MemoryStateNode) extends ArrayIndexNode {
  override def toShallowString: String = "ReadArray"

  override def inputsInternal: Array[Node] = Array(_base, _index, _memory)
}

case class WriteArrayNode(protected var _base: ValueNode,
                          protected var _index: ValueNode,
                          protected var _value: ValueNode,
                          protected var _memory: MemoryStateNode) extends ArrayIndexNode {
  addInput(_value)
  def value = _value
  override def toShallowString: String = "WriteArray"
  override def inputsInternal: Array[Node] = Array(_base, _index, _memory, _value)
}

case class ComposeNode(private var _value: ValueNode,
                       private var _ctrl: ControlNode) extends ValueNode {
  addInput(_value)
  addInput(_ctrl)

  def value = _value
  def ctrl = _ctrl

  def phi = {
    assert(uses.length == 1)
    uses.head.asInstanceOf[BasePhiNode]
  }

  def toShallowString: String = s"Compose"
  override def inputsInternal: Array[Node] = Array(_value, _ctrl)
}

sealed trait MemoryStateNode extends ValueNode

case class InitialMemoryStateNode() extends MemoryStateNode with NoInput {
  override def toShallowString: String = "InitialMemoryState"
}

case class MemoryStateAfterNode(_value: ValueNode) extends MemoryStateNode with UseSingleValue {
  override def toShallowString: String = "MemoryStateAfter"

  override def inputsInternal: Array[Node] = Array(_value)
}

sealed trait FixedNode extends ValueNode {
  protected var _region: RegionNode
  addInput(_region)

  def region = _region
  def region_=(newRegion: RegionNode): Unit = {
    _region = replaceInput(_region, newRegion)
  }
}

sealed trait BasePhiNode extends FixedNode {
  val composeInputs = ArrayBuffer.empty[ComposeNode]
  def addComposeInput(v: ComposeNode): ComposeNode = {
    super.addInput(v)
  }
}

case class ValuePhiNode(protected var _region: RegionNode) extends BasePhiNode {
  def toShallowString: String = s"Phi"
}

case class MemoryPhiNode(protected var _region: RegionNode) extends MemoryStateNode with BasePhiNode {
  override def toShallowString: String = "MemoryPhi"
}

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
          case c: ControlNode =>
            c.successors.map(go).foreach(s => {
              g.addEdge(id, s)
            })
            if (showBackedges) {
              c.predecessors.map(go).foreach(p => {
                g.addEdge(p, id, ("style", "dotted"))
              })
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
