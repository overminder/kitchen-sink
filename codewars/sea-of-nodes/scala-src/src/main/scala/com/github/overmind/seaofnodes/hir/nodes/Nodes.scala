package com.github.overmind.seaofnodes.hir.nodes

import com.github.overmind.seaofnodes.DotGen
import com.github.overmind.seaofnodes.hir.Graph

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

sealed trait NodeField[S <: Node, A <: Node]

case class SimpleNodeField[S <: Node, A <: Node](getter: S => A, setter: (S, A) => Unit) extends NodeField[S, A] {
  def get(s: S): A = getter(s)
  def set(s: S, a: A): Unit = setter(s, a)
}

case class NodeListField[S <: Node, A <: Node](getter: S => Array[A], setter: (S, Array[A]) => Unit) extends NodeField[S, A] {
  def get(s: S): Array[A] = getter(s)
  def set(s: S, a: Array[A]): Unit = setter(s, a)
}

case class NodeClass[S <: Node](inputFields: NodeClass.Fields[S], successorFields: NodeClass.Fields[S] = Array()) {
  def replaceAllUsesWith(onNode: S, toNode: Node): Unit = {
    onNode.nodeClass
  }
}

object NodeClass {
  type Fields[S] = Array[NodeField[S, Node]]
  def apply[S <: Node](inputFields: NodeField[S, Node]*): NodeClass[S] = {
    NodeClass[S](inputFields.toArray)
  }

  def successorOnly[S <: Node](successorFields: NodeField[S, Node]*): NodeClass[S] = {
    NodeClass[S](Array.empty[NodeField[S, Node]], successorFields.toArray)
  }
}

// NOTE: We deliberately allow null inputs. This makes partial nodes easier at the cost
// of maintainability.
sealed trait Node {
  type Edges[A] = ArrayBuffer[A]
  protected val _uses: Edges[Node] = ArrayBuffer.empty
  protected var _predecessor: Node = _

  def nodeClass: NodeClass[this.type]

  def uses = _uses.toArray
  final def inputs: Array[Node] = inputsInternal.flatMap(Option(_))
  final def inputsInternal = {
    nodeClass.inputFields.flatMap({
      case s: SimpleNodeField[this.type, Node] =>
        Array(s.get(this))
      case ss: NodeListField[this.type, Node] =>
        ss.get(this)
    })
  }

  def predecessor = _predecessor

  final def successors: Array[Node] = successorsInternal.flatMap(Option(_))
  final def successorsInternal = {
    nodeClass.successorFields.flatMap({
      case s: SimpleNodeField[this.type, Node] =>
        Array(s.get(this))
      case ss: NodeListField[this.type, Node] =>
        ss.get(this)
    })
  }

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

  def replaceFirstInputWith(oldInput: Node, newInput: Node) = {
    nodeClass.inputFields.find({
      case s: SimpleNodeField[this.type, Node] =>
        if (s.get(this) eq oldInput) {
          s.set(this, newInput)
          true
        } else {
          false
        }
      case ss: NodeListField[this.type, Node] =>
        val ns = ss.get(this)
        val ix = ns.indexWhere(_ eq oldInput)
        if (ix >= 0) {
          ns(ix) = newInput
          ss.set(this, ns)
          true
        } else {
          false
        }
    }).get
  }

  def replaceAllUsesWith(replacement: Node) = {
    uses.foreach(u => {
      u.replaceFirstInputWith(this, replacement)
    })
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

object Node {
  val nodeClass = NodeClass[Node]()
}

// Graal attaches lattices on ValueNodes - I current don't have such thing.
sealed trait ValueNode extends Node

sealed trait LogicNode extends ValueNode

object SingleNext {
  val nodeClass = NodeClass.successorOnly(
    SimpleNodeField[SingleNext[Node], Node](
      _.next,
      _.next = _
    )
  )
}

sealed trait SingleNext[N <: Node] extends Node {
  protected var _next: N

  addSuccessor(_next)

  def next = _next
  def next_=(newSucc: N) = {
    _next = replaceSuccessor(_next, newSucc)
  }
}

object UseSingleValue {
  val nodeClass = NodeClass(
    SimpleNodeField[UseSingleValue[ValueNode], Node](
      _.value,
      (s, a) => s.value = a.asInstanceOf[ValueNode]
    )
  )
}

sealed trait UseSingleValue[N <: ValueNode] extends Node {
  protected var _value: N

  addInput(_value)

  def value = _value
  def value_=(newV: N) = {
    _value = replaceInput(_value, newV)
  }
}

case class GraphEntryNode(protected var _next: Node = null) extends SingleNext[Node] {
  override def toShallowString: String = "Start"
  override def nodeClass: NodeClass[SingleNext[Node]] = SingleNext.nodeClass
}

object GraphExitNode {
  val nodeClass = NodeClass(
    NodeListField[GraphExitNode, Node](
      _.returns,
      _.setReturns(_)
    )
  )
}

case class GraphExitNode(protected var _returns: mutable.Buffer[Node] = ArrayBuffer.empty)
  extends Node {

  addInput(_returns)

  override def toShallowString: String = "End"

  def returns: Array[Node] = _returns.toArray

  def addReturn(r: RetNode): RetNode = {
    _returns += addInput(r)
    r
  }

  def setReturns(ns: Array[Node]) = {
    _returns.foreach(removeInput)
    ns.foreach(addInput)
    _returns = ns.toBuffer
  }

  override def nodeClass: NodeClass[GraphExitNode] = GraphExitNode.nodeClass
}

// Marks the begin of a basic block
sealed trait BaseBeginNode extends SingleNext[Node] {
  def id: Int
  def anchored = uses
}

sealed trait BaseMergeNode extends BaseBeginNode {
  protected var _comingFrom: ArrayBuffer[BaseEndNode]

  _comingFrom.foreach(addInput)
  def valuePhis: Array[ValuePhiNode] = uses.flatMap({
    case n: ValuePhiNode => Some(n)
    case _ => None
  })

  def comingFrom: Array[Node] = _comingFrom.toArray
  def setComingFrom(xs: Array[Node]) = {
    _comingFrom.foreach(removeInput)
    xs.foreach(addInput)
    _comingFrom = xs.map(_.asInstanceOf[BaseEndNode]).to[ArrayBuffer]
  }

  def addComingFrom[N <: BaseEndNode](n: N): N = {
    _comingFrom += addInput(n)
    n
  }
}

object BaseMergeNode {
  val nodeClass = NodeClass(
    Array[NodeField[BaseMergeNode, Node]](NodeListField(
      _.comingFrom,
      _.setComingFrom(_)
    )),
    Array[NodeField[BaseMergeNode, Node]](SimpleNodeField(
      _.next,
      _.next = _
    ))
  )
}

case class LoopBeginNode(id: Int,
                         protected val _comingFrom: ArrayBuffer[BaseEndNode] = ArrayBuffer.empty,
                         protected var _next: BaseEndNode = null) extends BaseMergeNode {

  override def toShallowString: String = "LoopBegin"
  override final def nodeClass: NodeClass[BaseMergeNode] = BaseMergeNode.nodeClass
}

case class MergeNode(id: Int,
                      protected val _comingFrom: ArrayBuffer[BaseEndNode] = ArrayBuffer.empty,
                     protected var _next: BaseEndNode = null) extends BaseMergeNode {

  override def toShallowString: String = "Merge"
  override final def nodeClass: NodeClass[BaseMergeNode] = BaseMergeNode.nodeClass
}

case class BeginNode(id: Int, protected var _next: BaseEndNode = null) extends BaseBeginNode {
  override def toShallowString: String = "Begin"
  override def nodeClass: NodeClass[SingleNext[Node]] = SingleNext.nodeClass
}

case class LoopExitNode(id: Int, protected var _next: BaseEndNode = null) extends BaseBeginNode {
  override def toShallowString: String = "LoopExit"

  def loopBegin = {
    assert(uses.length == 1)
    uses.head.asInstanceOf[LoopBeginNode]
  }
  override def nodeClass: NodeClass[SingleNext[Node]] = SingleNext.nodeClass
}

sealed trait BaseEndNode extends Node

// Just a marker.
sealed trait BaseBlockExitNode extends Node

case class LoopEndNode() extends BaseEndNode with BaseBlockExitNode {
  override def toShallowString: String = "BlockEnd"

  def loopBegin = {
    assert(uses.length == 1)
    uses.head.asInstanceOf[LoopBeginNode]
  }
  def nodeClass: NodeClass[Node] = Node.nodeClass
}

// Ends the current basic block.
case class EndNode() extends BaseEndNode with BaseBlockExitNode {
  override def toShallowString: String = "BlockEnd"

  def cfgSuccessor = {
    assert(uses.length == 1)
    uses.head.asInstanceOf[BaseBeginNode]
  }
  def nodeClass: NodeClass[Node] = Node.nodeClass
}

sealed trait ControlSplitNode extends BaseBlockExitNode {
  def cfgSuccessors: Array[BaseBeginNode]
}

case class RetNode(protected var _value: ValueNode = null)
  extends Node with UseSingleValue[ValueNode] with BaseBlockExitNode {

  override def toShallowString: String = s"Ret"

  override def nodeClass: NodeClass[UseSingleValue[ValueNode]] = UseSingleValue.nodeClass
}

object IfNode {
  val nodeClass = NodeClass(
    Array[NodeField[IfNode, Node]](SimpleNodeField(
      _.value,
      (s, a) => s.value = a.asInstanceOf[LogicNode]
    )),
    Array[NodeField[IfNode, Node]](
      SimpleNodeField(
        _.t,
        (s, a) => s.t = a.asInstanceOf[BaseBeginNode]
      ),
      SimpleNodeField(
        _.f,
        (s, a) => s.f = a.asInstanceOf[BaseBeginNode]
      )
    )
  )
}

case class IfNode(protected var _value: LogicNode,
                  protected var _t: BaseBeginNode,
                  protected var _f: BaseBeginNode)
  extends ControlSplitNode with UseSingleValue[LogicNode] {

  addInput(_value)
  addSuccessor(_t)
  addSuccessor(_f)

  override def toShallowString: String = s"If"

  def t = _t
  def t_=(t: BaseBeginNode) = _t = replaceInput(_t, t)
  def f = _f
  def f_=(f: BaseBeginNode) = _f = replaceInput(_f, f)

  override def cfgSuccessors: Array[BaseBeginNode] = Array(_t, _f)
  override def nodeClass: NodeClass[IfNode] = IfNode.nodeClass
}

case class LitNode(v: Long) extends ValueNode {
  def toShallowString: String = s"Lit $v"
  def nodeClass: NodeClass[Node] = Node.nodeClass
}

sealed trait UnaryNode extends ValueNode with UseSingleValue[ValueNode] {
  def nodeClass: NodeClass[_] = UseSingleValue.nodeClass
}

object BinaryNode {
  val nodeClass = NodeClass(
    SimpleNodeField[BinaryNode, Node](
      _.lhs,
      (s, a) => s.lhs = a.asInstanceOf[ValueNode]
    ),
    SimpleNodeField[BinaryNode, Node](
      _.rhs,
      (s, a) => s.rhs = a.asInstanceOf[ValueNode]
    )
  )
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

  override def nodeClass: NodeClass[BinaryNode] = BinaryNode.nodeClass
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
case class IsTruthyNode(var _value: ValueNode) extends UnaryLogicNode {
  def toShallowString: String = s"isTruthy"
}

case object TrueNode extends LogicNode {
  override def toShallowString: String = "True"
  def nodeClass: NodeClass[Node] = Node.nodeClass
}
case object FalseNode extends LogicNode {
  override def toShallowString: String = "False"
  def nodeClass: NodeClass[Node] = Node.nodeClass
}

// High-level array ops. All the high-level memory-related ops are treated pessimistically:
// they are simply threaded between the containing block's begin and end node. We will do
// floating on later phases.

case class AllocFixedArrayNode(length: Int,
                               protected var _next: SingleNext[Node] = null)
  extends ValueNode with SingleNext[Node] {
  override def toShallowString: String = s"AllocFixedArray(length = $length)"
  def nodeClass: NodeClass[_] = SingleNext.nodeClass
}

sealed trait ArrayIndexNode extends ValueNode with SingleNext[Node] {
  protected var _base: ValueNode
  protected var _index: ValueNode

  addInput(_base)
  addInput(_index)

  def base = _base
  def base_=(newBase: ValueNode) = _base = replaceInput(_base, newBase)
  def index = _index
  def index_=(newIndex: ValueNode) = _index = replaceInput(_index, newIndex)
}

case class ReadArrayNode(protected var _base: ValueNode,
                         protected var _index: ValueNode,
                         protected var _next: Node = null) extends ArrayIndexNode {
  override def toShallowString: String = "ReadArray"

  def nodeClass: NodeClass[_] = ReadArrayNode.nodeClass
}

object ReadArrayNode {
  val nodeClass: NodeClass[ReadArrayNode] = NodeClass(
    Array[NodeField[ReadArrayNode, Node]](
      SimpleNodeField(
        _.base,
        (s, a) => s.base = a.asInstanceOf[ValueNode]
      ),
      SimpleNodeField(
        _.index,
        (s, a) => s.index = a.asInstanceOf[ValueNode]
      )
    ),
    Array[NodeField[ReadArrayNode, Node]](
      SimpleNodeField(
        _.next,
        _.next = _
      )
    )
  )
}


case class WriteArrayNode(protected var _base: ValueNode,
                          protected var _index: ValueNode,
                          protected var _value: ValueNode,
                          protected var _next: SingleNext = null) extends ArrayIndexNode {
  addInput(_value)
  def value = _value
  def value_=(newValue: ValueNode) = _value = replaceInput(_value, newValue)

  override def toShallowString: String = "WriteArray"
  def nodeClass: NodeClass[_] = WriteArrayNode.nodeClass
}

object WriteArrayNode {
  val nodeClass: NodeClass[WriteArrayNode] = NodeClass(
    Array[NodeField[WriteArrayNode, Node]](
      SimpleNodeField(
        _.base,
        (s, a) => s.base = a.asInstanceOf[ValueNode]
      ),
      SimpleNodeField(
        _.index,
        (s, a) => s.index = a.asInstanceOf[ValueNode]
      ),
      SimpleNodeField(
        _.value,
        (s, a) => s.value = a.asInstanceOf[ValueNode]
      )
    ),
    Array[NodeField[WriteArrayNode, Node]](
      SimpleNodeField(
        _.next,
        _.next = _
      )
    )
  )
}

sealed trait AnchoredNode extends ValueNode {
  protected var _anchor: BaseBeginNode
  addInput(_anchor)

  def anchor = _anchor
  def anchor_=(newAnchor: BaseBeginNode): Unit = {
    _anchor = replaceInput(_anchor, newAnchor)
  }
}

sealed trait BasePhiNode[N <: ValueNode] extends AnchoredNode {
  protected var _composedInputs: ArrayBuffer[N]
  _composedInputs.foreach(addInput)

  def composedInputs = _composedInputs
  def addComposedInput(n: N): N = {
    super.addInput(n)
  }
  def setComposedInputs(newInputs: Array[N]) = {
    _composedInputs.foreach(removeInput)
    newInputs.foreach(addInput)
    _composedInputs = newInputs.to[ArrayBuffer]
  }
}

object BasePhiNode {
  val nodeClass: NodeClass[BasePhiNode[ValueNode]] = NodeClass(
    SimpleNodeField[BasePhiNode[ValueNode], Node](
      _.anchor,
      (s, a) => s.anchor = a.asInstanceOf[BaseBeginNode]
    ),
    NodeListField[BasePhiNode[ValueNode], Node](
      _.composedInputs.toArray,
      (s, a) => s.setComposedInputs(a.map(_.asInstanceOf[ValueNode]))
    )
  )
}

case class ValuePhiNode(protected var _anchor: BaseBeginNode = null,
                        protected var _composedInputs: ArrayBuffer[ValueNode] = ArrayBuffer.empty)
  extends BasePhiNode[ValueNode] {

  def toShallowString: String = s"ValuePhi"
  def nodeClass: NodeClass[_] = BasePhiNode.nodeClass
}

object ValuePhiNode {
  def apply(anchor: BaseBeginNode, values: Seq[ValueNode]): ValuePhiNode = {
    val phi = ValuePhiNode(anchor)
    values.foreach(phi.addComposedInput)
    phi
  }
}

// Lowered nodes
// Memory-related nodes are added into the graph on later phases (on Graal: FloatingReadPhase etc)

case class MemoryPhiNode(protected var _anchor: BaseBeginNode,
                         protected val _composedInputs: ArrayBuffer[MemoryStateNode] = ArrayBuffer.empty)
  extends BasePhiNode[MemoryStateNode] {
  def toShallowString: String = s"MemoryPhi"
  def nodeClass: NodeClass[_] = BasePhiNode.nodeClass
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
