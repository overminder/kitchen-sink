package com.github.overmind.seaofnodes.hir.nodes

import com.github.overmind.seaofnodes.hir.Graph

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.reflect.ClassTag

sealed trait NodeField[-S <: Node, A <: Node]

case class SimpleNodeField[S <: Node, A <: Node](getter: S => A, setter: (S, A) => Unit) extends NodeField[S, A] {
  def get(s: S): A = getter(s)
  def set(s: S, a: A): Unit = setter(s, a)
}

case class NodeListField[S <: Node, A <: Node](getter: S => Seq[A], setter: (S, Seq[A]) => Unit) extends NodeField[S, A] {
  def get(s: S): Seq[A] = getter(s)
  def set(s: S, a: Seq[A]): Unit = setter(s, a)
}

case class NodeClass[-S <: Node](inputFields: NodeClass.Fields[S],
                                successorFields: NodeClass.Fields[S] = Seq.empty[NodeField[S, Node]])

object NodeClass {
  type Fields[-S <: Node] = Seq[NodeField[S, Node]]
  def apply[S <: Node](inputFields: NodeField[S, Node]*): NodeClass[S] = {
    NodeClass[S](inputFields)
  }

  def successorOnly[S <: Node](successorFields: NodeField[S, Node]*): NodeClass[S] = {
    NodeClass[S](Seq.empty[NodeField[S, Node]], successorFields)
  }
}

object Node {
  private var idGen = 1
  def nextId = {
    val r = idGen
    idGen += 1
    r
  }

  val nodeClass = NodeClass[Node]()

  def asSomeNode[A <: Node: ClassTag](n: Node): Option[A] = {
    n match {
      case v: A =>
        Some(v)
      case _ =>
        None
    }
  }

  def asNodeOtherThan[A <: Node: ClassTag](n: Node): Option[Node] = {
    n match {
      case v: A =>
        None
      case _ =>
        Some(n)
    }
  }

  def asValueNode(n: Node) = asSomeNode[ValueNode](n)
  def asControlNode(n: Node) = asNodeOtherThan[ValueNode](n)
}

// NOTE: We deliberately allow null inputs. This makes partial nodes easier at the cost
// of maintainability.
sealed trait Node {
  type Edges[A] = ArrayBuffer[A]
  protected val _uses: Edges[Node] = ArrayBuffer.empty
  protected var _predecessor: Node = _

  val id = Node.nextId

  def nodeClass: NodeClass[this.type]

  // In a structured graph, can we simply gather this information when building the graph?
  def isIDomOf: Seq[Node]

  def identityHashCode = System.identityHashCode(this)

  final def uses: Seq[Node] = _uses.flatMap(Option(_))
  final def controlUses: Seq[Node] = _uses.flatMap(Node.asNodeOtherThan(_))
  final def valueUses: Seq[ValueNode] = _uses.flatMap(Node.asValueNode)

  final def inputs: Seq[Node] = inputsInternal.flatMap(Option(_))
  final def valueInputs: Seq[ValueNode] = inputs.flatMap(Node.asValueNode)
  final def inputsInternal = {
    nodeClass.inputFields.flatMap({
      case s: SimpleNodeField[this.type, Node] =>
        Seq(s.get(this))
      case ss: NodeListField[this.type, Node] =>
        ss.get(this)
    })
  }

  def predecessor = _predecessor

  final def successors: Seq[Node] = successorsInternal.flatMap(Option(_))
  final def successorsInternal = {
    nodeClass.successorFields.flatMap({
      case s: SimpleNodeField[this.type, Node] =>
        Seq(s.get(this))
      case ss: NodeListField[this.type, Node] =>
        ss.get(this)
    })
  }

  def toShallowString: String
  override def toString: String = s"$toShallowString @ $id"

  def remove(): Unit = {
    inputs.foreach(removeInput)
    successors.foreach(removeSuccessor)
  }

  // Call this after uses / preds is shrinked.
  def tryRemove(): Unit = {
    if (uses.isEmpty && predecessor == null) {
      remove()
    }
  }

  // XXX: First or every?
  def replaceMatchingInputWith(oldInput: Node, newInput: Node) = {
    nodeClass.inputFields.foreach(replaceOn(_, oldInput, newInput))
  }

  def replaceMatchingSuccessorWith(oldSuccessor: Node, newSuccessor: Node) = {
    nodeClass.successorFields.foreach(replaceOn(_, oldSuccessor, newSuccessor))
  }

  def replaceOn(field: NodeField[this.type, Node], oldInput: Node, newInput: Node) = {
    field match {
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
          ss.set(this, ns.updated(ix, newInput))
          true
        } else {
          false
        }
    }
  }

  def replaceAllUsesWith(replacement: Node, keepAlive: Boolean = false) = {
    uses.foreach(u => {
      u.replaceMatchingInputWith(this, replacement)
    })
    if (!keepAlive) {
      tryRemove()
    }
  }

  def replaceThisOnPredecessor(replacement: Node) = {
    predecessor.replaceMatchingSuccessorWith(this, replacement)
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
      input.addRefToArray(this, input._uses)
    }
    input
  }

  protected def removeInput(input: Node): Unit = {
    if (input != null) {
      input.removeRefFromArray(this, input._uses)
    }
    // input.tryRemove()
  }

  protected def replaceInput[N <: Node](oldInput: N, newInput: N): N = {
    removeInput(oldInput)
    addInput(newInput)
  }

  protected def addRefToArray[A <: AnyRef](ref: A, toArray: Edges[A]): Unit = {
    // Allow multiple copies to exist.
    // val ix = indexOfByRef(toArray, ref)
    // assert(ix < 0, s"Node $ref already exist on $this at $ix")
    toArray += ref
  }

  protected def removeRefFromArray[A <: AnyRef](ref: A, fromArray: Edges[A]): Unit = {
    val ix = indexOfByRef(fromArray, ref)
    assert(ix >= 0, s"Node $ref doesn't exist on $this (fromArray = $fromArray)")
    fromArray.remove(ix)
  }

  protected def indexOfByRef[A <: AnyRef](xs: Seq[A], to: A): Int = {
    xs.indexWhere(to.eq)
  }
}

// Graal attaches lattices on ValueNodes - I current don't have such thing.
sealed trait ValueNode extends Node {
  override def isIDomOf: Seq[Node] = Seq()
}

// Pure operations
sealed trait ValueNumberable extends ValueNode {
  def shallowHashCode: Int
  final override def hashCode = shallowHashCode
}

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
  def next_=(newSucc: N) = _next = replaceSuccessor(_next, newSucc)
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
  override def nodeClass = SingleNext.nodeClass

  override def next = _next.asInstanceOf[BaseBeginNode]

  // In a structured graph, can we simply gather this information when building the graph?
  override def isIDomOf: Seq[Node] = Seq(next)
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

  def isIDomOf = Seq()

  _returns.foreach(addInput)

  override def toShallowString: String = "End"

  def returns: Seq[Node] = _returns

  def addReturn(r: RetNode): RetNode = {
    _returns += addInput(r)
    r
  }

  def setReturns(ns: Seq[Node]) = {
    _returns.foreach(removeInput)
    ns.foreach(addInput)
    _returns = ns.toBuffer
  }

  override def nodeClass: NodeClass[GraphExitNode] = GraphExitNode.nodeClass
}

// Marks the begin of a basic block
sealed trait BaseBeginNode extends SingleNext[Node] {
  def anchored = uses.flatMap(Node.asSomeNode[AnchoringNode](_))

  def isIDomOf = Seq(next)
}

sealed trait BaseMergeNode extends BaseBeginNode {
  protected var _comingFrom: ArrayBuffer[BaseEndNode]

  _comingFrom.foreach(addInput)
  def valuePhis: Seq[ValuePhiNode] = uses.flatMap(
    Node.asSomeNode[ValuePhiNode](_))  // <- Idea really want me to write it in this way.

  def comingFrom: Seq[BaseEndNode] = _comingFrom
  def setComingFrom(xs: Seq[BaseEndNode]) = {
    _comingFrom.foreach(removeInput)
    xs.foreach(addInput)
    _comingFrom = xs.to[ArrayBuffer]
  }
  def removeComingFrom(n: BaseEndNode) = {
    removeRefFromArray(n, _comingFrom)
    removeInput(n)
  }

  def addComingFrom[N <: BaseEndNode](n: N): N = {
    _comingFrom += addInput(n)
    n
  }
}

object BaseMergeNode {
  val nodeClass = NodeClass(
    Seq[NodeField[BaseMergeNode, Node]](NodeListField(
      _.comingFrom,
      (s, a) => s.setComingFrom(a.map(_.asInstanceOf[BaseEndNode]))
    )),
    Seq[NodeField[BaseMergeNode, Node]](SimpleNodeField(
      _.next,
      _.next = _
    ))
  )
}

case class LoopBeginNode(protected var _comingFrom: ArrayBuffer[BaseEndNode] = ArrayBuffer.empty,
                         protected var _next: Node = null) extends BaseMergeNode {

  override def toShallowString: String = "LoopBegin"
  override final def nodeClass = BaseMergeNode.nodeClass
}

case class MergeNode(protected var _comingFrom: ArrayBuffer[BaseEndNode] = ArrayBuffer.empty,
                     protected var _next: Node = null) extends BaseMergeNode {

  override def toShallowString: String = "Merge"
  override final def nodeClass = BaseMergeNode.nodeClass
}

case class BeginNode(protected var _next: Node = null) extends BaseBeginNode {
  override def toShallowString: String = "Begin"
  override def nodeClass: NodeClass[SingleNext[Node]] = SingleNext.nodeClass
}

case class LoopExitNode(protected var _next: Node = null) extends BaseBeginNode {
  override def toShallowString: String = "LoopExit"

  def loopBegin = {
    assert(uses.length == 1)
    uses.head.asInstanceOf[LoopBeginNode]
  }
  override def nodeClass: NodeClass[SingleNext[Node]] = SingleNext.nodeClass
}

// Just a marker.
sealed trait BaseBlockExitNode extends Node {
  def belongsToBlock = predecessor.asInstanceOf[BaseBeginNode]
}

sealed trait BaseEndNode extends BaseBlockExitNode {
  def cfgSuccessor = {
    assert(uses.length == 1)
    uses.head.asInstanceOf[BaseBeginNode]
  }

  def isIDomOf = {
    cfgSuccessor match {
      case loop: LoopBeginNode if loop.comingFrom.head eq this =>
        // This is a loop header
        Seq(loop)
      case _ =>
        Seq()
    }
  }
}

case class LoopEndNode() extends BaseEndNode with BaseBlockExitNode {
  override def toShallowString: String = "BlockEnd"

  def loopBegin = cfgSuccessor.asInstanceOf[LoopBeginNode]
  def nodeClass: NodeClass[Node] = Node.nodeClass
}

// Ends the current basic block.
case class EndNode() extends BaseEndNode with BaseBlockExitNode {
  override def toShallowString: String = "BlockEnd"

  def nodeClass: NodeClass[Node] = Node.nodeClass
}

sealed trait ControlSplitNode extends BaseBlockExitNode {
  def cfgSuccessors: Seq[BaseBeginNode]
}

case class RetNode(protected var _value: ValueNode = null)
  extends Node with UseSingleValue[ValueNode] with BaseBlockExitNode {

  override def toShallowString: String = s"Ret"

  override def nodeClass: NodeClass[UseSingleValue[ValueNode]] = UseSingleValue.nodeClass

  def isIDomOf = Seq()
}

object IfNode {
  val nodeClass = NodeClass(
    Seq[NodeField[IfNode, Node]](SimpleNodeField(
      _.value,
      (s, a) => s.value = a.asInstanceOf[ValueNode]
    )),
    Seq[NodeField[IfNode, Node]](
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

case class IfNode(protected var _value: ValueNode,
                  protected var _t: BaseBeginNode,
                  protected var _f: BaseBeginNode)
  extends ControlSplitNode with UseSingleValue[ValueNode] {

  protected var _merge: BaseMergeNode = _

  addSuccessor(_t)
  addSuccessor(_f)

  override def toShallowString: String = s"If"

  def t = _t
  def t_=(t: BaseBeginNode) = _t = replaceSuccessor(_t, t)
  def f = _f
  def f_=(f: BaseBeginNode) = _f = replaceSuccessor(_f, f)
  def merge = _merge
  def merge_=(newM: BaseMergeNode) = _merge = newM

  override def cfgSuccessors: Seq[BaseBeginNode] = Seq(_t, _f)
  override def nodeClass: NodeClass[IfNode] = IfNode.nodeClass

  def isIDomOf = {
    val more = merge match {
      case null =>
        None
      case _: LoopBeginNode =>
        assert(predecessor eq merge)
        None
      case _: MergeNode =>
        Some(merge)
    }
    Seq(t, f) ++ more
  }
}

sealed trait LitNode extends ValueNode with ValueNumberable

object LitNode {
  def apply(b: Boolean): LogicNode = {
    if (b) {
      TrueNode
    } else {
      FalseNode
    }
  }

  def apply(lval: Long): LitLongNode = {
    LitLongNode(lval)
  }
}

case class LitLongNode(v: Long) extends LitNode {
  def toShallowString: String = s"LitLong $v"
  override def nodeClass = Node.nodeClass

  override def shallowHashCode = v.hashCode
}

// Pure
sealed trait UnaryNode extends ValueNode with UseSingleValue[ValueNode] with ValueNumberable {
  override def nodeClass = UseSingleValue.nodeClass

  override def shallowHashCode = getClass.hashCode + value.identityHashCode
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

// Pure
sealed trait BinaryNode extends ValueNode with ValueNumberable {
  protected var _lhs: ValueNode
  protected var _rhs: ValueNode

  addInput(_lhs)
  addInput(_rhs)

  override def shallowHashCode = getClass.hashCode + lhs.identityHashCode + rhs.identityHashCode

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
  def binaryOpLLL(op: (Long, Long) => Long)(lhs: ValueNode, rhs: ValueNode) = {
    binaryOpLLV((v1, v2) => LitNode(op(v1, v2)))(lhs, rhs)
  }

  def binaryOpLLB(op: (Long, Long) => Boolean)(lhs: ValueNode, rhs: ValueNode) = {
    binaryOpLLV((v1, v2) => LitNode(op(v1, v2)))(lhs, rhs)
  }

  def unaryOpLB(op: Long => Boolean)(v: ValueNode) = {
    unaryOpLV(b => LitNode(op(b)))(v)
  }

  def unaryOpLV(op: Long => ValueNode)(v: ValueNode): Option[ValueNode] = {
    v match {
      case LitLongNode(lv) =>
        Some(op(lv))
      case _ =>
        None
    }
  }

  def binaryOpLLV(op: (Long, Long) => ValueNode)(lhs: ValueNode, rhs: ValueNode): Option[ValueNode] = {
    (lhs, rhs) match {
      case (LitLongNode(a), LitLongNode(b)) =>
        Some(op(a, b))
      case _ =>
        None
    }
  }


  def ADD(a: Long, b: Long) = a + b
  def SUB(a: Long, b: Long) = a - b
  def LT(a: Long, b: Long) = if (a < b) 1 else 0
}

sealed trait Simplifiable extends ValueNode {
  protected def simplified: Option[ValueNode]

  final def simplifyInGraph(g: Graph): ValueNode = {
    simplified match {
      case Some(newValue) =>
        replaceAllUsesWith(newValue)
        newValue
      case None =>
        this
    }
  }
}

sealed trait BinaryArithNode extends BinaryNode with Simplifiable {
  import Simplifiable._
  def denoteOp: (Long, Long) => Long
  override protected def simplified: Option[ValueNode] = {
    binaryOpLLL(denoteOp)(lhs, rhs)
  }
}

case class AddNode(var _lhs: ValueNode, var _rhs: ValueNode) extends BinaryArithNode {
  def toShallowString: String = s"+"

  override def denoteOp: (Long, Long) => Long = _ + _
}

case class SubNode(var _lhs: ValueNode, var _rhs: ValueNode) extends BinaryArithNode {
  def toShallowString: String = s"-"

  override def denoteOp: (Long, Long) => Long = _ - _
}

sealed trait UnaryLogicNode extends UnaryNode with LogicNode
sealed trait BinaryLogicNode extends BinaryNode with LogicNode with Simplifiable {
  import Simplifiable._
  def denoteOp: (Long, Long) => Boolean
  override protected def simplified: Option[ValueNode] = {
    binaryOpLLB(denoteOp)(lhs, rhs)
  }
}
case class LessThanNode(var _lhs: ValueNode, var _rhs: ValueNode) extends BinaryLogicNode {
  def toShallowString: String = s"<"
  override def denoteOp = _ < _
}
case class IsTruthyNode(var _value: ValueNode) extends UnaryNode with LogicNode with Simplifiable {
  import Simplifiable._
  override protected def simplified: Option[ValueNode] = {
    unaryOpLB(_ != 0)(value)
  }
  def toShallowString: String = s"isTruthy"
}

case class FuncArgNode(ix: Int) extends ValueNode {
  override def nodeClass: NodeClass[FuncArgNode] = Node.nodeClass

  override def toShallowString: String = s"Arg($ix)"
}

case object TrueNode extends LogicNode with LitNode {
  override def toShallowString: String = "True"
  def nodeClass: NodeClass[Node] = Node.nodeClass

  override def shallowHashCode = true.hashCode
}
case object FalseNode extends LogicNode with LitNode {
  override def toShallowString: String = "False"
  def nodeClass: NodeClass[Node] = Node.nodeClass

  override def shallowHashCode = false.hashCode
}

// High-level array ops. All the high-level memory-related ops are treated pessimistically:
// they are simply threaded between the containing block's begin and end node. We will do
// floating on later phases.

sealed trait HLMemoryEffectNode extends FixedWithNextNode

case class AllocFixedArrayNode(length: Int,
                               protected var _next: Node = null)
  extends HLMemoryEffectNode {
  override def toShallowString: String = s"AllocFixedArray(length = $length)"
  override def nodeClass = SingleNext.nodeClass
}

sealed trait ArrayIndexNode extends HLMemoryEffectNode {
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

  override def nodeClass = ReadArrayNode.nodeClass
}

object ReadArrayNode {
  val nodeClass: NodeClass[ReadArrayNode] = NodeClass(
    Seq[NodeField[ReadArrayNode, Node]](
      SimpleNodeField(
        _.base,
        (s, a) => s.base = a.asInstanceOf[ValueNode]
      ),
      SimpleNodeField(
        _.index,
        (s, a) => s.index = a.asInstanceOf[ValueNode]
      )
    ),
    Seq[NodeField[ReadArrayNode, Node]](
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
                          protected var _next: Node = null) extends ArrayIndexNode {
  addInput(_value)
  def value = _value
  def value_=(newValue: ValueNode) = _value = replaceInput(_value, newValue)

  override def toShallowString: String = "WriteArray"
  override def nodeClass = WriteArrayNode.nodeClass
}

object WriteArrayNode {
  val nodeClass: NodeClass[WriteArrayNode] = NodeClass(
    Seq[NodeField[WriteArrayNode, Node]](
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
    Seq[NodeField[WriteArrayNode, Node]](
      SimpleNodeField(
        _.next,
        _.next = _
      )
    )
  )
}

sealed trait BaseAnchoredNode extends ValueNode {
  protected var _anchor: BaseBeginNode
  addInput(_anchor)

  def anchor = _anchor
  def anchor_=(newAnchor: BaseBeginNode): Unit = {
    _anchor = replaceInput(_anchor, newAnchor)
  }
}

object AnchoringNode {
  val nodeClass = NodeClass(
    SimpleNodeField[AnchoringNode, Node](
      _.value,
      (s, a) => s.value = a.asInstanceOf[ValueNode]
    ),
    SimpleNodeField[AnchoringNode, Node](
      _.anchor,
      (s, a) => s.anchor = a.asInstanceOf[BaseBeginNode]
    )
  )
}

case class AnchoringNode(protected var _value: ValueNode, protected var _anchor: BaseBeginNode)
  extends BaseAnchoredNode with UseSingleValue[ValueNode] {
  override def nodeClass: NodeClass[AnchoringNode] = AnchoringNode.nodeClass

  override def toShallowString: String = "Anchoring"
}

object ScheduledNode {
  val nodeClass = NodeClass(
    Seq[NodeField[ScheduledNode, Node]](
      SimpleNodeField[ScheduledNode, Node](
        _.value,
        (s, a) => s.value = a.asInstanceOf[ValueNode]
      )
    ),
    Seq[NodeField[ScheduledNode, Node]](
      SimpleNodeField(
        _.next,
        (s, a) => s.next = a
      )
    )
  )
}

sealed trait FixedWithNextNode extends SingleNext[Node] with ValueNode {
  override def isIDomOf: Seq[Node] = Seq(_next)
}

case class ScheduledNode(protected var _value: ValueNode,
                         protected var _next: Node)
  extends UseSingleValue[ValueNode] with FixedWithNextNode {
  override def nodeClass: NodeClass[ScheduledNode] = ScheduledNode.nodeClass

  override def toShallowString: String = value.toShallowString

  override def isIDomOf: Seq[Node] = Seq(_next)
}

sealed trait BasePhiNode[N <: ValueNode] extends BaseAnchoredNode {
  protected var _composedInputs: ArrayBuffer[N]
  _composedInputs.foreach(addInput)

  override def anchor: BaseMergeNode = _anchor.asInstanceOf[BaseMergeNode]

  def composedInputs = _composedInputs
  def addComposedInput(n: N): N = {
    _composedInputs += addInput(n)
    n
  }
  def setComposedInputs(newInputs: Seq[N]) = {
    _composedInputs.foreach(removeInput)
    newInputs.foreach(addInput)
    _composedInputs = newInputs.to[ArrayBuffer]
  }
}

object BasePhiNode {
  val valueNodeClass: NodeClass[BasePhiNode[ValueNode]] = NodeClass(
    SimpleNodeField[BasePhiNode[ValueNode], Node](
      _.anchor,
      (s, a) => s.anchor = a.asInstanceOf[BaseBeginNode]
    ),
    NodeListField[BasePhiNode[ValueNode], Node](
      _.composedInputs,
      (s, a) => s.setComposedInputs(a.map(_.asInstanceOf[ValueNode]))
    )
  )

  val memoryNodeClass: NodeClass[BasePhiNode[MemoryStateNode]] = NodeClass(
    SimpleNodeField[BasePhiNode[MemoryStateNode], Node](
      _.anchor,
      (s, a) => s.anchor = a.asInstanceOf[BaseBeginNode]
    ),
    NodeListField[BasePhiNode[MemoryStateNode], Node](
      _.composedInputs,
      (s, a) => s.setComposedInputs(a.map(_.asInstanceOf[MemoryStateNode]))
    )
  )
}

case class ValuePhiNode(protected var _anchor: BaseBeginNode = null,
                        protected var _composedInputs: ArrayBuffer[ValueNode] = ArrayBuffer.empty)
  extends BasePhiNode[ValueNode] {

  def toShallowString: String = s"ValuePhi"
  override def nodeClass = BasePhiNode.valueNodeClass
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
                         protected var _composedInputs: ArrayBuffer[MemoryStateNode] = ArrayBuffer.empty)
  extends BasePhiNode[MemoryStateNode] {
  def toShallowString: String = s"MemoryPhi"
  override def nodeClass = BasePhiNode.memoryNodeClass
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

