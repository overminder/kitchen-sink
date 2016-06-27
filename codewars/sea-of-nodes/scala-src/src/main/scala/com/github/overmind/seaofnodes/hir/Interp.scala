package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.ast._
import com.github.overmind.seaofnodes.hir.nodes._

import scala.annotation.tailrec
import scala.collection.mutable

case class Interp(args: Seq[Value] = Seq(),
                  env: Interp.Env = Graph.emptyIdentityNodeMap,
                  verbose: Boolean = false) {

  import Interp._

  var indent = 0

  // Virtual control register used to determine the dynamic control edge to the current block.
  var comingFrom: Option[BaseEndNode] = None

  def run(n: Node): Value = {
    try {
      go(n)
      throw UnexpectedNode("Never returns", n)
    } catch {
      case ReturnException(v) => v
    }
  }

  @tailrec
  final def go(n0: Node): Unit = {
    if (verbose) {
      println(s"go: $n0")
    }
    n0 match {
      case n: GraphEntryNode =>
        go(n.next)
      case n: GraphExitNode =>
        throw UnexpectedNode("GraphExitNode reached", n)

      case n: BaseBeginNode =>
        n match {
          // Is merge: calculate phi
          case merge: BaseMergeNode =>
            comingFrom match {
              case None =>
                assert(merge.valuePhis.isEmpty, s"Entry region has phis: $n")
              case Some(lastR) =>
                val comingFromIx = merge.comingFrom.indexWhere(_ eq lastR)
                val newPhis = merge.valuePhis.map(phi => {
                  val c = phi.composedInputs(comingFromIx)
                  pIndent(s"Pulling $phi from ix($comingFromIx)")
                  // Copy the value from the compose node to the phi.
                  val v = goV(c)
                  pDedent(s"$phi = $v")
                  (phi, v)
                })
                // And write back the freshly composed values.
                // This has to be done in a two-step style so that the newly composed values will not
                // interfere with the old ones consumed by the phi nodes.
                newPhis.foreach({ case (phi, v) =>
                  putPhi(phi, v)
                })
            }
          case _ =>
            ()
        }
        // `Forget` old anchored values.
        n.anchored.foreach(env -= _)
        // Evaluate other anchored nodes.
        n.anchored.foreach(goV)
        go(n.next)

      case n: BaseEndNode =>
        comingFrom = Some(n)
        go(n.cfgSuccessor)

      case n: IfNode =>
        if (goV(n.value).asBoolean) {
          go(n.t)
        } else {
          go(n.f)
        }

      case n: RetNode =>
        throw ReturnException(goV(n.value))

      case fix: FixedWithNextNode =>
        fix match {
          case n: AllocFixedArrayNode =>
            // XXX: Control dependency
            val v = ArrayValue.create(n.length)
            env += (n -> v)
          case n: ReadArrayNode =>
            // XXX: Control dependency
            val v = goV(n.base).at(goV(n.index))
            env += (n -> v)
          case n: WriteArrayNode =>
            // XXX: Control dependency
            goV(n.base).setAt(goV(n.index), goV(n.value))
          case n: ScheduledNode =>
            env += (n -> goV(n.value))
        }
        go(fix.next)

      case n: ValueNode =>
        sys.error(s"Shouldn't evaluate value nodes here: $n")
    }
  }

  def pIndent(s: String): Unit = {
    indent += 2
    pIfVerbose(s)
  }

  def pIfVerbose(s: String): Unit = {
    if (verbose) {
      println(s"${" " * indent}$s")
    }
  }

  def pDedent(s: String): Unit = {
    pIfVerbose(s)
    indent -= 2
  }

  // XXX: This can possibly evaluate a shared node multiple times.
  def goV(n0: ValueNode): Value = {
    pIndent(s"goV: $n0")
    val v = n0 match {
      case LitLongNode(lval) =>
        LongValue(lval)
      case TrueNode =>
        TrueValue
      case FalseNode =>
        FalseValue
      case AddNode(lhs, rhs) =>
        goV(lhs) + goV(rhs)
      case SubNode(lhs, rhs) =>
        goV(lhs) - goV(rhs)
      case LessThanNode(lhs, rhs) =>
        goV(lhs) < goV(rhs)
      case IsTruthyNode(n) =>
        BoolValue(goV(n).asInstanceOf[LongValue].lval)
      case phi: ValuePhiNode =>
        env(phi)
      case anc: AnchoringNode =>
        env.getOrElseUpdate(anc, goV(anc.value))
      case fix: FixedWithNextNode =>
        // This should have been evaluated in go.
        env(fix)
      case arg: FuncArgNode =>
        args(arg.ix)
      case _ =>
        sys.error(s"Not implemented: $n0")
    }
    pDedent(s"goV: $n0 -> $v")
    v
  }

  def putPhi(n: ValuePhiNode, v: Value) = {
    env += (n -> v)
  }
}

object Interp {
  type Env = mutable.Map[Node, Value]

  case class UnexpectedNode(reason: String, node: Node) extends Exception
  case class ReturnException(value: Value) extends Exception
}
