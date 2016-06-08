package com.github.overmind.seaofnodes.ir

import scala.annotation.tailrec
import scala.collection.mutable;

object Interp {
  type Env = mutable.Map[PhiNode, Value]

  def interp(g: Node): Value = {
    try {
      interp(Graph.emptyIdentityMap, g)
      throw UnexpectedNode("Never returns", g)
    } catch {
      case ReturnException(v) => v
    }
  }

  sealed trait Value {
    def +(that: Value): Value
    def -(that: Value): Value
    def <(that: Value): Value
  }

  sealed trait BoolValue extends Value {
    def isTruthy: Boolean
    def +(that: Value): Value = {
      throw UnexpectedValue("Not a LongValue", this)
    }
    def -(that: Value): Value = {
      throw UnexpectedValue("Not a LongValue", this)
    }
    def <(that: Value): Value = {
      throw UnexpectedValue("Not a LongValue", this)
    }
  }
  case object TrueValue extends BoolValue {
    override def isTruthy = true
  }
  case object FalseValue extends BoolValue {
    override def isTruthy = false
  }
  case object BoolValue {
    def apply(lval: Long): BoolValue = {
      if (lval == 0) {
        FalseValue
      } else {
        TrueValue
      }
    }
    def apply(bval: Boolean): BoolValue = {
      if (bval) {
        TrueValue
      } else {
        FalseValue
      }
    }
  }
  case class LongValue(lval: Long) extends Value {
    def expectLong(op: (Long, Long) => Value)(that: Value): Value = {
      that match {
        case LongValue(rhs) => op(lval, rhs)
        case _ => throw UnexpectedValue("Expect LongValue", that)
      }
    }
    override def +(that: Value) = expectLong((x, y) => LongValue(x + y))(that)
    override def -(that: Value) = expectLong((x, y) => LongValue(x - y))(that)
    override def <(that: Value) = expectLong((x, y) => BoolValue(x < y))(that)
  }

  def interp(env: Env, n0: Node, verbose: Boolean = false): Unit = {
    var indent = 0

    var lastRegion: Option[RegionNode] = None

    def phis(r: RegionNode): Seq[PhiNode] = {
      r.uses.flatMap({
        case phi: PhiNode => Some(phi)
        case _: ComposeNode => None
        case n => throw UnexpectedNode("RegionNode input", n)
      })
    }

    @tailrec
    def go(n0: Node): Unit = {
      if (verbose) {
        println(s"go: $n0")
      }
      n0 match {
        case n: StartNode =>
          go(n.successor)
        case n: EndNode =>
          throw UnexpectedNode("EndNode reached", n)
        case n: RegionNode =>
          // Calculate phi
          lastRegion match {
            case None =>
              assert(phis(n).isEmpty, s"Entry region has phis: $n")
            case Some(lastR) =>
              val phiValues = phis(n).map(phi => {
                val cs = phi.composeInputs.filter(c => c.ctrl eq lastR)
                assert(cs.length == 1)
                (phi, goV(cs.head.value))
              })
              // And assign the new phi values all at once.
              phiValues.foreach({ case (phi, v) =>
                putDef(phi, v)
              })
          }

          // Set lastRegion to here
          lastRegion = Some(n)

          // And jump to the next region.
          go(n.exit)

        case n: IfNode =>
          if (goV(n.cond).asInstanceOf[BoolValue].isTruthy) {
            go(n.t)
          } else {
            go(n.f)
          }

        case n: ValueNode =>
          goV(n)

        case n: RetNode =>
          throw ReturnException(goV(n.value))
      }
    }

    def pIndent(s: String): Unit = {
      if (verbose) {
        indent += 2
        println(s"${" " * indent}$s")
      }
    }

    def pDedent(s: String): Unit = {
      if (verbose) {
        println(s"${" " * indent}$s")
        indent -= 2
      }
    }

    def goV(n0: ValueNode): Value = {
      pIndent(s"goV: $n0")
      val v = n0 match {
        case LitNode(lval) =>
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
        case _: ComposeNode =>
          sys.error(s"ComposeNode should never be directly evaluated: $n0")
        case phi: PhiNode =>
          env(phi)
      }
      pDedent(s"goV: $n0 -> $v")
      v
    }

    def putDef(n: PhiNode, v: Value) = {
      env += (n -> v)
    }

    def delDef(n: PhiNode) = {
      env -= n
    }

    go(n0)
  }

  case class UnexpectedNode(reason: String, node: Node) extends Exception
  case class UnexpectedValue(reason: String, value: Value) extends Exception
  case class ReturnException(value: Value) extends Exception
}
