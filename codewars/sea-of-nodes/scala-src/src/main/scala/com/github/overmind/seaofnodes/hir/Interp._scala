package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.ast._
import com.github.overmind.seaofnodes.hir.nodes._

import scala.annotation.tailrec
import scala.collection.mutable

object Interp {
  type Env = mutable.Map[Node, Value]

  def interp(g: Node): Value = {
    try {
      interp(Graph.emptyIdentityMap, g)
      throw UnexpectedNode("Never returns", g)
    } catch {
      case ReturnException(v) => v
    }
  }


  def interp(env: Env, n0: Node, verbose: Boolean = false): Unit = {
    var indent = 0

    // Virtual control register used to determine the dynamic control edge to the current block.
    var lastRegion: Option[RegionNode] = None

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
          val composedValues = n.composes.map(c => {
            // Compose the outgoing values.
            (c, goV(c.value))
          })
          // Calculate phi
          lastRegion match {
            case None =>
              assert(n.phis.isEmpty, s"Entry region has phis: $n")
            case Some(lastR) =>
              n.phis.foreach(phi => {
                val cs = phi.composeInputs.filter(c => c.ctrl eq lastR)
                assert(cs.length == 1)
                // Copy the value from the compose node to the phi.
                putPhi(phi, popCompose(cs.head))
              })
          }
          // And write back the freshly composed values.
          // This has to be done in a two-step style so that the newly composed values will not
          // interfere with the old ones consumed by the phi nodes.
          composedValues.foreach({ case (c, v) =>
            putCompose(c, v)
          })

          // Set lastRegion to here
          lastRegion = Some(n)

          // And jump to the next region.
          go(n.exit)

        case n: IfNode =>
          if (goV(n.cond).asBoolean) {
            go(n.t)
          } else {
            go(n.f)
          }

        case n: RetNode =>
          throw ReturnException(goV(n.value))

        case n: ValueNode =>
          sys.error(s"Shouldn't evaluate value nodes here: $n")
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

    // XXX: This can possibly evaluate a shared node multiple times.
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
        case phi: BasePhiNode =>
          env(phi)
        case _: ComposeNode =>
          sys.error(s"ComposeNode should never be directly evaluated: $n0")
        case _ =>
          sys.error(s"Not implemented: $n0")
      }
      pDedent(s"goV: $n0 -> $v")
      v
    }

    def putCompose(n: ComposeNode, v: Value) = {
      env += (n -> v)
    }

    def putPhi(n: BasePhiNode, v: Value) = {
      env += (n -> v)
    }

    def popCompose(n: ComposeNode): Value = {
      env.remove(n).getOrElse(sys.error(s"No such compose node: $n (${n.value} from ${n.ctrl})"))
    }

    go(n0)
  }

  case class UnexpectedNode(reason: String, node: Node) extends Exception
  case class ReturnException(value: Value) extends Exception
}
