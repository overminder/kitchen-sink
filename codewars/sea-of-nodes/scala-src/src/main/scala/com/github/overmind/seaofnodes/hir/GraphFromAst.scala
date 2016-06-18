package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.ast.BinaryOp.{Add, LessThan, Sub}
import com.github.overmind.seaofnodes.ast.Interp.UndefinedVar

import scala.collection.mutable
import com.github.overmind.seaofnodes.ast._
import com.github.overmind.seaofnodes.hir.Graph.UndefinedVarInGraph
import com.github.overmind.seaofnodes.hir.nodes._

object GraphFromAst {
  def build(rootStmt: Stmt): Graph = {
    val b = Builder(rootStmt)
    b.buildRoot()
    b.g
  }

  case class Builder(rootStmt: Stmt) {
    val start = GraphEntryNode()
    val end = GraphExitNode()
    val g = Graph(start, end)
    var current: Option[SingleNext[Node]] = Some(start)
    var nextBlockId = 1

    val cached = mutable.Map.empty[Node, Node]

    def buildRoot(): Unit = {
      buildStmt(consEnv(NilEnv), rootStmt)
      if (current.isDefined) {
        sys.error("You forget to write a return.")
      }
    }

    // Maybe move this to Graph?
    def unique[N <: Node](n: N): N = {
      n match {
        case vn: ValueNumberable =>
          g.unique(n)
        case _ =>
          n
      }
    }

    def simplify(n: Node): Node = {
      unique(n match {
        case s: Simplifiable =>
          s.simplifyInGraph(g)
        case _ =>
          n
      })
    }

    def attachNext[N <: Node](next: N): N = {
      current match {
        case Some(c) =>
          c.next = next
          next match {
            case n: SingleNext[_] =>
              current = Some(n.asInstanceOf[SingleNext[Node]])
            case _ =>
              current = None
          }
        case None =>
          sys.error(s"Attaching dead code: $next")
          ()
      }
      next
    }

    def attachPhisAfterIf(tEnv: ConsEnv, fEnv: ConsEnv, merge: MergeNode): Unit = {
      val keys = tEnv.head.keys.toSet.union(fEnv.head.keys.toSet)
      val mergedValues = keys.flatMap(k => {
        (tEnv.useVar(k), fEnv.useVar(k)) match {
          case (Some(t), Some(f)) =>
            // Both defined: merge both.
            Some(Seq(t, f))
          case (Some(t), None) =>
            // Only one branch defined: if consEnv.tail defines this var, merge it.
            // Otherwise don't let it escape.
            fEnv.tail.useVar(k).map(Seq(t, _))
          case (None, Some(f)) =>
            // Same as above.
            tEnv.tail.useVar(k).map(Seq(_, f))
          case _ =>
            // Neither defined: no need for a phi here
            None
        }
      }.map((k, _)))

      // Move escaped defs to outer.
      val env = tEnv.tail
      mergedValues.foreach({ case (k, ns) =>
        // XXX: Need to properly manage live nodes in the graph.
        val phi = ValuePhiNode(merge, ns)

        // And `escape` the defined values.
        env.defVar(k, phi)
      })
    }

    def killPhisInAbruptlyReturnedWhileBody(loopEnv: MergingEnv) = {
      loopEnv.possiblePhis.foreach({ case (k, phi) =>
        loopEnv.body.getOrElse(k, sys.error("Impossible")) match {
          case n =>
            // All the possible phis should be degenerated.
            assert(n eq phi)
            val pointsTo = phi.composedInputs.head
            phi.replaceAllUsesWith(pointsTo)
            phi.remove()
            // Should probably do this in a later phase with a worklist.
            pointsTo.uses.foreach(simplify)
        }
      })
    }

    def attachPhisOnWhile(loopEnv: MergingEnv, loopMerge: LoopBeginNode) = {
      // For each possibly phi-introducing use in the loop body...
      loopEnv.possiblePhis.foreach({ case (k, phi) =>
        loopEnv.body.getOrElse(k, sys.error("Impossible")) match {
          // Check its definition at the loop exit
          case n if phi eq n =>
            // Not defined in the loop: degenerated phi.
            val pointsTo = phi.composedInputs.head
            phi.replaceAllUsesWith(pointsTo)
            loopEnv.body += (k -> pointsTo)
          case n =>
            // Defined in the loop: add this def to phi.
            phi.anchor = loopMerge
            phi.addComposedInput(n)
        }
      })

      // Calculate escaped defs.
      val escapedValues = loopEnv.body.flatMap({ case (k, v) =>
        // For each def in the loop body...
        if (!loopEnv.possiblePhis.contains(k)) {
          // ...that is not used in the loop body:
          loopEnv.parent.useVar(k) match {
            case Some(outerDef) =>
              // If the outer env also defined this value:
              // Let this value escape.
              val phi = ValuePhiNode(loopMerge, Seq(outerDef, v))
              Some(k, phi)
            case _ =>
              // Otherwise kill this value.
              None
          }
        } else {
          Some(k, v)
        }
      })

      // Move escaped defs to outer.
      escapedValues.foreach({ case (k, v) =>
        loopEnv.parent.defVar(k, v)
      })
    }

    def buildStmt(env: Env, s: Stmt): Unit = {
      val currentWit = current match {
        case Some(x) =>
          x
        case None =>
          return
      }

      s match {
        case Begin(ss) => ss.foreach(buildStmt(env, _))
        case Assign(v, e) => v match {
          case LVar(v) =>
            env.defVar(v, buildExpr(env, e))
          case LIndex(base, index) =>
            attachNext(
              WriteArrayNode(
                buildExpr(env, base),
                buildExpr(env, index),
                buildExpr(env, e)
              ))
        }
        case If(cond, t, f) =>
          val condNode = asLogicNode(buildExpr(env, cond))
          val tBegin = makeBegin
          val fBegin = makeBegin
          attachNext(IfNode(condNode, tBegin, fBegin))
          current = Some(tBegin)
          val tEnv = consEnv(env)
          buildStmt(tEnv, t)
          val tEnd = EndNode()
          val tReturned = current.isEmpty
          if (!tReturned) {
            attachNext(tEnd)
          }

          current = Some(fBegin)
          val fEnv = consEnv(env)
          buildStmt(fEnv, f)
          val fReturned = current.isEmpty
          val fEnd = EndNode()
          if (!fReturned)  {
            attachNext(fEnd)
          }

          if (tReturned && fReturned) {
            // We are done - both branches are end.
          } else if (tReturned) {
            // Reopen the false branch
            val prevNext = fEnd.predecessor.asInstanceOf[SingleNext[Node]]
            prevNext.next = null
            current = Some(prevNext)
            fEnv.collapseDefs()
          } else if (fReturned) {
            // Reopen the true branch
            val prevNext = tEnd.predecessor.asInstanceOf[SingleNext[Node]]
            prevNext.next = null
            current = Some(prevNext)
            tEnv.collapseDefs()
          } else {
            val merge = makeMerge
            current = Some(merge)
            merge.addComingFrom(tEnd)
            merge.addComingFrom(fEnd)
            attachPhisAfterIf(tEnv, fEnv, merge)
          }

        case While(cond, body) =>
          val blockEnd = EndNode()
          attachNext(blockEnd)

          val loopEnv = mergingEnv(env)
          val condNode = asLogicNode(buildExpr(loopEnv, cond))
          val loopMerge = makeLoopBegin
          val loopBodyStart = makeBegin
          val loopBodyEnd = LoopEndNode()
          val loopExit = makeLoopExit
          loopMerge.addComingFrom(blockEnd)
          loopMerge.addComingFrom(loopBodyEnd)
          loopMerge.next = IfNode(condNode, loopBodyStart, loopExit)

          current = Some(loopBodyStart)
          buildStmt(loopEnv, body)
          val abruptReturn = current.isEmpty
          if (abruptReturn) {
            // We are not on a merge node anymore,
            // rewrite [ ... -> End <- Merge -> If ] into [ ... -> If ],
            // and don't let any of the the newly created defs escape.
            val ifNode = loopMerge.next
            loopMerge.remove()
            blockEnd.replaceThisOnPredecessor(ifNode)
            blockEnd.remove()
            killPhisInAbruptlyReturnedWhileBody(loopEnv)
          } else {
            attachNext(loopBodyEnd)
            attachPhisOnWhile(loopEnv, loopMerge)
          }

          current = Some(loopExit)

        case Ret(e) =>
          val ret = RetNode(buildExpr(env, e))
          attachNext(ret)
          end.addReturn(ret)
      }
    }

    def buildExpr(env: Env, e: Expr): ValueNode = {
      e match {
        case Binary(op, lhs, rhs) => simplify(denoteOp(op)(buildExpr(env, lhs), buildExpr(env, rhs))).asInstanceOf[ValueNode]
        case Lit(lval) => unique(LitNode(lval))
        case LVar(v) => env.useVarOrThrow(v)
        case LIndex(base, index) =>
          attachNext(
            ReadArrayNode(
              buildExpr(env, base),
              buildExpr(env, index)
            ))
        case AllocArray(len) =>
          attachNext(
            AllocFixedArrayNode(len)
          )
      }
    }

    def denoteOp(op: BinaryOp): (ValueNode, ValueNode) => ValueNode = {
      op match {
        case Add => AddNode
        case Sub => SubNode
        case LessThan => LessThanNode
      }
    }

    def makeBegin = {
      val n = BeginNode(nextBlockId)
      nextBlockId += 1
      n
    }

    def makeMerge = {
      val n = MergeNode(nextBlockId)
      nextBlockId += 1
      n
    }

    def makeLoopBegin = {
      val n = LoopBeginNode(nextBlockId)
      nextBlockId += 1
      n
    }

    def makeLoopExit = {
      val n = LoopExitNode(nextBlockId)
      nextBlockId += 1
      n
    }

    def asLogicNode(node: ValueNode) = {
      node match {
        case x: LogicNode => x
        case _ => IsTruthyNode(node)
      }
    }

    def consEnv(tail: Env) = {
      ConsEnv(mutable.Map.empty, tail)
    }

    def mergingEnv(parent: Env) = {
      MergingEnv(mutable.Map.empty, parent)
    }

    // !Builder
  }

  sealed trait Env {
    def useVar(v: String): Option[ValueNode]
    def defVar(v: String, n: ValueNode)
    def keys: Iterable[String]

    final def useVarOrThrow(v: String): ValueNode = {
      useVar(v).getOrElse(throw UndefinedVarInGraph(v))
    }
  }

  case object NilEnv extends Env {
    override def useVar(v: String): Option[ValueNode] = None

    override def defVar(v: String, n: ValueNode): Unit = {
      sys.error("Shouldn't be reachable")
    }

    override def keys: Iterable[String] = Iterable.empty
  }

  case class ConsEnv(head: mutable.Map[String, ValueNode], tail: Env) extends Env {
    override def useVar(v: String): Option[ValueNode] = {
      head.get(v).orElse(tail.useVar(v))
    }

    override def keys = head.keys ++ tail.keys

    override def defVar(v: String, n: ValueNode): Unit = {
      head += (v -> n)
    }

    def collapseDefs() = {
      head.foreach({ case (k, v) => tail.defVar(k,v ) })
    }
  }

  case class MergingEnv(body: mutable.Map[String, ValueNode], parent: Env) extends Env {
    val possiblePhis = mutable.Map.empty[String, ValuePhiNode]

    override def useVar(v: String): Option[ValueNode] = {
      body.get(v).orElse({
        val parentV = parent.useVarOrThrow(v)
        val phi = ValuePhiNode(null, Seq(parentV))
        possiblePhis += (v -> phi)
        body += (v -> phi)
        Some(phi)
      })
    }

    override def defVar(v: String, n: ValueNode): Unit = {
      body += (v -> n)
    }

    override def keys: Iterable[String] = body.keys ++ parent.keys
  }
}

