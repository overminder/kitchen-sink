package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.ast.BinaryOp.{Add, LessThan, Sub}
import com.github.overmind.seaofnodes.ast.Interp.UndefinedVar

import scala.collection.mutable
import com.github.overmind.seaofnodes.ast._
import com.github.overmind.seaofnodes.hir.Graph.UndefinedVarInGraph
import com.github.overmind.seaofnodes.hir.nodes._

object GraphFromAst {
  case class Builder(rootStmt: Stmt) {
    val start = GraphEntryNode()
    var current: SingleNext[Node] = start
    var nextBlockId = 1

    def buildRoot(): Unit = {
      buildStmt(SimpleEnv(), rootStmt)
    }

    def attachNext(next: Node): Unit = {
      current.next = next
      next match {
        case n: SingleNext[Node] =>
          current = n
        case _ =>
          current = null
      }
    }

    def attachPhisForIf(tEnv: ConsEnv, fEnv: ConsEnv, merge: MergeNode): Unit = {
      val keys = tEnv.head.keys.toSet.union(fEnv.head.keys.toSet)
      val mergedValues = keys.flatMap(k => {
        (tEnv.useVar(k), fEnv.useVar(k)) match {
          case (Some(t), Some(f)) =>
            // Both defined: merge both.
            Some(Seq(t, f))
          case (Some(t), None) =>
            // Only one branch defined: get the other value from consEnv.tail
            Some(Seq(t, fEnv.tail.useVarOrThrow(k)))
          case (None, Some(f)) =>
            // Only one branch defined: get the other value from consEnv.tail
            Some(Seq(tEnv.tail.useVarOrThrow(k), f))
          case _ =>
            // Neither defined: no need for a phi here
            None
        }
      }.map((k, _)))
      val env = tEnv.tail
      mergedValues.foreach({ case (k, ns) =>
        // XXX: Need to properly manage live nodes in the graph.
        val phi = ValuePhiNode(merge, ns)

        // And `escape` the defined values.
        env.defVar(k, phi)
      })
    }

    def attachPhisForWhile(loopEnv: MergingEnv, loopMerge: LoopBeginNode) = {
      loopEnv.possiblePhis.foreach({
        case (k, n) =>
          loopEnv.body.useVarOrThrow(k) match {
            case phi if phi eq n =>
              // No def: degenerated phi.
              n.replaceAllUsagesWith(n.composedInput.head)
            case notPhi =>
              // Add this def to phi.
              n.addComposedInput(notPhi)
          }
      })
    }

    def buildStmt(env: Env, s: Stmt): Unit = {
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
          current = tBegin
          val tEnv = consEnv(env)
          buildStmt(tEnv, t)
          val tEnd = EndNode()
          attachNext(tEnd)

          current = fBegin
          val fEnv = consEnv(env)
          buildStmt(fEnv, f)
          val fEnd = EndNode()
          attachNext(fEnd)

          val merge = makeMerge
          current = merge
          attachPhisForIf(tEnv, fEnv, merge)

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

          current = loopBodyStart
          buildStmt(loopEnv, body)
          attachNext(loopBodyEnd)

          attachPhisForWhile(loopEnv, loopMerge)

          current = loopExit

        case Ret(e) =>
          throw ReturnFrom(buildExpr(env, e))
      }
    }

    def buildExpr(env: Env, e: Expr): ValueNode = {
      e match {
        case Binary(op, lhs, rhs) => denoteOp(op)(evalExpr(env, lhs), evalExpr(env, rhs))
        case Lit(lit) => LongValue(lit)
        case LVar(v) => env.getOrElse(v, throw UndefinedVar(env, v))
        case LIndex(base, index) => evalExpr(env, base).at(evalExpr(env, index))
        case AllocArray(len) => ArrayValue.create(len)
      }
    }

    def denoteOp(op: BinaryOp): (ValueNode, ValueNode) => ValueNode = {
      op match {
        case Add => AddNode
        case Sub => _ - _
        case LessThan => (lhs, rhs) => lhs < rhs
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
      ConsEnv(SimpleEnv(), tail)
    }

    def mergingEnv(parent: Env) = {
      MergingEnv(SimpleEnv(), parent)
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

  case class SimpleEnv(m: mutable.Map[String, ValueNode] = mutable.Map.empty) extends Env {
    override def useVar(v: String): Option[ValueNode] = {
      m.get(v)
    }
    override def keys = m.keys
    override def defVar(v: String, n: ValueNode) = {
      m += (v -> n)
    }
  }

  case class ConsEnv(head: Env, tail: Env) extends Env {
    override def useVar(v: String): Option[ValueNode] = {
      head.useVar(v).orElse(tail.useVar(v))
    }

    override def keys = head.keys ++ tail.keys

    override def defVar(v: String, n: ValueNode): Unit = {
      head.defVar(v, n)
    }
  }

  case class MergingEnv(body: Env, parent: Env) extends Env {
    val possiblePhis = mutable.Map.empty[String, ValuePhiNode]

    override def useVar(v: String): Option[ValueNode] = {
      body.useVar(v).orElse({
        val parentV = parent.useVarOrThrow(v)
        val phi = ValuePhiNode(null, Seq(parentV))
        possiblePhis += (v -> phi)
        body.defVar(v, phi)
        Some(phi)
      })
    }

    override def defVar(v: String, n: ValueNode): Unit = {
      body.defVar(v, n)
    }

    override def keys: Iterable[String] = body.keys ++ parent.keys
  }

  case class ReturnFrom(n: ValueNode) extends Exception
}

