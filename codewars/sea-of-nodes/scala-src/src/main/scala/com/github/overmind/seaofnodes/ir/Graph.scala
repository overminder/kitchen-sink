package com.github.overmind.seaofnodes.ir

import java.util
import java.util.Collections

import com.github.overmind.seaofnodes.DotGen
import com.github.overmind.seaofnodes.ir.Graph.Unexpected

import scala.collection.JavaConverters._
import scala.collection.mutable

object ShallowRegionBuilder {
  def exits(e: RegionNode): Seq[RegionNode] = {
    e match {
      case r: RegionNode => r.exit match {
        case toR: RegionNode => Seq(toR)
        case EndNode() => Seq()
        case IfNode(t, f) => Seq(t, f)
        case RetNode() => Seq()
        case otherwise => throw Unexpected(s"Shouldn't be an exit: $otherwise")
      }
    }
  }

  def preds(region: RegionNode): Seq[RegionNode] = {
    region.predecessors.flatMap {
      case r: RegionNode =>
        Some(r)
      case i: IfNode =>
        Some(i.region)
      case s: StartNode =>
        None
      case pred =>
        throw Unexpected(s"Shouldn't have such predecessor: $pred")
    }
  }

  def dfsRegion(b: RegionNode)(f: RegionNode => Unit): Unit = {
    def go(b: RegionNode, visited: mutable.Set[RegionNode]): Unit = {
      if (!visited.contains(b)) {
        visited.add(b)
        f(b)
        exits(b).foreach(go(_, visited))
      }
    }

    go(b, Graph.emptyIdentitySet)
  }
}

case class ShallowRegionBuilder() {
  // Scan through the ASTs to build all the blocks.
  import com.github.overmind.seaofnodes.Ast._

  var nextRegionId = 0
  var currentRegion: Option[RegionNode] = None
  var entryRegion: Option[RegionNode] = None

  def buildRootStmt(s: Stmt): RegionNode = {
    val entry = ensureRegion()
    entryRegion = Some(entry)
    buildStmt(s)
    entry
  }

  def allocRegion(): RegionNode = {
    val r = RegionNode(nextRegionId)
    nextRegionId += 1
    r
  }

  def ensureRegion(): RegionNode = {
    currentRegion match {
      case None =>
        val b = allocRegion()
        currentRegion = Some(b)
        b
      case Some(b) => b
    }
  }

  def finishRegion(exit: ControlNode): RegionNode = {
    val r = ensureRegion()
    r.exit = exit
    currentRegion = None
    r
  }

  def startRegionThatEndsWith(b: RegionNode, s: Option[Stmt], exit: ControlNode): RegionNode = {
    setCurrentRegion(b)
    s.foreach(buildStmt)
    finishRegion(exit)
  }

  def setCurrentRegion(r: RegionNode): Unit = {
    assert(currentRegion.isEmpty, s"currentRegion is not None: $currentRegion")
    currentRegion = Some(r)
  }

  def buildStmt(s: Stmt): Unit = {
    ensureRegion()
    s match {
      case Stmt.Begin(ss) => ss.foreach(buildStmt)

      case Stmt.If(_, t, f) =>
        val tB = allocRegion()
        val fB = allocRegion()
        val endB = allocRegion()

        finishRegion(IfNode(tB, fB))
        startRegionThatEndsWith(tB, Some(t), endB)
        startRegionThatEndsWith(fB, Some(f), endB)
        setCurrentRegion(endB)

      case Stmt.While(cond, body) =>
        val checkB = allocRegion()
        val loopB = allocRegion()
        val endB = allocRegion()

        finishRegion(checkB)
        startRegionThatEndsWith(checkB, None, IfNode(loopB, endB))
        startRegionThatEndsWith(loopB, Some(body), checkB)
        setCurrentRegion(endB)

      case Stmt.Ret(e) =>
        finishRegion(RetNode())

      case _: Stmt.Assign => ()
    }
  }
}

object Graph {
  def emptyIdentitySet[A <: AnyRef] =
    Collections.newSetFromMap(new util.IdentityHashMap[A, java.lang.Boolean]()).asScala

  def emptyIdentityMap[A <: AnyRef, B] = new util.IdentityHashMap[A, B]().asScala


  case class UndefinedVarInGraph(name: String) extends Exception
  case class Unexpected(what: String) extends Exception

  case class DotContext(name: String) {
    val g = DotGen.Graph(name)

    def addNode(n: Node): DotContext = {
      val visited = emptyIdentityMap[Node, DotGen.NodeId]
      def go(n: Node): DotGen.NodeId = {
        visited.getOrElse(n, {
          val id = g.addText(n.toShallowString)
          visited += (n -> id)
          n.inputs.map(go).foreach(i => {
            g.addEdge(id, i)
          })
          n match {
            case c: ControlNode =>
              c.successors.map(go).foreach(s => {
                g.addEdge(id, s)
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

  case class GraphBuilder() {
    import ShallowRegionBuilder._
    import com.github.overmind.seaofnodes.Ast._

    type Defs = mutable.Map[String, ValueNode]
    type RegionId = RegionNode.Id

    var currentRegion: RegionNode = _  // Unsafe
    val blockDefs = mutable.Map.empty[RegionId, Defs]
    val regions = mutable.Map.empty[RegionId, RegionNode]
    val deferredPhis = mutable.ArrayBuffer.empty[(String, PhiNode)]

    def build(start: RegionNode, s: Stmt): RegionNode = {
      buildRegions(start)
      buildRootStmt(s)
      start
    }

    def buildRegions(start: RegionNode): Unit = {
      dfsRegion(start)(r => {
        blockDefs += (r.id -> mutable.Map.empty)
        regions += (r.id -> r)
      })
      currentRegion = start
    }

    def buildRootStmt(s: Stmt): Unit = {
      buildStmt(s)
      resolveDeferredPhis()
    }

    def buildStmt(s: Stmt): Unit = {
      s match {
        case Stmt.Assign(v, e) =>
          defineVar(v, buildExpr(e))

        case Stmt.Begin(ss) =>
          ss.foreach(buildStmt)

        case Stmt.If(cond, t, f) =>
          // A bit repetitive..
          val condNode = asLogicNode(buildExpr(cond))
          val exit = currentRegion.exit.asInstanceOf[IfNode]
          exit.cond = condNode

          currentRegion = exit.t
          buildStmt(t)

          currentRegion = exit.f
          buildStmt(f)

          currentRegion = exit.t.exit.asInstanceOf[RegionNode]

        case Stmt.While(cond, body) =>
          val checkRegion = currentRegion.exit.asInstanceOf[RegionNode]

          currentRegion = checkRegion
          val condNode = asLogicNode(buildExpr(cond))
          val loopExit = currentRegion.exit.asInstanceOf[IfNode]
          loopExit.cond = condNode
          val bodyRegion = loopExit.t
          val endRegion = loopExit.f

          currentRegion = bodyRegion
          buildStmt(body)

          currentRegion = endRegion

        case Stmt.Ret(v) =>
          currentRegion.exit.asInstanceOf[RetNode].value = buildExpr(v)
      }
    }

    def addDeferredPhi(v: String, phi: PhiNode): Unit = {
      deferredPhis += ((v, phi))
    }

    def resolveDeferredPhis(): Unit = {
      def resolve(v: String, onRegion: RegionNode, fromPred: RegionNode): ValueNode = {
        blockDefs(fromPred.id)(v)
      }
      deferredPhis.foreach({ case (v, phi) =>
        val phiPreds = preds(phi.region)
        val defs = phiPreds.map(resolve(v, phi.region, _)).zip(phiPreds).map {
          case (v, r) => ComposeNode(v, r)
        }
        defs.foreach(phi.addInput)
      })
    }

    def useVar(v: String): ValueNode = {
      useVarAt(v, currentRegion.id)
    }

    def useVarAt(v: String, id: RegionId): ValueNode = {
      val here = regions(id)
      val defs = blockDefs(id)
      defs.get(v) match {
        case Some(n) => n
        case None =>
          // Hmm...
          val ps = preds(here)
          ps.length match {
            case 0 =>
              throw UndefinedVarInGraph(v)
            case 1 =>
              assert(ps.head.id != id)
              useVarAt(v, ps.head.id)
            case _ =>
              val phi = PhiNode(here)
              defs += (v -> phi)
              addDeferredPhi(v, phi)
              ps.foreach(p => {
                useVarAt(v, p.id)
              })
              phi
          }
      }
    }

    def defineVar[N <: ValueNode](v: String, n: N): N = {
      val defs = blockDefs(currentRegion.id)
      defs += (v -> n)
      n
    }

    def buildOp(op: BinaryOp)(lhs: ValueNode, rhs: ValueNode): ValueNode = {
      op match {
        case BinaryOp.Add => AddNode(lhs, rhs)
        case BinaryOp.Sub => SubNode(lhs, rhs)
        case BinaryOp.LessThan => LessThanNode(lhs, rhs)
      }
    }

    def buildExpr(e: Expr): ValueNode = {
      e match {
        case Expr.Binary(op, lhs, rhs) =>
          buildOp(op)(buildExpr(lhs), buildExpr(rhs))
        case Expr.Lit(lval) =>
          LitNode(lval)
        case Expr.Var(v) =>
          useVar(v)
      }
    }
  }

  def asLogicNode(v: ValueNode): LogicNode = {
    v match {
      case logic: LogicNode => logic
      case _ => IsTruthyNode(v)
    }
  }
}
