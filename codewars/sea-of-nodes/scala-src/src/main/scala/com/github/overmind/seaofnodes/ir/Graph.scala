package com.github.overmind.seaofnodes.ir

import java.util
import java.util.Collections

import scala.collection.JavaConverters._
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

case class ShallowRegionBuilder() {
  // Scan through the ASTs to build all the blocks.
  import Graph._
  import com.github.overmind.seaofnodes.Ast._

  var nextRegionId = 0
  var currentRegion: Option[RegionNode] = None
  var entryRegion: Option[RegionNode] = None
  val endNode = EndNode()

  def buildRootStmt(s: Stmt): RegionNode = {
    val entry = ensureRegion()
    entryRegion = Some(entry)
    buildStmt(s)
    dceRegion(entry)
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
        finishRegion(RetNode(endNode))

      case _: Stmt.Assign => ()
    }
  }

  def dceRegion(entry: RegionNode): Unit = {
    val reachable = mutable.Set.empty[Int]
    dfsRegion(entry) { r =>
      reachable += r.id
    }

    val deleted = EndNode()
    dfsRegion(entry) { r =>
      val ps = preds(r).toArray
      ps.foreach(p => {
        if (!reachable.contains(p.id)) {
          p.exit = deleted
        }
      })
    }
  }
}

object Graph {
  def emptyIdentitySet[A <: AnyRef] =
    Collections.newSetFromMap(new util.IdentityHashMap[A, java.lang.Boolean]()).asScala

  def emptyIdentityMap[A <: AnyRef, B] = new util.IdentityHashMap[A, B]().asScala

  case class UndefinedVarInGraph(name: String) extends Exception
  case class Unexpected(what: String) extends Exception


  case class GraphBuilder() {
    import com.github.overmind.seaofnodes.Ast._

    type Defs = mutable.Map[String, ValueNode]
    type RegionId = RegionNode.Id

    var currentRegion: Option[RegionNode] = None
    val blockDefs = mutable.Map.empty[RegionId, Defs]
    val regions = mutable.Map.empty[RegionId, RegionNode]
    val deferredPhis = ArrayBuffer.empty[(String, PhiNode)]
    val cachedNodes = mutable.Map.empty[Node, Node]

    def build(start: RegionNode, s: Stmt): StartNode = {
      buildRegions(start)
      buildRootStmt(s)
      StartNode(start)
    }

    def unique[N <: Node](n: N): N = {
      cachedNodes.getOrElseUpdate(n, n).asInstanceOf[N]
    }

    def buildRegions(start: RegionNode): Unit = {
      dfsRegion(start)(r => {
        regions += (r.id -> r)
      })
      currentRegion = Some(start)
    }

    def buildRootStmt(s: Stmt): Unit = {
      buildStmt(s)
      resolveDeferredPhis()
    }

    def buildStmt(s: Stmt): Unit = {
      // So that we won't build unreachable code.
      currentRegion.foreach(buildStmt(s, _))
    }

    def buildStmt(s: Stmt, here: RegionNode): Unit = {
      s match {
        case Stmt.Assign(v, e) =>
          defineVar(v, buildExpr(e, here), here)

        case Stmt.Begin(ss) =>
          ss.foreach(buildStmt)

        case Stmt.If(cond, t, f) =>
          // A bit repetitive..
          val condNode = asLogicNode(buildExpr(cond, here))
          val exit = here.exit.asInstanceOf[IfNode]
          exit.cond = condNode

          currentRegion = Some(exit.t)
          buildStmt(t)

          currentRegion = Some(exit.f)
          buildStmt(f)

          currentRegion = (exit.t.exit, exit.f.exit) match {
            case (r: RegionNode, _) =>
              Some(r)
            case (_, r: RegionNode) =>
              Some(r)
            case _ =>
              None
          }

        case Stmt.While(cond, body) =>
          val checkRegion = here.exit.asInstanceOf[RegionNode]

          currentRegion = Some(checkRegion)
          val condNode = asLogicNode(buildExpr(cond, checkRegion))
          val loopExit = checkRegion.exit.asInstanceOf[IfNode]
          loopExit.cond = condNode
          val bodyRegion = loopExit.t
          val endRegion = loopExit.f

          currentRegion = Some(bodyRegion)
          buildStmt(body)

          currentRegion = Some(endRegion)

        case Stmt.Ret(v) =>
          here.exit.asInstanceOf[RetNode].value = buildExpr(v, here)
          currentRegion = None
      }
    }

    def addDeferredPhi(v: String, phi: PhiNode): Unit = {
      deferredPhis += ((v, phi))
    }

    def resolveDeferredPhis(): Unit = {
      def resolve(v: String, onRegion: RegionNode, fromPred: RegionNode): ValueNode = {
        defsAt(fromPred.id)(v)
      }
      deferredPhis.foreach({ case (v, phi) =>
        val phiPreds = preds(phi.region)
        val defs = phiPreds.map(resolve(v, phi.region, _)).zip(phiPreds).map {
          case (v, r) => ComposeNode(v, r)
        }
        defs.foreach(phi.addInput)
      })
    }

    def defsAt(id: RegionId): Defs = {
      blockDefs.getOrElseUpdate(id, mutable.Map.empty)
    }

    def useVarAt(v: String, id: RegionId): ValueNode = {
      val here = regions(id)
      val defs = defsAt(id)
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

    def defineVar[N <: ValueNode](v: String, n: N, here: RegionNode): N = {
      val defs = defsAt(here.id)
      defs += (v -> n)
      n
    }

    def buildOp(op: BinaryOp)(lhs: ValueNode, rhs: ValueNode): ValueNode = {
      unique(op match {
        case BinaryOp.Add => AddNode(lhs, rhs).simplified(this)
        case BinaryOp.Sub => SubNode(lhs, rhs).simplified(this)
        case BinaryOp.LessThan => LessThanNode(lhs, rhs).simplified(this)
      })
    }

    def buildExpr(e: Expr, here: RegionNode): ValueNode = {
      e match {
        case Expr.Binary(op, lhs, rhs) =>
          buildOp(op)(buildExpr(lhs, here), buildExpr(rhs, here))
        case Expr.Lit(lval) =>
          unique(LitNode(lval))
        case Expr.Var(v) =>
          useVarAt(v, here.id)
      }
    }

    def asLogicNode(v: ValueNode): LogicNode = {
      v match {
        case logic: LogicNode => logic
        case _ => unique(IsTruthyNode(v))
      }
    }
  }

  // Utils
  def exits(e: RegionNode): Seq[RegionNode] = {
    // println(s"region ${e.id}")
    val es = e.exit match {
      case toR: RegionNode => Seq(toR)
      case EndNode() => Seq()
      case IfNode(t, f) => Seq(t, f)
      case RetNode(_) => Seq()
      case otherwise => throw Unexpected(s"Shouldn't be an exit: $otherwise")
    }
    // println(s"-> ${es.length} exits")
    es
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
