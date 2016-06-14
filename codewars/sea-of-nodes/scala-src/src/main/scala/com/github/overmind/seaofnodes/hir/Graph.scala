package com.github.overmind.seaofnodes.hir

import java.util
import java.util.Collections

import com.github.overmind.seaofnodes.ast._
import com.github.overmind.seaofnodes.hir.nodes._

import scala.collection.JavaConverters._
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

case class ShallowBlockBuilder(rootStmt: Stmt) {
  // Scan through the ASTs to build all the blocks.
  import Graph._

  var nextBlockId = 0
  var currentBlock: Option[BaseBeginNode] = None
  var entryBlock: Option[BaseBeginNode] = None
  val endNode = GraphExitNode()

  val firstBlock = buildRootStmt(rootStmt)

  private def buildRootStmt(s: Stmt): BaseBeginNode = {
    val entry = ensureBlock()
    entryBlock = Some(entry)
    buildStmt(s)
    dceBlock(entry)
    entry
  }

  private def allocBlock(): BeginNode = {
    val r = BeginNode(nextBlockId)
    nextBlockId += 1
    r
  }

  private def allocMerge(): MergeNode = {
    val r = MergeNode(nextBlockId)
    nextBlockId += 1
    r
  }

  private def ensureBlock(): BaseBeginNode = {
    currentBlock match {
      case None =>
        val b = allocBlock()
        currentBlock = Some(b)
        b
      case Some(b) => b
    }
  }

  private def finishBlock(exit: Node): BaseBeginNode = {
    val r = ensureBlock()
    r.next = exit
    currentBlock = None
    r
  }

  private def finishBlockWithIf(exit: IfNode): BaseBeginNode = {
    val r = ensureBlock()
    r.next = exit
    currentBlock = None
    r
  }

  private def startBlockThatEndsWith(b: BaseBeginNode, s: Option[Stmt], exit: BaseBlockExitNode): BaseBeginNode = {
    setCurrentBlock(b)
    s.foreach(buildStmt)
    finishBlock(exit)
  }

  private def setCurrentBlock(r: BaseBeginNode): Unit = {
    assert(currentBlock.isEmpty, s"currentBlock is not None: $currentBlock")
    currentBlock = Some(r)
  }

  private def buildStmt(s: Stmt): Unit = {
    ensureBlock()
    s match {
      case Begin(ss) => ss.foreach(buildStmt)

      case If(_, t, f) =>
        val tB = allocBlock()
        val fB = allocBlock()
        val endB = allocMerge()

        finishBlock(IfNode(null, tB, fB))
        val tEnd = endB.addComingFrom(EndNode())
        startBlockThatEndsWith(tB, Some(t), tEnd)
        val fEnd = endB.addComingFrom(EndNode())
        startBlockThatEndsWith(fB, Some(f), fEnd)
        setCurrentBlock(endB)

      case While(cond, body) =>
        val checkB = allocMerge()
        val loopB = allocBlock()
        val endB = allocBlock()

        val jumpToCheck = checkB.addComingFrom(EndNode())
        finishBlock(jumpToCheck)
        startBlockThatEndsWith(checkB, None, IfNode(null, loopB, endB))
        val loopBExit = checkB.addComingFrom(EndNode())
        startBlockThatEndsWith(loopB, Some(body), loopBExit)
        setCurrentBlock(endB)

      case Ret(e) =>
        finishBlock(endNode.addReturn(RetNode()))

      case _: Assign => ()
    }
  }

  private def dceBlock(entry: BaseBeginNode): Unit = {
    val reachable = mutable.Set.empty[Int]
    dfsBlock(entry) { r =>
      reachable += r.id
    }

    val deleted = EndNode()
    dfsBlock(entry) { r =>
      val ps = preds(r).toArray
      ps.foreach(p => {
        if (!reachable.contains(p.id)) {
          p.next = deleted
        }
      })
    }
  }
}

object Graph {
  def emptyIdentitySet[A <: AnyRef] =
    Collections.newSetFromMap(new util.IdentityHashMap[A, java.lang.Boolean]()).asScala

  def emptyIdentityMap[A <: AnyRef, B] = new util.IdentityHashMap[A, B]().asScala

  case class UndefinedVarInGraph(name: DefId) extends Exception
  case class Unexpected(what: String) extends Exception

  def interp(n: Node) = Interp.interp(n)

  sealed trait DefId {
    type DefType <: ValueNode
    def mkPhi(here: BaseBeginNode): BasePhiNode
  }
  case class VarId(v: String) extends DefId {
    type DefType = ValueNode
    override def mkPhi(here: BaseBeginNode): BasePhiNode = ValuePhiNode(here)
  }
  case object MemId extends DefId {
    type DefType = MemoryStateNode
    override def mkPhi(here: BaseBeginNode): BasePhiNode = MemoryPhiNode(here)
  }

  case class GraphBuilder() {
    type Defs = mutable.Map[DefId, ValueNode]
    type BlockId = Int

    var _currentBlock: Option[BaseBeginNode] = None
    var currentNode: Option[SingleNext[Node]] = None
    var currentBlockExit: Option[BaseBlockExitNode] = None
    val blockDefs = mutable.Map.empty[BlockId, Defs]
    val regions = mutable.Map.empty[BlockId, BaseBeginNode]
    val deferredPhis = ArrayBuffer.empty[(DefId, BasePhiNode)]
    val cachedNodes = mutable.Map.empty[Node, Node]
    var start: Option[GraphEntryNode] = None
    var end: Option[GraphExitNode] = None

    def currentBlock = _currentBlock
    def currentBlock_=(newBlock: Option[BaseBeginNode]): Unit = {
      _currentBlock = newBlock
      currentNode = newBlock
      currentBlockExit = newBlock.map(_.next.asInstanceOf[BaseBlockExitNode])
    }

    def build(first: BaseBeginNode, endNode: GraphExitNode, s: Stmt): GraphEntryNode = {
      end = Some(endNode)
      val startNode = GraphEntryNode(first)
      start = Some(startNode)
      buildBlocks(first)
      buildRootStmt(first, s)
      startNode
    }

    def unique[N <: Node](n: N): N = {
      cachedNodes.getOrElseUpdate(n, n).asInstanceOf[N]
    }

    def buildBlocks(start: BaseBeginNode): Unit = {
      // The initial memory state.
      dfsBlock(start)(r => {
        regions += (r.id -> r)
      })
      currentBlock = Some(start)
    }

    def buildRootStmt(first: BaseBeginNode, s: Stmt): Unit = {
      currentBlock = Some(first)
      buildStmt(s, first)
      resolveDeferredPhis()
    }

    def buildStmt(s: Stmt): Unit = {
      currentBlock.foreach(buildStmt(s, _))
    }

    def buildStmt(s: Stmt, here: BaseBeginNode): Unit = {
      s match {
        case Assign(v, e) =>
          v match {
            case LVar(v) =>
              defineVar(v, buildExpr(e, here), here)
            case LIndex(base, index) =>
              val n = WriteArrayNode(buildExpr(base, here), buildExpr(index, here),
                buildExpr(e, here))
              modifyMemBy(here.id, n)
          }

        case Begin(ss) =>
          ss.foreach(buildStmt)

        case If(cond, t, f) =>
          // A bit repetitive..
          val condNode = asLogicNode(buildExpr(cond, here))
          val exit = currentBlockExit.get.asInstanceOf[IfNode]
          exit.value = condNode

          currentBlock = Some(exit.t)
          buildStmt(t)

          currentBlock = Some(exit.f)
          buildStmt(f)

          // DCE
          currentBlock = (exit.t, exit.f) match {
            case (r: BaseBeginNode, _) =>
              Some(r)
            case (_, r: BaseBeginNode) =>
              Some(r)
            case _ =>
              None
          }

        case While(cond, body) =>
          val checkBlock = currentBlockExit.get.asInstanceOf[EndNode].cfgSuccessor

          currentBlock = Some(checkBlock)
          val condNode = asLogicNode(buildExpr(cond, checkBlock))
          val loopExit = checkBlock.next.asInstanceOf[IfNode]
          loopExit.value = condNode
          val bodyBlock = loopExit.t
          val endBlock = loopExit.f

          currentBlock = Some(bodyBlock)
          buildStmt(body)

          currentBlock = Some(endBlock)

        case Ret(v) =>
          val asRet = currentBlockExit.get.asInstanceOf[RetNode]
          asRet.value = buildExpr(v, here)
          currentBlock = None
      }
    }

    def addDeferredPhi(v: DefId, phi: BasePhiNode): Unit = {
      deferredPhis += ((v, phi))
    }

    def resolveDeferredPhis(): Unit = {
      def resolve(v: DefId, onBlock: BaseBeginNode, fromPred: BaseBeginNode): ValueNode = {
        defsAt(fromPred.id)(v)
      }
      deferredPhis.foreach({ case (v, phi) =>
        val phiPreds = preds(phi.anchor)
        val defs = phiPreds.map(resolve(v, phi.region, _)).zip(phiPreds).map {
          case (v, r) => ComposeNode(v, r)
        }
        defs.foreach(phi.addInput)
      })
    }

    def defsAt(id: BlockId): Defs = {
      blockDefs.getOrElseUpdate(id, mutable.Map.empty)
    }

    def useMemAt(id: BlockId): MemoryStateNode = {
      useIdAt(MemId, id)
    }

    def modifyMemBy(id: BlockId, v: ValueNode): ValueNode = {
      defsAt(id) += (MemId -> MemoryStateAfterNode(v))
      v
    }

    def useIdAt[D <: DefId](v: D, id: BlockId): D#DefType = {
      val here = regions(id)
      val defs = defsAt(id)
      val got = defs.get(v) match {
        case Some(n) => n
        case None =>
          // Hmm...
          val ps = preds(here)
          ps.length match {
            case 0 =>
              throw UndefinedVarInGraph(v)
            case 1 =>
              assert(ps.head.id != id)
              val there = useIdAt(v, ps.head.id)
              defs += (v -> there)  // Cached
              there
            case _ =>
              val phi = v.mkPhi(here)
              defs += (v -> phi)
              addDeferredPhi(v, phi)
              ps.foreach(p => {
                useIdAt(v, p.id)
              })
              phi
          }
      }
      got.asInstanceOf[D#DefType]
    }

    def defineVar[N <: ValueNode](v: String, n: N, here: BaseBeginNode): N = {
      val defs = defsAt(here.id)
      defs += (VarId(v) -> n)
      n
    }

    def buildOp(op: BinaryOp)(lhs: ValueNode, rhs: ValueNode): ValueNode = {
      unique(op match {
        case BinaryOp.Add => AddNode(lhs, rhs).simplified(this)
        case BinaryOp.Sub => SubNode(lhs, rhs).simplified(this)
        case BinaryOp.LessThan => LessThanNode(lhs, rhs).simplified(this)
      })
    }

    def buildExpr(e: Expr, here: BaseBeginNode): ValueNode = {
      e match {
        case Binary(op, lhs, rhs) =>
          buildOp(op)(buildExpr(lhs, here), buildExpr(rhs, here))
        case Lit(lval) =>
          unique(LitNode(lval))
        case LVar(v) =>
          useIdAt(VarId(v), here.id)
        case LIndex(base, index) =>
          ReadArrayNode(buildExpr(base, here), buildExpr(index, here), useMemAt(here.id))
        case AllocArray(len) =>
          modifyMemBy(here.id, AllocFixedArrayNode(len, useMemAt(here.id)))
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
  def exits(e: BaseBeginNode): Seq[BaseBeginNode] = {
    // println(s"region ${e.id}")
    val es = e.exit match {
      case toR: BaseBeginNode => Seq(toR)
      case EndNode() => Seq()
      case IfNode(t, f) => Seq(t, f)
      case RetNode(_) => Seq()
      case otherwise => throw Unexpected(s"Shouldn't be an exit: $otherwise")
    }
    // println(s"-> ${es.length} exits")
    es
  }

  def preds(region: BaseBeginNode): Seq[BaseBeginNode] = {
    match region.predecessor {
      case r: BaseBeginNode =>
        Some(r)
      case i: IfNode =>
        Some(i.region)
      case s: StartNode =>
        None
      case pred =>
        throw Unexpected(s"Shouldn't have such predecessor: $pred")
    }
  }

  def dfsBlock(b: BaseBeginNode)(f: BaseBeginNode => Unit): Unit = {
    def go(b: BaseBeginNode, visited: mutable.Set[BaseBeginNode]): Unit = {
      if (!visited.contains(b)) {
        visited.add(b)
        f(b)
        exits(b).foreach(go(_, visited))
      }
    }

    go(b, Graph.emptyIdentitySet)
  }
}
