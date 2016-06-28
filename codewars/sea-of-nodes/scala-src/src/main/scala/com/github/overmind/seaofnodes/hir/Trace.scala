package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.DotGen
import com.github.overmind.seaofnodes.hir.DotFromNode.DotContext
import com.github.overmind.seaofnodes.hir.nodes._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

object Trace {
  def build(g: Graph): TGraph = {
    val tg = TGraph(g)

    var blockEntry = Option.empty[BaseBeginNode]
    val blockBody = ArrayBuffer.empty[ValueNode]
    Graph.dfsIdom(g.entry, { e =>
      e.of match {
        case n: GraphEntryNode =>
          ()
        case n: GraphExitNode =>
          ()
        case n: BaseBeginNode =>
          blockBody ++= topoSorted(n.anchored)
          blockEntry = Some(n)
        case n: BaseBlockExitNode =>
          val b = TBlock(tg, blockEntry.get, blockBody.toArray[ValueNode], n)
          blockEntry = None
          blockBody.clear()
          tg.blocks += (b.first -> b)
        case v: ValueNode =>
          blockBody += v
        case n =>
          sys.error(s"Unknown node: $n")
      }
    })
    tg
  }

  def toDot(g: TGraph): String = {
    import DotGen.NodeId

    val ctx = DotGen.Graph("trace")
    val bidToNid = mutable.Map.empty[Int, NodeId]
    def ensureBlock(block: TBlock): NodeId = {
      bidToNid.getOrElseUpdate(block.id, ctx.addText(renderBlock(block)))
    }
    def renderBlock(block: TBlock): String = {
      block.nodes.flatMap(renderInstr).mkString("\n")
    }
    def renderInstr(n0: Node): Seq[String] = {
      n0 match {
        case anc: AnchoringNode => anc.value match {
          case n: BinaryNode =>
            Seq(s"${renderValue(anc)} = ${renderValue(n.lhs)} ${n.toShallowString} ${renderValue(n.rhs)}")
          case n: UnaryNode =>
            Seq(s"${renderValue(anc)} = ${n.toShallowString} ${renderValue(n.value)}")
          case n: LitNode =>
            Seq(s"${renderValue(anc)} = ${n.toShallowString}")
          case n: FuncArgNode =>
            Seq(s"${renderValue(anc)} = arg(${n.ix})")
          case _ =>
            sys.error(s"Unknown node: $n0")
        }
        case n: ValuePhiNode =>
          Seq(s"${renderValue(n)} = phi(${n.composedInputs.map(renderValue).mkString(", ")})")
        case n: BaseMergeNode =>
          renderFirst(n) +: n.valuePhis.flatMap(renderInstr)
        case n: BaseBeginNode =>
          Seq(renderFirst(n))
        case n: BaseBlockExitNode =>
          Seq(renderLast(n))
        case _ =>
          sys.error(s"Unknown node: $n0")
      }
    }
    def renderFirst(n0: BaseBeginNode): String = {
      s"Block ${n0.id}"
    }
    def renderLast(n0: BaseBlockExitNode): String = {
      n0 match {
        case n: IfNode =>
          s"If ${renderValue(n.value)} then ${renderFirst(n.t)} else ${renderFirst(n.f)}"
        case n: RetNode =>
          s"Ret ${renderValue(n.value)}"
        case _ =>
          n0.toShallowString
      }
    }
    def renderValue(v: ValueNode): String = {
      s"v${v.id}"
    }
    ctx.addEdge(ctx.addText("Entry"), ensureBlock(g.firstBlock))
    g.blocks.values.foreach(b => {
      b.cfgSuccessors.foreach(s => {
        ctx.addEdge(ensureBlock(b), ensureBlock(s))
      })
    })

    ctx.toDot
  }

  case class TBlock(g: TGraph, first: BaseBeginNode, mids: Seq[ValueNode], last: BaseBlockExitNode) {
    def id: Int = first.id
    def nodes: Seq[Node] = first +: mids :+ last

    def isIDomOf = first.isIDomOf
    def valuePhis = first match {
      case n: BaseMergeNode =>
        n.valuePhis
      case _ =>
        Seq()
    }
    def cfgPredecessors: Seq[TBlock] = first match {
      case n: BaseMergeNode =>
        n.comingFrom.map(_.belongsToBlock).map(g.blocks(_))
      case _ =>
        Seq(g.blocks(first.cfgPredecessor.belongsToBlock))
    }
    def cfgSuccessors: Seq[TBlock] = last.cfgSuccessors.map(g.blocks(_))
  }

  case class TGraph(g: Graph) {
    def entry = g.entry
    def exit = g.exit

    def firstBlock = blocks(entry.next)

    val blocks = Graph.emptyIdentityMap[BaseBeginNode, TBlock]
  }

  // We might also want to find a way to minimize the register pressure. IIRC the dragon book has a chapter about
  // DAG instruction selection...
  def topoSorted(anchored: Seq[AnchoringNode]): Seq[AnchoringNode] = {
    val vs = Graph.emptyIdentityNodeSet
    vs ++= anchored
    val out = ArrayBuffer.empty[AnchoringNode]

    // Very naive - O(V * (V + E)) complexity
    while (vs.nonEmpty) {
      val depLess = anchored.filter(v => {
        // None of the input...
        !v.inputs.exists(i => {
          // ...reference anchored nodes in this block.
          vs.exists(_.eq(i))
        })
      })
      assert(depLess.nonEmpty)
      out ++= depLess
      vs --= depLess
    }

    out
  }
}
