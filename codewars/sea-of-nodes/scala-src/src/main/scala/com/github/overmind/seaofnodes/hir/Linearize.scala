package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.DotGen
import com.github.overmind.seaofnodes.hir.nodes._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

// Naively linearize and number instrutions for LSRA's consumption.
object Linearize {
  def build(g: Graph): TGraph = {
    val tg = TGraph(g)

    var nextInstrIx = instrIxIncr

    var blockEntry = Option.empty[BaseBeginNode]
    val blockBody = ArrayBuffer.empty[ValueNode]
    Graph.dfsIdom(g.entry, { e =>
      e.of match {
        case n: GraphEntryNode =>
          ()
        case n: GraphExitNode =>
          ()
        case n: BaseBeginNode =>
          blockBody ++= topoSorted(n.anchored.map(unwrapAnchoring))
          blockEntry = Some(n)
        case n: BaseBlockExitNode =>
          val b = TBlock(tg, blockEntry.get, blockBody.toArray[ValueNode], n)
          nextInstrIx = b.numberInstrs(nextInstrIx)
          blockEntry = None
          blockBody.clear()
          tg.blocks += (b.first -> b)
        // case v: ValueNode =>
        //   blockBody += v
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
      block.numberedInstrs.flatMap(renderInstr).mkString("\n")
    }
    def renderPhi(n: ValuePhiNode) = {
      s"${renderValue(n)} = phi(${n.composedInputs.map(renderValue).mkString(", ")})"
    }
    def renderInstr(tup: (Int, Node)): Seq[String] = {
      val (ix, n0) = tup
      var extra: Seq[String] = Seq()
      val first = n0 match {
        case n: BinaryNode =>
          s"${renderValue(n)} = ${renderValue(n.lhs)} ${n.toShallowString} ${renderValue(n.rhs)}"
        case n: UnaryNode =>
          s"${renderValue(n)} = ${n.toShallowString} ${renderValue(n.value)}"
        case n: LitNode =>
          s"${renderValue(n)} = ${n.toShallowString}"
        case n: FuncArgNode =>
          s"${renderValue(n)} = arg(${n.ix})"
        case n: BaseMergeNode =>
          extra = n.valuePhis.map(renderPhi)
          renderFirst(n)
        case n: BaseBeginNode =>
          renderFirst(n)
        case n: BaseBlockExitNode =>
          renderLast(n)
        case _ =>
          sys.error(s"Unknown node: $n0")
      }
      s"$ix: $first" +: extra
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
      b.isIDomOf.foreach(idom => {
        ctx.addEdge(ensureBlock(b), ensureBlock(idom), ("style", "dotted"), ("color", "red"))
      })
    })

    ctx.toDot
  }

  def instrIxIncr = 2

  case class TBlock(g: TGraph, first: BaseBeginNode, mids: Seq[ValueNode], last: BaseBlockExitNode) {

    def id: Int = first.id

    var instrIxStart: Int = -1
    def instrIxEnd = instrIxStart + (mids.length + 2) * instrIxIncr

    def numberInstrs(nextInstrIx: Int): Int = {
      instrIxStart = nextInstrIx
      // Reserve one more ix to denote 'live-out'.
      instrIxEnd
    }

    def range = (instrIxStart, instrIxEnd)

    def instrs: Seq[Node] = first +: mids :+ last
    def mergedInstrs(from: collection.Map[Int, Seq[Node]]): Seq[Node] = {
      val (bStart, bEnd) = range
      val orig = Map(numberedInstrs: _*)
      (bStart to bEnd).flatMap(ix => {
        val origAtHere = orig.get(ix).iterator
        val fromAtHere = from.getOrElse(ix, Seq.empty)
        // Make sure we don't have ordering issues.
        if (origAtHere.nonEmpty) {
          assert(fromAtHere.isEmpty)
        } else if (fromAtHere.nonEmpty) {
          assert(origAtHere.isEmpty)
        }
        origAtHere ++ fromAtHere
      })
    }
    def numberedInstrs: Seq[(Int, Node)] = {
      Range(instrIxStart, Int.MaxValue, instrIxIncr).view.zip(instrs)
    }

    def isIDomOf = last.isIDomOf.map(n => g.blocks(n.asInstanceOf[BaseBeginNode]))
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
    def isLoopBegin = first.isInstanceOf[LoopBeginNode]
  }

  case class TGraph(g: Graph) {
    def entry = g.entry
    def exit = g.exit

    def firstBlock = blocks(entry.next)

    val blocks = Graph.emptyIdentityMap[BaseBeginNode, TBlock]

    def dfsIdom(f: TBlock => Unit): Unit = {
      def go(b: TBlock): Unit = {
        f(b)
        b.isIDomOf.foreach(go)
      }
      go(firstBlock)
    }
  }

  // We might also want to find a way to minimize the register pressure. IIRC the dragon book has a chapter about
  // DAG instruction selection...
  def topoSorted(anchored: Seq[ValueNode]): Seq[ValueNode] = {
    val vs = Graph.emptyIdentitySet[ValueNode]
    vs ++= anchored
    val out = ArrayBuffer.empty[ValueNode]

    // Very naive - O(V * (V + E)) complexity
    while (vs.nonEmpty) {
      // Can't filter directly as that will call hashcode on v... WAT
      val depLess = vs.toSeq.filter(v => {
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

  def unwrapAnchoring(anc: AnchoringNode): ValueNode = {
    val v = anc.value
    anc.value = null
    anc.replaceAllUsesWith(v)
    v
  }
}
