package com.github.overmind.seaofnodes.hir

import scala.collection.mutable

import com.github.overmind.seaofnodes.DotGen
import com.github.overmind.seaofnodes.hir.nodes.Node

object DotFromNode {
  def gen(name: String, node: Node): String = {
    val ctx = DotContext(name)
    ctx.addNode(node)
    ctx.render
  }

  case class DotContext(name: String) {
    import DotGen.NodeId

    val g = DotGen.Graph(name)
    val nodes = Graph.emptyIdentityMap[Node, NodeId]

    def renderedNode(n: Node): DotGen.NodeId = {
      nodes.getOrElseUpdate(n, {
        g.addText(n.toShallowString)
      })
    }

    def renderEdge(from: NodeId, to: NodeId, edgeIx: Int, isControlDep: Boolean): Unit = {
      val opts = if (!isControlDep) {
        Seq(("color", "blue"))
      } else {
        Seq(("style", "dotted"))
      }
      g.addEdge(from, to, opts: _*)
    }

    def addNode(n: Node) = {
      Graph.dfsEdge(n) { e =>
        renderEdge(renderedNode(e.from), renderedNode(e.to), e.ix, e.isControlDep)
      }
    }

    def render = g.toDot
  }
}
