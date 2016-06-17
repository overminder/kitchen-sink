package com.github.overmind.seaofnodes.hir

import scala.collection.mutable

import com.github.overmind.seaofnodes.DotGen
import com.github.overmind.seaofnodes.hir.nodes.Node

object DotFromNode {
  def gen(name: String, node: Node, showBackedges: Boolean = false): String = {
    val ctx = DotContext(name, showBackedges)
    ctx.addNeighbour(node)
    ctx.render
  }

  case class DotContext(name: String, showBackedges: Boolean = false) {
    import DotGen.NodeId

    val g = DotGen.Graph(name)
    val nodes = Graph.emptyIdentityMap[Node, NodeId]
    val edges = mutable.Set.empty[(NodeId, NodeId, Boolean)]
    val visited = Graph.emptyIdentitySet[Node]

    def addNode(n: Node): DotGen.NodeId = {
      nodes.getOrElseUpdate(n, {
        g.addText(n.toShallowString)
      })
    }

    def addEdge(from: NodeId, to: NodeId, isControlDep: Boolean): Unit = {
      if (edges.add((from, to, isControlDep))) {
        val opts = if (!isControlDep) {
          Seq(("color", "blue"))
        } else {
          Seq()
        }
        g.addEdge(from, to, opts: _*)
      }
    }

    def addNeighbour(n: Node) = {
      def go(n: Node): Unit = {
        if (!visited.add(n)) {
          return
        }
        val id = addNode(n)
          n.inputs.foreach(i => {
            addEdge(id, addNode(i), isControlDep = false)
            go(i)
          })
          if (showBackedges) {
            n.uses.foreach(u => {
              addEdge(addNode(u), id, isControlDep = false)
              go(u)
            })
          }
        n.successors.foreach(s => {
          addEdge(id, addNode(s), isControlDep = true)
          go(s)
        })
        if (showBackedges) {
          Option(n.predecessor).foreach(p => {
            addEdge(addNode(p), id, isControlDep = true)
            go(p)
          })
        }
      }
      go(n)
    }

    def render = g.toDot
  }
}
