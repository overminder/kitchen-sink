package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.hir.nodes.{AnchoredNode, Node, ValueNode}

// Click's Global Code Motion.
object Gcm {
  def buildIDomTree(g: Graph): Unit = {

    Graph.dfsIdom(g.entry, e => {
      e.idom
    })
    g.entry

  }

  def scheduleEarly(n: Node): Unit = {
    def setBlock()
    Graph.dfsNode(n) {
      case n: AnchoredNode =>
        n.anchor
      case _ =>
        ()
    }
  }
}
