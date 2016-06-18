package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.hir.nodes.{IfNode, Node}


/**
  * Created by tim.jiang on 6/6/2016.
  */
object Opt {
  def simplifyIf(n: IfNode, g: Graph): Unit = {
  }

  def simplifyControl(entry: Node, g: Graph): Unit = {
    Graph.dfsNode(entry) {
      case n: IfNode =>
        simplifyIf(n, g)
      case _ =>
        ()
    }
  }
}
