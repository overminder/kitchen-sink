package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.hir.Graph.GraphBuilder
import com.github.overmind.seaofnodes.hir.nodes.{IfNode, RegionNode}

/**
  * Created by tim.jiang on 6/6/2016.
  */
object Opt {
  def simplifyControl(entry: RegionNode, builder: GraphBuilder): Unit = {
    Graph.dfsRegion(entry) { r =>
      r.exit match {
        case i: IfNode =>
          val e = r.exit
          r.exit = i.simplified(builder)
          e.tryRemove()
        case _ =>
          ()
      }
    }
  }
}
