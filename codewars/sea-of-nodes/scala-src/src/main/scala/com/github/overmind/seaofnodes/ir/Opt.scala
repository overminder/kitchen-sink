package com.github.overmind.seaofnodes.ir

import com.github.overmind.seaofnodes.ir.Graph.GraphBuilder

/**
  * Created by tim.jiang on 6/6/2016.
  */
object Opt {
  def simplifyControl(entry: RegionNode, builder: GraphBuilder): Unit = {
    Graph.dfsRegion(entry) { r =>
      r.exit match {
        case i: IfNode =>
          r.exit = i.simplified(builder)
        case _ =>
          ()
      }
    }
  }
}
