package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.hir.Graph.{IDomEdge, NodeSet}
import com.github.overmind.seaofnodes.hir.nodes._

case class IDomTree() {
  val edges = Graph.emptyIdentityNodeMap[IDomEdge]
}

object IDomTree {
  def build(g: Graph) = {
    val t = IDomTree()

    Graph.dfsIdom(g.entry, e => {
      t.edges += (e.of -> e)
    })

    t
  }
}

// Click's Global Code Motion.
case class Gcm(g: Graph) {
  val idomTree = IDomTree.build(g)
  val earliestSchedules = Graph.emptyIdentityMap[ValueNode, BaseBeginNode]
  val latestSchedules = Graph.emptyIdentityMap[ValueNode, BaseBeginNode]

  def latestScheduleOf(n: ValueNode): BaseBeginNode = {
    val onExit = n.controlUses.flatMap({
      case exit: BaseBlockExitNode =>
        Some(exit)
      case _ =>
        None
    })
    assert(onExit.length <= 1)
    if (onExit.isEmpty) {
      latestSchedules(n)
    } else {
      onExit.head.belongsToBlock
    }
  }

  def earliestScheduleOf(n: ValueNode): BaseBeginNode = {
    n match {
      case an: BaseAnchoredNode =>
        an.anchor
      case _ =>
        earliestSchedules(n)
    }
  }

  def firstBlock = g.entry.next

  def idomDepth(n: Node) = {
    idomTree.edges(n).treeDepth
  }

  def idomOf(n: Node) = {
    idomTree.edges(n).idom.get
  }

  def scheduleEarly(writeback: Boolean = false): Unit = {
    val visited = Graph.emptyIdentityNodeSet

    // For each control-dependent node that introduce defs:
    Graph.dfsNode(g.entry) {
      case n: BaseAnchoredNode =>
        scheduleAnchoredNodeEarly(n, n.anchor, visited)
      case _ =>
        ()
    }

    if (writeback) {
      writeBackEarlySchedule()
    }
  }

  def writeBackSchedule(schedule: collection.Map[ValueNode, BaseBeginNode]): Unit = {
    schedule.foreach({ case (n, nb) =>
      n match {
        case an: BaseAnchoredNode =>
          // Already anchored.
          ()

        case _ =>
          println(s"writeBack: wrapping $n")
          // Not an anchored node: need to wrap it
          val anchored = AnchoringNode(null, nb.asInstanceOf[BaseBeginNode])
          n.replaceAllUsesWith(anchored, keepAlive = true)
          anchored.value = n
      }
    })
  }

  def writeBackEarlySchedule(): Unit = {
    writeBackSchedule(earliestSchedules)
  }

  def writeBackLateSchedule(): Unit = {
    writeBackSchedule(latestSchedules)
  }

  def scheduleAnchoredNodeEarly(n: ValueNode, anchor: BaseBeginNode, visited: NodeSet): Unit = {
    assert(visited.add(n), s"Duplicated node: $n")
    earliestSchedules += (n -> anchor)
    n.valueInputs.foreach(scheduleEarly(_, visited))
  }

  def scheduleEarly(n: ValueNode, visited: NodeSet): Unit = {
    if (n.isInstanceOf[BaseAnchoredNode]) {
      // Already anchored.
      return
    }

    if (!visited.add(n)) {
      return
    }


    earliestSchedules += (n -> firstBlock)
    n.valueInputs.foreach({ i =>
      scheduleEarly(i, visited)
      val ib = earliestScheduleOf(i)
      val nb = earliestScheduleOf(n)
      if (idomDepth(ib) > idomDepth(nb)) {
        // Need to move n downwards, as otherwise this input will not be available when n is evaluated.
        earliestSchedules += (n -> ib)
      }
    })
  }

  def scheduleLate(writeback: Boolean = false): Unit = {
    val visited = Graph.emptyIdentityNodeSet

    // For each control-dependent node that uses values:
    Graph.dfsNode(g.entry) {
      case vn: ValueNode =>
        val onExit = vn.controlUses.flatMap({
          case exit: BaseBlockExitNode =>
            Some(exit)
          case _ =>
            None
        })
        // Inputs: the values used by this control node.
        n.valueInputs.foreach(scheduleAnchoredNodeLate(_, n.belongsToBlock, visited))

      case _ =>
        ()
    }

    if (writeback) {
      writeBackLateSchedule()
    }
  }

  def scheduleAnchoredNodeLate(v: ValueNode, n: BaseBeginNode, visited: NodeSet): Unit = {
    assert(visited.add(v), s"Duplicated node: $v on $n")
    println(s"schedule late: $v -> $n")
    latestSchedules += (v -> n)
    v.valueUses.foreach(scheduleLate(_, visited))
  }

  def scheduleLate(n: ValueNode, visited: NodeSet): Unit = {
    if (!visited.add(n)) {
      return
    }

    var lca: Option[BaseBeginNode] = None
    n.valueUses.foreach({ u =>
      scheduleLate(u, visited)
      var ub = latestScheduleOf(u)
      u match {
        // A phi node's input cannot be scheduled later than the incoming block that it resides in.
        case phi: ValuePhiNode =>
          val nthPhiInput = phi.composedInputs.indexWhere(_ eq n)
          ub = phi.anchor.comingFrom(nthPhiInput).belongsToBlock
        case _ =>
          ()
      }

      lca = Some(findLca(lca, ub))
    })

    println(s"schedule late: $n -> $lca")
    latestSchedules += (n -> lca.getOrElse(firstBlock))
  }

  // LCA: Lowest common ancestor
  def findLca(mbX: Option[BaseBeginNode], y0: BaseBeginNode): BaseBeginNode = {
    mbX match {
      case Some(x0) =>
        val depthDiff = idomDepth(x0) - idomDepth(y0)
        // Balance their depths
        var (x1, y1) = if (depthDiff < 0) {
          // y is deeper: climb y up -depthDiff steps.
          var y: Node = y0
          (1 to -depthDiff).foreach(_ => {
            y = idomOf(y)
          })
          (x0, y)
        } else {
          // x is deeper: climb x up depthDiff steps.
          var x: Node = x0
          (1 to depthDiff).foreach(_ => {
            x = idomOf(x)
          })
          (x, y0)
        }
        // And find their common predecessor
        while (x1 ne y1) {
          x1 = idomOf(x1)
          y1 = idomOf(y1)
        }
        // XXX: Hmm...
        x1 match {
          case ifNode: IfNode =>
            ifNode.belongsToBlock
          case b: BaseBeginNode =>
            b
          case _ =>
            sys.error(s"findLca: unknown node $x1")
        }
      case None =>
        y0
    }
  }
}
