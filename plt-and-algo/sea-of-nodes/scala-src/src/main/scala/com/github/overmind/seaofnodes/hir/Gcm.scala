package com.github.overmind.seaofnodes.hir

import java.util.NoSuchElementException

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
case class Gcm(g: Graph, verbose: Boolean = false) {
  val idomTree = IDomTree.build(g)
  val earliestSchedules = Graph.emptyIdentityMap[ValueNode, BaseBeginNode]
  val latestSchedules = Graph.emptyIdentityMap[ValueNode, BaseBeginNode]
  var earliestScheduleFrozen = false

  def run(): Unit = {
    scheduleEarly()
    scheduleLate()
    writeBackEarlySchedule()
  }

  def pinnedWithEarliestBlock(n: ValueNode): Option[BaseBeginNode] = {
    n match {
      case anc: BaseAnchoredNode =>
        // Anchored node can't move.
        Some(anc.anchor)
      case _ =>
        None
    }
  }

  def isPinned(n: Node): Boolean = {
    n match {
      case _: BaseAnchoredNode =>
        true
      case _: IfNode =>
        true
      case _: RetNode =>
        true
      case _ =>
        false
    }
  }

  def pinnedWithLatestBlock(n: ValueNode): Option[BaseBeginNode] = {
    n match {
      case anc: BaseAnchoredNode =>
        // Anchored node can't move.
        Some(anc.anchor)
      case _ =>
        val onExit = n.controlUses.flatMap({
          // IfNode / RetNode etc.
          // Nodes used by control nodes can't be moved later .
          case exit: BaseBlockExitNode =>
            Some(exit)
          case _ =>
            None
        })
        // A value can be pinned by multiple control users - choose a LCA.
        onExit.map(_.belongsToBlock).foldLeft(Option.empty[BaseBeginNode]) { (x, y) =>
          Some(findLca(x, y))
        }
    }
  }

  def belongsToBlock(n: Node): BaseBeginNode = {
    n match {
      case exit: BaseBlockExitNode =>
        exit.belongsToBlock
      case b: BaseBeginNode =>
        b
      case _ =>
        sys.error(s"belongsToBlock: unknown node $n")
    }
  }

  def latestScheduleOf(n: ValueNode): BaseBeginNode = {
    pinnedWithLatestBlock(n).getOrElse(latestSchedules(n))
  }

  def earliestScheduleOf(n: ValueNode): BaseBeginNode = {
    pinnedWithEarliestBlock(n).orElse(earliestSchedules.get(n)).getOrElse({
      if (earliestScheduleFrozen) {
        firstBlock
      } else {
        throw new NoSuchElementException(s"No such key: $n")
      }
    })
  }

  def firstBlock = g.entry.next

  def idomDepth(n: Node) = {
    idomTree.edges(n).treeDepth
  }

  def loopNest(n: Node) = {
    idomTree.edges(n).loopNestingDepth
  }

  def idomOf(n: Node) = {
    idomTree.edges(n).idom.get
  }

  def scheduleEarly(writeback: Boolean = false): Unit = {
    val visited = Graph.emptyIdentityNodeSet

    // For each control-dependent node that introduce defs:
    Graph.dfsNode(g.entry) {
      case n if isPinned(n) =>
        // A phi node is always pinned, and it should dominate any use of it.
        // assert(visited.add(n), s"Duplicated node: $n")
        n.valueInputs.foreach(scheduleEarly(_, visited))
      case _ =>
        ()
    }

    earliestScheduleFrozen = true
    if (writeback) {
      writeBackEarlySchedule()
    }
  }

  def scheduleEarly(n: ValueNode, visited: NodeSet): Unit = {
    /*
    if (pinnedWithEarliestBlock(n).isDefined) {
      // Already anchored.
      return
    }
    */

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

    if (verbose) {
      println(s"Earliest schedule: $n -> ${earliestSchedules(n)}")
    }
  }

  def scheduleLate(writeback: Boolean = false): Unit = {
    val visited = Graph.emptyIdentityNodeSet

    assert(earliestScheduleFrozen)
    earliestSchedules.keySet.foreach(scheduleLate(_, visited))

    /*
    Graph.dfsNode(g.entry) {
      case n: Node =>
        pinnedWithLatestBlock(vn).foreach({ pin =>
          // Is a value node pinned by some control node
          assert(visited.add(vn), s"Duplicated node: $vn on $pin")
          // All of its inputs should dominate this node.
          vn.valueInputs.foreach(scheduleLate(_, visited))
        })

      case _ =>
        ()
    }
    */

    if (writeback) {
      writeBackLateSchedule()
    }
  }

  def scheduleLate(n: ValueNode, visited: NodeSet): Unit = {
    // Already pinned.
    // if (pinnedWithLatestBlock(n).isDefined) {
    //   return
    // }

    if (!visited.add(n)) {
      return
    }

    var lca: Option[BaseBeginNode] = None
    n.uses.foreach({ i =>
      // Find the scheduled block for each use
      val ib = i match {
        case pinned: BaseBlockExitNode =>
          pinned.belongsToBlock
        case phi: ValuePhiNode =>
          // A phi node's input cannot be scheduled later than the incoming block that it resides in.
          scheduleLate(phi, visited)
          val nthPhiInput = phi.composedInputs.indexWhere(_ eq n)
          phi.anchor.comingFrom(nthPhiInput).belongsToBlock
        case v: ValueNode =>
          scheduleLate(v, visited)
          earliestScheduleOf(v)
        case _ =>
          sys.error(s"Unknown use $i on $n")
      }

      // And make sure this node dominate this use
      lca = Some(findLca(lca, ib))
    })

    if (verbose) {
      println(s"Latest schedule: $n -> $lca")
    }
    scheduleFromLatestToEarliest(n, lca.get)
  }

  def scheduleFromLatestToEarliest(n: ValueNode, latest: BaseBeginNode): Unit = {
    var iter: Node = latest
    var best = iter
    val earliest = earliestScheduleOf(n)

    while (iter.ne(earliest)) {
      assert(idomDepth(earliest) < idomDepth(iter), s"n $n, earliest ${idomTree.edges(earliest)}, iter ${idomTree.edges(iter)}")
      if (loopNest(iter) < loopNest(best)) {
        best = iter
      }
      iter = idomOf(iter)
    }
    if (verbose) {
      println(s"Final schedule: $n -> $best")
    }
    earliestSchedules += (n -> belongsToBlock(best))
    // latestSchedules += (n -> lca.getOrElse(firstBlock))
  }

  // LCA: Lowest common ancestor
  def findLca(mbX: Option[BaseBeginNode], y0: BaseBeginNode): BaseBeginNode = {
    mbX match {
      case None =>
        y0
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
        belongsToBlock(x1)
    }
  }

  def writeBackSchedule(schedule: collection.Map[ValueNode, BaseBeginNode]): Unit = {
    schedule.foreach({ case (n, nb) =>
      n match {
        case an: BaseAnchoredNode =>
          // Already anchored.
          ()

        case _ =>
          if (verbose) {
            println(s"WriteBack: wrapping $n")
          }
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

}
