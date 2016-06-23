package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.hir.Graph.IDomEdge
import com.github.overmind.seaofnodes.hir.nodes._

case class IDomTree() {
  val edges = Graph.emptyIdentityMap[Node, IDomEdge]
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
  val visited = Graph.emptyIdentitySet[ValueNode]
  val earliestScheduleOf = Graph.emptyIdentityMap[ValueNode, Node]
  val latestScheduleOf = Graph.emptyIdentityMap[ValueNode, Node]

  def firstBlock = g.entry.next

  def idomDepth(n: Node) = {
    idomTree.edges(n).treeDepth
  }

  def scheduleEarly(writeback: Boolean = false): Unit = {
    // For each control-dependent node that introduce defs:
    Graph.dfsNode(g.entry) {
      case n: BaseAnchoredNode =>
        scheduleAnchoredNodeEarly(n, n.anchor)
      case _ =>
        ()
    }

    if (writeback) {
      writeBackEarlySchedule()
    }
  }

  def writeBackEarlySchedule(): Unit = {
    earliestScheduleOf.foreach({ case (n, nb) =>
      n match {
        case an: BaseAnchoredNode =>
        // Already anchored.

        case _ =>
          // Not an anchored node: need to wrap it
          val anchored = AnchoredNode(null, nb.asInstanceOf[BaseBeginNode])
          n.replaceAllUsesWith(anchored, keepAlive = true)
          anchored.value = n
      }
    })
  }

  def scheduleAnchoredNodeEarly(n: ValueNode, anchor: BaseBeginNode): Unit = {
    visited.add(n)
    earliestScheduleOf += (n -> anchor)
    n.inputs.foreach(i => {
      scheduleEarly(i)
    })
  }

  def scheduleEarly(n0: Node): Unit = {
    n0 match {
      case n: ValueNode =>
        if (!visited.add(n)) {
          return
        }

        earliestScheduleOf += (n -> firstBlock)
        n.inputs.foreach({
          case i: ValueNode =>
            scheduleEarly(i)
            val ib = earliestScheduleOf(i)
            val nb = earliestScheduleOf(n)
            if (idomDepth(ib) > idomDepth(nb)) {
              // Need to move n downwards, as otherwise this input will not be available when n is evaluated.
              earliestScheduleOf += (n -> ib)
          }
          case _ =>
            ()
        })
      case _ =>
        ()
    }
  }

  def scheduleLate(): Unit = {
    // For each control-dependent node that uses values:
    Graph.dfsNode(g.entry) {
      case n: BaseBlockExitNode =>
        n.inputs.foreach(v => {
          scheduleAnchoredNodeLate(v.asInstanceOf[ValueNode], n.belongsToBlock)
        })

      case n: ValuePhiNode =>
        n.composedInputs.foreach()
        n.anchor.comingFrom
    }
  }

  def scheduleAnchoredNodeLate(value: ValueNode, n: BaseBeginNode): Unit = {
  }
}
