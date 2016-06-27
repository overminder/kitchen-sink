package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.hir.nodes._

object Opt {
  object Kit {
    // This can be perfectly solved by looking up the node that the IfNode immediately dominates...
    def mergeForIf(n: IfNode): Option[BaseMergeNode] = {
      Option(n.merge)
    }

    // In a forward way.
    // XXX: This is obviously too simple - we need a worklist approach.
    def killCfg(n: Node): Unit = {
      def go(n0: Node): Unit = {
        if (n0 == null) {
          return
        }

        n0 match {
          case n: IfNode =>
            n.value = null
            val t = n.t
            val f = n.f
            n.t = null
            n.f = null
            go(n.t)
            go(n.f)
          case n: SingleNext[_] =>
            val nn = n.asInstanceOf[SingleNext[Node]]
            val next = nn.next
            nn.next = null
            go(next)
          case n: BaseEndNode =>
            val succ = n.cfgSuccessor
            n.replaceAllUsesWith(null)
            go(succ)
          case _ =>
            n0.replaceAllUsesWith(null)
        }
      }
      go(n)
    }
  }

  def simplifyIf(n: IfNode, g: Graph): Unit = {
    def replaceByBranch(n: IfNode, t: Boolean): Unit = {
      val merge = Kit.mergeForIf(n)
      val (brIx, br, brToKill) = if (t) {
        val br = n.t
        n.t = null
        (0, br, n.f)
      } else {
        val br = n.f
        n.f = null
        (1, br, n.t)
      }
      // Kill the value node
      val condNode = n.value
      n.value = null
      condNode.tryRemove()
      // Replace this IfNode by the chosen branch
      n.replaceThisOnPredecessor(br)
      merge match {
        case Some(m) =>
          // Select phis coming from the chosen branch
          m.valuePhis.foreach(phi => {
            phi.replaceAllUsesWith(phi.composedInputs(brIx))
          })
          // Connect the end of the chosen branch to the merge successor
          val brEnd = m.comingFrom(brIx).asInstanceOf[EndNode]
          val mergeNext = m.next
          m.next = null
          brEnd.replaceThisOnPredecessor(mergeNext)
        case None =>
          // We are already done.
      }
      Kit.killCfg(brToKill)
    }
    n.value match {
      case TrueNode =>
        replaceByBranch(n, t = true)
      case FalseNode =>
        replaceByBranch(n, t = false)
      case _ =>
        ()
    }
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
