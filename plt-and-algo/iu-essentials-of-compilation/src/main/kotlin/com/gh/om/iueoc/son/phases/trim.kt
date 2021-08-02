package com.gh.om.iueoc.son.phases

import com.gh.om.iueoc.son.EdgeKind
import com.gh.om.iueoc.son.MutGraph
import com.gh.om.iueoc.son.MutGraphRef
import com.gh.om.iueoc.son.NodeId
import com.gh.om.iueoc.son.NodeTraversal
import com.gh.om.iueoc.son.OpCode
import com.gh.om.iueoc.son.get
import com.gh.om.iueoc.son.singleValueInput


object TrimPhase : Phase {
    override fun run(g: MutGraphRef): Boolean {
        return TrimPhaseRunner(g.g).once()
    }
}

/**
 * Remove unreachable nodes in [Graph.nodes], and compact nodeId. Note that this creates another graph reference.
 */
private class TrimPhaseRunner(private val g: MutGraph) {
    fun once(): Boolean {
        // 1. Remove values without uses.
        val changed = removeValueWithoutUses()

        // 2. Trim
        val gCopy = g.makeEmptyCopy()
        val idMap = gCopy.copyFrom(NodeTraversal.full(g).reachableNodes)
        require(gCopy.nodes.size == idMap.size)
        gCopy.setAnchors(
            start = requireNotNull(idMap[g.start]),
            end = requireNotNull(idMap[g.end]),
        )
        g.owner.replace(g, gCopy)
        return changed || g.nodes.size != gCopy.nodes.size
    }

    private fun removeValueWithoutUses(): Boolean {
        var changed = false
        val reachableNodeIds = NodeTraversal.live(g).reachableNodeIds

        for (nid in reachableNodeIds) {
            val n = g[nid]
            for (vo in n.valueOutputs.map(g::get)) {
                // If a value use is not reachable, then it can be safely removed.
                if (vo.id !in reachableNodeIds) {
                    vo.removeInput(n, EdgeKind.Value)
                    changed = true
                }
            }
            for (co in n.controlOutputs.map(g::get)) {
                if (co.id !in reachableNodeIds) {
                    co.removeInput(n, EdgeKind.Control)
                    changed = true
                }
            }
        }
        return changed
    }
}
