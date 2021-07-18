package com.gh.om.iueoc.son.phases

import com.gh.om.iueoc.son.EdgeKind
import com.gh.om.iueoc.son.MutGraph
import com.gh.om.iueoc.son.MutGraphRef
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
 * Also does a bit of simplifying, e.g. compact ->Effect->Effect-> to ->Effect->
 */
private class TrimPhaseRunner(private val g: MutGraph) {
    fun once(): Boolean {
        var changed = false

        // 1. Remove Effect->Effect and EffectPhi->Effect
        for (n in NodeTraversal.full(g).reachableNodes) {
            if (n.opCode == OpCode.Effect) {
                val vin = g[n.singleValueInput]
                if (vin.opCode == OpCode.Effect || vin.opCode == OpCode.EffectPhi) {
                    n.removeInput(vin, EdgeKind.Value)
                    n.valueOutputs.map(g::get).forEach { nUse ->
                        nUse.replaceInput(n, vin, EdgeKind.Value)
                    }
                    changed = true
                }
            }
        }

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
}
