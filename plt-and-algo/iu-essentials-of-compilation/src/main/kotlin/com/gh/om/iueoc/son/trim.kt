package com.gh.om.iueoc.son


object TrimPhase : Phase {
    override fun run(g: MutGraph): Boolean {
        return TrimPhaseRunner(g).once()
    }
}

/**
 * Remove unreachable nodes in [Graph.nodes], and compact nodeId.
 * Also does a bit of simplifying, e.g. compact ->Effect->Effect-> to ->Effect->
 */
private class TrimPhaseRunner(private val g: MutGraph) {
    fun once(): Boolean {
        val gCopy = g.makeEmptyCopy()
        val idMap = gCopy.copyFrom(NodeTraversal.full(g).reachableNodes)
        require(gCopy.nodes.size == idMap.size)
        gCopy.setAnchors(
            start = requireNotNull(idMap[g.start]),
            end = requireNotNull(idMap[g.end]),
        )
        g.owner.replace(g, gCopy)
        return g.nodes.size != gCopy.nodes.size
    }
}
