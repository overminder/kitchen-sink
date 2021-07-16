package com.gh.om.iueoc.son

/**
 * Remove unreachable nodes in [Graph.nodes], and compact nodeId.
 * Also does a bit of simplifying, e.g. compact ->Effect->Effect-> to ->Effect->
 */
class TrimPhase(private val g: Graph) {
    fun run() {
        val idMap = mutableMapOf<NodeId, NodeId>()
        for (n in NodeTraversal(g).liveNodes) {
        }
    }
}
