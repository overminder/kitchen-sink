package com.gh.om.iueoc.son

class NodeTraversal(val g: Graph, followOutputs: Boolean = false) {
    val liveNodeIds: Collection<NodeId>
        get() = _liveNodeIds

    val liveNodes
        get() = _liveNodeIds.asSequence().map { g[it] }

    private val _liveNodeIds = findLiveNodes(g, followOutputs)
}

private fun findLiveNodes(g: Graph, followOutputs: Boolean): MutableSet<NodeId> {
    val workList = ArrayDeque<NodeId>()
    val enqueued = mutableSetOf<NodeId>()
    workList.addLast(g.end)
    enqueued += g.end

    fun go(nodeId: NodeId) {
        if (nodeId !in enqueued) {
            enqueued += nodeId
            workList.addLast(nodeId)
        }
    }

    while (workList.isNotEmpty()) {
        val nid = workList.removeFirst()
        val n = g[nid]
        n.valueInputs.forEach(::go)
        n.controlInputs.forEach(::go)
        if (followOutputs) {
            n.valueOutputs.forEach(::go)
            n.controlOutputs.forEach(::go)
        }
    }
    return enqueued
}
