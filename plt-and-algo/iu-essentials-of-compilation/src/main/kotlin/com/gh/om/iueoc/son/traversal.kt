package com.gh.om.iueoc.son

class NodeTraversal private constructor(private val nodes: List<Node>, private val reachable: MutableSet<NodeId>) {
    val reachableNodeIds: Set<NodeId>
        get() = reachable

    val reachableNodes
        get() = reachable.asSequence().map { Graph[nodes, it] }

    companion object {
        // [followOutputs] allows dead code (e.g. unused argument) to be considered as live.
        // Unless we do DCE between every traversal (which is likely beneficial?), we have to do this.
        fun full(g: Graph) = of(g.nodes, g.end, followOutputs = true)
        fun live(g: Graph) = of(g.nodes, g.end, followOutputs = false)

        private fun of(nodes: List<Node>, end: NodeId, followOutputs: Boolean = true): NodeTraversal {
            return NodeTraversal(nodes, findReachable(nodes, end, followOutputs))
        }
    }
}

private fun findReachable(nodes: List<Node>, end: NodeId, followOutputs: Boolean): MutableSet<NodeId> {
    val workList = ArrayDeque<NodeId>()
    val enqueued = mutableSetOf<NodeId>()
    workList.addLast(end)
    enqueued += end

    fun go(nodeId: NodeId) {
        if (nodeId !in enqueued) {
            enqueued += nodeId
            workList.addLast(nodeId)
        }
    }

    while (workList.isNotEmpty()) {
        val nid = workList.removeFirst()
        val n = Graph[nodes, nid]
        n.valueInputs.forEach(::go)
        n.controlInputs.forEach(::go)
        if (followOutputs) {
            n.valueOutputs.forEach(::go)
            n.controlOutputs.forEach(::go)
        }
    }
    return enqueued
}
