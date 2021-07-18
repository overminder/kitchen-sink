package com.gh.om.iueoc.algo

object Dom

// Naive dataflow, from Cooper's A Simple, Fast Dominance Algorithm
fun <G, N: Any> Dom.naive(cap: DagCapabilityP<G, N>, g: G, start: N): List<List<N>> {
    val dom = MutableList(cap.size(g)) {
        if (cap.hasNodeId(g, it)) {
            setOf(it)
        } else {
            emptySet()
        }
    }

    var changed = true
    while (changed) {
        changed = false
        val rpo = cap.dfs(g, start, TraversalOrder.Post).toMutableList().also {
            it.reverse()
        }
        for (n in rpo) {
            val nid = cap.nodeToId(n)
            val predDoms = cap.predecessors(g, n).map {
                dom[cap.nodeToId(it)]
            }
            // println("predDoms($n) = $predDoms")
            val newSet = if (predDoms.isEmpty()) {
                emptySet()
            } else {
                predDoms.reduce(Set<Int>::intersect)
            }.union(setOf(nid))
            if (newSet != dom[nid]) {
                // println("newSet($n) <- $newSet")
                dom[nid] = newSet
                changed = true
            }
        }
    }

    return dom.map { ids ->
        ids.map {
            requireNotNull(cap.idToNode(g, it))
        }
    }
}

// Optimized dataflow, also from Cooper
fun <G, N: Any> Dom.cooper(cap: DagCapabilityP<G, N>, g: G, start: N): List<List<N>> {
    TODO()
}
