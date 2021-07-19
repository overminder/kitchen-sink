package com.gh.om.iueoc.algo

object Dom

// Naive dataflow, from Cooper's A Simple, Fast Dominance Algorithm
fun <G> Dom.naiveI(cap: GraphTraversalCap<G>, g: G, start: Int): List<Set<Int>> {
    val doms = MutableList(cap.size(g)) {
        if (cap.hasNodeId(g, it)) {
            setOf(it)
        } else {
            emptySet()
        }
    }

    var changed = true
    val rpo = rpo(cap, g, start)
    while (changed) {
        changed = false
        for (n in rpo) {
            val predDoms = cap.predecessors(g, n).map {
                doms[it]
            }
            // println("predDoms($n) = $predDoms")
            val newSet = if (predDoms.isEmpty()) {
                emptySet()
            } else {
                predDoms.reduce(Set<Int>::intersect)
            }.union(setOf(n))
            if (newSet != doms[n]) {
                // println("newSet($n) <- $newSet")
                doms[n] = newSet
                changed = true
            }
        }
    }

    return doms
}

// Optimized dataflow, also from Cooper
fun <G> Dom.cooper(cap: GraphTraversalCap<G>, g: G, start: Int): List<Set<Int>> {
    val doms = MutableList(cap.size(g)) {
        UNDEFINED
    }
    doms[start] = start
    var changed = true
    val rpoNoStart = rpo(cap, g, start) { it != start }
    while (changed) {
        changed = false
        for (n in rpoNoStart) {
            val ps = cap.predecessors(g, n)
            val pIx = ps.indexOfFirst {
                doms[it] != UNDEFINED
            }
            var newIDom = ps[pIx]
            for ((ix, p) in ps.withIndex()) {
                if (ix == pIx) {
                    continue
                }
            }
        }
    }
    TODO()
}

private const val UNDEFINED = -100

private fun <G> rpo(cap: GraphTraversalCap<G>, g: G, start: Int, filterBy: ((Int) -> Boolean)? = null): List<Int> {
    val postOrder = cap.dfsI(g, start, TraversalOrder.Post)
    val out = if (filterBy != null) {
        postOrder.filter(filterBy)
    } else {
        postOrder
    }.toMutableList()
    out.reverse()
    return out
}
