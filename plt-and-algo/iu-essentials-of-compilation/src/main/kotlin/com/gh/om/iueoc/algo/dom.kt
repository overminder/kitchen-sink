package com.gh.om.iueoc.algo

object Dom

// Naive dataflow, from Cooper's A Simple, Fast Dominance Algorithm
fun <G> Dom.naiveI(cap: GraphTraversalCap<G>, g: G, start: Int): Array<Set<Int>> {
    val doms = Array(cap.size(g)) {
        if (cap.hasNodeId(g, it)) {
            setOf(it)
        } else {
            emptySet()
        }
    }

    var changed = true
    val (rpo, _) = rpo(cap, g, start)
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
fun <G> Dom.cooperI(cap: GraphTraversalCap<G>, g: G, start: Int): IntArray {
    val doms = IntArray(cap.size(g)) {
        GraphCap.UNDEFINED
    }
    val (rpo, n2po) = rpo(cap, g, start)
    println("rpo ${rpo.toList()}")
    println("n2po ${n2po.toList()}")
    fun getPo(id: Int): Int {
        val po = n2po[id]
        require(GraphCap.isDefined(po))
        return po
    }
    val startPo = getPo(start)
    doms[startPo] = startPo
    var changed = true
    while (changed) {
        changed = false
        for (n in rpo) {
            if (n == start) {
                continue
            }

            val ps = cap.predecessors(g, n)
            val definedIx = ps.indexOfFirst {
                GraphCap.isDefined(doms[getPo(it)])
            }
            var newIDom = getPo(ps[definedIx])
            for ((ix, p) in ps.withIndex()) {
                if (ix == definedIx) {
                    continue
                }
                newIDom = intersect(doms, getPo(p), newIDom)
            }
            val nPo = getPo(n)
            if (doms[nPo] != newIDom) {
                doms[nPo] = newIDom
                changed = true
            }
        }
    }
    for ((ix, dom) in doms.withIndex()) {
        doms[ix] = dom
    }
    return doms
}

private fun intersect(doms: IntArray, x: Int, y: Int): Int {
    var finger1 = x
    var finger2 = y
    while (finger1 != finger2) {
        while (finger1 < finger2) {
            finger1 = doms[finger1]
            require(GraphCap.isDefined(finger1))
        }
        while (finger2 < finger1) {
            finger2 = doms[finger2]
            require(GraphCap.isDefined(finger2))
        }
    }
    return finger1
}

// Returns rpo, n2po
private fun <G> rpo(cap: GraphTraversalCap<G>, g: G, start: Int): Pair<IntArray, IntArray> {
    val postOrder = cap.dfsI(g, start, TraversalOrder.Post)
    val n2po = IntArray(cap.size(g)) { GraphCap.UNDEFINED }
    for ((ix, id) in postOrder.withIndex()) {
        n2po[id] = ix
    }

    postOrder.reverse()
    return postOrder to n2po
}
