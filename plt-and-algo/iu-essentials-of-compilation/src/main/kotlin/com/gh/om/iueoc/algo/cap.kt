package com.gh.om.iueoc.algo

import java.util.BitSet

// To avoid coupling with the exact graph repr.
// Node IDs are (preferably dense) non-negative ints, smaller than [size].
interface GraphTraversalCap<G> {
    // Maximum node ID
    fun size(g: G): Int

    // In case the size is sparse.
    fun hasNodeId(g: G, id: Int): Boolean

    // Only makes sense if hasNodeId(id) is true.
    fun predecessors(g: G, id: Int): List<Int>
    fun successors(g: G, id: Int): List<Int>
}

interface GraphMapperCap<G, N : Any> {
    fun nodeToId(g: G, n: N): Int
    fun idToNode(g: G, id: Int): N
}

interface GraphCap<G, N : Any> : GraphTraversalCap<G>, GraphMapperCap<G, N>

private class InversedGraphTraversalCap<G>(private val cap: GraphTraversalCap<G>) : GraphTraversalCap<G> by cap {
    override fun successors(g: G, id: Int) = cap.predecessors(g, id)
    override fun predecessors(g: G, id: Int) = cap.successors(g, id)
}

fun <G> GraphTraversalCap<G>.inversed(): GraphTraversalCap<G> = InversedGraphTraversalCap(this)
fun <G> GraphTraversalCap<G>.maybeInverse(direction: TraversalDirection): GraphTraversalCap<G> = when (direction) {
    TraversalDirection.Fwd -> this
    TraversalDirection.Bwd -> inversed()
}

enum class TraversalOrder {
    Pre,
    Post,
}

enum class TraversalDirection {
    Fwd,
    Bwd,
}

fun <GC, G, N : Any> GC.bfs(
    g: G,
    start: N,
    direction: TraversalDirection = TraversalDirection.Fwd,
): Sequence<N> where GC : GraphTraversalCap<G>, GC : GraphMapperCap<G, N> =
    maybeInverse(direction).bfsI(g, nodeToId(g, start)).mapToNode(this, g)

fun <GC, G, N : Any> GC.dfs(
    g: G,
    start: N,
    order: TraversalOrder,
    direction: TraversalDirection = TraversalDirection.Fwd,
): Sequence<N> where GC : GraphTraversalCap<G>, GC : GraphMapperCap<G, N> =
    maybeInverse(direction).dfsI(g, nodeToId(g, start), order).mapToNode(this, g)

fun <G> GraphTraversalCap<G>.bfsI(g: G, start: Int): Sequence<Int> = sequence {
    val visited = BitSet(size(g))
    val queue = ArrayDeque<Int>()
    queue.add(start)
    visited.set(start)

    while (queue.isNotEmpty()) {
        val n = queue.removeFirst()
        yield(n)
        for (s in successors(g, n)) {
            if (!visited.get(s)) {
                visited.set(s)
                queue.add(s)
            }
        }
    }
}

fun <G> GraphTraversalCap<G>.dfsI(g: G, start: Int, order: TraversalOrder): Sequence<Int> = sequence {
    val visited = BitSet(size(g))
    val stack = mutableListOf(start to false)
    visited.set(start)

    while (stack.isNotEmpty()) {
        val (n, childVisited) = stack.removeLast()
        when (order) {
            TraversalOrder.Pre -> {
                if (!childVisited) {
                    yield(n)
                }
            }
            TraversalOrder.Post -> {
                if (childVisited) {
                    yield(n)
                    continue
                } else {
                    stack.add(n to true)
                }
            }
        }
        for (s in successors(g, n).reversed()) {
            if (!visited.get(s)) {
                visited.set(s)
                stack.add(s to false)
            }
        }
    }
}

private fun <G, N : Any> Sequence<Int>.mapToNode(cap: GraphMapperCap<G, N>, g: G): Sequence<N> {
    return map {
        requireNotNull(cap.idToNode(g, it))
    }
}