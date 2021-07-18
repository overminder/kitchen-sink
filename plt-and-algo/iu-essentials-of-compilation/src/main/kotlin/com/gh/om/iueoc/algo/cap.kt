package com.gh.om.iueoc.algo

import java.util.BitSet

// To avoid coupling with the exact graph repr.
// XXX can we avoid the conversion between N and Int?
interface DagCapability<G, N> {
    fun successors(g: G, n: N): List<N>

    // Gives a (preferably dense) non-negative int, smaller than [size].
    fun nodeToId(n: N): Int

    // Maximum node ID
    fun size(g: G): Int
}

// With predecessors.
interface DagCapabilityP<G, N: Any> : DagCapability<G, N> {
    fun predecessors(g: G, n: N): List<N>
    fun idToNode(g: G, id: Int): N?
}

private class InversedDag<G, N: Any>(private val cap: DagCapabilityP<G, N>): DagCapabilityP<G, N> by cap {
    override fun successors(g: G, n: N) = cap.predecessors(g, n)
    override fun predecessors(g: G, n: N) = cap.successors(g, n)
}

fun <G, N: Any> DagCapabilityP<G, N>.hasNodeId(g: G, id: Int): Boolean {
    return idToNode(g, id) != null
}

fun <G, N: Any> DagCapabilityP<G, N>.inversed(): DagCapabilityP<G, N> = InversedDag(this)

enum class TraversalOrder {
    Pre,
    Post,
}

fun <G, N> DagCapability<G, N>.bfs(g: G, start: N): Sequence<N> = sequence {
    val visited = BitSet(size(g))
    val queue = ArrayDeque<N>()
    queue.add(start)
    visited.set(nodeToId(start))

    while (queue.isNotEmpty()) {
        val n = queue.removeFirst()
        yield(n)
        for (s in successors(g, n)) {
            val id = nodeToId(s)
            if (!visited.get(id)) {
                visited.set(id)
                queue.add(s)
            }
        }
    }
}

fun <G, N> DagCapability<G, N>.dfs(g: G, start: N, order: TraversalOrder): Sequence<N> = sequence {
    val visited = BitSet(size(g))
    val stack = mutableListOf(start to false)
    visited.set(nodeToId(start))

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
            val id = nodeToId(s)
            if (!visited.get(id)) {
                visited.set(id)
                stack.add(s to false)
            }
        }
    }
}
