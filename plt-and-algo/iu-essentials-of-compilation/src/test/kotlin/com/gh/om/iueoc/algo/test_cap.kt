package com.gh.om.iueoc.algo

import org.junit.jupiter.api.Test
import kotlin.test.assertEquals

class TestGraphCap {
    @Test
    fun bfs() {
        val order = MapGraphCap.bfs(CASE_1, 0).toList()
        assertEquals(listOf(0, 1, 2, 3, 4, 5, 6), order)
    }

    @Test
    fun inversedBfs() {
        val order = MapGraphCap.bfs(CASE_1, 6, TraversalDirection.Bwd).toList()
        assertEquals(listOf(6, 5, 3, 4, 1, 2, 0), order)
    }

    @Test
    fun preOrderDfs() {
        val order = MapGraphCap.dfs(CASE_1, 0, TraversalOrder.Pre).toList()
        assertEquals(listOf(0, 1, 2, 4, 5, 6, 3), order)
    }

    @Test
    fun postOrderDfs() {
        val order = MapGraphCap.dfs(CASE_1, 0, TraversalOrder.Post).toList()
        assertEquals(listOf(6, 5, 4, 2, 3, 1, 0), order)
    }

    @Test
    fun domNaive() {
        val dom = Dom.naiveI(MapGraphCap, CASE_1, 0)
        val expected = listOf(
            setOf(0),
            setOf(0, 1),
            setOf(0, 1, 2),
            setOf(0, 1, 3),
            setOf(0, 1, 2, 4),
            setOf(0, 1, 5),
            setOf(0, 1, 5, 6)
        )
        for ((i, e) in expected.withIndex()) {
            assertEquals(e, dom[i])
        }
    }
}

val CASE_1: MapGraph = mapOf(
    0 to listOf(1),
    1 to listOf(2, 3),
    2 to listOf(4),
    3 to listOf(5),
    4 to listOf(5),
    5 to listOf(6),
    6 to emptyList(),
)

private typealias MapGraph = Map<Int, List<Int>>

private object MapGraphCap : GraphCap<MapGraph, Int> {
    override fun successors(g: MapGraph, id: Int): List<Int> {
        return g[id] ?: emptyList()
    }

    override fun nodeToId(g: MapGraph, n: Int): Int {
        return n
    }

    override fun size(g: MapGraph): Int {
        return g.size
    }

    override fun predecessors(g: MapGraph, id: Int): List<Int> {
        // This can be more performant in real implementations.
        return g.entries.mapNotNull { (k, v) ->
            if (id in v) {
                k
            } else {
                null
            }
        }
    }

    override fun idToNode(g: MapGraph, id: Int): Int {
        require(id in g)
        return id
    }

    override fun hasNodeId(g: MapGraph, id: Int): Boolean {
        return id in g
    }
}
