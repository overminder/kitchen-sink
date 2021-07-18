package com.gh.om.iueoc.algo

import org.junit.jupiter.api.Test
import kotlin.test.assertEquals

private typealias MapDag = Map<Int, List<Int>>
private typealias MutMapDag = MutableMap<Int, MutableList<Int>>

private object MapDagCap : DagCapabilityP<MapDag, Int> {
    override fun successors(g: MapDag, n: Int): List<Int> {
        return g[n] ?: emptyList()
    }

    override fun nodeToId(n: Int): Int {
        return n
    }

    override fun size(g: MapDag): Int {
        return g.size
    }

    override fun predecessors(g: MapDag, n: Int): List<Int> {
        // This can be more performant in real implementations.
        return g.entries.mapNotNull { (k, v) ->
            if (n in v) {
                k
            } else {
                null
            }
        }
    }

    override fun idToNode(g: MapDag, id: Int): Int? {
        return if (id in g) {
            id
        } else {
            null
        }
    }
}

val CASE_1: MapDag = mapOf(
    0 to listOf(1),
    1 to listOf(2, 3),
    2 to listOf(4),
    3 to listOf(5),
    4 to listOf(5),
    5 to listOf(6),
    6 to emptyList(),
)

class TestDagCapability {
    @Test
    fun bfs() {
        val order = MapDagCap.bfs(CASE_1, 0).toList()
        assertEquals(listOf(0, 1, 2, 3, 4, 5, 6), order)
    }

    @Test
    fun inversedBfs() {
        val order = MapDagCap.inversed().bfs(CASE_1, 6).toList()
        assertEquals(listOf(6, 5, 3, 4, 1, 2, 0), order)
    }

    @Test
    fun preOrderDfs() {
        val order = MapDagCap.dfs(CASE_1, 0, TraversalOrder.Pre).toList()
        assertEquals(listOf(0, 1, 2, 4, 5, 6, 3), order)
    }

    @Test
    fun postOrderDfs() {
        val order = MapDagCap.dfs(CASE_1, 0, TraversalOrder.Post).toList()
        assertEquals(listOf(6, 5, 4, 2, 3, 1, 0), order)
    }

    @Test
    fun domNaive() {
        val dom = Dom.naive(MapDagCap, CASE_1, 0)
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
            assertEquals(e, dom[i].toSet())
        }
    }
}