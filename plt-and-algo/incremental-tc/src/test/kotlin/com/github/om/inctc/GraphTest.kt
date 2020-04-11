package com.github.om.inctc

import com.github.om.inctc.graph.GraphAlgo
import com.github.om.inctc.graph.HasCycles
import com.github.om.inctc.graph.MapDAGBuilder
import com.github.om.inctc.graph.buildGraph
import com.github.om.inctc.graph.debugRepr
import com.github.om.inctc.graph.topoSort
import org.junit.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

class GraphTest {
    @Test
    fun testBuilder() {
        val gb = MapDAGBuilder.create<Int, Unit>()
        val nodes = (0 until 10).map(gb::addNode)
        nodes.zip(nodes.drop(1)).forEach {
            gb.addEdge(it.first, it.second, Unit)
        }

        val g = gb.build()

        nodes.forEach {
            assertTrue(g.nodes.contains(it), "node not added?")
        }

        nodes.zip(nodes.drop(1)).forEach {
            assertEquals(listOf(it.second), g.succs(it.first)?.toList(), "succ is wrong?")
            assertEquals(listOf(it.first), g.preds(it.second)?.toList(), "pred is wrong?")
            assertEquals(Unit, g.get(it.first, it.second), "edge is wrong?")
        }
    }

    // region toposort

    @Test
    fun testTopoOk() {
        val g = buildGraph<Int> {
            it += 1 to 2
            it += 2 to 3
            it += 2 to 4
            it += 3 to 5
            it += 4 to 5
        }

        val sorted = GraphAlgo.topoSort(g).map(g::get)
        assertEquals(listOf(1, 2, 3, 4, 5), sorted)
    }

    @Test
    fun testTopoFullCycle() {
        val g = buildGraph<Int> {
            it += 1 to 2
            it += 2 to 3
            it += 3 to 1
        }

        assertFailsWith(HasCycles::class) {
            GraphAlgo.topoSort(g)
        }
    }

    @Test
    fun testTopoSmallerCycle() {
        val g = buildGraph<Int> {
            it += 1 to 2
            it += 2 to 3
            it += 3 to 2
        }

        assertFailsWith(HasCycles::class) {
            GraphAlgo.topoSort(g)
        }
    }

    // endregion
}