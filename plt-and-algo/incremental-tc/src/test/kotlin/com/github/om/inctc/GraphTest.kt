package com.github.om.inctc

import com.github.om.inctc.graph.DAG
import com.github.om.inctc.graph.GraphAlgo
import com.github.om.inctc.graph.GraphTraversal
import com.github.om.inctc.graph.HasCycles
import com.github.om.inctc.graph.MapDAGBuilder
import com.github.om.inctc.graph.NodeId
import com.github.om.inctc.graph.addMany
import com.github.om.inctc.graph.buildGraph
import com.github.om.inctc.graph.debugRepr
import com.github.om.inctc.graph.dfs
import com.github.om.inctc.graph.sccKosaraju
import com.github.om.inctc.graph.topoSort
import com.github.om.inctc.graph.transpose
import org.junit.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class GraphTest {
    // region base graph structure
    @Test
    fun testMapDAGBuilder() {
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
            assertEquals(listOf(it.second), g.succs(it.first).toList(), "succ is wrong?")
            assertEquals(listOf(it.first), g.preds(it.second).toList(), "pred is wrong?")
            assertEquals(Unit, g.get(it.first, it.second), "edge is wrong?")
        }
    }

    @Test
    fun testBuilderDsl() {
        var getN: (Int) -> NodeId<Int>
        val g = buildGraph<Int> {
            it.addMany(1 to 2 to 3)
            getN = it::nodeId
        }
        println(g.debugRepr)

        assertNotNull(g.get(getN(1), getN(2)))
        assertNotNull(g.get(getN(2), getN(3)))
        assertTrue(g.preds(getN(1)).isEmpty())
        assertTrue(g.succs(getN(3)).isEmpty())
    }

    @Test
    fun testTranpose() {
        var getN: (Int) -> NodeId<Int>
        val g = buildGraph<Int> {
            it.addMany(1 to 2 to 3)
            getN = it::nodeId
        }
        g.transpose()
        println(g.debugRepr)

        assertNotNull(g.get(getN(2), getN(1)))
        assertNotNull(g.get(getN(3), getN(2)))
        assertTrue(g.succs(getN(1)).isEmpty())
        assertTrue(g.preds(getN(3)).isEmpty())
    }
    // endregion

    // region traversal
    @Test
    fun testDfs() {
        val g = buildGraph<Int> {
            it += 1 to 2
            it += 2 to 3
            it += 2 to 4
            it += 3 to 5
            it += 4 to 5
        }

        assertEquals(listOf(1, 2, 3, 5, 4), dfs(g.nodes.first(), g, GraphTraversal.Order.Pre))
        assertEquals(listOf(5, 3, 4, 2, 1), dfs(g.nodes.first(), g, GraphTraversal.Order.Post))
    }
    // endregion

    @Test
    fun testSccSimple() {
        val g = buildGraph<Int> {
            it.addMany(7 to 4 to 1 to 7 to 9 to 6 to 8 to 2 to 5 to 8)
            it.addMany(6 to 3 to 9)
        }
        g.transpose()

        val sccs = GraphAlgo.sccKosaraju(g)
        assertEquals(
            setOf(setOf(1, 4, 7), setOf(3, 6, 9), setOf(2, 5, 8)),
            sccs.mapTo(mutableSetOf()) { it.mapNotNull(g::get).toSet() }
        )
    }

    @Test
    fun testSccNotConnected() {
        val g = buildGraph<Int> {
            it += 1
            it += 2
            it += 3
            it += 4
            it += 5
        }
        val sccs = GraphAlgo.sccKosaraju(g)
        assertEquals(5, sccs.size)
        assertEquals(List(5) { 1 }, sccs.map{ it.size })
    }

    @Test
    fun testSccDoesTopoSort() {
        val g = buildGraph<Int> {
            it.addMany(1 to 2 to 3 to 2)
            it.addMany(3 to 4 to 5)
            it.addMany(3 to 6 to 5)
        }

        val sccs = GraphAlgo.sccKosaraju(g)
        assertEquals(
            listOf(setOf(1), setOf(2, 3), setOf(4), setOf(6), setOf(5)),
            sccs.mapTo(mutableListOf()) { it.mapNotNull(g::get).toSet() }.reversed()
        )
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

private fun <N: Any> dfs(
    start: NodeId<N>,
    g: DAG<N, *>,
    order: GraphTraversal.Order,
    direction: GraphTraversal.Direction = GraphTraversal.Direction.Fwd
): List<N> {
    val nids = mutableListOf<NodeId<N>>()
    GraphTraversal.dfs(start, g, order, direction) {
        nids += it
    }
    return nids.map { requireNotNull(g.get(it)) }
}

