package com.github.om.inctc.graph

import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.InvocationKind
import kotlin.contracts.contract

@Suppress("unused")
inline class NodeId<N>(val value: Int)

interface DAG<N: Any, out E: Any> {
    val nodes: Set<NodeId<N>>

    // Operator fun makes it harder to find usage...
    fun get(n: NodeId<N>): N?
    fun get(n1: NodeId<N>, n2: NodeId<N>): E?

    fun preds(n: NodeId<N>): Set<NodeId<N>>
    fun succs(n: NodeId<N>): Set<NodeId<N>>
}

interface DAGBuilder<N: Any, E: Any> : DAG<N, E> {
    fun addNode(v: N): NodeId<N>
    fun removeNode(n: NodeId<N>): N?
    fun addEdge(n1: NodeId<N>, n2: NodeId<N>, e: E)
    fun removeEdge(n1: NodeId<N>, n2: NodeId<N>): E?
    fun build(): DAG<N, E>
}

class MapDAG<N: Any, out E: Any>(
    internal val succs: Map<NodeId<N>, Set<NodeId<N>>>,
    internal val preds: Map<NodeId<N>, Set<NodeId<N>>>,
    internal val nodeMap: Map<NodeId<N>, N>,
    internal val edges: Map<Pair<NodeId<N>, NodeId<N>>, E>
) : DAG<N, E> {
    override val nodes: Set<NodeId<N>>
        get() = nodeMap.keys

    override fun get(n: NodeId<N>): N? = nodeMap[n]

    override fun get(n1: NodeId<N>, n2: NodeId<N>): E? = edges[n1 to n2]

    override fun preds(n: NodeId<N>): Set<NodeId<N>> = preds[n] ?: emptySet()

    override fun succs(n: NodeId<N>): Set<NodeId<N>> = succs[n] ?: emptySet()
}

class MapDAGBuilder<N: Any, E: Any> internal constructor(
    // Make these vars to support efficient transpose
    internal var succs: MutableMap<NodeId<N>, MutableSet<NodeId<N>>>,
    internal var preds: MutableMap<NodeId<N>, MutableSet<NodeId<N>>>,
    internal val nodeMap: MutableMap<NodeId<N>, N>,
    internal var edges: MutableMap<Pair<NodeId<N>, NodeId<N>>, E>
) : DAGBuilder<N, E> {
    private var idGen = 1

    companion object {
        fun <N: Any, E: Any> create(): MapDAGBuilder<N, E> {
            return MapDAGBuilder(mutableMapOf(), mutableMapOf(), mutableMapOf(), mutableMapOf())
        }
    }

    override fun addNode(v: N): NodeId<N> {
        val id = NodeId<N>(idGen++)
        nodeMap += id to v
        return id
    }

    override fun removeNode(n: NodeId<N>): N? {
        val v = nodeMap.remove(n)
        if (v == null) {
            return v
        }

        succs.remove(n)?.forEach { succ ->
            preds[succ]?.remove(n)
        }
        preds.remove(n)?.forEach { pred ->
            succs[pred]?.remove(n)
        }
        return v
    }

    override fun addEdge(n1: NodeId<N>, n2: NodeId<N>, e: E) {
        edges.put(n1 to n2, e)
        succs.compute(n1) { _, v ->
            (v ?: mutableSetOf()).also {
                it += n2
            }
        }
        preds.compute(n2) { _, v ->
            (v ?: mutableSetOf()).also {
                it += n1
            }
        }
    }

    override fun removeEdge(n1: NodeId<N>, n2: NodeId<N>): E? {
        val e = edges.remove(n1 to n2)
        if (e == null) {
            return e
        }

        succs.compute(n1) { _, v ->
            v?.apply { remove(n2) }
        }
        preds.compute(n2) { _, v ->
            v?.apply { remove(n1) }
        }
        return e
    }

    override fun build(): DAG<N, E> = MapDAG(freeze(succs), freeze(preds), freeze(nodeMap), freeze(edges))

    fun transpose() {
        // Swap preds and succs
        val ps = preds
        preds = succs
        succs = ps

        // Swap edges
        val es = edges
        edges = mutableMapOf()
        es.mapKeysTo(edges) {
            it.key.second to it.key.first
        }
    }

    // DAG (XXX: this duplication is unfortunate... But is necessary due to transpose changing field references.)

    override val nodes: Set<NodeId<N>>
        get() = nodeMap.keys

    override fun get(n: NodeId<N>): N? = nodeMap[n]

    override fun get(n1: NodeId<N>, n2: NodeId<N>): E? = edges[n1 to n2]

    override fun preds(n: NodeId<N>): Set<NodeId<N>> = preds[n] ?: emptySet()

    override fun succs(n: NodeId<N>): Set<NodeId<N>> = succs[n] ?: emptySet()
}

private fun <N: Any, E: Any> DAG<N, E>.debugReprForSucc(succs: Map<NodeId<N>, Set<NodeId<N>>>): List<String> {
    return succs.map {
        "${get(it.key)} -> ${it.value.map(::get)}"
    }
}

val <N: Any, E: Any> DAG<N, E>.debugRepr: String
    get() {
        return when (this) {
            is MapDAG -> "MapDAG${debugReprForSucc(succs)}"
            is MapDAGBuilder -> "MapDAG${debugReprForSucc(succs)}"
            else -> error("Don't know what this is: $this")
        }
    }


val DAG<*, *>.isEmpty: Boolean
    get() = nodes.isEmpty()

fun <N: Any, E: Any> DAGBuilder<N, E>.transpose() {
    when (this) {
        is MapDAGBuilder -> transpose()
        else -> error("Don't know what this is: $this")
    }
}

fun <N: Any, E: Any> DAG<N, E>.toBuilder(): DAGBuilder<N, E> {
    // too hacky
    return when (this) {
        is MapDAG -> MapDAGBuilder(thaw(succs), thaw(preds), nodeMap.toMutableMap(), edges.toMutableMap())
        is MapDAGBuilder -> MapDAGBuilder(thaw(succs), thaw(preds), nodeMap.toMutableMap(), edges.toMutableMap())
        else -> error("Don't know what this is: $this")
    }
}

interface DAGBuilderDsl<N: Any> {
    operator fun plusAssign(e: Pair<N, N>)
    operator fun plusAssign(v: N)
    fun nodeId(v: N): NodeId<N>
}

private class DAGBuilderDslImpl<N: Any> : DAGBuilderDsl<N> {
    val gb = MapDAGBuilder.create<N, Unit>()
    val n2id = mutableMapOf<N, NodeId<N>>()

    override fun plusAssign(e: Pair<N, N>) {
        gb.addEdge(nodeId(e.first), nodeId(e.second), Unit)
    }

    override fun plusAssign(v: N) {
        nodeId(v)
    }

    override fun nodeId(v: N): NodeId<N> = n2id.getOrPut(v) {
        gb.addNode(v)
    }
}

inline fun <reified N: Any> DAGBuilderDsl<N>.addMany(es: Pair<*, N>) {
    var car = es.first
    var cdr = es.second

    while (car is Pair<*, *>) {
        val cadr = car.second as N
        this += cadr to cdr
        car = car.first
        cdr = cadr
    }
    this += car as N to cdr
}

@ExperimentalContracts
fun <N: Any> buildGraph(block: (DAGBuilderDsl<N>) -> Unit): DAGBuilder<N, Unit> {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }

    val b = DAGBuilderDslImpl<N>()
    block(b)
    return b.gb
}

// Helpers

private fun <K, V> freeze(m: Map<K, Set<V>>): Map<K, Set<V>> = freeze(m) { freeze(it) }

private fun <K, V> freeze(m: Map<K, V>, freezeValue: (V) -> V = { it }): Map<K, V> {
    return m.mapValues {
        freezeValue(it.value)
    }
}

private fun <V> freeze(s: Set<V>, freezeValue: (V) -> V = { it }): Set<V> {
    return s.asSequence().map(freezeValue).toSet()
}

private fun <K, V> thaw(m: Map<K, Set<V>>): MutableMap<K, MutableSet<V>> = thaw(m) { thaw(it) }

private fun <K, V, V2> thaw(m: Map<K, V>, thawValue: (V) -> V2): MutableMap<K, V2> {
    val res = mutableMapOf<K, V2>()
    return m.mapValuesTo(res) { thawValue(it.value) }
}

private fun <V> thaw(s: Set<V>, thawValue: (V) -> V = { it }): MutableSet<V> {
    return s.asSequence().map(thawValue).toMutableSet()
}
