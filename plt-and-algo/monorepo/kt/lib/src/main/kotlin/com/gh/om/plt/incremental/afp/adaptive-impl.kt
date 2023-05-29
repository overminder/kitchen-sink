package com.gh.om.plt.incremental.afp

import java.util.PriorityQueue
import kotlin.RuntimeException
import kotlin.reflect.KMutableProperty0

class AdaptiveModuleImpl<T>(
    private val ord: OrderedList<T>,
) : AdaptiveModule<Unit> {
    private var currentTime = ord.init()
    private val pq = PriorityQueue(edgeComparator(ord.comparator))

    override fun init() {
        currentTime = ord.init()
        pq.clear()
    }

    override fun <A> mod(
        cmp: (A, A) -> Boolean,
        f: (Dest<A>) -> Unit
    ): Mod<A> {
        val node = Node<A, T>(
            { throw UnsetMod() },
            { throw UnsetMod() },
            emptyList(),
        )

        fun change(
            t: T,
            v: A
        ) {
            if (!cmp(v, node.value())) {
                // Changed.
                node.value = { v }
                node.outEdges.forEach(pq::add)
                node.outEdges = emptyList()
            }
            // Always record the change time (even if value is effectively unchanged).
            currentTime = t
        }
        node.wrt = { v ->
            node.value = { v }
            node.wrt = { wrtTime -> change(ord.insert(::currentTime), wrtTime) }
        }
        f(node)
        return node
    }

    override fun <A> write(
        dest: Dest<A>,
        value: A
    ) {
        // Blame the lack of hkt
        @Suppress("UNCHECKED_CAST")
        dest as Node<A, T>

        dest.wrt(value)
    }

    override fun <A> read(
        mod: Mod<A>,
        f: (A) -> Unit
    ) {
        // Blame the lack of hkt
        @Suppress("UNCHECKED_CAST")
        mod as Node<A, T>

        val start = ord.insert(::currentTime)
        fun run() {
            f(mod.value())
            val newEdge = Edge(
                reader = ::run,
                timeSpan = start to currentTime
            )
            mod.outEdges = listOf(newEdge) + mod.outEdges
        }
        run()
    }

    override fun <A> change(
        mod: Mod<A>,
        value: A
    ) {
        // Blame the lack of hkt
        @Suppress("UNCHECKED_CAST")
        mod as Node<A, T>

        mod.wrt(value)
    }

    override fun propagate() {
        val snapshot = currentTime
        propagateInternal()
        currentTime = snapshot
    }

    private fun propagateInternal() {
        while (pq.isNotEmpty()) {
            val edge = pq.remove()
            val (start, stop) = edge.timeSpan
            if (ord.isSplicedOut(start)) {
                // Deleted read, discard
                continue
            }
            ord.spliceOut(start, stop)
            currentTime = start
            // Rerun the read
            edge.reader()
        }
    }
}

private class UnsetMod : RuntimeException()

interface OrderedList<T> {
    fun init(): T

    val comparator: Comparator<T>

    // Seems to take a ref in the paper
    fun insert(t: KMutableProperty0<T>): T

    /**
     * Delete items between [x] and [y] (inclusive)
     */
    fun spliceOut(
        x: T,
        y: T
    )
    /**
     * @return True if the item is deleted.
     */
    fun isSplicedOut(t: T): Boolean
}

private data class Edge<T>(
    val reader: () -> Unit,
    val timeSpan: Pair<T, T>,
)

private fun <T> edgeComparator(compareT: Comparator<T>): Comparator<Edge<T>> {
    return Comparator
        .comparing({ edge: Edge<T> -> edge.timeSpan.first }, compareT)
        .thenComparing({ it.timeSpan.second }, compareT)
}

private data class Node<A, T>(
    var value: () -> A,
    var wrt: (A) -> Unit,
    var outEdges: List<Edge<T>>,
) : Mod<A>, Dest<A>

class NaiveOrderedList : OrderedList<Int> {
    private val store = mutableListOf<Int>()
    private var nextId = 0
    override fun init(): Int {
        store.clear()
        nextId = 0
        val res = ++nextId
        store.add(res)
        return res
    }

    override val comparator: Comparator<Int> = Comparator { x, y ->
        val xPos = store.indexOf(x)
        val yPos = store.indexOf(y)
        xPos.compareTo(yPos)
    }

    override fun isSplicedOut(t: Int): Boolean {
        return store.contains(t)
    }

    override fun spliceOut(
        x: Int,
        y: Int
    ) {
        val xPos = store.indexOf(x)
        val yPos = store.indexOf(y)
        store.subList(xPos, yPos + 1).clear()
    }

    override fun insert(t: KMutableProperty0<Int>): Int {
        val res = ++nextId
        val pos = store.indexOf(t.get())
        store.add(pos, res)
        return res
    }
}