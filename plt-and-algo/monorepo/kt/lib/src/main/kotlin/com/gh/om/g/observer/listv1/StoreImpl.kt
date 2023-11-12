package com.gh.om.g.observer.listv1

import com.gh.om.g.observer.frp.Behavior
import com.gh.om.g.observer.frp.MutableBehavior
import com.gh.om.g.observer.frp.ReentryGuard

class StoreImpl<K : Any, V> {
    private val reentryGuard = ReentryGuard(this.javaClass.simpleName)
    val idToNodes = mutableMapOf<K, Node<K, V>>()
    val watchers = mutableSetOf<Watcher<K, V>>()

    /**
     * @param mb A [Behavior] that represents the current node value
     */
    // XXX what about deletion?
    fun watch(mb: MutableBehavior<Node<K, V>>): AutoCloseable {
        val node = mb.value
        return reentryGuard {
            val doNotify = write(node)
            val rwNode = read(node)
            val w = newWatcher(rwNode, mb)
            mb.value = rwNode
            watchers += w
            doNotify()
            AutoCloseable {
                reentryGuard {
                    watchers -= w
                }
            }
        }
    }

    fun writeAndNotify(node: Node<K, V>) {
        reentryGuard {
            write(node)()
        }
    }

    private fun write(newNode: Node<K, V>): () -> Unit {
        // Update id map
        for (node in newNode.genNodes()) {
            node.id?.let { id ->
                mergeAndWrite(id, node)
            }
        }
        // Reconstruct updated nodes that are being watched
        val idsUpdated = newNode.ids().toSet()
        val thunksToNotify = watchers.mapNotNull { w ->
            buildThunkToNotify(idsUpdated, w)
        }
        // XXX when to GC unreachable nodes?
        return { thunksToNotify.forEach(Thunk::invoke) }
    }

    private fun mergeAndWrite(
        id: K,
        node: Node<K, V>
    ) {
        val oldNode = idToNodes[id]
        val merged = if (oldNode != null) {
            // Could even avoid the alloc if everything is the same.
            MutableNode(
                id = id,
                value = node.value,
                next = if (node.next.isPresent) {
                    node.next
                } else {
                    oldNode.next
                }
            )
        } else {
            node
        }
        idToNodes[id] = merged
    }

    private fun read(rNode: Node<K, V>): Node<K, V> {
        // A local graph to cache results and avoid recomputing cycles
        val mutGraph = mutableMapOf<K, MutableNode<K, V>>()
        val mutNode = readOnceMut(rNode, mutGraph)
        readIter(mutNode, mutNode, mutGraph)
        return mutNode
    }

    private tailrec fun readIter(
        head: Node<K, V>,
        tail: MutableNode<K, V>,
        mutGraph: MutableMap<K, MutableNode<K, V>>,
    ) {
        val next = tail.next.valueOrNull ?: return
        val visited = next.id != null && next.id in mutGraph
        val newNext = readOnceMut(next, mutGraph)
        tail.next = TriState.HasValue(newNext)
        if (visited) {
            // Assume we reached a fixed point. This is probably the case for singly linked list..
            return
        }
        readIter(head, newNext, mutGraph)
    }

    private fun readOnceMut(
        node: Node<K, V>,
        g: MutableMap<K, MutableNode<K, V>>
    ): MutableNode<K, V> {
        val id = node.id
        return if (id != null) {
            g.getOrPut(id) {
                requireNotNull(idToNodes[id]) {
                    "The node $id was just written and should exist"
                }.mutableCopy()
            }
        } else {
            node.mutableCopy()
        }
    }

    private fun buildThunkToNotify(
        idsUpdated: Set<K>,
        w: Watcher<K, V>
    ): Thunk? {
        if (!idsUpdated.any(w.contains::contains)) {
            return null
        }

        val rNode = read(w.mb.value)
        w.contains = rNode.ids().toSet()
        return if (rNode.stackSafeEq(w.mb.value)) {
            // Nothing to notify
            null
        } else {
            { w.mb.value = rNode }
        }
    }

    private fun newWatcher(
        newNode: Node<K, V>,
        mb: MutableBehavior<Node<K, V>>
    ): Watcher<K, V> {
        return Watcher(
            mb,
            newNode.ids().toSet()
        )
    }

    private fun Node<K, V>.mutableCopy(): MutableNode<K, V> {
        return MutableNode(id, next, value)
    }

    private fun Node<K, V>.genNodes(): Sequence<Node<K, V>> {
        val seenIds = mutableSetOf<K>()
        return generateSequence(this) {
            it.next.valueOrNull
        }.takeWhile {
            val id = it.id
            if (id == null) {
                true
            } else {
                // Avoid cycles.
                seenIds.add(id)
            }
        }.constrainOnce()
    }

    private fun Node<K, V>.ids() = genNodes().mapNotNull { it.id }
}

// Mutable to make certain operation faster
private class MutableNode<K : Any, V>(
    override val id: K?,
    override var next: TriState<Node<K, V>>,
    override val value: V
) : Node<K, V>

class Watcher<K : Any, V>(
    val mb: MutableBehavior<Node<K, V>>,
    /**
     * The transitive child ids in the node, such that when any of these
     * are updated, [mb] should be notified.
     */
    var contains: Set<K>,
)
