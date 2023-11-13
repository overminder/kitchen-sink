package com.gh.om.g.observer.listv1

import com.gh.om.g.observer.frp.Behavior
import com.gh.om.g.observer.frp.MutableBehavior
import com.gh.om.g.observer.frp.ReentryGuard
import com.gh.om.g.observer.listv1.NodeAdjUtil.ids
import com.gh.om.g.observer.listv1.NodeAdjUtil.splitToAdjsRec
import java.util.IdentityHashMap

/**
 * [Node] but in adjacency-list representation: [next] is an indirect ref rather than a direct ref.
 * Used as an internal representation in [StoreImpl]: [Node] are deconstructed when written to store,
 * and reconstructed when read from store.
 */
class NodeAdj<out ID, K : Any, V>(
    val id: ID,
    var next: TriState<NodeAdjEdge<K, V>>,
    val value: V,
)

private typealias NodeAdjRoot<K, V> = NodeAdj<K, K, V>

/**
 * Describes where the next node is stored.
 */
sealed class NodeAdjEdge<K : Any, V> {
    class Ref<K : Any, V>(val id: K) : NodeAdjEdge<K, V>()
    class Inlined<K : Any, V>(val value: NodeAdj<Unit, K, V>) : NodeAdjEdge<K, V>()
}

class StoreImpl<K : Any, V> {
    private val reentryGuard = ReentryGuard(this.javaClass.simpleName)
    val idToNodes = mutableMapOf<K, NodeAdjRoot<K, V>>()
    val watchers = mutableSetOf<Watcher<K, V>>()

    /**
     * @param mb A [Behavior] that represents the current node value
     */
    // XXX what about deletion?
    fun watch(mb: MutableBehavior<Node<K, V>>): AutoCloseable {
        val node = mb.value
        val (root, nodeAdjs) = node.splitToAdjsRec()
        // A local graph to build circular nodes
        val snapshot = mutableMapOf<K, MutableNode<K, V>>()
        return reentryGuard {
            val doNotify = write(nodeAdjs, snapshot)
            val rwNode = read(root, snapshot)
            val w = newWatcher(root, rwNode, mb)
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
        val (_, nodeAdjs) = node.splitToAdjsRec()
        reentryGuard {
            write(nodeAdjs, mutableMapOf())()
        }
    }

    private fun write(
        newNodes: List<NodeAdjRoot<K, V>>,
        snapshot: MutableMap<K, MutableNode<K, V>>
    ): () -> Unit {
        // Update id map
        for (node in newNodes) {
            mergeAndWrite(node)
        }
        // Reconstruct updated nodes that are being watched
        val idsUpdated = newNodes.map { it.id }.toSet()
        val thunksToNotify = watchers.mapNotNull { w ->
            buildThunkToNotify(idsUpdated, w, snapshot)
        }
        // XXX when to GC unreachable nodes?
        return { thunksToNotify.forEach(Thunk::invoke) }
    }

    private fun mergeAndWrite(node: NodeAdjRoot<K, V>) {
        val id = node.id
        val oldNode = idToNodes[id]
        val merged = if (oldNode != null) {
            NodeAdjRoot(
                id,
                if (node.next.isPresent) {
                    node.next
                } else {
                    oldNode.next
                },
                node.value
            )
        } else {
            node
        }
        idToNodes[id] = merged
    }

    /**
     * Reconstruct nodes from [root], reusing [snapshot] for structural sharing and to build cycles.
     */
    private fun read(
        root: NodeAdjEdge<K, V>,
        snapshot: MutableMap<K, MutableNode<K, V>>
    ): Node<K, V> {
        fun go(node: NodeAdjEdge<K, V>): Node<K, V> {
            return when (node) {
                is NodeAdjEdge.Inlined -> {
                    val deref = node.value
                    MutableNode(
                        id = null,
                        next = deref.next.fmap(::go),
                        value = deref.value
                    )
                }
                is NodeAdjEdge.Ref -> {
                    val existing = snapshot[node.id]
                    if (existing == null) {
                        val deref = requireNotNull(idToNodes[node.id]) {
                            "The node ${node.id} was just written and should exist"
                        }
                        val mutNode = MutableNode(
                            deref.id,
                            // To be populated later
                            TriState.NotPresent,
                            deref.value
                        )
                        snapshot[node.id] = mutNode
                        mutNode.next = deref.next.fmap(::go)
                        mutNode
                    } else {
                        existing
                    }
                }
            }
        }
        return go(root)
    }

    private fun buildThunkToNotify(
        idsUpdated: Set<K>,
        w: Watcher<K, V>,
        sharedNodeMap: MutableMap<K, MutableNode<K, V>>
    ): Thunk? {
        if (!idsUpdated.any(w.contains::contains)) {
            return null
        }

        val rNode = read(w.root, sharedNodeMap)
        w.contains = rNode.ids().toSet()
        return if (rNode.stackSafeEq(w.mb.value)) {
            // Nothing to notify
            null
        } else {
            { w.mb.value = rNode }
        }
    }

    private fun newWatcher(
        root: NodeAdjEdge<K, V>,
        currentValue: Node<K, V>,
        mb: MutableBehavior<Node<K, V>>
    ): Watcher<K, V> {
        return Watcher(
            root,
            mb,
            currentValue.ids().toSet()
        )
    }
}

fun <K : Any, V> Node<K, V>.mutableCopy(): MutableNode<K, V> {
    return MutableNode(id, next, value)
}

object NodeAdjUtil {
    fun <K : Any, V> Node<K, V>.genNodes(): Sequence<Node<K, V>> {
        val seenIds = IdentityHashMap<Node<*, *>, Unit>()
        return generateSequence(this) {
            it.next.valueOrNull
        }.takeWhile {
            // Avoid cycles.
            // XXX are nodes without ids supposed to have cycles? Probably still yes,
            // as each id-less node is still uniquely identifiable under an id-ful node or watcher's root.
            seenIds.put(it, Unit) == null
        }.constrainOnce()
    }

    fun <K : Any, V> Node<K, V>.ids() = genNodes().mapNotNull { it.id }

    /**
     * Deconstruct [this] to adjacency graph representation ([NodeAdjEdge]).
     */
    // Brute force, assuming no cycles, not tailrec
    fun <K : Any, V> Node<K, V>.splitToAdjsRec(): Pair<NodeAdjEdge<K, V>, List<NodeAdjRoot<K, V>>> {
        // In reversed order (child first, parent last)
        val out = mutableListOf<NodeAdjRoot<K, V>>()
        fun go(node: Node<K, V>): NodeAdjEdge<K, V> {
            val id = node.id
            val next = node.next.fmap(::go)
            return if (id == null) {
                NodeAdjEdge.Inlined(
                    NodeAdj(
                        Unit,
                        next,
                        node.value
                    )
                )
            } else {
                val newNode = NodeAdj(
                    id,
                    next,
                    node.value
                )
                out += newNode
                NodeAdjEdge.Ref(id)
            }
        }

        val root = go(this)
        // Such that it's ordered as parent first and child last
        out.reverse()
        return root to out
    }

    fun <K : Any, V> Node<K, V>.splitToAdjs(): Sequence<NodeAdj<K?, K, V>> {
        return sequence {
            var head: NodeAdj<K?, K, V>? = null
            var tail: NodeAdjEdge<K, V>? = null
            for (node in genNodes()) {
                val id = node.id
                /*
                val next = node.next.bind {
                    val nextId = it.id
                    if (nextId != null) {
                        TriState.HasValue(NodeAdjEdge.Ref(nextId))
                    } else {
                        // To be replaced later
                        TriState.NotPresent
                    }
                }
                 */
                val next = if (id != null) {
                    NodeAdjEdge.Ref(id)
                } else {
                    NodeAdjEdge.Inlined(
                        NodeAdj(
                            Unit,
                            TriState.NotPresent,
                            node.value
                        )
                    )
                }
            }
        }
    }
}

// Mutable to make certain operation faster, and to allow cycles
class MutableNode<K : Any, V>(
    override val id: K?,
    override var next: TriState<Node<K, V>>,
    override val value: V
) : Node<K, V>

class Watcher<K : Any, V>(
    /**
     * The "dehydrated" root node.
     */
    val root: NodeAdjEdge<K, V>,
    val mb: MutableBehavior<Node<K, V>>,
    /**
     * The transitive child ids in the node, such that when any of these
     * are updated, [mb] should be notified.
     */
    var contains: Set<K>,
)
