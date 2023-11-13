package com.gh.om.g.observer.listv1

import java.util.IdentityHashMap
import java.util.Objects

/**
 * Version 1: [Node]s directly refer to each other. This means every parent node
 * will have to be recreated whenever there's a change (assuming nodes are immutable).
 *
 * Possible optimizations: Use an external map for indirection, such that [next] is no longer
 * a [Node] but a key in a map.
 * - pros: This allows unchanged nodes to not have to be recreated.
 * - cons: How should unreachable nodes be GCed? Might have to use ephemerons
 *   (Barry Hayes, 1997)
 */
interface Node<out K : Any, out V> {
    /**
     * The (globally unique) identifier for this node, or null if this node is not
     * directly addressable.
     */
    val id: K?

    /**
     * The next node.
     */
    val next: TriState<Node<K, V>>

    /**
     * The value for this node.
     */
    val value: V
}

sealed class TriState<out A : Any> {
    data object NotPresent : TriState<Nothing>()
    data object IsNull : TriState<Nothing>()
    data class HasValue<out A : Any>(val value: A) : TriState<A>()
}

fun <A: Any, B: Any> TriState<A>.fmap(f: (A) -> B): TriState<B> {
    return bind {
        TriState.HasValue(f(it))
    }
}

fun <A: Any, B: Any> TriState<A>.bind(f: (A) -> TriState<B>): TriState<B> {
    return when (this) {
        is TriState.HasValue -> f(value)
        TriState.IsNull -> TriState.IsNull
        TriState.NotPresent -> TriState.NotPresent
    }
}

val TriState<*>.isPresent: Boolean
    get() = this !is TriState.NotPresent

val <A : Any> TriState<A>.valueOrNull: A?
    get() = (this as? TriState.HasValue)?.value

private class SeenPair(
    val lhs: Node<*, *>,
    val rhs: Node<*, *>
) {
    override fun hashCode(): Int {
        return Objects.hash(System.identityHashCode(lhs), System.identityHashCode(rhs))
    }

    override fun equals(other: Any?): Boolean {
        if (other !is SeenPair) return false
        return lhs === other.lhs && rhs === other.rhs
    }
}

private tailrec fun <K : Any, V> Node<K, V>?.eqIter(
    other: Node<K, V>?,
    seen: MutableMap<SeenPair, Unit>
): Boolean {
    if (this === other) {
        return true
    }
    if (other == null && this == null) {
        return true
    }
    if (other == null || this == null) {
        return false
    }

    if (id != other.id || value != other.value) {
        return false
    }
    // Ugh tailrec won't work across function boundary, even for inline (KT-14389)
    return when (val next = next) {
        is TriState.HasValue -> {
            val otherNext = other.next
            if (otherNext is TriState.HasValue) {
                val pair = SeenPair(this, other)
                if (seen.put(pair, Unit) == null) {
                    // If never seen: continue iter
                    next.value.eqIter(otherNext.value, seen)
                } else {
                    // If already seen: optimistically assume they are the same.
                    true
                }
            } else {
                false
            }
        }

        TriState.IsNull -> other.next is TriState.IsNull
        TriState.NotPresent -> other.next is TriState.NotPresent
    }
}

fun <K : Any, V> Node<K, V>?.stackSafeEq(
    other: Node<K, V>?,
): Boolean {
    return eqIter(other, IdentityHashMap<SeenPair, Unit>())
}

typealias Thunk = () -> Unit
