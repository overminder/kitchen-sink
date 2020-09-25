package om.lang.pie

sealed class ConsList<A : Any> {
    object Nil : ConsList<Any>()
    data class Cons<A : Any>(val head: A, val tail: ConsList<A>) : ConsList<A>()

    companion object {
        @Suppress("UNCHECKED_CAST")
        fun <A: Any> nil(): ConsList<A> = Nil as ConsList<A>
    }

    fun cons(a: A) : ConsList<A> {
        return Cons(a, this)
    }

    fun <B: Any> mapNotNull(f: (A) -> B?): ConsList<B> {
        var iter = this
        val out = mutableListOf<B>()
        while (iter is Cons) {
            f(iter.head)?.let(out::add)
            iter = iter.tail
        }
        return out.foldRight(nil()) { item, acc ->
            acc.cons(item)
        }
    }
}

fun <K : Any, V : Any> ConsList<Pair<K, V>>.assoc(k: K): ConsList.Cons<Pair<K, V>>? {
    var iter = this
    while (iter is ConsList.Cons) {
        if (iter.head.first == k) {
            return iter
        }
        iter = iter.tail
    }
    return null
}

fun <K : Any, V : Any> ConsList<Pair<K, V>>.assocv(k: K): V? {
    return assoc(k)?.head?.second
}

