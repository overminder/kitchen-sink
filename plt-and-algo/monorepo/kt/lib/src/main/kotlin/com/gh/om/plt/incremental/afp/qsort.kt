package com.gh.om.plt.incremental.afp

import java.util.Comparator

sealed class Lst<out A> {
    object Nil : Lst<Nothing>()
    data class Cons<out A>(val head: A, val tail: Lst<A>) : Lst<A>()

    companion object {
        fun <A> fromList(xs: List<A>): Lst<A> = xs.foldRight<A, Lst<A>>(Lst.Nil) { h, t ->
            Lst.Cons(h, t)
        }
    }
}


fun <A> Lst<A>.toList(): List<A> = foldl({ acc, x ->
    acc += x
    acc
}, mutableListOf())

fun <A, R> Lst<A>.foldl(f: (R, A) -> R, initial: R): R {
    tailrec fun go(xs: Lst<A>, acc: R): R = when (xs) {
        is Lst.Cons -> go(xs.tail, f(acc, xs.head))
        Lst.Nil -> acc
    }
    return go(this, initial)
}

fun <A> Lst<A>.filter(f: (A) -> Boolean): Lst<A> = when (this) {
    Lst.Nil -> Lst.Nil
    is Lst.Cons -> if (f(head)) {
        Lst.Cons(head, tail.filter(f))
    } else {
        tail.filter(f)
    }
}

fun <A> Lst<A>.qsort(cmp: Comparator<A>): Lst<A> {
    tailrec fun go(xs: Lst<A>, rest: Lst<A>): Lst<A> = when (xs) {
        Lst.Nil -> rest
        is Lst.Cons -> {
            val h = xs.head
            val t = xs.tail
            val l = t.filter { cmp.compare(it, h) < 0 }
            val g = t.filter { cmp.compare(it, h) >= 0 }

            @Suppress("NON_TAIL_RECURSIVE_CALL")
            val gs = go(g, rest)
            go(l, Lst.Cons(h, gs))
        }
    }
    return go(this, Lst.Nil)
}

fun main() {
    val xs = Lst.fromList(listOf(1, 3, 2, 4))
    val sorted = xs.qsort(Comparator.naturalOrder())
    println("${xs.toList()} => ${sorted.toList()}")
}