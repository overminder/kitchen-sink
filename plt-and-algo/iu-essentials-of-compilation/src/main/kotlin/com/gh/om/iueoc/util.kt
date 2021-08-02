package com.gh.om.iueoc

sealed class Trampoline<out A> {
    class MoreToGo<A>(val call: () -> Trampoline<A>) : Trampoline<A>()
    class Done<A>(val result: A) : Trampoline<A>()
}

tailrec fun <A> Trampoline<A>.value(): A = when (this) {
    is Trampoline.Done -> result
    is Trampoline.MoreToGo -> call().value()
}

object Tr {
    fun <A> pure(a: A) = Trampoline.Done(a)
    fun <A> more(a: () -> Trampoline<A>) = Trampoline.MoreToGo(a)
    fun <A> once(a: () -> A) = Trampoline.MoreToGo { pure(a()) }
}

fun <A> Collection<A>.indexOfSafe(a: A): Int? {
    val ix = indexOf(a)
    return ix.takeUnless { it == -1 }
}