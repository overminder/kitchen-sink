package com.gh.om.plt.incremental.afp

import java.util.Comparator

sealed class ModLst<out A> {
    object Nil : ModLst<Nothing>()
    data class Cons<out A>(
        val head: A,
        val tail: Mml<A>
    ) : ModLst<A>()

    companion object {
        fun <A, C> newElt(
            adaptive: AdaptiveModule<C>,
            x: ModLst<A>
        ): Mml<A> {
            return adaptive.modl { d -> adaptive.write(d, x) }
        }

        fun <A, C> fromList(
            adaptive: AdaptiveModule<C>,
            xs: List<A>
        ): Pair<Mml<A>, Mml<A>> {
            val m: Mml<A> = newElt(adaptive, Nil)
            return xs.foldRight(m to m) { h, (l, last) ->
                newElt(adaptive, Cons(h, l)) to last
            }
        }
    }
}

typealias Mml<A> = Mod<ModLst<A>>

fun <A> modLstEq(
    x: ModLst<A>,
    y: ModLst<A>
): Boolean {
    return x is ModLst.Nil && y is ModLst.Nil
}

fun <A, C> AdaptiveModule<C>.modl(f: (Dest<ModLst<A>>) -> C): Mml<A> {
    return mod(::modLstEq, f)
}


fun <A> Mml<A>.toList(adaptive: AdaptiveModule<*>): List<A> = foldl(adaptive, { acc, x ->
    acc += x
    acc
}, mutableListOf())

// XXX is this the correct way to "snapshot" the list?
fun <A, C, R> Mml<A>.foldl(adaptive: AdaptiveModule<C>, f: (R, A) -> R, initial: R): R {
    var acc = initial
    fun go(mxs: Mml<A>, dest: Dest<ModLst<A>>): C {
        return adaptive.read(mxs) { xs ->
            when (xs) {
                is ModLst.Cons -> {
                    // XXX is side effect okay? Probably not, given the memoization...
                    acc = f(acc, xs.head)
                    go(xs.tail, dest)
                }
                ModLst.Nil -> adaptive.write(dest, ModLst.Nil)
            }
        }
    }
    adaptive.modl { dest ->
        go(this, dest)
    }
    return acc
}

fun <A, C> Mml<A>.filter(
    adaptive: AdaptiveModule<C>,
    f: (A) -> Boolean
): Mml<A> {
    fun go(
        mxs: Mml<A>,
        dest: Dest<ModLst<A>>
    ): C {
        return adaptive.read(mxs) { xs ->
            when (xs) {
                ModLst.Nil -> adaptive.write(dest, ModLst.Nil)
                is ModLst.Cons -> {
                    if (f(xs.head)) {
                        adaptive.write(
                            dest,
                            ModLst.Cons(xs.head, adaptive.modl { tailDest ->
                                go(xs.tail, tailDest)
                            })
                        )
                    } else {
                        go(xs.tail, dest)
                    }
                }
            }
        }
    }
    return adaptive.modl { dest -> go(this, dest) }
}

fun <A, C> Mml<A>.qsort(
    adaptive: AdaptiveModule<C>,
    cmp: Comparator<A>
): Mml<A> {
    fun go(
        mxs: Mml<A>,
        rest: ModLst<A>,
        dest: Dest<ModLst<A>>
    ): C {
        return adaptive.read(mxs) { xs ->
            when (xs) {
                ModLst.Nil -> adaptive.write(dest, ModLst.Nil)
                is ModLst.Cons -> {
                    val h = xs.head
                    val t = xs.tail
                    val l = t.filter(adaptive) { cmp.compare(it, h) < 0 }
                    val g = t.filter(adaptive) { cmp.compare(it, h) >= 0 }

                    val gs = adaptive.modl { dRest -> go(g, rest, dRest) }
                    // Unfortunately this is not tail...
                    go(l, ModLst.Cons(h, gs), dest)
                }
            }
        }
    }
    return adaptive.modl { dest -> go(this, ModLst.Nil, dest) }
}

fun <C> test(adaptive: AdaptiveModule<C>): Mml<Int> {
    adaptive.init()
    val (l, last) = ModLst.fromList(adaptive, listOf(1, 3, 2))
    println("Unsorted: ${l.toList(adaptive)}")
    val r = l.qsort(adaptive, Comparator.naturalOrder())
    println("Sorted: ${l.toList(adaptive)}")
    adaptive.change(last, ModLst.Cons(0, ModLst.newElt(adaptive, ModLst.Nil)))
    adaptive.propagate()
    println("Changed: ${l.toList(adaptive)}")
    return r
}

fun main() {
    test(AdaptiveModuleImpl(NaiveOrderedList()))
}
