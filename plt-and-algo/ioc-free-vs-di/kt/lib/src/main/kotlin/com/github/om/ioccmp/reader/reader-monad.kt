/*
 * This Kotlin source file was generated by the Gradle 'init' task.
 */
package com.github.om.ioccmp

@JvmInline
value class Reader<in A, out R> internal constructor(internal val f: (A) -> R)

class ReaderModule<A> {
    fun <R> run(m: Reader<A, R>, a: A): R = m.f(a)

    fun ret(r: A): Reader<A, A> = Reader { it }

    fun <R> reader(f: (A) -> R): Reader<A, R> = Reader(f)

    fun <R> join(m: Reader<A, Reader<A, R>>): Reader<A, R> {
        return Reader { a ->
            run(run(m, a), a)
        }
    }

    fun <B, C> bind(m: Reader<A, B>, f: (B) -> Reader<A, C>): Reader<A, C> {
        return Reader { a -> run(f(run(m, a)), a) }
    }

    fun <B, C> fmap(f: (B) -> C, m: Reader<A, B>): Reader<A, C> {
        return Reader { a -> f(run(m, a)) }
    }
}