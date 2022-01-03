package com.github.om.ioccmp.free

// Free, but substitute join for bind
object Draft1 {
    sealed class FOp<out A> {
        data class Pure<A>(val a: A) : FOp<A>()

        // A is existential. Free uses join which hides the existential.
        data class Bind<A, B>(val m: FOp<A>, val f: (A) -> FOp<B>) : FOp<B>()

        // Op
        object Get : FOp<Int>()
        data class Incr(val by: Int = 1) : FOp<Unit>()
    }

    fun incrAndGet(by: Int): FOp<Int> {
        return FOp.Bind(FOp.Incr(by)) {
            FOp.Get
        }
    }

    fun <A> twice(op: FOp<A>): FOp<Pair<A, A>> {
        return FOp.Bind(op) { fst ->
            FOp.Bind(op) { snd ->
                FOp.Pure(fst to snd)
            }
        }
    }

    class State {
        var value: Int = 0
    }

    tailrec fun <R> interp(m: FOp<R>, state: State): R {
        return when (m) {
            is FOp.Bind<*, *> -> {
                @Suppress("NON_TAIL_RECURSIVE_CALL")
                val ma = interp(m.m, state)

                @Suppress("UNCHECKED_CAST")
                val f = m.f as (Any?) -> FOp<R>
                interp(f(ma), state)
            }
            FOp.Get -> {
                // No GADT
                @Suppress("UNCHECKED_CAST")
                state.value as R
            }
            is FOp.Incr -> {
                // No GADT
                state.value += m.by
                @Suppress("UNCHECKED_CAST")
                Unit as R
            }
            is FOp.Pure -> {
                m.a
            }
        }
    }

    fun main() {
        val out = interp(twice(incrAndGet(2)), State())
        assert(out == 2 to 4)
    }
}

// Ordinary Free
object Draft2 {
    // Due to not having HKT, the Free Monad and the DSL are tightly coupled.
    sealed class F<out A> {
        data class Pure<A>(val a: A) : F<A>()
        data class Join<A>(val m: Op<F<A>>) : F<A>()

        fun <B> fmap(f: (A) -> B): F<B> = when (this) {
            is Pure -> Pure(f(a))
            is Join -> Join(m.fmap { it.fmap(f) })
        }

        fun <B> bind(f: (A) -> F<B>): F<B> = when (this) {
            is Pure -> f(a)
            is Join -> Join(m.fmap { it.bind(f) })
        }

        companion object {
            fun <A> liftF(op: Op<A>): F<A> = Join(op.fmap(::Pure))
        }
    }

    sealed class Op<out A> {
        data class Get<out A>(val k: (Int) -> A) : Op<A>()
        data class Incr<out A>(val k: (Unit) -> A) : Op<A>()

        fun <B> fmap(f: (A) -> B): Op<B> = when (this) {
            is Get -> Get { f(k(it)) }
            is Incr -> Incr { f(k(it)) }
            // ^ Good: f is lazily composed with k
        }

        companion object {
            val get: F<Int> = F.liftF(Get { it })
            val incr: F<Unit> = F.liftF(Incr { it })
        }
    }

    fun incrAndGet(by: Int): F<Int> {
        return Op.incr.bind {
            Op.get
        }
    }

    fun <A> twice(op: F<A>): F<Pair<A, A>> {
        return op.bind { fst ->
            op.bind { snd ->
                F.Pure(fst to snd)
            }
        }
    }

    class State {
        var value: Int = 0
    }

    tailrec fun <R> interp(m: F<R>, state: State): R {
        return when (m) {
            is F.Pure -> m.a
            is F.Join -> when (val op = m.m) {
                is Op.Get -> {
                    val v = op.k(state.value)
                    interp(v, state)
                }
                is Op.Incr -> {
                    state.value += 1
                    interp(op.k(Unit), state)
                }
            }
        }
    }

    fun main() {
        val out = interp(twice(incrAndGet(2)), State())
        assert(out == 2 to 4)
    }
}

// Ordinary Free, but with the binding structure (k) factored out.
object Draft3 {
    sealed class F<out A> {
        data class Pure<A>(val a: A) : F<A>()
        data class Join<A>(val m: Bind<F<A>, *>) : F<A>()

        fun <B> fmap(f: (A) -> B): F<B> = when (this) {
            is Pure -> Pure(f(a))
            is Join -> Join(m.fmap { it.fmap(f) })
        }

        fun <B> bind(f: (A) -> F<B>): F<B> = when (this) {
            is Pure -> f(a)
            is Join -> Join(m.fmap { it.bind(f) })
        }

        companion object {
            fun <A> liftF(op: Op<A>): F<A> = Join(Bind(op) { it }.fmap(::Pure))
        }
    }

    data class Bind<out A, B>(val op: Op<B>, val k: (B) -> A) {
        fun <C> fmap(f: (A) -> C): Bind<C, B> = Bind(op) { f(k(it)) }
    }

    sealed class Op<out A> {
        object Get: Op<Int>()
        object Incr: Op<Unit>()

        companion object {
            val get = F.liftF(Get)
            val incr = F.liftF(Incr)
        }
    }

    fun incrAndGet(by: Int): F<Int> {
        return Op.incr.bind {
            Op.get
        }
    }

    fun <A> twice(op: F<A>): F<Pair<A, A>> {
        return op.bind { fst ->
            op.bind { snd ->
                F.Pure(fst to snd)
            }
        }
    }

    class State {
        var value: Int = 0
    }

    tailrec fun <R> interpF(m: F<R>, state: State): R {
        return when (m) {
            is F.Pure -> m.a
            is F.Join -> interpF(interpB(m.m, state), state)
        }
    }

    // The existentials don't have to casted, since B is encoded in Bind's fields
    fun <A, B> interpB(m: Bind<A, B>, state: State): A {
        return m.k(interpO(m.op, state))
    }

    // No GADT smart cast, unfortunately.
    @Suppress("UNCHECKED_CAST")
    fun <A> interpO(op: Op<A>, state: State): A {
        return when (op) {
            is Op.Get -> {
                state.value
            }
            is Op.Incr -> {
                state.value += 1
                Unit
            }
        } as A
    }

    fun main() {
        val out = interpF(twice(incrAndGet(2)), State())
        assert(out == 2 to 4)
    }
}

fun main() {
    Draft3.main()
}