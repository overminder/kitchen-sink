package com.gh.om.plt.incremental.afp

// Unfortunately there's no hkt in Kotlin. We'll have to make mod and dest separate interfaces that
// are not tied to Adaptive instead.
interface AdaptiveModule<C> {
    fun <A> mod(
        /**
         * Returns true if the arguments are the same value.
         */
        cmp: (A, A) -> Boolean,
        f: (Dest<A>) -> C
    ): Mod<A>

    fun <A> read(
        mod: Mod<A>,
        f: (A) -> C
    ): C

    fun <A> write(
        dest: Dest<A>,
        value: A
    ): C

    fun init()
    fun <A> change(
        mod: Mod<A>,
        value: A
    )

    fun propagate()
}

interface Mod<out A>

interface Dest<A>
