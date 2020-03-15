package yux.ktcpg

interface A {
    fun a()
}

interface AB: A {
    fun b()
}

// Can't write AB by a -- has to delegate on the exact type.
class ExtraB(a: A): A by a, AB {
    override fun b() {
    }
}

// Doesn't need to be in the constructor -- anything that's accessible from the ctor will do.
// The `this` is not yet an AB.
class ExtraB2(): A by a(), AB {
    companion object {
        fun a() = object: A {
            override fun a() {
            }
        }
    }
    override fun b() {
    }
}

fun everyA(xs: List<A>): A {
    return object: A {
        override fun a() {
            xs.forEach(A::a)
        }
    }
}

class AppendableA(val xs: MutableList<A>): A by everyA(xs) {
    fun addA(a: A) {
        xs.add(a)
    }
}

