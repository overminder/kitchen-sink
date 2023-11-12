package com.gh.om.g.observer.frp

// Basic continuous stream.

interface Behavior<out A> {
    val value: A

    /**
     * @return To stop observation
     */
    fun observe(f: (A) -> Unit): AutoCloseable
}

class MutableBehavior<A>(initialValue: A) : Behavior<A> {
    private val reentryGuard = ReentryGuard(this.javaClass.simpleName)
    private var _value = initialValue
    override var value
        get() = _value
        set(newValue) {
            reentryGuard {
                _value = newValue
                observers.forEach {
                    it(newValue)
                }
            }
        }

    private val observers = mutableSetOf<(A) -> Unit>()

    override fun observe(f: (A) -> Unit): AutoCloseable {
        reentryGuard {
            f(value)
        }
        observers += f
        return AutoCloseable {
            reentryGuard {
                observers -= f
            }
        }
    }
}

class ReentryGuard(private val name: String? = null) {
    // To make sure this is not entered multiple times
    private var entered = false
    operator fun <A> invoke(block: () -> A): A {
        require(!entered) {
            "Reentry (name = $name)"
        }
        entered = true
        val res = block()
        entered = false
        return res
    }
}
