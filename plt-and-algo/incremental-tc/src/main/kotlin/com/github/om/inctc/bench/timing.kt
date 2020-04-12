package com.github.om.inctc.bench

interface Timer {
    fun <A> timed(name: String, run: () -> A): A
    fun scoped(name: String): Timer
    fun printStat()
    var printImmediately: Boolean

    companion object {
        val DEFAULT = create()
        fun create(): Timer = TimerImpl(mutableListOf(), mutableMapOf())
    }
}

fun <A> Timer.timedLazy(name: String, run: () -> A): Lazy<A> = lazy {
    timed(name, run)
}

class TimerImpl internal constructor(
    private val callStack: MutableList<String>,
    private val records: MutableMap<List<String>, MutableList<Pair<Long, Long>>>
): Timer {

    override var printImmediately = false

    override fun <A> timed(name: String, run: () -> A): A {
        callStack.add(name)
        val tag = callStack.toList()
        val start = System.currentTimeMillis()
        val r = run()
        val end = System.currentTimeMillis()
        records.compute(tag) { k, v ->
            (v ?: mutableListOf()).apply {
                add(start to end)
            }
        }
        callStack.removeAt(callStack.size - 1)
        if (printImmediately) {
            printStatFor(tag)
        }
        return r
    }

    override fun scoped(name: String): Timer {
        val cs = callStack.toMutableList()
        cs += name
        return TimerImpl(cs, records)
    }

    override fun printStat() {
        for (r in records.keys) {
            printStatFor(r)
        }
    }

    private fun printStatFor(rawTag: List<String>) {
        val tag = rawTag.joinToString(".")
        val value = requireNotNull(records[rawTag])
        val totalTime = value.sumBy { (it.second - it.first).toInt() }
        println("$tag: $totalTime millis")
    }
}

