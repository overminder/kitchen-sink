package com.github.om.inctc.bench

class Timer {
    private val callStack = mutableListOf<String>()
    private val records = mutableMapOf<List<String>, MutableList<Pair<Long, Long>>>()
    var printImmediately = false

    fun <A> timed(name: String, run: () -> A): A {
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

    fun printStat() {
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

    companion object {
        val DEFAULT = Timer()
    }
}

