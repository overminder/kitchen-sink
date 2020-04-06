package com.github.om.inctc.bench

class Timer {
    private val callStack = mutableListOf<String>()
    private val records = mutableMapOf<List<String>, MutableList<Pair<Long, Long>>>()

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
        return r
    }

    fun printStat() {
        for (r in records) {
            val tag = r.key.joinToString(".")
            val totalTime = r.value.sumBy { (it.second - it.first).toInt() }
            println("$tag: $totalTime millis")
        }
    }

    companion object {
        val DEFAULT = Timer()
    }
}

