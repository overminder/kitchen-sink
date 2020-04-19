package com.github.om.inctc

object Log {
    private val minimalLevel = Level.Error

    enum class Level { Debug, Error }
    private val levels = Level.values()

    private val Level.index: Int
        get() = levels.indexOf(this)

    fun enabled(level: Level): Boolean {
        return level.index >= minimalLevel.index
    }

    inline fun d(crossinline msg: () -> String) {
        if (!enabled(Level.Debug)) return

        println(msg())
    }

    inline fun e(crossinline msg: () -> String) {
        if (!enabled(Level.Error)) return

        println(msg())
    }
}