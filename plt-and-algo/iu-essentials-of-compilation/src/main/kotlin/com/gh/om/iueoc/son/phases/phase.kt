package com.gh.om.iueoc.son.phases

import com.gh.om.iueoc.son.MutGraphRef

interface Phase {
    // Returns true if [g] was changed.
    fun run(g: MutGraphRef): Boolean
}

class RepPhase(private val n: Int, private val phase: Phase) : Phase {
    init {
        require(n >= 1)
    }

    override fun run(g: MutGraphRef): Boolean {
        var changed = false
        repeat(n) {
            val changedThisTime = phase.run(g)
            if (!changedThisTime) {
                return@repeat
            }
            changed = true
        }
        return changed
    }
}

object Phases {
    val SIMPLE = listOf(
        InlinePhase.rep(6),
        ConstantPropagationPhase.rep(1),
        // ConstantPropagationPhase,
        // ConstantPropagationPhase,
        TrimPhase,
    )

    val SIMPLE_REP = SIMPLE.rep(2)
}

private fun Phase.rep(n: Int): Phase {
    return if (n == 1) {
        this
    } else {
        RepPhase(n, this)
    }
}

private fun <A> List<A>.rep(n: Int): List<A> {
    return (0..n).flatMap { this }
}