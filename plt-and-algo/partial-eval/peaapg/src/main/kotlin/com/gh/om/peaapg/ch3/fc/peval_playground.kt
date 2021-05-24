package com.gh.om.peaapg.ch3.fc

import com.github.h0tk3y.betterParse.grammar.parseToEnd

fun main() {
    // showPeval(Sources.range, listOf("n"), mapOf("n" to Value.I(10)))
    // -> If only n is specialized: it's loop unrolling but the list still needs to be constructed at runtime
    // -> If both n and r are specialized: the only residual code is to return the fully built value

    // showPeval(Sources.fibo, listOf("a", "b", "t"), mapOf("n" to Value.I(10)), 20)
    // -> If n is specialized: it's also loop unrolling
    // -> If a b t are specialized: it's calculating the blocks indefinitely (and generating the wrong code, as
    // the mutating `n` is never stored to the map.
}

fun showPeval(source: String, staticVars: List<String>, args: Map<String, Value>, maxSteps: Int? = null) {
    val g = ProgramGrammar()
    val program = g.parseToEnd(source)

    val result = mix(program, object: Division() {
        override fun isStatic(v: String) = v in staticVars
    }, args, maxSteps)
    println(result.ppr())
}

object Sources {
    val fibo = """
read n;
start:
    a = 0;
    b = 1;
    goto loopStart;
loopStart:
    if n == 0 goto end else loop;
loop:
    t = b;
    b = a + b;
    a = t;
    n = n - 1;
    goto loopStart;
end:
    return a;
""".trimIndent()

    val range = """
read n;
start:
    r = [];
    goto loop;
loop:
    n = n - 1;
    r = n :: r;
    goto check;
check:
    if n == 0 goto end else loop;
end:
    return r;
""".trimIndent()
}