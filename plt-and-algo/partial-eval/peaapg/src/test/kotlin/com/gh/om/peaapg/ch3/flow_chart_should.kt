package com.gh.om.peaapg.ch3

import com.gh.om.peaapg.ch3.fc.Expr
import com.gh.om.peaapg.ch3.fc.Program
import com.gh.om.peaapg.ch3.fc.ProgramGrammar
import com.gh.om.peaapg.ch3.fc.Value
import com.gh.om.peaapg.ch3.fc.execute
import com.gh.om.peaapg.ch3.fc.ppr
import com.github.h0tk3y.betterParse.grammar.parseToEnd
import com.github.h0tk3y.betterParse.parser.parseToEnd
import org.junit.Test
import kotlin.test.assertEquals

class FlowChartShould {
    @Test
    fun parseExprRoundtrip() {
        val sources = listOf(
            "a + 1",
            // source to expected-ppr
            "a + 1 + 2" to "(a + 1) + 2",
            "a + 1 * b" to "a + (1 * b)",
            "a :: b :: c" to "a :: (b :: c)",
        )

        for (source in sources) {
            if (source is String) {
                assertEquals(source, parseExpr(source).ppr())
            } else {
                require(source is Pair<*, *>)
                val (s, ppr) = source
                assertEquals(ppr, parseExpr(s as String).ppr())
            }
        }
    }

    @Test
    fun parseProgramRoundtrip() {
        val program = parseProgram(PROGRAM_1)
        assertEquals(PROGRAM_1, program.ppr().trim())
    }

    @Test
    fun executeFiboProgram() {
        val fibo = parseProgram(PROGRAM_FIBO)
        val result = fibo.execute(listOf(Value.I(10)))
        assertEquals(Value.I(55), result)
    }

    @Test
    fun executeRangeProgram() {
        val p = parseProgram(PROGRAM_RANGE)
        val result = p.execute(listOf(Value.I(10)))
        assertEquals("[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]", result.ppr())
    }

    private fun parseProgram(source: String): Program {
        val g = ProgramGrammar()
        return g.parseToEnd(source)
    }

    private fun parseExpr(source: String): Expr {
        val g = ProgramGrammar()

        val tokens = g.tokenizer.tokenize(source)
        return g.expr.parseToEnd(tokens)
    }
}

private const val EXPR_1 = "(a + 1) * b"

private val PROGRAM_1 = """
read a, b;
foo:
    a = a + 1;
    b = 2 + b;
    goto bar;
bar:
    if a == 10 goto baz else foo;
baz:
    return b;
""".trimIndent()

private val PROGRAM_FIBO = """
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

private val PROGRAM_RANGE = """
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