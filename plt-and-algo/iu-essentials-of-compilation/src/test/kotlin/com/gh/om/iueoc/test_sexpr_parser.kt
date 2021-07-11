package com.gh.om.iueoc

import com.github.h0tk3y.betterParse.parser.Parser
import com.github.h0tk3y.betterParse.parser.parseToEnd
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class TestSexpr {
    @Test
    fun readAndPpr() {
        val cases = listOf(
            "abc",
            "123",
            "()",
            "(abc 123 . def)",
            "(abc 123)",
            "(abc def [123 456] {} ())",
            "`(,@abc 'def)",
        )
        cases.forEach(::assertReadAndPpr)
    }

    private fun assertReadAndPpr(input: String) {
        val sexpr = parseA(SexprGrammar.P.sexpr, input)
        val ppr = sexpr.unwrap.ppr()
        assertEquals(input, ppr)
    }

    private fun <A> parseA(p: Parser<A>, input: String): A {
        val toks = SexprGrammar.tokenizer.tokenize(input)
        return p.parseToEnd(toks)
    }
}