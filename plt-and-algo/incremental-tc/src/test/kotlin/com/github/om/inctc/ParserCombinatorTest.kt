package com.github.om.inctc

import com.github.om.inctc.lang.poly.*
import com.github.om.inctc.parse.Parser
import com.github.om.inctc.parse.ParserCombinators0
import org.junit.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull
import kotlin.test.assertTrue

class ParserCombinatorTest {
    val p = ParserCombinators0

    @Test
    fun testSimpleCombinators() {
        assertParses(p.char('a'), "aa", 'a')
        assertParses(p.string("asdf"), "asdf", "asdf")
        assertParses(p.string("asdf"), "asdfx", "asdf")

        assertParses(p.many(p.char('c')), "ccccx", "cccc".toList())
        assertParses(p.many(p.char('c')), "x", emptyList())
        assertParses(p.many1(p.char('c')), "ccccx", "cccc".toList())
        assertParsesNothing(p.many1(p.char('c')), "x")

        assertParses(p.eof(), "", Unit)
        assertParsesNothing(p.eof(), "123")
        assertParses(p.pure(42), "", 42)

        assertParsesNothing(p.char('c').ignoreRight(p.peekIf { it != 'c' }), "cc")
    }

    @Test
    fun testPolyLangParser() {
        val p = PolyLangParser
        val p0 = ParserCombinators0
        assertTrue {
            p.keywords.containsAll(listOf("fun", "end", "in"))
        }
        assertParsesNothing(p.name, "fun")

        assertParses(p.exp, "x", Var(Ident("x")), wholely = true)
        assertParses(p.exp, "fun x in x end",
                Lam(listOf(Ident("x")), Var(Ident("x"))),
                wholely = true)
        assertParses(p.exp, "fun x in 5 end",
                Lam(listOf(Ident("x")), LitI(5)),
                wholely = true)
        assertParses(p.exp, "fun x in if 5 then 1 else 2 end end",
                Lam(listOf(Ident("x")), If(LitI(5), LitI(1), LitI(2))),
                wholely = true)
        assertParses(p.exp, "x(y, z)",
                App(App(Var(Ident("x")), Var(Ident("y"))),
                        Var(Ident("z"))),
                wholely = true)

        assertParses(p.exp, "x(y)(z)",
                App(App(Var(Ident("x")), Var(Ident("y"))),
                        Var(Ident("z"))),
                wholely = true)

        assertParses(p.exp, "x(y) < (z)",
                BOp(BRator.LT,
                        App(Var(Ident("x")), Var(Ident("y"))),
                        Var(Ident("z"))),
                wholely = true)

        assertParses(p.decl, "use foo.bar",
                Import(ModuleName("foo"), Ident("bar")),
                wholely = true)

        assertParses(p.decl, "pub def foo = 5",
                Define(Ident("foo"), Visibility.Public, LitI(5)),
                wholely = true)

        assertParses(p.decl, "def foo = 5",
                Define(Ident("foo"), Visibility.Internal, LitI(5)),
                wholely = true)
    }

    private fun <A> assertParses(pa: Parser<A>, source: String, expected: A, wholely: Boolean = false) {
        val res = if (wholely) { pa.ignoreRight(p.eof()) } else { pa }.run(source)
        assertEquals(expected, res)
    }

    private fun <A> assertParsesNothing(p: Parser<A>, source: String) {
        val res = p.run(source)
        assertNull(res)
    }
}