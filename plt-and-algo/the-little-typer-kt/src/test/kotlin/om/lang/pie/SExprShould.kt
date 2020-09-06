package om.lang.pie

import org.junit.Test
import kotlin.random.Random
import kotlin.test.assertEquals

class SExprShould {
    private val r = Random(1234)

    @Test
    fun beParsedToExpr() {
        assertParsedToExpr("0", Zero)
        assertParsedToExpr("1", Succ(Zero))
        assertParsedToExpr("(add1 0)", Succ(Zero))
        assertParsedToExpr("Nat", Nat)
        assertParsedToExpr("Set", Set)
    }

    @Test
    fun beParsedToTopLevel() {
        assertParsedToTopLevel("(define a 0)", Define("a", Zero))
        assertParsedToTopLevel("(claim a Nat)", Claim("a", Nat))
    }

    @Test
    fun haveIdentityRoundtrip() {
        repeat(10) {
            assertRoundtripExpr(genExpr(r, it))
        }
        repeat(10) {
            assertRoundtripExprs(List(it) { genExpr(r, 5) })
        }
    }

    private fun assertRoundtripExpr(source: String) {
        assertEquals(source, SExprParser.parseOne(source).ppr())
    }

    private fun assertRoundtripExprs(sources: List<String>) {
        val source = sources.joinToString(" ")
        assertEquals(source, SExprParser.parseMany(source).joinToString(" ", transform = SExpr::ppr))
    }

    private fun assertParsedToExpr(source: String, expected: Expr) {
        val sexpr = SExprParser.parseOne(source)
        assertEquals(expected, SExprToProgram.expr(sexpr))
    }

    private fun assertParsedToTopLevel(source: String, expected: TopLevel) {
        val sexpr = SExprParser.parseOne(source)
        assertEquals(expected, SExprToProgram.topLevel(sexpr))
    }

    private fun genTopLevel(r: Random, fuel: Int): String {
        if (fuel <= 0) {
            return ""
        }

        val choices = listOf(
            { arg: String -> "(claim name $arg)" } to 1,
            { arg: String -> "(define name $arg)" } to 1
        )
        val (gen, argc) = choices.random(r)
        return renderChoice(gen, argc) {
            genExpr(r, fuel - 1)
        }
    }

    private fun genExpr(r: Random, fuel: Int): String {
        if (fuel <= 0) {
            return "()"
        }

        val choices = listOf(
            "abc" to 0,
            "()" to 0,
            { arg: String -> "($arg)" } to 1,
            { arg1: String, arg2: String -> "($arg1 sep $arg2)" } to 2
        )
        val (gen, argc) = choices.random(r)
        return renderChoice(gen, argc) {
            genExpr(r, fuel - 1)
        }
    }

    private fun renderChoice(stringOrFun: Any, argc: Int, gen: () -> String): String {
        return when (argc) {
            0 -> stringOrFun as String
            1 -> {
                val f1 = stringOrFun as (String) -> String
                f1(gen())
            }
            2 -> {
                val f2 = stringOrFun as (String, String) -> String
                f2(gen(), gen())
            }
            else -> error("Unreachable")
        }
    }
}