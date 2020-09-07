package om.lang.pie

import org.junit.Test
import kotlin.random.Random
import kotlin.test.assertEquals

class SExprShould {
    private val r = Random(1234)

    @Test
    fun beParsedToExpr() {
        assertParsedToExpr("zero", PiExpr.Zero)
        assertParsedToExpr("1", PiExpr.NatLit(1))
        assertParsedToExpr("(add1 zero)", PiExpr.Succ(PiExpr.Zero))
        assertParsedToExpr("Nat", PiExpr.Nat)
        assertParsedToExpr("Set", PiExpr.Set)
    }

    @Test
    fun beParsedToTopLevel() {
        assertParsedToTopLevel("(define a zero)", Define("a", PiExpr.Zero))
        assertParsedToTopLevel("(claim a Nat)", Claim("a", PiExpr.Nat))
    }

    @Test
    fun haveIdentityRoundtripForSExpr() {
        repeat(10) {
            assertRoundtripSExpr(genSExpr(r, it))
        }
        repeat(10) {
            assertRoundtripSExprs(List(it) { genSExpr(r, 5) })
        }
    }

    @Test
    fun haveIdentityRoundtripForExpr() {
        repeat(10) {
            assertRoundtripExpr(genExpr(r, it))
        }
    }

    @Test
    fun haveIdentityRoundtripForTopLevel() {
        repeat(10) {
            assertRoundtripTopLevel(genTopLevel(r, it + 1))
        }
    }

    private fun assertRoundtripSExpr(source: String) {
        assertEquals(source, SExprParser.parseOne(source).ppr())
    }

    private fun assertRoundtripSExprs(sources: List<String>) {
        val source = sources.joinToString(" ")
        assertEquals(source, SExprParser.parseMany(source).joinToString(" ", transform = SExpr::ppr))
    }

    private fun assertParsedToExpr(source: String, expected: PiExpr) {
        val sexpr = SExprParser.parseOne(source)
        assertEquals(expected, SExprToProgram.expr(sexpr))
    }

    private fun assertRoundtripExpr(source: String) {
        val expr = SExprToProgram.expr(SExprParser.parseOne(source))
        assertEquals(source, expr.ppr())
    }

    private fun assertRoundtripTopLevel(source: String) {
        val p = SExprToProgram.topLevel(SExprParser.parseOne(source))
        assertEquals(source, p.ppr())
    }

    private fun assertParsedToTopLevel(source: String, expected: TopLevel) {
        val sexpr = SExprParser.parseOne(source)
        assertEquals(expected, SExprToProgram.topLevel(sexpr))
    }

    private fun genWithChoices(
        r: Random,
        fuel: Int,
        choices: List<Pair<Any, Int>>,
        defaultValue: String,
        subChoices: List<Pair<Any, Int>>? = null,
        subDefaultValue: String? = null
    ): String {
        if (fuel <= 0) {
            return defaultValue
        }

        val (gen, argc) = choices.random(r)
        return renderChoice(gen, argc) {
            genWithChoices(r, fuel - 1, subChoices ?: choices, subDefaultValue ?: defaultValue)
        }
    }

    private fun genTopLevel(r: Random, fuel: Int): String {
        return genWithChoices(r, fuel, listOf(
            { arg: String -> "(claim name $arg)" } to 1,
            { arg: String -> "(define name $arg)" } to 1,
        ), "", EXPR_CHOICES, "0")
    }

    private fun genExpr(r: Random, fuel: Int): String {
        return genWithChoices(r, fuel, EXPR_CHOICES, "0")
    }

    private fun genSExpr(r: Random, fuel: Int): String {
        return genWithChoices(r, fuel, listOf(
            "abc" to 0,
            "()" to 0,
            { arg: String -> "($arg)" } to 1,
            { arg1: String, arg2: String -> "($arg1 sep $arg2)" } to 2,
        ), "()")
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

private val EXPR_CHOICES = listOf(
    "0" to 0,
    "aVar" to 0,
    "Nat" to 0,
    { arg: String -> "(add1 $arg)" } to 1,
    { arg: String -> "(lam (x) $arg)" } to 1,
    { arg: String -> "(-> Nat $arg)" } to 1,
)

