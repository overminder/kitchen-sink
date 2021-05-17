package com.gh.om.peaapg.ch3

import org.junit.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith

class RecursiveEquationsShould {
    @Test
    fun parseExprs() {
        assertEquals(Expr.I(42), Expr.parseToEnd("42"))
        assertEquals(Expr.Var("x"), Expr.parseToEnd("x"))
        assertEquals(Expr.Add(Expr.Var("x"), Expr.Var("y")), Expr.parseToEnd("x + y"))
        assertEquals(Expr.App(Expr.Var("x"), Expr.Var("y")), Expr.parseToEnd("x(y)"))
        assertEquals(Expr.App(Expr.App(Expr.Var("x"), Expr.Var("y")), Expr.Var("z")), Expr.parseToEnd("x(y, z)"))
        assertEquals(Expr.App(Expr.App(Expr.Var("x"), Expr.Var("y")), Expr.Var("z")), Expr.parseToEnd("x(y)(z)"))
        assertEquals(Expr.Lam("x", Expr.Var("x")), Expr.parseToEnd("\\x -> x"))
        assertEquals(
            Expr.Lam("x", Expr.Lam("y", Expr.Add(Expr.Var("x"), Expr.Var("y")))),
            Expr.parseToEnd("\\x y -> x + y")
        )
    }

    @Test
    fun runCbvExamples() {
        fun evalsTo(src: String, value: Cbv.Value) {
            val p = Program.parseToEnd(src)
            assertEquals(value, Cbv.run(p.defns, p.body))
        }

        fun failsToEval(src: String, checkError: (Cbv.Stuck) -> Unit) {
            val p = Program.parseToEnd(src)
            val ex = assertFailsWith(Cbv.Stuck::class) {
                Cbv.run(p.defns, p.body)
            }
            checkError(ex)
        }

        evalsTo("40 + 2", Cbv.Value.I(42))
        evalsTo("(\\x -> x + 1)(1)", Cbv.Value.I(2))
        evalsTo("(\\x -> x + x)(1)", Cbv.Value.I(2))
        evalsTo("add1 x = x + 1; add1(41)", Cbv.Value.I(42))
        evalsTo("s f g x = f(x, g(x)); k x y = x; i = s(k, k); i(42)", Cbv.Value.I(42))
        failsToEval("bot") { it is Cbv.Stuck.Bottom }
        failsToEval("k x y = x; k(42, bot)") { it is Cbv.Stuck.Bottom }
    }
}