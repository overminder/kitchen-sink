package com.gh.om.pl.cwai

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test

class ExpFromSExpTest {
    private fun parse(src: String): Exp =
        Exp.fromSExp(SExp.parse(src))

    @Test
    fun testIntAndSym() {
        val ei = parse("-123") as Exp.EInt
        assertEquals(
            -123,
            ei.value
        )
        val es = parse("foo") as Exp.ESym
        assertEquals(
            "foo",
            es.name
        )
    }

    @Test
    fun testLetrecParses() {
        val e = parse(
            """
            (letrec
              ([f (lambda (n) (if (<# n 1) 0 (+# n (f (-# n 1)))))])
              (f 3))
            """.trimIndent()
        ) as Exp.ELet
        assertEquals(true, e.isRec)
        assertEquals(listOf("f"), e.bindings.map { it.first })
        val body = e.body as Exp.EApp
        val callee = body.callee as Exp.ESym
        assertEquals("f", callee.name)
    }

    @Test
    fun testPrimAddAndSub() {
        val add = parse("(+# 1 2)") as Exp.EPrimOp
        assertEquals(
            PrimOp.INT_ADD,
            add.op
        )
        assertEquals(
            2,
            add.args.size
        )
        val sub = parse("(-# 3 1)") as Exp.EPrimOp
        assertEquals(
            PrimOp.INT_SUB,
            sub.op
        )
        assertEquals(
            listOf(
                3,
                1
            ),
            sub.args.map { (it as Exp.EInt).value })
    }

    @Test
    fun testPrimLt() {
        val lt = parse("(<# 1 2)") as Exp.EPrimOp
        assertEquals(PrimOp.INT_LT, lt.op)
        assertEquals(listOf(1, 2), lt.args.map { (it as Exp.EInt).value })
    }

    @Test
    fun testPrimWrongArity() {
        val ex = assertThrows(IllegalArgumentException::class.java) {
            parse("(+# 1)")
        }
        assertTrue(ex.message!!.contains("expects 2 args"))
    }

    @Test
    fun testPrimLtWrongArity() {
        val ex = assertThrows(IllegalArgumentException::class.java) {
            parse("(<# 1 2 3)")
        }
        assertTrue(ex.message!!.contains("expects 2 args"))
    }

    @Test
    fun testLetDesugars() {
        val e = parse(
            """
            (let
              ([x 1]
               [y 2])
              (+# x y))
        """.trimIndent()
        )
        e as Exp.ELet
        // Check names and values without asserting exact SourceLocs
        assertEquals(
            listOf(
                "x",
                "y"
            ),
            e.bindings.map { it.first })
        assertEquals(
            listOf(
                1,
                2
            ),
            e.bindings.map { (it.second as Exp.EInt).value })
        val body = e.body as Exp.EPrimOp
        assertEquals(
            PrimOp.INT_ADD,
            body.op
        )
        // Arguments should be symbols x and y
        assertEquals(
            listOf(
                "x",
                "y"
            ),
            body.args.map { (it as Exp.ESym).name })
    }

    @Test
    fun testLambda() {
        val e = parse("(lambda (x y) (+# x y))") as Exp.EAbs
        assertEquals(
            listOf(
                "x",
                "y"
            ),
            e.args
        )
        val body = e.body as Exp.EPrimOp
        assertEquals(
            PrimOp.INT_ADD,
            body.op
        )
    }

    @Test
    fun testBoolLiterals() {
        val t = parse("#t") as Exp.EBool
        assertTrue(t.value)
        val f = parse("#f") as Exp.EBool
        assertFalse(f.value)
    }

    @Test
    fun testIfExpression() {
        val e = parse("(if (<# 1 2) 1 0)") as Exp.EIf
        val cond = e.condition as Exp.EPrimOp
        assertEquals(PrimOp.INT_LT, cond.op)
        assertEquals(listOf(1, 2), cond.args.map { (it as Exp.EInt).value })
        assertEquals(1, (e.trueBranch as Exp.EInt).value)
        assertEquals(0, (e.falseBranch as Exp.EInt).value)
    }

    @Test
    fun testIfWrongArity() {
        assertThrows(IllegalArgumentException::class.java) { parse("(if 1 2)") }
        assertThrows(IllegalArgumentException::class.java) { parse("(if 1 2 3 4)") }
    }

    @Test
    fun testApplication() {
        val e = parse("(f 1 2)") as Exp.EApp
        val callee = e.callee as Exp.ESym
        assertEquals(
            "f",
            callee.name
        )
        assertEquals(
            listOf(
                1,
                2
            ),
            e.args.map { (it as Exp.EInt).value })
    }

    @Test
    fun testEmptyListError() {
        val ex = assertThrows(IllegalArgumentException::class.java) {
            parse("()")
        }
        assertTrue(ex.message!!.contains("empty list"))
    }

    @Test
    fun testLetShapeErrors() {
        assertThrows(IllegalArgumentException::class.java) { parse("(let x 1)") }
        assertThrows(IllegalArgumentException::class.java) { parse("(let ([x]) 1)") }
        assertThrows(IllegalArgumentException::class.java) { parse("(let ([1 2]) 3)") }
    }

    @Test
    fun testLambdaParamNotSymbol() {
        val ex = assertThrows(IllegalArgumentException::class.java) { parse("(lambda (1) 2)") }
        assertTrue(ex.message!!.contains("parameters must be symbols"))
    }
}
