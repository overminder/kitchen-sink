package com.gh.om.pl.cwai

import org.assertj.core.api.Assertions.assertThat
import org.assertj.core.api.Assertions.assertThatThrownBy
import org.junit.jupiter.api.Test

class InterpTest {
    private fun parseExp(src: String): Exp =
        Exp.fromSExp(SExp.parse(src))

    private fun evalSrc(
        src: String,
        env: IEnv = emptyMap(),
    ): IValue =
        eval(
            parseExp(src),
            env,
        )

    @Test
    fun testAddSubLt() {
        val v1 = evalSrc("(+# 1 2)") as IValue.IVInt
        assertThat(v1.value).isEqualTo(3)
        val v2 = evalSrc("(+# (-# 5 2) 4)") as IValue.IVInt
        assertThat(v2.value).isEqualTo(7)
        val b1 = evalSrc("(<# 1 2)") as IValue.IVBool
        assertThat(b1.value).isTrue()
        val b2 = evalSrc("(<# 2 1)") as IValue.IVBool
        assertThat(b2.value).isFalse()
    }

    @Test
    fun testLetrecRecursiveSum() {
        // Define a recursive function f(n) = if n < 1 then 0 else n + f(n-1)
        val v = evalSrc(
            """
            (letrec
              ([f (lambda (n)
                     (if (<# n 1)
                         0
                         (+# n (f (-# n 1)))) )])
              (f 5))
            """.trimIndent(),
        ) as IValue.IVInt
        // 5+4+3+2+1 = 15
        assertThat(v.value).isEqualTo(15)
    }

    @Test
    fun testFibo() {
        val v = evalSrc(
            """
            (letrec
              ([fibo (lambda (n)
                       (if (<# n 2)
                           n
                           (+# (fibo (-# n 1)) (fibo (-# n 2)))))])
              (fibo 10))
            """.trimIndent(),
        ) as IValue.IVInt
        assertThat(v.value).isEqualTo(55)
    }

    @Test
    fun testIfTrueFalse() {
        val t = evalSrc("(if (<# 1 2) 10 20)") as IValue.IVInt
        assertThat(t.value).isEqualTo(10)
        val f = evalSrc("(if (<# 3 2) 10 20)") as IValue.IVInt
        assertThat(f.value).isEqualTo(20)
    }

    @Test
    fun testLetBasic() {
        val v = evalSrc(
            """
            (let
              ([x 1]
               [y 2])
              (+# x y))
        """.trimIndent(),
        ) as IValue.IVInt
        assertThat(v.value).isEqualTo(3)

        val v2 = evalSrc("(let ([x 1]) (let ([x 2]) x))") as IValue.IVInt
        assertThat(v2.value).isEqualTo(2)
    }

    @Test
    fun testLambdaApplication() {
        // Using external env binding
        val v = evalSrc(
            "((lambda (x) (+# x y)) 3)",
            env = mapOf("y" to IValue.IVInt(4)),
        ) as IValue.IVInt
        assertThat(v.value).isEqualTo(7)

        // Without env capture
        val v2 = evalSrc("((lambda (x) (+# x 4)) 3)") as IValue.IVInt
        assertThat(v2.value).isEqualTo(7)
    }

    @Test
    fun testClosureCapturesOuterEnvAgainstShadowing() {
        val v = evalSrc(
            """
            (let ([y 1])
              (let ([f (lambda (x) (+# x y))]
                    [y 100])
                (f 1)))
            """.trimIndent(),
        ) as IValue.IVInt
        assertThat(v.value).isEqualTo(2) // f captures y=1, not inner y=100
    }

    @Test
    fun testErrors() {
        // Unbound variable
        assertThatThrownBy { evalSrc("x") }
            .isInstanceOf(IllegalArgumentException::class.java)
            .hasMessageContaining("unbound")
        // Call non-function
        assertThatThrownBy { evalSrc("(1 2)") }
            .isInstanceOf(IllegalArgumentException::class.java)
            .hasMessageContaining("non-function")
        // Arity mismatch
        assertThatThrownBy { evalSrc("((lambda (x y) x) 1)") }
            .isInstanceOf(IllegalArgumentException::class.java)
            .hasMessageContaining("arity mismatch")
        // If condition not boolean
        assertThatThrownBy { evalSrc("(if 1 2 3)") }
            .isInstanceOf(IllegalArgumentException::class.java)
            .hasMessageContaining("expected boolean")
    }
}
