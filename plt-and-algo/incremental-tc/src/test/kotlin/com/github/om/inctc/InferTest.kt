package com.github.om.inctc

import com.github.om.inctc.lang.poly.*
import org.junit.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class InferTest {
    @Test
    fun testGatherDeps() {
        val fibo = """
            pub def fibo = fun n in
              if n < 2
                then n
                else fibo(n - 1) + fibo(n - 2)
              end
            end
        """.trimIndent()
        val fiboMain = """
            use fibo.fibo 
            
            pub def main = fibo(10)
        """.trimIndent()

        val modules = parseFiles(listOf(
                "fibo" to fibo,
                "main" to fiboMain
        ))
        val rCtx = ResolutionContext(modules)

        assertEquals(mapOf(
                FqName.parse("fibo.fibo") to setOf(FqName.parse("fibo.fibo"), FqName.parse("main.fibo")),
                FqName.parse("main.main") to setOf(FqName.parse("main.fibo"))
        ), defUseToMap(rCtx))

        assertNull(rCtx.findUndefinedUses().firstOrNull())
    }

    @Test
    fun testInfer1() {
        checkInfer(listOf(
            "main" to """
                def a = 5
                def b = fun x in x + a end
                def c = let
                  id = fun x in x end
                in id(5) < 8 end
                def d = e
                def e = if 1 < 2 then d else 1 end
            """.trimIndent()
        ), listOf(
            "main.a" to TyInt,
            "main.b" to TyArr(TyInt, TyInt)
        ))
    }

    @Test
    fun testInferLocalPolyLambda() {
        checkInfer(listOf(
            "main" to """
                def a =
                  let id = fun x in x end
                   in id(id(5) < 8) end
            """.trimIndent()
        ), listOf("main.a" to TyBool))
    }

    @Test
    fun testInferReturnPoly() {
        checkInfer(listOf(
            "main" to """
                def a =
                  let id = fun x in x end
                   in id end
            """.trimIndent()
        ), listOf("main.a" to TyBool))
    }

    @Test
    fun testInferToplevelPolyLambda() {
        checkInfer(listOf(
            "main" to """
                def id = fun x in x end
            """.trimIndent()
        ), listOf("main.id" to TyBool))
    }

    @Test
    fun testInferSimple() {
        val files = listOf(
            "main" to """
                def a = 5
                def b = a + 5
                def c = fun x in x + 5 end
                def d = a < 5
                def e = if a < 5 then c(a) else 7 end
                def rec = fun x in if x < 5 then x < 5 else rec(x + 1) end end
                def even = fun x in if x < 1 then 1 else odd(x - 1) - 1 end end
                def odd = fun x in if x < 2 then 1 else even(x - 1) - 1 end end

                def deadCode = 5

                def tryLet = let x = 5 y = x + a in x + y end
            """.trimIndent()
        )

        val cases = listOf(
            "main.a" to TyInt,
            "main.b" to TyInt,
            "main.c" to TyArr(TyInt, TyInt),
            "main.d" to TyBool,
            "main.e" to TyInt,
            "main.rec" to TyArr(TyInt, TyBool),
            "main.even" to TyArr(TyInt, TyInt),
            "main.deadCode" to TyInt,
            "main.tryLet" to TyInt
        )
        checkInfer(files, cases)
    }

    private fun <A: Any> checkInferBy(files: List<Pair<String, String>>, types: List<Pair<String, A>>,
                                      eq: (A, TyScm) -> Boolean) {
        val rCtx = ResolutionContext(parseFiles(files))
        val tCtx = TypeChecker(rCtx)
        assertTrue(rCtx.topoSortedModules.value.isNotEmpty())
        tCtx.inferModules()
        for ((name, exTy) in types) {
            val inferred = tCtx.inferredType(FqName.parse(name))
            assertTrue(eq(exTy, inferred), "$name should have type $exTy, but got $inferred")
        }
    }

    private fun checkInfer(files: List<Pair<String, String>>, types: List<Pair<String, Type>>) {
        checkInferBy(files, types) { ty, tyScm ->
            tyScm.alphaEq(TyScm(emptyList(), ty))
        }
    }

    private fun checkInferScm(files: List<Pair<String, String>>, types: List<Pair<String, TyScm>>) {
        checkInferBy(files, types, TyScm::alphaEq)
    }
}

private fun parseFiles(files: List<Pair<String, String>>): List<Module> {
    return files.map {
        val moduleName = ModuleName(it.first)
        assertNotNull(PolyLangParser.file(moduleName).run(it.second))
    }
}

private fun rCtxFromFiles(vararg files: Pair<String, String>): ResolutionContext {
    val ms = parseFiles(files.toList())
    return ResolutionContext(ms)
}

private fun defUseToMap(rCtx: ResolutionContext): Map<FqName, Set<FqName>> {
    val res = mutableMapOf<FqName, MutableSet<FqName>>()
    val dus = rCtx.deps.value
    for (du in dus) {
        val m = du.key
        for ((def, use) in du.value.imports) {
            res.compute(def) { _, uss ->
                (uss ?: mutableSetOf()).apply {
                    this += FqName(m, use)
                }
            }
        }
        for ((def, use) in du.value.local) {
            if (use.isEmpty()) {
                // Ignore empty uses so we don't have to write empty sets in tests...
                continue
            }
            res.compute(FqName(m, def)) { _, uss ->
                (uss ?: mutableSetOf()).apply {
                    addAll(use.map { FqName(m, it) })
                }
            }
        }
    }
    return res
}
