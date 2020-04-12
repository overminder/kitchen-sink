package com.github.om.inctc

import com.github.om.inctc.lang.stlc.*
import org.junit.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class StlcTest {
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
    fun testInferSimple() {
        val rCtx = rCtxFromFiles(
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
                """.trimIndent()
        )

        val tCtx = TypeChecker(rCtx)
        assertTrue(rCtx.topoSortedModules.value.isNotEmpty())
        tCtx.inferModules()
        val cases = listOf(
            TyInt to "main.a",
            TyInt to "main.b",
            TyArr(TyInt, TyInt) to "main.c",
            TyBool to "main.d",
            TyInt to "main.e",
            TyArr(TyInt, TyBool) to "main.rec",
            TyArr(TyInt, TyInt) to "main.even",
            TyInt to "main.deadCode"
        )
        for ((exTy, name) in cases) {
            assertEquals(exTy, tCtx.inferredType(FqName.parse(name)), "$name should have type $exTy")
        }
    }
}

private fun parseFiles(files: List<Pair<String, String>>): List<Module> {
    return files.map {
        val moduleName = ModuleName(it.first)
        assertNotNull(StlcParser.file(moduleName).run(it.second))
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
