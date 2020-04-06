package com.github.om.inctc

import com.github.om.inctc.lang.stlc.*
import org.junit.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

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
        ), rCtx.defUses.value)

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
                """.trimIndent()
        )

        val tCtx = TypeContext()
        tCtx.populateAndInferModules(rCtx)
        assertEquals(TyInt, tCtx.nameToType[FqName.parse("main.a")])
        assertEquals(TyInt, tCtx.nameToType[FqName.parse("main.b")])
        assertEquals(TyArr(TyInt, TyInt), tCtx.nameToType[FqName.parse("main.c")])
        assertEquals(TyBool, tCtx.nameToType[FqName.parse("main.d")])
        assertEquals(TyInt, tCtx.nameToType[FqName.parse("main.e")])
        assertEquals(TyArr(TyInt, TyInt), tCtx.nameToType[FqName.parse("main.even")])
        assertEquals(TyArr(TyInt, TyInt), tCtx.nameToType[FqName.parse("main.odd")])
    }
}
