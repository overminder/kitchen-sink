package com.github.om.inctc

import com.github.om.inctc.lang.stlc.*
import org.junit.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

private fun parseFiles(files: List<Pair<String, String>>): Map<ModuleName, Module> {
    return files.map {
        val moduleName = ModuleName(it.first)
        moduleName to assertNotNull(StlcParser.file(moduleName).run(it.second))
    }.toMap()
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
        val main = """
            use fibo.fibo 
            
            pub def main = fibo(10)
        """.trimIndent()

        val modules = parseFiles(listOf(
                "fibo" to fibo,
                "main" to main
        ))

        val deps = gatherDeclarationDependencies(modules)
        assertEquals(mapOf(
                FqName.parse("fibo.fibo") to setOf(FqName.parse("fibo.fibo"), FqName.parse("main.fibo")),
                FqName.parse("main.main") to setOf(FqName.parse("main.fibo"))
        ), deps)
    }
}
