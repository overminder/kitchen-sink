package org.jetbrains.kotlin.runner.yux

import org.jetbrains.kotlin.runner.ExpressionRunner
import java.io.File
import java.net.URL

// XXX
private val KOTLIN_HOME = File("/Users/yxjiang/ref/jb-kotlin/dist/kotlinc")

object Exprs {
    private fun String.moar(ss: String): String {
        return this + "\n" + ss
    }

    val SIMPLE = """
    val x = 1
    """.trimIndent()

    val ASSIGN_TO_VAL = """
    val x = 1
    x = 5
    """.trimIndent()

    val RECURSIVE_GENERIC_BASE = """
    interface Rec<A: Rec<A>> 
    fun <A: Rec<A>> mk(): A? = null
    """.trimIndent()

    val RECURSIVE_GENERIC_CANT_INFER = RECURSIVE_GENERIC_BASE.moar("""
    val x = mk()
    """.trimIndent())

    val RECURSIVE_GENERIC_BAD_BOUND = RECURSIVE_GENERIC_BASE.moar("""
    val x = mk<Rec<*>>()
    """.trimIndent())
}

fun main() {
    val cp = listOf(
        "lib/kotlin-stdlib.jar",
        "lib/kotlin-reflect.jar"
    ).map(::resolveKt)

    val compilerCp = listOf(
        "lib/kotlin-compiler.jar"
    ).map(::resolveKt)

    val runner = ExpressionRunner(Exprs.RECURSIVE_GENERIC_BAD_BOUND)
    runner.run(cp, listOf(), compilerCp)
}

private fun File.toURL2(): URL {
    return absoluteFile.toURI().toURL()
}

private fun resolveKt(s: String): URL {
    return KOTLIN_HOME.resolve(s).toURL2()
}
