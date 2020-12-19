/*
 * This Kotlin source file was generated by the Gradle 'init' task.
 */
package com.github.om.inctc

import com.github.om.inctc.bench.PolyLangGenerator
import com.github.om.inctc.bench.Timer
import com.github.om.inctc.lang.poly.*

/**
 * Some notes: 5k decls per file cause the parser to stack overflow.
 * 2k decls per file, 5 files -- parsing needs 1.5-2.3s (after JIT warms up: .9s) and tc 1.2s LOL
 *
 * Though this is partly because the language permits recursive definitions across module boundaries --
 * this is something GHC doesn't allow (https://wiki.haskell.org/Mutually_recursive_modules).
 * Essentially this makes the whole module system a giant single file, which is bad. Let me try disabling that...
 *
 * Kt OTOH allows mutually recursive decls split across different files. Though you have to specify one of the
 * return type for the decl (this is the same even if they are defined in the same file).
 */

fun bench(modules: List<Module>, files: List<Pair<ModuleName, String>>, redoParse: Boolean = false, printStat: Boolean = false) {
    val tm = Timer.create().apply {
        printImmediately = false
    }
    val parsedAgain = if (redoParse) {
        tm.timed("parse") {
            files.map {
                requireNotNull(PolyLangParser.file(it.first).run(it.second))
            }
        }
    } else {
        modules
    }
    val rCtx = ResolutionContext(parsedAgain, tm)
    tm.timed("findUndef") { rCtx.findUndefinedUses().firstOrNull() }
    val tCtx = TypeChecker(rCtx)
    tm.timed("tc") { tCtx.inferModules() }
    if (printStat) {
        tm.printStat()
    }
}

fun main() {
    val tm = Timer.create()
    val modules = tm.timed("poet") {
        val g = PolyLangGenerator(15, 20000)
        val totalSteps = tm.timed("run") { g.run() }
        println("Total steps: $totalSteps")
        tm.timed("build") { g.build() }
    }
    println("N modules: ${modules.size}")
    val files = tm.timed("ppr") {
        modules.map {
            it.name to PprState.ppr(it)
        }
    }

    repeat(3) {
        println("${it + 1}th run")
        bench(modules, files, redoParse = false, printStat = false)
    }

    bench(modules, files, redoParse = false, printStat = true)
}