package com.github.om.inctc.bench

import com.github.om.inctc.lang.stlc.*
import kotlin.random.Random
import kotlin.random.asJavaRandom

// Generate module files.

class StlcGenerator(val nModules: Int, val nSteps: Int, rngSeed: Long = 12345678L) {
    private val rng = Random(rngSeed)
    private var idGen = 1

    private val modules = mutableMapOf<ModuleName, MutableMap<Ident, Decl>>()
    private val modulesOrder = mutableMapOf<ModuleName, Int>()

    fun build(): List<Module> {
        return modules.map {
            Module(it.key, it.value.values.toList())
        }
    }

    fun run(): Int {
        repeat(nModules) {
            addModule()
        }

        var actualIteration = 0
        var i = 0
        while (i < nSteps) {
            if (nextStep()) {
                i += 1
            }
            actualIteration += 1
        }
        return actualIteration
    }

    private fun nextStep(): Boolean {
        val xs = listOf(this::addImport, this::addDef)
        val shuffled = xs.shuffled(rng)
        return shuffled.first()()
    }

    private fun addImport(): Boolean {
        if (modules.size < 2) {
            return false
        }
        val moduleNames = modules.entries.shuffled(rng)
        val useSite = moduleNames[0]
        for (defSite in moduleNames.drop(1)) {
            if (requireNotNull(modulesOrder[useSite.key]) > requireNotNull(modulesOrder[defSite.key])) {
                // Make sure we don't create cycles between modules (this is an unfortunate performance restriction)
                continue
            }
            for (def in defSite.value.asIterable().shuffled(rng)) {
                if (useSite.value.containsKey(def.key)) {
                    // Avoid redeclaration
                    continue
                }
                useSite.value += def.key to Import(defSite.key, def.key)
                return true
            }
        }
        return false
    }

    private fun addDef(): Boolean {
        if (modules.isEmpty()) {
            return false
        }
        // Assume all defs are int -> int
        val moduleNames = modules.entries.shuffled(rng)
        val defSite = moduleNames[0]
        val ident = mkIdent()
        val arg = mkIdent()
        val body = Lam(listOf(arg), BOp(BRator.PLUS, Var(arg), LitI(5)))
        defSite.value += ident to Define(ident, Visibility.Public, body)
        return true
    }

    private fun addModule(): Boolean {
        val name = mkModuleName()
        modules += name to mutableMapOf()
        modulesOrder += name to modulesOrder.size
        return true
    }

    // Helpers

    private fun mkName(): String = "v${idGen++}"
    private fun mkIdent(): Ident = Ident(mkName())
    private fun mkModuleName(): ModuleName = ModuleName(mkName())
}

