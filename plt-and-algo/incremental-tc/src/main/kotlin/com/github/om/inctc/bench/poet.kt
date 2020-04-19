package com.github.om.inctc.bench

import com.github.om.inctc.lang.poly.App
import com.github.om.inctc.lang.poly.BOp
import com.github.om.inctc.lang.poly.BRator
import com.github.om.inctc.lang.poly.Decl
import com.github.om.inctc.lang.poly.ValueDef
import com.github.om.inctc.lang.poly.Ident
import com.github.om.inctc.lang.poly.Import
import com.github.om.inctc.lang.poly.Lam
import com.github.om.inctc.lang.poly.LitI
import com.github.om.inctc.lang.poly.Module
import com.github.om.inctc.lang.poly.ModuleName
import com.github.om.inctc.lang.poly.Var
import com.github.om.inctc.lang.poly.Visibility
import kotlin.random.Random

// Generate module files.

class PolyLangGenerator(val nModules: Int, val nSteps: Int, rngSeed: Long = 12345678L) {
    private val rng = Random(rngSeed)
    private var idGen = 1

    private val modules = mutableMapOf<ModuleName, MutableMap<Ident, Decl>>()
    private val modulesOrder = mutableMapOf<ModuleName, Int>()

    private val stepChoices = prepareStepChoices(nImp = 5, nDef = 5, nRefDef = 1)

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
            i += nextStep()
            actualIteration += 1
        }
        return actualIteration
    }

    private fun prepareStepChoices(nImp: Int, nDef: Int, nRefDef: Int): List<() -> Int> {
        return List(nImp, { this::addImport }) +
            List(nDef, { this::addDef }) +
            List(nRefDef) { this::addRecDef }
    }

    private fun nextStep(): Int {
        val todo = stepChoices.shuffled(rng).first()
        return todo()
    }

    private fun addImport(): Int {
        if (modules.size < 2) {
            return 0
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
                return 1
            }
        }
        return 0
    }

    private fun addDef(): Int {
        if (modules.isEmpty()) {
            return 0
        }
        // Assume all defs are int -> int
        val moduleNames = modules.entries.shuffled(rng)
        val defSite = moduleNames[0]
        val ident = mkIdent()
        val arg = mkIdent()
        val body = Lam(listOf(arg), BOp(BRator.PLUS, Var(arg), LitI(5)))
        defSite.value += ident to ValueDef(ident, Visibility.Public, body)
        return 1
    }

    private fun addRecDef(): Int {
        if (modules.isEmpty()) {
            return 0
        }

        val defSite = modules.entries.shuffled(rng).first()

        val chooseFrom = (1 until 10).toList()
        val nDecls = chooseFrom.shuffled(rng).first()

        fun mkDecl(func: Ident, arg: Ident) =
            Lam(listOf(arg),
                BOp(BRator.PLUS,
                    Var(arg),
                    App(Var(func), LitI(5))))

        val idents = List(nDecls) { mkIdent() }
        val args = List(nDecls) { mkIdent() }
        if (nDecls == 1) {
            val ident = idents.first()
            val arg = args.first()
            defSite.value += ident to ValueDef(ident, Visibility.Public, mkDecl(ident, arg))
        } else {
            // f1 call f2, ..., fN-1 call fN
            val fs = idents.drop(1).zip(args).map { (nextFunc, arg) ->
                mkDecl(nextFunc, arg)
            }
            // fN call f1
            val f = mkDecl(idents.first(), args.last())

            for ((ident, body) in idents.zip(listOf(f) + fs)) {
                defSite.value += ident to ValueDef(ident, Visibility.Public, body)
            }
        }
        return nDecls
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

