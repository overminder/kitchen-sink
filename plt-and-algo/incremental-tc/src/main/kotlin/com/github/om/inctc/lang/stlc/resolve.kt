package com.github.om.inctc.lang.stlc

import com.github.om.inctc.bench.Timer
import com.github.om.inctc.bench.timedLazy
import com.github.om.inctc.graph.GraphAlgo
import com.github.om.inctc.graph.buildGraph
import com.github.om.inctc.graph.sccKosaraju
import com.github.om.inctc.graph.topoSort

class ResolutionContext(
    modules: List<Module>,
    outerTimer: Timer = Timer.DEFAULT
) {
    val moduleMap: Map<ModuleName, Module>
    val moduleDecls: Map<FqName, Decl>
    val deps: Lazy<Map<ModuleName, ModuleDependencies>>
    val moduleDefUses: Lazy<Map<ModuleName,  Set<ModuleName>>>
    val topoSortedModules: Lazy<List<ModuleName>>
    val moduleDeclSccs: Lazy<Map<ModuleName, List<List<Ident>>>>

    private val tm = outerTimer.scoped("rCtx")

    init {
        moduleMap = modules.map { it.name to it }.toMap()
        moduleDecls = modules.flatMap { m ->
            m.decls.map { d ->
                FqName(m.name, d.ident) to d
            }
        }.toMap()
        deps = tm.timedLazy("deps") {
            collectModuleDeps(modules)
        }
        moduleDefUses = tm.timedLazy("moduleDefUses") {
            val res = mutableMapOf<ModuleName, MutableSet<ModuleName>>()
            for (du in deps.value) {
                for (imp in du.value.imports) {
                    res.compute(imp.key.moduleName) { _, v ->
                        (v ?: mutableSetOf()).apply {
                            this += du.key
                        }
                    }
                }
            }
            res
        }
        topoSortedModules = tm.timedLazy("toposortModules") {
            topoSortModules()
        }
        moduleDeclSccs = tm.timedLazy("moduleDeclSccs") {
            deps.value.mapValues {
                gatherModuleSccs(it.value.local)
            }
        }
    }

    fun findUndefinedUses(): Sequence<Pair<FqName, ModuleName>> {
        return deps.value.asSequence().flatMap {
            val m = it.key
            val imports = it.value.imports.keys.asSequence()
            imports.filter {
                !moduleDecls.containsKey(it)
            }.map {
                it to m
            }
        }
    }

    private fun topoSortModules(): List<ModuleName> {
        val depG = buildGraph<ModuleName> { gb ->
            for (m in moduleMap.keys) {
                // Always add each module (because modules are not necessarily connected)
                gb += m
            }
            for (du in moduleDefUses.value) {
                for (u in du.value) {
                    // Ignore self-edges, because we don't treat these as cycles.
                    if (u != du.key) {
                        gb += du.key to u
                    }
                }
            }
        }
        return GraphAlgo.topoSort(depG).map { requireNotNull(depG.get(it)) }
    }
}

// Use of toplevel bindings, not local bindings.
private fun usesOfExp(e: Exp, localEnv: List<Ident> = listOf()): List<Ident> = when (e) {
    is Var -> if (localEnv.contains(e.ident)) {
        emptyList()
    } else {
        listOf(e.ident)
    }
    is Lam -> usesOfExp(e.body, localEnv + e.args)
    is LitI -> listOf()
    is If -> usesOfExp(e.cond, localEnv) +
        usesOfExp(e.then, localEnv) +
        usesOfExp(e.else_, localEnv)
    is App -> usesOfExp(e.func, localEnv) + usesOfExp(e.arg, localEnv)
    is BOp -> usesOfExp(e.left, localEnv) + usesOfExp(e.right, localEnv)
}

// Def -> Uses
data class ModuleDependencies(val local: Map<Ident, Set<Ident>>, val imports: Map<FqName, Ident>)

private fun collectModuleDeps(ms: List<Module>): Map<ModuleName, ModuleDependencies> {
    return ms.associate { it.name to collectSingleModuleDeps(it) }
}

private fun collectSingleModuleDeps(m: Module): ModuleDependencies {
    val local = mutableMapOf<Ident, MutableSet<Ident>>()
    val imports = mutableMapOf<FqName, Ident>()
    for (decl in m.decls) {
        when (decl) {
            is Import -> imports += decl.defSite to decl.ident
            is Define -> local.compute(decl.ident) { _, v ->
                (v ?: mutableSetOf()).apply {
                    addAll(usesOfExp(decl.body))
                }
            }
        }
    }
    return ModuleDependencies(local, imports)
}

private fun gatherModuleSccs(dus: Map<Ident, Set<Ident>>): List<List<Ident>> {
    val g = buildGraph<Ident> {
        dus.forEach { (d, us) ->
            us.forEach { u ->
                it += d to u
            }
        }
    }

    return GraphAlgo.sccKosaraju(g).map { it.map { requireNotNull(g.get(it)) } }
}
