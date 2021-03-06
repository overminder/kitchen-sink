package com.github.om.inctc.lang.poly

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

// Def -> Uses
data class ModuleDependencies(val local: Map<Ident, Set<Ident>>, val imports: Map<FqName, Ident>)

private fun collectModuleDeps(ms: List<Module>): Map<ModuleName, ModuleDependencies> {
    return ms.associate { it.name to collectSingleModuleDeps(it) }
}

private fun collectSingleModuleDeps(m: Module): ModuleDependencies {
    // Pre-populate sets, because we need to keep track of all local defs.
    val local = m.decls.associateTo(mutableMapOf()) {
        it.ident to mutableSetOf<Ident>()
    }
    val imports = mutableMapOf<FqName, Ident>()
    for (decl in m.decls) {
        when (decl) {
            is Import -> imports += decl.defSite to decl.ident
            is ValueDef -> local.compute(decl.ident) { _, v ->
                requireNotNull(v).apply {
                    addAll(decl.body.freeVariables())
                }
            }
        }
    }
    return ModuleDependencies(local, imports)
}

private fun gatherModuleSccs(dus: Map<Ident, Set<Ident>>): List<List<Ident>> {
    val g = buildGraph<Ident> {
        dus.forEach { (d, us) ->
            // Since uses can be empty.
            it += d
            us.forEach { u ->
                it += d to u
            }
        }
    }

    return GraphAlgo.sccKosaraju(g).map { it.map { requireNotNull(g.get(it)) } }
}
