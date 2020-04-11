package com.github.om.inctc.lang.stlc

import com.github.om.inctc.graph.GraphAlgo
import com.github.om.inctc.graph.buildGraph
import com.github.om.inctc.graph.topoSort

class ResolutionContext(modules: List<Module>) {
    val moduleMap: Map<ModuleName, Module>
    val moduleDecls: Map<FqName, Decl>
    val defUses: Lazy<Map<FqName, Set<FqName>>>
    val moduleDefUses: Lazy<Map<ModuleName,  Set<ModuleName>>>

    init {
        moduleMap = modules.map { it.name to it }.toMap()
        moduleDecls = modules.flatMap { m ->
            m.decls.map { d ->
                FqName(m.name, d.ident) to d
            }
        }.toMap()
        defUses = lazy {
            gatherDeclarationDependencies(moduleMap)
        }
        moduleDefUses = lazy {
            val res = mutableMapOf<ModuleName, MutableSet<ModuleName>>()
            for (du in defUses.value) {
                res.compute(du.key.moduleName) { k, v ->
                    (v ?: mutableSetOf()).apply {
                        addAll(du.value.map { it.moduleName })
                    }
                }
            }
            res
        }
    }

    fun findUndefinedUses(): Sequence<Pair<FqName, Set<FqName>>> {
        return defUses.value.asSequence().filter {
            !moduleDecls.containsKey(it.key)
        }.map { it.toPair() }
    }

    fun topoSortedModules(): List<ModuleName> {
        val depG = buildGraph<ModuleName> { gb ->
            for (du in moduleDefUses.value) {
                // Always add node (because otherwise we can be ignoring a single main module)
                gb += du.key
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

// Returns {def: uses}
private fun gatherDeclarationDependencies(ms: Map<ModuleName, Module>): Map<FqName, Set<FqName>> {
    val dependsOn = mutableMapOf<FqName, MutableSet<FqName>>()

    fun usesOfExp(e: Exp, here: ModuleName, localDefined: List<Ident> = listOf()): List<FqName> = when (e) {
        is Var -> if (localDefined.contains(e.ident)) {
            emptyList()
        } else {
            listOf(FqName(here, e.ident))
        }
        is Lam -> usesOfExp(e.body, here, localDefined + e.args)
        is LitI -> listOf()
        is If -> usesOfExp(e.cond, here, localDefined) +
                usesOfExp(e.then, here, localDefined) +
                usesOfExp(e.else_, here, localDefined)
        is App -> usesOfExp(e.func, here, localDefined) + usesOfExp(e.arg, here, localDefined)
        is BOp -> usesOfExp(e.left, here, localDefined) + usesOfExp(e.right, here, localDefined)
    }

    for (m in ms) {
        for (decl in m.value.decls) {
            val (def, uses) = when (decl) {
                is Import -> {
                    val def = FqName(decl.moduleName, decl.ident)
                    def to listOf(FqName(m.key, decl.ident))
                }
                is Define -> {
                    val def = FqName(m.key, decl.ident)
                    def to usesOfExp(decl.body, m.key)
                }
            }
            dependsOn.compute(def) { _, mbUses ->
                (mbUses ?: mutableSetOf()).also {
                    it += uses
                }
            }
        }
    }

    return dependsOn
}
