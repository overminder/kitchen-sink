package com.github.om.inctc.lang.stlc

typealias MaybeTypeMap = MutableMap<FqName, MaybeType>

sealed class MaybeType
data class ResolvedType(val unwrap: Type): MaybeType()
data class UnresolvedType(val resolve: (MaybeTypeMap) -> Type): MaybeType()

// Returns {def: uses}
fun gatherDeclarationDependencies(ms: Map<ModuleName, Module>): Map<FqName, Set<FqName>> {
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


fun inferModules(ms: List<Module>) {
    val everything: MaybeTypeMap = mutableMapOf()
    for (m in ms) {
    }
}

