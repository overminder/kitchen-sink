package com.github.om.inctc.lang.stlc

class ResolutionContext(modules: List<Module>) {
    val moduleMap: Map<ModuleName, Module>
    val moduleDecls: Map<FqName, Decl>
    val defUses: Lazy<Map<FqName, Set<FqName>>>

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
    }

    fun findUndefinedUses(): Sequence<Pair<FqName, Set<FqName>>> {
        return defUses.value.asSequence().filter {
            !moduleDecls.containsKey(it.key)
        }.map { it.toPair() }
    }
}

class TypeContext {
    private var uniqGen = 1

    val nameToType = mutableMapOf<FqName, Type>()

    val substitutions = mutableMapOf<TyVar, Type>()

    fun mkTyVar(): TyVar = TyVar(uniqGen++)
    private fun getOrPutTyVar(key: FqName): Type = nameToType.getOrPut(key, this::mkTyVar)

    fun addImport(def: FqName, use: FqName) {
        val defTy = requireNotNull(nameToType[def])
        val useTy = requireNotNull(nameToType[use])
        unify(defTy, useTy)
    }

    fun addDef(def: FqName): Type = getOrPutTyVar(def)

    fun populateFrom(rCtx: ResolutionContext) {
        for (name in rCtx.moduleDecls.keys) {
            addDef(name)
        }
    }
}

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

fun TypeContext.populateAndInferModules(rCtx: ResolutionContext) {
    populateFrom(rCtx)
    for (m in rCtx.moduleMap.values) {
        inferModule(m, rCtx)
    }
    for (declTy in nameToType) {
        declTy.setValue(subst(declTy.value))
    }
}

fun TypeContext.inferModule(m: Module, rCtx: ResolutionContext) {
    val moduleEnv = rCtx.moduleDecls.keys.map {
        it.ident to requireNotNull(nameToType[it])
    }.toMap()
    for (d in m.decls) {
        inferDecl(d, m.name, moduleEnv)
    }
}

fun TypeContext.inferDecl(d: Decl, here: ModuleName, env: Map<Ident, Type>): Unit = when(d) {
    is Import -> {
        val def = FqName(d.moduleName, d.ident)
        val use = FqName(here, d.ident)
        addImport(def, use)
    }
    is Define -> {
        val def = FqName(here, d.ident)
        val ty = addDef(def)
        val bodyTy = infer(d.body, env)
        unify(ty, bodyTy)
        Unit
    }
}

fun TypeContext.subst(t: Type): Type = when (t) {
    is TyArr -> {
        val from = subst(t.from)
        val to = subst(t.to)
        if (from == t.from && to == t.to) {
            t
        } else {
            subst(TyArr(from, to))
        }
    }
    is TyVar -> {
        val t2 = substitutions.getOrDefault(t, t)
        if (t2 == t) {
            t
        } else {
            // XXX Do we need this? Can we remove indirections on all substitutions?
            subst(t2)
        }
    }
    else -> t
}

fun TypeContext.unify(t1: Type, t2: Type): Type {
    if (t1 is TyVar) {
        return unifyTyVar(t1, t2)
    }
    if (t2 is TyVar) {
        return unifyTyVar(t2, t1)
    }
    val mkErr = { "Can't unify $t1 with $t2" }
    return when (t1) {
        is TyInt -> {
            require(t2 == TyInt, mkErr)
            TyInt
        }
        is TyBool -> {
            require(t2 == TyBool, mkErr)
            TyInt
        }
        is TyArr -> {
            require(t2 is TyArr, mkErr)
            TyArr(unify(t1.from, t2.from), unify(t1.to, t2.to))
        }
        is TyVar -> {
            error("Not reachable")
        }
    }
}

fun TypeContext.unifyTyVar(t1: TyVar, t2: Type): Type {
    substitutions += t1 to t2
    return t2
}

private fun mkTyArr(args: List<Type>, resTy: Type): Type = args.foldRight(resTy, ::TyArr)

fun TypeContext.infer(e: Exp, env: Map<Ident, Type> = emptyMap()) = subst(infer0(e, env))

fun TypeContext.infer0(e: Exp, env: Map<Ident, Type>): Type = when (e) {
    is Var -> requireNotNull(env[e.ident]) { "Unbound var: ${e.ident.name}" }
    is Lam -> {
        val argTys = e.args.map {
            mkTyVar()
        }
        val newEnv = env + e.args.zip(argTys).toMap()
        // Probably need to make a local subst as well.
        val bodyTy = infer(e.body, newEnv)
        // Probably need to run subst on arg. And check no tyVar leakage.
        mkTyArr(argTys, bodyTy)
    }
    is LitI -> TyInt
    is If -> {
        val condTy = infer(e.cond, env)
        unify(condTy, TyBool)
        val thenTy = infer(e.then, env)
        val elseTy = infer(e.else_, env)
        unify(thenTy, elseTy)
    }
    is App -> {
        val argTy = infer(e.arg, env)
        val resTy = mkTyVar()
        val funcTy = infer(e.func, env)
        unify(funcTy, TyArr(argTy, resTy))
        resTy
    }
    is BOp -> {
        val (ratorTy, resTy) = when (e.op) {
            BRator.LT -> Pair(TyInt, TyBool)
            BRator.PLUS -> Pair(TyInt, TyInt)
            BRator.MINUS -> Pair(TyInt, TyInt)
        }
        val leftTy = infer(e.left, env)
        val rightTy = infer(e.right, env)
        unify(leftTy, ratorTy)
        unify(rightTy, ratorTy)
        resTy
    }
}
