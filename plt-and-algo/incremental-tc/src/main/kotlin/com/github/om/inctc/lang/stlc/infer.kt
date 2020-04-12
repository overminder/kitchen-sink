package com.github.om.inctc.lang.stlc

class ModuleTypeContext(
    internal val global: TypeChecker,
    internal val u: UnificationContext,
    internal val here: Module,
    internal val bindingOrdering: List<List<Ident>>
) {
    internal val nameToType = mutableMapOf<Ident, Type>()
}

class UnificationContext {
    private var uniqGen = 1

    internal val substitutions = mutableMapOf<TyVar, Type>()
    fun mkTyVar(): TyVar = TyVar(uniqGen++)
}

class TypeChecker(
    internal val rCtx: ResolutionContext
) {
    internal val ordering = rCtx.topoSortedModules.value
    internal val bindingOrdering = rCtx.moduleDeclSccs.value
    internal val moduleTyCtxs = mutableMapOf<ModuleName, ModuleTypeContext>()

    fun inferredType(defSite: FqName): Type {
        val m = requireNotNull(moduleTyCtxs[defSite.moduleName]) {
            "No module for ${defSite.moduleName} -- all modules: ${moduleTyCtxs.keys}"
        }
        return requireNotNull(m.nameToType[defSite.ident]) {
            "No type for ${defSite.ident} -- all idents: ${m.nameToType.keys}"
        }
    }
}

fun TypeChecker.inferModules() {
    val uCtx = UnificationContext()
    for (mn in ordering) {
        val m = requireNotNull(rCtx.moduleMap[mn])
        val mTyCtx = ModuleTypeContext(this, uCtx, m, requireNotNull(bindingOrdering[mn]))
        moduleTyCtxs[mn] = mTyCtx

        mTyCtx.inferAll()
    }
}

private fun ModuleTypeContext.isSelfRecursive(x: Ident): Boolean {
    val deps = requireNotNull(global.rCtx.deps.value[here.name])
    return (deps.local[x] ?: emptySet()).contains(x)
}

private fun ModuleTypeContext.declFromName(x: Ident): Decl {
    return requireNotNull(global.rCtx.moduleDecls[FqName(here.name, x)])
}

fun ModuleTypeContext.inferAll() {
    for (scc in bindingOrdering) {
        if (scc.size == 1) {
            val id = scc.first()
            val decl = declFromName(id)
            val isRec = isSelfRecursive(id)
            if (isRec) {
                makeTyVarPlaceholderForDecl(decl)
            }
            inferTopLevelDecl(decl)
        } else {
            val decls = scc.map(::declFromName)
            decls.forEach(::makeTyVarPlaceholderForDecl)
            decls.forEach {
                inferTopLevelDecl(it)
            }
        }
        lintInferredTypes(scc)
        cleanUpSubst()
    }
}

fun ModuleTypeContext.makeTyVarPlaceholderForDecl(d: Decl) {
    when (d) {
        is Import -> nameToType += d.ident to global.inferredType(d.defSite)
        is Define -> require(nameToType.put(d.ident, u.mkTyVar()) == null)
    }
}

fun ModuleTypeContext.inferTopLevelDecl(d: Decl): Unit = when(d) {
    is Import -> {
        nameToType += d.ident to global.inferredType(d.defSite)
    }
    is Define -> {
        // Populated beforehand in ModuleTC.populateDeclTypes. But we can optimize this better.
        val placeholderTy = nameToType[d.ident]
        val bodyTy = infer(d.body, TyEnv.topLevel(nameToType))
        nameToType[d.ident] = if (placeholderTy != null) {
            // This is for recursive decls.
            u.unify(placeholderTy, bodyTy)
        } else {
            assert(bodyTy !is TyVar) { "$bodyTy leaked from $d" }
            bodyTy
        }
        Unit
    }
}

fun UnificationContext.subst(t: Type): Type = when (t) {
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
            val finalTy = subst(t2)
            substitutions += t to finalTy
            finalTy
        }
    }
    else -> t
}

fun UnificationContext.unify(t1: Type, t2: Type): Type {
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

fun UnificationContext.unifyTyVar(t1: TyVar, t2: Type): Type {
    substitutions += t1 to t2
    return t2
}

private fun mkTyArr(args: List<Type>, resTy: Type): Type = args.foldRight(resTy, ::TyArr)

private fun ModuleTypeContext.infer(e: Exp, env: TyEnv) = u.subst(infer0(e, env))

private class TyEnv private constructor(val parent: TyEnv?, val here: Map<Ident, Type>) {
    companion object {
        fun topLevel(env: Map<Ident, Type>) = TyEnv(null, env)
    }

    fun extend(inner: Map<Ident, Type>) = TyEnv(this, inner)
    operator fun get(id: Ident): Type? {
        var env: TyEnv? = this
        while (env != null) {
            val ty = env.here[id]
            if (ty != null) {
                return ty
            }
            env = env.parent
        }
        return null
    }
}

private fun ModuleTypeContext.infer0(e: Exp, env: TyEnv): Type = when (e) {
    is Var -> requireNotNull(env[e.ident]) { "Unbound var: ${e.ident.name}" }
    is Lam -> {
        val argTys = e.args.map {
            u.mkTyVar()
        }
        // This line was originally "accidentally quadratic" ;D -- We used to do Map.plus here, so this ends up
        // allocating a new map with all the entries. And since env can be huge...
        val newEnv = env.extend(e.args.zip(argTys).toMap())
        // Probably need to make a local subst as well.
        val bodyTy = infer(e.body, newEnv)
        // Probably need to run subst on arg. And check no tyVar leakage.
        mkTyArr(argTys, bodyTy)
    }
    is LitI -> TyInt
    is If -> {
        val condTy = infer(e.cond, env)
        u.unify(condTy, TyBool)
        val thenTy = infer(e.then, env)
        val elseTy = infer(e.else_, env)
        u.unify(thenTy, elseTy)
    }
    is App -> {
        val argTy = infer(e.arg, env)
        val resTy = u.mkTyVar()
        val funcTy = infer(e.func, env)
        u.unify(funcTy, TyArr(argTy, resTy))
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
        u.unify(leftTy, ratorTy)
        u.unify(rightTy, ratorTy)
        resTy
    }
}

fun ModuleTypeContext.cleanUpSubst() {
    u.substitutions.clear()
}

fun ModuleTypeContext.lintInferredTypes(names: Iterable<Ident>) {
    names.forEach {
        val ty = requireNotNull(nameToType[it])
        require(!ty.hasTyVars) {
            "$ty ($it) still has type vars! Current subst: ${u.substitutions.keys}"
        }
    }
}
