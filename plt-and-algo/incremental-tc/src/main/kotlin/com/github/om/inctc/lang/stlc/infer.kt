package com.github.om.inctc.lang.stlc

class ModuleTypeContext(
    internal val global: TypeChecker,
    internal val u: UnificationContext,
    internal val here: Module
) {
    internal val nameToType = mutableMapOf<Ident, Type>()
}

class UnificationContext {
    private var uniqGen = 1

    internal val substitutions = mutableMapOf<TyVar, Type>()
    fun mkTyVar(): TyVar = TyVar(uniqGen++)
}

class TypeChecker(
    internal val rCtx: ResolutionContext,
    internal val ordering: List<ModuleName>
) {
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
        val mTyCtx = ModuleTypeContext(this, uCtx, m)
        moduleTyCtxs[mn] = mTyCtx

        // Assume all local defs are mutual exclusive -- grab imports and make placeholder types for definitions.
        mTyCtx.populateDeclTypes()
        mTyCtx.inferDecls()
        mTyCtx.freeze()
    }
}

fun ModuleTypeContext.populateDeclTypes() {
    for (d in here.decls) {
        when (d) {
            is Import -> nameToType += d.ident to global.inferredType(d.defSite)
            is Define -> require(nameToType.put(d.ident, u.mkTyVar()) == null)
        }
    }
}

fun ModuleTypeContext.inferDecls() {
    for (d in here.decls) {
        inferDecl(d, nameToType)
    }
}

fun ModuleTypeContext.inferDecl(d: Decl, env: Map<Ident, Type>): Unit = when(d) {
    is Import -> {
        nameToType += d.ident to global.inferredType(d.defSite)
    }
    is Define -> {
        // Populated beforehand in ModuleTC.populateDeclTypes. But we can optimize this better.
        val ty = requireNotNull(nameToType[d.ident])
        val bodyTy = infer(d.body, env)
        nameToType[d.ident] = u.unify(ty, bodyTy)
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

fun ModuleTypeContext.infer(e: Exp, env: Map<Ident, Type> = emptyMap()) = u.subst(infer0(e, env))

fun ModuleTypeContext.infer0(e: Exp, env: Map<Ident, Type>): Type = when (e) {
    is Var -> requireNotNull(env[e.ident]) { "Unbound var: ${e.ident.name}" }
    is Lam -> {
        val argTys = e.args.map {
            u.mkTyVar()
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

fun ModuleTypeContext.freeze() {
    nameToType.mapValues {
        val sTy = u.subst(it.value)
        require(!sTy.hasTyVars) {
            "$sTy still has type vars! Current subst: ${u.substitutions.keys}"
        }
        sTy
    }

    u.substitutions.clear()
}
