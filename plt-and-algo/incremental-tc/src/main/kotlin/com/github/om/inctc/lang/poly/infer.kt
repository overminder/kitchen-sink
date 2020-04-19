package com.github.om.inctc.lang.poly

import com.github.om.inctc.Log

// region Global type checker context

sealed class InferenceError: Throwable()
data class CannotUnify(val t1: Type, val t2: Type): InferenceError()

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
    val uniqueGen = UniqueGen()
    for (mn in ordering) {
        val m = requireNotNull(rCtx.moduleMap[mn])
        val mTyCtx = ModuleTypeContext(this, m, requireNotNull(bindingOrdering[mn]), uniqueGen)
        moduleTyCtxs[mn] = mTyCtx

        mTyCtx.inferAll()
    }
}

// endregion

// region Module type checking context

class ModuleTypeContext(
    internal val global: TypeChecker,
    internal val here: Module,
    internal val bindingOrdering: List<List<Ident>>,
    uniqGen: UniqueGen
) {
    internal val nameToType = mutableMapOf<Ident, Type>()

    internal val uStack = mutableListOf(UnificationContext(uniqGen))

    internal val Decl.asDefine: Define?
        get() = this as? Define
}

internal val ModuleTypeContext.u: UnificationContext
    get() = requireNotNull(uStack.lastOrNull())

internal fun <A: Any> ModuleTypeContext.withNewUCtx(f: () -> A): A {
    uStack += u.mkChild()
    val r = f()
    uStack.removeLast()
    return r
}

private fun ModuleTypeContext.inferAndGeneralize(e: Exp, env: TyEnv): Type = withNewUCtx {
    val ty = infer(e, env)
    Log.d { "Let: infer as $ty" }
    u.solveAll()
    // XXX(perf) also is this correct?
    ty.gen(env.freeTyVars())
}

private fun ModuleTypeContext.isSelfRecursive(x: Ident): Boolean {
    val deps = requireNotNull(global.rCtx.deps.value[here.name])
    return (deps.local[x] ?: emptySet()).contains(x)
}

private fun ModuleTypeContext.declFromName(x: Ident): Decl {
    return requireNotNull(global.rCtx.moduleDecls[FqName(here.name, x)]) {
        "Undefined name: $x in ${here.name}"
    }
}

fun ModuleTypeContext.inferAll() {
    for (scc in bindingOrdering) {
        inferScc(scc)
        lintInferredTypes(scc)
        u.clear()
    }
}

fun ModuleTypeContext.inferScc(scc: List<Ident>) {
    val topEnv = TyEnv.topLevel(nameToType)
    val needGen = if (scc.size == 1) {
        val id = scc.first()
        val decl = declFromName(id)
        val isRec = isSelfRecursive(id)
        val env = if (isRec) {
            makeTyVarPlaceholderForDecl(decl)?.let {
                topEnv.extend(mapOf(decl.ident to it))
            } ?: topEnv
        } else {
            topEnv
        }
        val ty = inferTopLevelDecl(decl, env)
        listOfNotNull(decl.asDefine?.ident?.to(ty))
    } else {
        val phEnv = mutableMapOf<Ident, Type>()
        val env = topEnv.extend(phEnv)
        val decls = scc.map(::declFromName)
        decls.forEach { d ->
            makeTyVarPlaceholderForDecl(d)?.let { ty ->
                phEnv += d.ident to ty
            }
        }

        val inferredTypes = decls.associate { it.ident to inferTopLevelDecl(it, env) }
        phEnv.keys.map {
            it to requireNotNull(inferredTypes[it])
        }
    }

    Log.d { "InferScc($scc): before solveAll" }
    u.solveAll()
    val ftvsFromEnv = topEnv.freeTyVars()
    Log.d { "InferScc: moduleEnv = $nameToType, toGen = $needGen, ftvs(env) = $ftvsFromEnv" }
    for ((name, ty) in needGen) {
        val gty = ty.pruned.gen(ftvsFromEnv)
        Log.d { "InferScc.gen: (${name.name}: $ty) into $gty" }
        nameToType += name to gty
    }
}

fun ModuleTypeContext.makeTyVarPlaceholderForDecl(d: Decl): Type? =
    when (d) {
        is Import -> {
            nameToType += d.ident to global.inferredType(d.defSite)
            null
        }
        is Define -> {
            // Not sure if this works...
            val tv = u.mkTyVar()
            val originalTy = nameToType.get(d.ident)
            require(originalTy == null) {
                "${d.ident} already had a type: $originalTy"
            }
            tv
        }
    }

private fun ModuleTypeContext.inferTopLevelDecl(d: Decl, env: TyEnv): Type = when(d) {
    is Import -> {
        val ty = global.inferredType(d.defSite)
        nameToType += d.ident to ty
        ty
    }
    is Define -> {
        // Populated beforehand in ModuleTC.populateDeclTypes. But we can optimize this better.
        val placeholderTy = env[d.ident]
        val bodyTy = infer(d.body, env)
        if (placeholderTy != null) {
            // This is for recursive decls.
            u.deferUnify(placeholderTy, bodyTy, "TopLevel define placeholder")
        }
        bodyTy
    }
}

private fun ModuleTypeContext.lookupVar(i: Ident, env: TyEnv): Type {
    val ty = requireNotNull(env[i]) { "Unbound var: ${i.name}" }
    val ity = ty.inst(u::mkTyVar)
    Log.d { "lookup($i): found $ty, instantiate as $ity" }
    return ity
}

private fun ModuleTypeContext.infer(e: Exp, env: TyEnv): Type = when (e) {
    is Var -> lookupVar(e.ident, env)
    is Lam -> {
        val argTys = e.args.map { u.mkTyVar() }
        // This line was originally "accidentally quadratic" ;D -- We used to do Map.plus here, so this ends up
        // allocating a new map with all the entries. And since env can be huge...
        val newEnv = env.extend(e.args.zip(argTys).toMap())
        // Probably need to make a local subst as well.
        val bodyTy = infer(e.body, newEnv)
        // Probably need to run subst on arg. And check no tyVar leakage.
        mkTyArr(argTys, bodyTy)
    }
    is Let -> {
        val newBindings = mutableMapOf<Ident, Type>()
        val letEnv = env.extend(newBindings)
        for ((ident, rhs) in e.bindings) {
            val ty = inferAndGeneralize(rhs, letEnv)
            Log.d { "Let: generalize as $ty" }

            newBindings += ident to ty
        }
        infer(e.body, letEnv)
    }
    is LitI -> TyInt
    is If -> {
        val condTy = infer(e.cond, env)
        val thenTy = infer(e.then, env)
        val elseTy = infer(e.else_, env)
        u.deferUnify(condTy, TyBool, "cond must be bool")
        u.deferUnify(thenTy, elseTy, "then/else must be same")
        thenTy
    }
    is App -> {
        val argTy = infer(e.arg, env)
        val resTy = u.mkTyVar()
        val funcTy = infer(e.func, env)
        u.deferUnify(funcTy, TyArr(argTy, resTy), "funcTy must be arrow")
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
        u.deferUnify(leftTy, ratorTy, "bop lhs")
        u.deferUnify(rightTy, ratorTy, "bop rhs")
        resTy
    }
}

fun ModuleTypeContext.lintInferredTypes(names: Iterable<Ident>) {
    names.forEach {
        val ty = requireNotNull(nameToType[it])
        require(!ty.hasTyVars) {
            "$it: $ty still has free type vars! Current u: ${u.debugRepr}"
        }
    }
}
// endregion

// region Unification

class UniqueGen(private var nextValue: Int = 1) {
    fun next(): Int = nextValue++
}

internal fun UniqueGen.freshTyVar(): TyVar = TyVar.unbound(next())

data class SameType(val t1: Type, val t2: Type, val why: String)

class UnificationContext(private val uniqGen: UniqueGen = UniqueGen()) {
    internal val constraints = mutableListOf<SameType>()

    internal fun clear() {
        constraints.clear()
    }

    fun mkTyVar() = uniqGen.freshTyVar()

    val debugRepr: String
        get() {
            return "cs: $constraints"
        }

    fun mkChild(): UnificationContext = UnificationContext(uniqGen)
}

// Does a quick check, but defer heavy works to the final solver.
fun UnificationContext.deferUnify(t1: Type, t2: Type, why: String) {
    if (t1 === t2) {
        return
    }
    constraints += SameType(t1, t2, why)
}

fun UnificationContext.unify(t1: Type, t2: Type) {
    unify0(t1.pruned, t2.pruned)
}

fun UnificationContext.unify0(t1: Type, t2: Type) {
    if (t1 is TyVar) {
        return unifyTyVar(t1.ref, t2)
    }
    if (t2 is TyVar) {
        return unifyTyVar(t2.ref, t1)
    }

    when (t1) {
        is TyInt -> {
            if (t2 !is TyInt) {
                throw CannotUnify(t1, t2)
            }
        }
        is TyBool -> {
            if (t2 !is TyBool) {
                throw CannotUnify(t1, t2)
            }
        }
        is TyArr -> {
            if (t2 !is TyArr) {
                throw CannotUnify(t1, t2)
            }
            unify(t1.from, t2.from)
            unify(t1.to, t2.to)
        }
        is TyGen -> {
            if (t2 !is TyGen || t2.id != t1.id) {
                throw CannotUnify(t1, t2)
            }
        }
        is TyVar -> {
            error("Not reachable")
        }
    }
}

fun UnificationContext.unifyTyVar(t1: TvRef, t2: Type) {
    if (t2 is TyVar) {
        if (t1 !== t2.ref) {
            t1.link(t2)
        }
        return
    }


    if (t1.occursIn(t2)) {
        error("OccursCheck failed for $t1 on $t2")
    }

    t1.link(t2)
}

fun UnificationContext.solveAll() {
    for (c in constraints) {
        Log.d { "Solving $c" }
        try {
            unify(c.t1, c.t2)
        } catch (e: CannotUnify) {
            Log.e { "Cannot unify -- u = $debugRepr" }
            throw e
        }
    }
}

// endregion

// region Type environment
private typealias TyMap = Map<Ident, Type>

private class TyEnv private constructor(val parent: TyEnv?, val here: TyMap) {
    companion object {
        fun topLevel(env: TyMap) = TyEnv(null, env)
    }

    fun extend(inner: TyMap) = TyEnv(this, inner)

    operator fun get(id: Ident): Type? {
        for (scope in scopes()) {
            return scope[id] ?: continue
        }
        return null
    }

    fun freeTyVars(): Set<Int> {
        val r = mutableSetOf<Int>()
        // XXX(perf)
        for (scope in scopes().dropLast(1)) {
            // ^ HACK(perf): The last is the topmost env which shouldn't contain any freeTyVars.
            for (v in scope.values) {
                r.addAll(v.freeTyVars)
            }
        }
        return r
    }

    fun scopes(): List<TyMap> {
        val out = mutableListOf<TyMap>()
        var env: TyEnv? = this
        while (env != null) {
            out += env.here
            env = env.parent
        }
        return out
    }
}

// endregion

// region Extension methods for other modules

private fun mkTyArr(args: List<Type>, resTy: Type): Type = args.foldRight(resTy, ::TyArr)

// endregion
