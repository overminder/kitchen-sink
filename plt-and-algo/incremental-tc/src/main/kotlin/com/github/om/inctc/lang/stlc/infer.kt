package com.github.om.inctc.lang.stlc

// STLC inference is relative simpl.
// H-M OTOH requires defining type schemes (https://www.cl.cam.ac.uk/teaching/1415/L28/type-inference.pdf)

// region Global type checker context

sealed class InferenceError: Throwable()
data class CannotUnify(val t1: Type, val t2: Type): InferenceError()

class TypeChecker(
    internal val rCtx: ResolutionContext
) {
    internal val ordering = rCtx.topoSortedModules.value
    internal val bindingOrdering = rCtx.moduleDeclSccs.value
    internal val moduleTyCtxs = mutableMapOf<ModuleName, ModuleTypeContext>()

    fun inferredType(defSite: FqName): TyScm {
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
    internal val nameToType = mutableMapOf<Ident, TyScm>()

    internal val uStack = mutableListOf(UnificationContext(uniqGen))

    internal fun TyScm.instantiate(): Type {
        val subst = args.associateWith { u.mkTyVar() }
        return body.applyFrom(subst)
    }

    internal fun Type.generalize(ftvsFromEnv: Sequence<TyVar>): TyScm {
        val ftv = freeTyVars.toMutableSet()
        ftv -= ftvsFromEnv
        return TyScm(ftv.toList(), this)
    }

    internal fun Type.closeOver(): TyScm = TyScm(emptyList(), this)

    internal val Decl.identThatNeedsSubst: Ident?
        get() = when (this) {
            is Define -> ident
            else -> null
        }
}

internal val ModuleTypeContext.u: UnificationContext
    get() = requireNotNull(uStack.lastOrNull())

internal fun <A: Any> ModuleTypeContext.withNewUCtx(f: () -> A): A {
    uStack += u.mkChild()
    val r = f()
    uStack.removeLast()
    return r
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
    val needSubst = if (scc.size == 1) {
        val id = scc.first()
        val decl = declFromName(id)
        val isRec = isSelfRecursive(id)
        if (isRec) {
            makeTyVarPlaceholderForDecl(decl)
        }
        inferTopLevelDecl(decl)
        listOfNotNull(decl.identThatNeedsSubst)
    } else {
        val decls = scc.map(::declFromName)
        decls.forEach(::makeTyVarPlaceholderForDecl)
        decls.forEach {
            inferTopLevelDecl(it)
        }
        decls.mapNotNull { it.identThatNeedsSubst }
    }

    u.solveAll()
    for (name in needSubst) {
        val tv = requireNotNull(nameToType[name]).body
        nameToType += name to tv.applyFrom(u.substitutions).closeOver()
    }
}

fun ModuleTypeContext.makeTyVarPlaceholderForDecl(d: Decl) {
    when (d) {
        is Import -> {
            nameToType += d.ident to global.inferredType(d.defSite)
        }
        is Define -> {
            // Not sure if this works...
            val tv = u.mkTyVar()
            val originalTy = nameToType.put(d.ident, tv.closeOver())
            require(originalTy == null) {
                "${d.ident} already had a type: $originalTy"
            }
        }
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
        nameToType[d.ident] = bodyTy.closeOver()
        if (placeholderTy != null) {
            // This is for recursive decls.
            // HACK: placeholder is always a tyVar closedOver [].
            u.deferUnify(placeholderTy.body, bodyTy)
        }
        Unit
    }
}

private fun ModuleTypeContext.lookupVar(i: Ident, env: TyEnv): Type {
    val ty = requireNotNull(env[i]) { "Unbound var: ${i.name}" }
    val ity = ty.instantiate()
    // println("lookup($i): found $ty, instantiate as $ity")
    return ity
}

private fun ModuleTypeContext.infer(e: Exp, env: TyEnv): Type = when (e) {
    is Var -> lookupVar(e.ident, env)
    is Lam -> {
        val argTys = e.args.map { u.mkTyVar() }
        // This line was originally "accidentally quadratic" ;D -- We used to do Map.plus here, so this ends up
        // allocating a new map with all the entries. And since env can be huge...
        val newEnv = env.extend(e.args.zip(argTys.map { it.closeOver() }).toMap(mutableMapOf()))
        // Probably need to make a local subst as well.
        val bodyTy = infer(e.body, newEnv)
        // Probably need to run subst on arg. And check no tyVar leakage.
        mkTyArr(argTys, bodyTy)
    }
    is Let -> {
        val newBindings = mutableMapOf<Ident, TyScm>()
        val letEnv = env.extend(newBindings)
        for ((ident, rhs) in e.bindings) {
            val ty = withNewUCtx {
                val ty = infer(rhs, letEnv)
                // println("Let: infer as $ty")
                u.solveAll()
                val subst = u.substitutions
                // XXX(perf) also is this correct?
                letEnv.applyFrom(subst)
                ty.applyFrom(subst).generalize(letEnv.freeTyVars())
            }
            // println("Let: generalize as $ty")

            newBindings += ident to ty
        }
        infer(e.body, letEnv)
    }
    is LitI -> TyInt
    is If -> {
        val condTy = infer(e.cond, env)
        val thenTy = infer(e.then, env)
        val elseTy = infer(e.else_, env)
        u.deferUnify(condTy, TyBool)
        u.deferUnify(thenTy, elseTy)
        thenTy
    }
    is App -> {
        val argTy = infer(e.arg, env)
        val resTy = u.mkTyVar()
        val funcTy = infer(e.func, env)
        u.deferUnify(funcTy, TyArr(argTy, resTy))
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
        u.deferUnify(leftTy, ratorTy)
        u.deferUnify(rightTy, ratorTy)
        resTy
    }
}

fun ModuleTypeContext.lintInferredTypes(names: Iterable<Ident>) {
    names.forEach {
        val ty = requireNotNull(nameToType[it])
        require(!ty.hasFreeTyVars) {
            "$it: $ty still has free type vars! Current u: ${u.debugRepr}"
        }
    }
}
// endregion

// region Unification

class UniqueGen(private var nextValue: Int = 1) {
    fun next(): Int = nextValue++
}

class UnificationContext(private val uniqGen: UniqueGen = UniqueGen()) {
    internal val substitutions = mutableMapOf<TyVar, Type>()
    internal val constraints = mutableListOf<Pair<Type, Type>>()

    fun mkTyVar(): TyVar = TyVar(uniqGen.next())

    internal fun clear() {
        substitutions.clear()
    }

    val debugRepr: String
        get() {
            return "subst: $substitutions, cs: $constraints"
        }

    fun mkChild(): UnificationContext = UnificationContext(uniqGen)
}

// Not used for now, but this might be a useful short-circuiting subst.
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

// Does a quick check, but defer heavy works to the final solver.
fun UnificationContext.deferUnify(t1: Type, t2: Type) {
    if (t1 == t2) {
        return
    }
    constraints += t1 to t2
}

fun UnificationContext.unify(t1: Type, t2: Type): Subst {
    if (t1 === t2) {
        return emptyMap()
    }
    if (t1 is TyVar) {
        return unifyTyVar(t1, t2)
    }
    if (t2 is TyVar) {
        return unifyTyVar(t2, t1)
    }
    return when (t1) {
        is TyInt -> {
            if (t2 !is TyInt) {
                throw CannotUnify(t1, t2)
            }
            emptyMap()
        }
        is TyBool -> {
            if (t2 !is TyBool) {
                throw CannotUnify(t1, t2)
            }
            emptyMap()
        }
        is TyArr -> {
            if (t2 !is TyArr) {
                throw CannotUnify(t1, t2)
            }
            val s1 = unify(t1.from, t2.from)
            val s2 = unify(t1.to.applyFrom(s1), t2.to.applyFrom(s1))
            s1.applyFrom(s2)
        }
        is TyVar -> {
            error("Not reachable")
        }
        else -> {
            error("Shouldn't unify $t1 with $t2")
        }
    }
}

fun UnificationContext.unifyTyVar(t1: TyVar, t2: Type): Subst = when (t2) {
    t1 -> emptyMap()
    else -> {
        if (t2.containsFree(t1)) {
            error("OccursCheck failed for $t1 on $t2")
        } else {
            mapOf(t1 to t2)
        }
    }
}

private fun Type.containsFree(tv: TyVar): Boolean = freeTyVars.contains(tv)

fun UnificationContext.solveAll() {
    for ((t1, t2) in constraints) {
        // println("solve $t1 = $t2, subst = $substitutions")
        val newSubst = try {
            unify(t1.applyFrom(substitutions), t2.applyFrom(substitutions))
        } catch (e: CannotUnify) {
            println("Cannot unify -- u = $debugRepr")
            throw e
        }
        substitutions.applyFrom(newSubst)
    }
}

// endregion

// region Type environment
private typealias TyMap = Map<Ident, TyScm>
private typealias MutableTyMap = MutableMap<Ident, TyScm>

private class TyEnv private constructor(val parent: TyEnv?, val here: MutableTyMap) {
    companion object {
        fun topLevel(env: MutableTyMap) = TyEnv(null, env)
    }

    fun extend(inner: MutableTyMap) = TyEnv(this, inner)

    operator fun get(id: Ident): TyScm? {
        for (scope in scopes()) {
            return scope[id] ?: continue
        }
        return null
    }

    fun freeTyVars(): Sequence<TyVar> {
        // XXX(perf)
        return scopes().asSequence().flatMap {
            it.values.asSequence().flatMap {
                it.freeTyVars
            }
        }
    }

    fun scopes(): List<MutableTyMap> {
        val out = mutableListOf<MutableTyMap>()
        var env: TyEnv? = this
        while (env != null) {
            out += env.here
            env = env.parent
        }
        return out
    }
}

private fun TyEnv.applyFrom(subst: Subst) {
    scopes().forEach {
        it.entries.forEach {
            it.setValue(it.value.applyFrom(subst))
        }
    }
}

// endregion

// region Substitution
private typealias Subst = Map<TyVar, Type>
private typealias MutableSubst = MutableMap<TyVar, Type>

/*
// Not sure if this works
private fun <A: TypeOrScheme> A.applyFrom(subst: Subst): A = when (this) {
    is TyVar -> this
    else -> this
}
 */

private fun Type.applyFrom(subst: Subst): Type = when (this) {
    is TyVar -> subst.getOrDefault(this, this)
    is TyArr -> TyArr(from.applyFrom(subst), to.applyFrom(subst))
    else -> this
}

private fun TyScm.applyFrom(subst: Subst): TyScm {
    // XXX(perf)
    return TyScm(args, body.applyFrom(subst - args))
}

private fun Subst.applyFrom(subst: Subst): Subst {
    // XXX(perf)
    return mapValues { it.value.applyFrom(subst) } + subst
}

private fun MutableSubst.applyFrom(subst: Subst) {
    entries.forEach {
        it.setValue(it.value.applyFrom(subst))
    }

    this += subst
}
// endregion

// region Extension methods for other modules

private fun mkTyArr(args: List<Type>, resTy: Type): Type = args.foldRight(resTy, ::TyArr)

// endregion
