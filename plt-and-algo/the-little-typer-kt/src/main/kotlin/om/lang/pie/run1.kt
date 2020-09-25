package om.lang.pie

/**
 * First try: types are not yet dependent -- terms at
 */

sealed class CtxEntry {
    abstract val type: PiType

    // Local binding
    data class HasType(override val type: PiType) : CtxEntry()

    // Global binding: claimed but not yet defined
    data class Claimed(override val type: PiType) : CtxEntry()

    // Global binding: defined
    data class Defined(override val type: PiType, val value: PiValue) : CtxEntry()
}

typealias Env = ConsList<Pair<String, PiValue>>
typealias Ctx = ConsList<Pair<String, CtxEntry>>

object Eval {
    fun program(ts: List<TopLevel>): List<PiValue> {
        var ctx = TypeChecking.emptyCtx
        val outputs = mutableListOf<PiValue>()
        for (t in ts) {
            when (t) {
                is Claim -> {
                    val type = TypeChecking.evalSimpleType(t.type)
                    ctx = ctx.cons(t.name to CtxEntry.Claimed(type))
                }
                is Define -> {
                    val type = requireNotNull(ctx.assocv(t.name)?.type)
                    TypeChecking.check(t.value, type, ctx)
                    val value = eval(t.value, ctxToEnv(ctx))
                    ctx = ctx.cons(t.name to CtxEntry.Defined(type, value))
                }
                is Output -> {
                    outputs += eval(t.value, ctxToEnv(ctx))
                }
            }
        }
        return outputs
    }

    fun ctxToEnv(ctx: Ctx): Env {
        return ctx.mapNotNull {
            (it.second as? CtxEntry.Defined)?.let { def ->
                it.first to def.value
            }
        }
    }

    fun eval(e: PiExpr, env: Env): PiValue {
        return when (e) {
            PiExpr.Zero -> PiValue.Zero
            is PiExpr.Succ -> PiValue.Succ(eval(e.pred, env))
            is PiExpr.NatLit -> PiValue.fromInt(e.value)
            is PiExpr.RecNat -> {
                var nat = eval(e.nat, env)
                var res: PiValue = eval(e.base, env)
                val step = eval(e.step, env)
                while (nat is PiValue.Succ) {
                    // XXX Which order?
                    res = doApp(doApp(step, nat), res)
                    nat = nat.pred
                }
                require(nat is PiValue.Zero)
                res
            }
            is PiExpr.Var -> requireNotNull(env.assocv(e.name))
            is PiExpr.The -> eval(e.body, env)
            is PiExpr.Lam -> {
                val arg = e.args.first()
                if (e.args.size <= 1) {
                    PiValue.Lam(arg, env, e.body)
                } else {
                    PiValue.Lam(arg, env, PiExpr.Lam(e.args.drop(1), e.body))
                }
            }
            is PiExpr.App -> {
                // XXX We probably want a lazy semantics
                val f = eval(e.f, env)
                val args = e.args.map { eval(it, env) }
                args.fold(f, ::doApp)
            }
            PiExpr.Nat -> PiType.Nat
            PiExpr.Set -> PiType.Set
            is PiExpr.Arr -> {
                val args = e.args.map { eval(it, env).asType }
                val res = eval(e.res, env).asType
                args.foldRight(res, PiType::Arr)
            }
        }
    }

    fun doApp(f: PiValue, arg: PiValue): PiValue {
        require(f is PiValue.Lam)
        val env = f.env.cons(f.arg to arg)
        return eval(f.body, env)
    }
}

object TypeChecking {
    val emptyCtx: Ctx = ConsList.nil()

    fun synth(e: PiExpr, ctx: Ctx): PiType? {
        return when (e) {
            is PiExpr.Var -> ctx.assocv(e.name)?.type ?: error("Undefined var: ${e.name}")
            PiExpr.Zero -> PiType.Nat
            is PiExpr.Succ -> {
                check(e.pred, PiType.Nat, ctx)
                PiType.Nat
            }
            is PiExpr.NatLit -> PiType.Nat
            // Can't synth a lambda.
            is PiExpr.Lam -> null
            is PiExpr.The -> {
                // We actually need to eval the type here. But for now let's do it in a simpler way.
                val type = evalSimpleType(e.type)
                check(e.body, type, ctx)
                type
            }
            PiExpr.Nat -> PiType.Set
            PiExpr.Set -> PiType.Set
            is PiExpr.Arr -> PiType.Set
            is PiExpr.App -> {
                val fType = synth(e.f, ctx) ?: return null
                e.args.fold(fType) { acc, arg ->
                    require(acc is PiType.Arr)
                    check(arg, acc.arg, ctx)
                    acc.res
                }
            }
            is PiExpr.RecNat -> {
                val type = evalSimpleType(e.type)
                check(e.nat, PiType.Nat, ctx)
                check(e.base, type, ctx)
                check(e.step, PiType.Arr(PiType.Nat, PiType.Arr(type, type)), ctx)
                type
            }
        }
    }

    fun check(e: PiExpr, type: PiType, ctx: Ctx) {
        val synthType = synth(e, ctx)
        if (synthType != null) {
            require(alphaEq(synthType, type)) { "$e is expected to be $type, but is actually $synthType" }
            return
        }

        when (e) {
            is PiExpr.Lam -> {
                val (ctx, type) = e.args.fold(ctx to type) { (ctx, type), arg ->
                    require(type is PiType.Arr)
                    ctx.cons(arg to CtxEntry.HasType(type.arg)) to type.res
                }
                check(e.body, type, ctx)
            }
            else -> error("Can't type check $e")
        }
    }

    private fun alphaEq(x: PiType, y: PiType): Boolean {
        // TODO
        return x == y
    }

    fun evalSimpleType(e: PiExpr): PiType {
        return when (e) {
            is PiExpr.Nat -> PiType.Nat
            is PiExpr.Arr -> e.args.foldRight(evalSimpleType(e.res)) { argTy, acc ->
                PiType.Arr(evalSimpleType(argTy), acc)
            }
            else -> error("Can't evaluate complex type: $e")
        }
    }
}

