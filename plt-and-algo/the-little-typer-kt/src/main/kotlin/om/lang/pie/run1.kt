package om.lang.pie

/**
 * First try: types are not yet dependent.
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

object TypeChecking {
    val emptyCtx: Ctx = ConsList.nil()

    fun program(ts: List<TopLevel>) {
        var ctx = emptyCtx
        for (t in ts) {
            when (t) {
                is Claim -> {
                    val type = evalSimpleType(t.type)
                    ctx = ctx.cons(t.name to CtxEntry.Claimed(type))
                }
                is Define -> {
                    val type = requireNotNull(ctx.assocv(t.name)?.type)
                    check(t.value, type, ctx)
                }
            }
        }
    }

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
        }
    }

    fun check(e: PiExpr, type: PiType, ctx: Ctx) {
        val synthType = synth(e, ctx)
        if (synthType != null) {
            require(alphaEq(synthType, type)) { "$e is expected to be $type, but is actuall $synthType" }
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

