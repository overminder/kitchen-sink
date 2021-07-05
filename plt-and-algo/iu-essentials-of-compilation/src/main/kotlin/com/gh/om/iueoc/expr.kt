package com.gh.om.iueoc

// Closed world Scheme-ish AST

sealed class Expr

typealias AnnExpr = AnnS<Expr>

sealed class ExprVar : Expr() {
    data class V(val name: String) : ExprVar()
    data class I(val value: Int) : ExprVar()
    data class B(val value: Boolean) : ExprVar()
    data class Sym(val name: String) : ExprVar()
}

// Single inheritance, or a la carte?
sealed class ExprOp : Expr() {
    data class Let(val vs: List<AnnS<String>>, val es: List<AnnExpr>, val body: AnnExpr) : ExprOp()
    data class If(val cond: AnnExpr, val ifT: AnnExpr, val ifF: AnnExpr) : ExprOp()
    data class Op(val op: AnnS<PrimOp>, val args: List<AnnExpr>) : ExprOp()
}

sealed class ExprLam : Expr() {
    data class Lam(val args: List<AnnS<String>>, val body: List<AnnExpr>) : ExprLam()
    data class Ap(val f: AnnExpr, val args: List<AnnExpr>) : ExprLam()
}

enum class PrimOp(val symbol: String) {
    // (Fx, Fx) -> Fx
    FxAdd("#fx+"),
    // (Fx, Fx) -> Bool
    FxLessThan("#fx<"),
}

// Sexpr -> Expr

object SexprToExpr {
    // Can this also be a la carte?
    fun toExpr(annSe: SexprWithLoc): AnnExpr {
        val e = when (val se = annSe.unwrap) {
            is Sexpr.Cons -> {
                if (se.cdr != null) {
                    throw EocError(annSe.ann, "Unhandled dotted tail")
                }
                val car = se.cars.first()
                val rest = se.cars.drop(1)
                val carSym = car.unwrap as? Sexpr.Sym
                carSym?.let {
                    trySpecialForm(it.name, car.ann, rest, annSe)
                } ?: toApply(car, rest)
            }
            is Sexpr.Flo -> throw EocError(annSe.ann, "Flonum not implemented yet")
            is Sexpr.Fx -> ExprVar.I(se.value)
            is Sexpr.Nil -> throw EocError(annSe.ann, "Empty application")
            is Sexpr.Quote -> {
                val quotedAnn = se.value
                val quoted = quotedAnn.unwrap
                when (se.kind) {
                    Sexpr.QuoteKind.Quote -> {
                        when (quoted) {
                            is Sexpr.Fx -> ExprVar.I(quoted.value)
                            is Sexpr.Sym -> ExprVar.Sym(quoted.name)
                            else -> throw EocError(annSe.ann, "(${se.kind} $quoted) not implemented yet")
                        }
                    }
                    Sexpr.QuoteKind.QuasiQuote,
                    Sexpr.QuoteKind.Unquote,
                    Sexpr.QuoteKind.UnquoteSplicing -> throw EocError(annSe.ann, "${se.kind} not implemented yet")
                }
            }
            is Sexpr.Sym -> when (val name = se.name) {
                "#t" -> ExprVar.B(true)
                "#f" -> ExprVar.B(false)
                else -> ExprVar.V(name)
            }
        }
        return annSe.wrap(e)
    }

    private fun trySpecialForm(
        carSym: String,
        carAnn: SourceLoc,
        cdrs: List<AnnSexpr<SourceLoc>>,
        root: SexprWithLoc,
    ): Expr? = when (carSym) {
        "if" -> {
            EocError.ensure(cdrs.size == 3, root.ann) {
                "If should take 3 arguments"
            }
            val (cond, ifT, ifF) = cdrs
            ExprOp.If(toExpr(cond), toExpr(ifT), toExpr(ifF))
        }
        "let" -> {
            EocError.ensure(cdrs.size == 2, root.ann) {
                "Let should take 2 arguments"
            }
            val (kvsAnn, bodyAnn) = cdrs
            val kvs = kvsAnn.unwrap
            EocError.ensure(kvs is Sexpr.Cons && kvs.cdr == null, kvsAnn.ann) {
                "Let bindings should be a list"
            }
            val (vs, es) = kvs.cars.map { bindingAnn ->
                val binding = bindingAnn.unwrap
                EocError.ensure(
                    binding is Sexpr.Cons && binding.cdr == null && binding.cars.size == 2,
                    bindingAnn.ann
                ) {
                    "Let binding should be in the form of [k v]"
                }
                val (kAnn, vAnn) = binding.cars
                val k = kAnn.unwrap
                EocError.ensure(k is Sexpr.Sym, kAnn.ann) {
                    "In let binding [k v], k should be a sym"
                }
                bindingAnn.wrap(k.name) to toExpr(vAnn)
            }.unzip()
            ExprOp.Let(vs, es, toExpr(bodyAnn))
        }
        "lambda" -> {
            EocError.ensure(cdrs.size >= 2, root.ann) {
                "Lambda should be in the form of (lambda args body...)"
            }

            val (argsAnn, args) = cdrs.first()
            // Varargs not implemented for now.
            EocError.ensure(args is Sexpr.Cons && args.cdr == null, argsAnn) {
                "Lambda args should be list"
            }
            val argNames = args.cars.map {
                EocError.ensure(it.unwrap is Sexpr.Sym, it.ann) {
                    "Lambda arg should be symbol"
                }
                it.wrap(it.unwrap.name)
            }

            val bodyE = cdrs.drop(1).map(::toExpr)
            ExprLam.Lam(argNames, bodyE)
        }
        else -> {
            primDescrs.firstNotNullOfOrNull { pd ->
                if (carSym == pd.symbol && cdrs.size == pd.argc) {
                    ExprOp.Op(carAnn.wrap(pd.op), cdrs.map(::toExpr))
                } else {
                    null
                }
            }
        }
    }

    private fun toApply(f: SexprWithLoc, args: List<SexprWithLoc>): Expr {
        val fE = toExpr(f)
        val argsE = args.map(::toExpr)
        return ExprLam.Ap(fE, argsE)
    }

    private class PrimDescr(val op: PrimOp, val argc: Int, val symbol: String = op.symbol)
    private val primDescrs = listOf(
        PrimDescr(PrimOp.FxAdd, 2),
        PrimDescr(PrimOp.FxLessThan, 2),
    )
}
