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
    data class Let(val vs: List<AnnS<String>>, val es: List<AnnExpr>, val body: List<AnnExpr>, val kind: LetKind) : ExprOp()
    data class If(val cond: AnnExpr, val ifT: AnnExpr, val ifF: AnnExpr) : ExprOp()
    data class Op(val op: AnnS<PrimOp>, val args: List<AnnExpr>) : ExprOp()
}

sealed class ExprLam : Expr() {
    // Name can be inferred during sexpr->expr
    data class Lam(val name: String? = null, val args: List<AnnS<String>>, val body: List<AnnExpr>) : ExprLam()
    data class Ap(val f: AnnExpr, val args: List<AnnExpr>) : ExprLam()
}

sealed class ExprImp : Expr() {
    data class While(val cond: AnnExpr, val body: List<AnnExpr>) : ExprImp()
    data class Set(val name: AnnS<String>, val value: AnnExpr) : ExprImp()
}

enum class LetKind {
    Basic,
    Seq,
    Rec,
}

enum class PrimOp(val symbol: String) {
    // (Fx, Fx) -> Fx
    FxAdd("#fx+"),
    FxSub("#fx-"),
    // (Fx, Fx) -> Bool
    FxLessThan("#fx<"),

    // any -> Box
    BoxMk("#box"),
    BoxGet("#box-get"),
    BoxSet("#box-set!"),

    Opaque("#opaque"),
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
        "let", "let*", "letrec" -> {
            val kind = when (carSym) {
                "let" -> LetKind.Basic
                "let*" -> LetKind.Seq
                "letrec" -> LetKind.Rec
                else -> error("Not reachable")
            }
            EocError.ensure(cdrs.size >= 2, root.ann) {
                "Let should be in the form of (let (bindings...) body...)"
            }
            val kvsAnn = cdrs.first()
            val body = cdrs.drop(1)
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
                bindingAnn.wrap(k.name) to tryAssignName(k.name, toExpr(vAnn))
            }.unzip()
            ExprOp.Let(vs, es, body.map(::toExpr), kind)
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
            ExprLam.Lam(null, argNames, bodyE)
        }
        "while" -> {
            EocError.ensure(cdrs.size >= 2, root.ann) {
                "While should be in the form of (while cond body...)"
            }

            val cond = toExpr(cdrs.first())
            val body = cdrs.drop(1).map(::toExpr)
            ExprImp.While(cond, body)
        }
        "set!" -> {
            EocError.ensure(cdrs.size == 2, root.ann) {
                "Set! should be in the form of (set! name expr)"
            }
            val (name, value) = cdrs
            EocError.ensure(name.unwrap is Sexpr.Sym, name.ann) {
                "Set! var name must be a symbol"
            }
            ExprImp.Set(name.wrap(name.unwrap.name), toExpr(value))
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

    private fun tryAssignName(name: String, annE: AnnExpr): AnnExpr {
        return if (annE.unwrap is ExprLam.Lam) {
            annE.wrap(annE.unwrap.copy(name = name))
        } else {
            annE
        }
    }

    private class PrimDescr(val op: PrimOp, val argc: Int, val symbol: String = op.symbol)
    private val primDescrs = listOf(
        PrimDescr(PrimOp.FxAdd, 2),
        PrimDescr(PrimOp.FxSub, 2),
        PrimDescr(PrimOp.FxLessThan, 2),
        PrimDescr(PrimOp.BoxMk, 1),
        PrimDescr(PrimOp.BoxGet, 1),
        PrimDescr(PrimOp.BoxSet, 2),
        PrimDescr(PrimOp.Opaque, 1),
    )
}
