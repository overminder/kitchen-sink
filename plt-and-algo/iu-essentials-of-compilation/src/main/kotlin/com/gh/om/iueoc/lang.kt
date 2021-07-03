package com.gh.om.iueoc

// Closed world Scheme-ish AST

sealed class Expr

typealias AnnExpr = Ann<SourceLoc, Expr>

sealed class ExprVar : Expr() {
    data class V(val name: String) : ExprVar()
    data class I(val value: Int) : ExprVar()
    data class B(val value: Boolean) : ExprVar()
    data class Sym(val name: String) : ExprVar()
}

// Single inheritance, or a la carte?
sealed class ExprOp : Expr() {
    data class Let(val vs: List<String>, val es: List<AnnExpr>, val body: AnnExpr) : ExprOp()
    data class If(val cond: AnnExpr, val ifT: AnnExpr, val ifF: AnnExpr) : ExprOp()
    data class Op(val op: AnnS<PrimOp>, val args: List<AnnExpr>) : ExprOp()
}

enum class PrimOp(val symbol: String) {
    IntAdd("#I.+"),
    IntLessThan("#I.<"),
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
                val annCar = se.cars.first()
                val rest = se.cars.drop(1)
                val carSym = annCar.unwrap as? Sexpr.Sym
                EocError.ensure(carSym != null, annCar.ann) {
                    "Must be symbol"
                }
                when (val sym = carSym.name) {
                    "if" -> {
                        EocError.ensure(rest.size == 3, annSe.ann) {
                            "If should take 3 arguments"
                        }
                        val (cond, ifT, ifF) = rest
                        ExprOp.If(toExpr(cond), toExpr(ifT), toExpr(ifF))
                    }
                    "let" -> {
                        EocError.ensure(rest.size == 2, annSe.ann) {
                            "Let should take 2 arguments"
                        }
                        val (kvsAnn, bodyAnn) = rest
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
                            k.name to toExpr(vAnn)
                        }.unzip()
                        ExprOp.Let(vs, es, toExpr(bodyAnn))
                    }
                    else -> {
                        primDescrs.firstNotNullOfOrNull { pd ->
                            if (sym == pd.symbol && rest.size == pd.argc) {
                                ExprOp.Op(annCar.wrap(pd.op), rest.map(::toExpr))
                            } else {
                                null
                            }
                        } ?: throw EocError(annSe.ann, "Unknown application")
                    }
                }
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

    private class PrimDescr(val op: PrimOp, val argc: Int, val symbol: String = op.symbol)
    private val primDescrs = listOf(
        PrimDescr(PrimOp.IntAdd, 2),
        PrimDescr(PrimOp.IntLessThan, 2),
    )
}
