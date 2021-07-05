package com.gh.om.iueoc

sealed class Value {
    data class I(val value: Int) : Value()
    data class B(val value: Boolean) : Value()
    data class Sym(val name: String) : Value()
    data class Lam(val env: Env, val args: List<AnnS<String>>, val body: List<AnnExpr>) : Value()
}

val Value.asBoolean: Boolean
    get() = this != Value.B(false)

interface Interp {
    fun interp(eAnn: AnnExpr, env: Env): Trampoline<Value>
}

fun Interp.interpToplevel(eAnn: AnnExpr): Value {
    return interp(eAnn, emptyList()).value()
}

typealias Env = List<Pair<String, Value>>

private fun Env.assocv(key: String): Value? {
    for ((k, v) in this) {
        if (k == key) {
            return v
        }
    }
    return null
}

// Open to allow extension
open class InterpVar : Interp {
    override fun interp(eAnn: AnnExpr, env: Env): Trampoline<Value> {
        val e = eAnn.unwrap
        EocError.ensure(e is ExprVar, eAnn.ann) {
            "Not a ExprVar"
        }
        return Tr.pure(interpInternal(e, eAnn.ann, env))
    }

    private fun interpInternal(e: ExprVar, sourceLoc: SourceLoc, env: Env): Value = when (e) {
        is ExprVar.I -> Value.I(e.value)
        is ExprVar.V -> {
            val value = env.assocv(e.name)
            EocError.ensure(value != null, sourceLoc) {
                "Unbound variable: ${e.name}"
            }
            value
        }
        is ExprVar.B -> Value.B(e.value)
        is ExprVar.Sym -> Value.Sym(e.name)
    }
}

open class InterpOp : InterpVar() {
    override fun interp(eAnn: AnnExpr, env: Env): Trampoline<Value> {
        val eop = eAnn.unwrap
        return if (eop is ExprOp) {
            interpInternal(eop, eAnn.ann, env)
        } else {
            super.interp(eAnn, env)
        }
    }

    private fun interpInternal(e: ExprOp, sourceLoc: SourceLoc, env: Env): Trampoline<Value> = when (e) {
        is ExprOp.If -> {
            val cond = interp(e.cond, env).value()
            val next = if (cond.asBoolean) {
                e.ifT
            } else {
                e.ifF
            }
            Tr.more { interp(next, env) }
        }
        is ExprOp.Let -> {
            val vs = e.es.map { interp(it, env).value() }
            val newEnv = e.vs.map { it.unwrap }.zip(vs) + env
            Tr.more { interp(e.body, newEnv) }
        }
        is ExprOp.Op -> {
            val op = e.op.unwrap
            val values = e.args.map { interp(it, env).value() }
            when (op) {
                PrimOp.FxAdd ->
                    binaryIntOp(e, values) { x, y -> Value.I(x + y) }
                PrimOp.FxLessThan ->
                    binaryIntOp(e, values) { x, y -> Value.B(x < y) }
            }
        }
    }

    private fun <R> binaryIntOp(e: ExprOp.Op, argValues: List<Value>, func: (Int, Int) -> R): Trampoline<R> {
        val symbol = e.op.unwrap.symbol
        val (lhs, rhs) = e.args
        val (lhsV, rhsV) = argValues
        EocError.ensure(lhsV is Value.I, lhs.ann) {
            "$symbol takes int value, not $lhsV"
        }
        EocError.ensure(rhsV is Value.I, rhs.ann) {
            "$symbol takes int value, not $rhsV"
        }
        return Tr.pure(func(lhsV.value, rhsV.value))
    }
}

open class InterpLam : InterpOp() {
    override fun interp(eAnn: AnnExpr, env: Env): Trampoline<Value> {
        val eop = eAnn.unwrap
        return if (eop is ExprLam) {
            interpInternal(eop, eAnn.ann, env)
        } else {
            super.interp(eAnn, env)
        }
    }

    private fun interpInternal(e: ExprLam, sourceLoc: SourceLoc, env: Env): Trampoline<Value> = when (e) {
        is ExprLam.Ap -> {
            val f = interp(e.f, env).value()
            EocError.ensure(f is Value.Lam, e.f.ann) {
                "Not a function: $f"
            }
            // Evaluate from left to right.
            val argValues = e.args.map { interp(it, env).value() }
            EocError.ensure(f.args.size == argValues.size, sourceLoc) {
                "Argument count mismatch: expecting ${f.args.size}, got ${argValues.size}"
            }
            val newEnv = f.args.map { it.unwrap }.zip(argValues) + f.env
            val bodySize = f.body.size
            Tr.more {
                // Throw away values
                f.body.take(bodySize - 1).forEach {
                    interp(it, newEnv).value()
                }
                interp(f.body.last(), newEnv)
            }
        }
        is ExprLam.Lam -> {
            Tr.pure(Value.Lam(env, e.args, e.body))
        }
    }
}
