package com.gh.om.iueoc

import kotlinx.collections.immutable.PersistentMap
import kotlinx.collections.immutable.persistentMapOf
import kotlinx.collections.immutable.putAll

sealed class Value {
    data class I(val value: Int) : Value()
    data class B(val value: Boolean) : Value()
    data class Sym(val name: String) : Value()
    data class Lam(val env: Env, val args: List<AnnS<String>>, val body: List<AnnExpr>) : Value()
    data class Box(var value: Value): Value()
}

val Value.asBoolean: Boolean
    get() = this != Value.B(false)

interface Interp {
    fun interp(eAnn: AnnExpr, env: Env): Trampoline<Value>
}

fun Interp.interpToplevel(eAnn: AnnExpr): Value {
    return interp(eAnn, persistentMapOf()).value()
}

private typealias Env = PersistentMap<String, Value>

private fun Interp.seq(es: List<AnnExpr>, env: Env): Trampoline<Value> {
    for (e in es.take(es.size - 1)) {
        interp(e, env).value()
    }
    return interp(es.last(), env)
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
            val value = env[e.name]
            EocError.ensure(value != null, sourceLoc) {
                "Unbound variable: ${e.name}, all vars: ${env.keys}"
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
            val newEnv = when (e.kind) {
                LetKind.Basic -> {
                    val vs = e.es.map { interp(it, env).value() }
                    env.putAll(e.vs.map { it.unwrap }.zip(vs))
                }
                LetKind.Seq -> {
                    e.vs.zip(e.es).fold(env) { currentEnv, ve ->
                        val (k, rhs) = ve
                        val value = interp(rhs, currentEnv).value()
                        currentEnv.put(k.unwrap, value)
                    }
                }
                LetKind.Rec -> {
                    EocError.todo(sourceLoc, "letrec not yet implemented")
                }
            }
            seq(e.body, newEnv)
        }
        is ExprOp.Op -> {
            val op = e.op.unwrap
            val values = e.args.map { interp(it, env).value() }
            when (op) {
                PrimOp.FxAdd ->
                    binaryIntOp(e, values) { x, y -> Value.I(x + y) }
                PrimOp.FxLessThan ->
                    binaryIntOp(e, values) { x, y -> Value.B(x < y) }
                PrimOp.BoxMk ->
                    Tr.pure(Value.Box(values.first()))
                PrimOp.BoxGet -> {
                    val box = values.first()
                    EocError.ensure(box is Value.Box, sourceLoc) {
                        "Not a box: $box"
                    }
                    Tr.pure(box.value)
                }
                PrimOp.BoxSet -> {
                    val (box, newValue) = values
                    EocError.ensure(box is Value.Box, sourceLoc) {
                        "Not a box: $box"
                    }
                    val oldValue = box.value
                    box.value = newValue
                    Tr.pure(oldValue)
                }
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
            val newEnv = f.env.putAll(f.args.map { it.unwrap }.zip(argValues))
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

open class InterpImp : InterpOp() {
    override fun interp(eAnn: AnnExpr, env: Env): Trampoline<Value> {
        val eop = eAnn.unwrap
        return if (eop is ExprImp) {
            interpInternal(eop, eAnn.ann, env)
        } else {
            super.interp(eAnn, env)
        }
    }

    private fun interpInternal(e: ExprImp, sourceLoc: SourceLoc, env: Env): Trampoline<Value> = when (e) {
        is ExprImp.While -> {
            while (interp(e.cond, env).value().asBoolean) {
                seq(e.body, env).value()
            }
            Tr.pure(Value.Sym("#undefined"))
        }
    }
}
