package com.gh.om.peaapg.ch3.fc

import java.lang.Exception
import kotlin.reflect.KClass

sealed class Value {
    data class I(val value: Int) : Value()
    data class Symbol(val name: String) : Value()
    data class Cons(val head: Value, val tail: Value) : Value()
    object Nil: Value()
}

fun Program.execute(argValues: List<Value>): Value {
    // Build label to program map first
    val bbMap = bbs.associateBy(BB::label)

    // Build store and populate the args
    val store = args.zip(argValues).toMap(mutableMapOf())

    return execute(bbs.first(), bbMap, store)
}

fun Expr.eval(store: Store): Value = when (this) {
    is Expr.BOp -> {
        when (op) {
            BinaryRator.Add -> doIntBOp(this, store) { l, r -> l + r }
            BinaryRator.Sub -> doIntBOp(this, store) { l, r -> l - r }
            BinaryRator.Eqv -> doBOp<Value>(this, store) { l, r -> toValue(doEqv(l, r)) }
            BinaryRator.Mul -> doIntBOp(this, store) { l, r -> l * r }
            BinaryRator.Cons -> doBOp<Value>(this, store) { l, r -> Value.Cons(l, r) }
        }
    }
    is Expr.I -> Value.I(value)
    is Expr.Symbol -> Value.Symbol(name)
    is Expr.UOp -> {
        when (op) {
            UnaryRator.Head -> evalAs<Value.Cons>(arg, store).head
            UnaryRator.Tail -> evalAs<Value.Cons>(arg, store).tail
        }
    }
    is Expr.Var -> store[name] ?: throw Stuck.UnboundVariable(name).intoException()
    is Expr.MkList -> {
        val values = args.map { it.eval(store) }
        values.foldRight(Value.Nil, Value::Cons)
    }
}

typealias Store = Map<String, Value>
typealias MutableStore = MutableMap<String, Value>

class StuckException(val why: Stuck) : Exception(why.message)

sealed class Stuck {
    val message: String
        get() = when (this) {
            is IncorrectType -> "$expr evaluates to $result which is not a ${type.simpleName}"
            is UnboundVariable -> "Unbound variable: $varName"
        }

    fun intoException() = StuckException(this)

    class UnboundVariable(val varName: String) : Stuck()
    class IncorrectType(val expr: Expr, val result: Value, val type: KClass<*>) : Stuck()
}

val Value.isTrue: Boolean
    get() = !isFalsy

val Value.isFalsy: Boolean
    get() = this is Value.I && value == 0

private tailrec fun execute(bb: BB, bbMap: Map<Label, BB>, store: MutableStore): Value {
    for (stmt in bb.body) {
        store[stmt.name] = stmt.expr.eval(store)
    }
    val nextLabel = when (val jump = bb.last) {
        is Jump.Goto -> jump.label
        is Jump.If -> {
            if (jump.cond.eval(store).isTrue) {
                jump.ifTrue
            } else {
                jump.ifFalse
            }
        }
        is Jump.Return -> return jump.expr.eval(store)
    }
    val nextBB = requireNotNull(bbMap[nextLabel]) { "Label $nextLabel not found" }
    return execute(nextBB, bbMap, store)
}

private inline fun <reified A: Value> doBOp(e: Expr.BOp, store: Store, op: (A, A) -> Value): Value {
    return op(evalAs(e.lhs, store), evalAs(e.rhs, store))
}

private inline fun doIntBOp(e: Expr.BOp, store: Store, op: (Int, Int) -> Int): Value {
    return doBOp<Value.I>(e, store) { lv, rv ->
        Value.I(op(lv.value, rv.value))
    }
}

private inline fun <reified A: Value> evalAs(e: Expr, store: Store): A {
    val v = e.eval(store)
    if (v !is A) {
        throw Stuck.IncorrectType(e, v, A::class).intoException()
    }
    return v
}

private fun doEqv(x: Value, y: Value): Boolean {
    // Rely on the generated equals method on data classes
    return x == y
}

private fun toValue(b: Boolean): Value {
    return Value.I(if (b) {
        1
    } else {
        0
    })
}

fun Value.toHost(): Any {
    when (this) {
        is Value.Cons -> TODO()
        is Value.I -> TODO()
        Value.Nil -> TODO()
        is Value.Symbol -> TODO()
    }
}

fun fromHost(v: Any): Value {
    TODO()
}
