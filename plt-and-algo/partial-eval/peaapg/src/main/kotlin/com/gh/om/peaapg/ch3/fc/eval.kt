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
    val store = MutableStore()
    store.populate(args, argValues)

    return execute(bbs.first(), bbMap, store)
}

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

private abstract class Store {
    abstract operator fun get(name: String): Value?
}

private class MutableStore : Store() {
    private val values = mutableListOf<Value>()
    private val nameToSlot = mutableMapOf<String, Int>()
    private var nextSlot = 0

    override operator fun get(name: String): Value? {
        val slot = nameToSlot[name] ?: return null
        return values[slot]
    }

    operator fun set(name: String, value: Value) {
        val slot = nameToSlot.getOrPut(name) { nextSlot++ }
        if (slot >= values.size) {
            require(slot == values.size)
            values.add(value)
        } else {
            values[slot] = value
        }
    }

    fun populate(names: List<String>, values: List<Value>) {
        require(names.size == values.size)
        names.zip(values).forEach { (name, value) -> set(name, value) }
    }
}

private tailrec fun execute(bb: BB, bbMap: Map<Label, BB>, store: MutableStore): Value {
    for (stmt in bb.body) {
        store[stmt.name] = eval(stmt.expr, store)
    }
    val nextLabel = when (val jump = bb.last) {
        is Jump.Goto -> jump.label
        is Jump.If -> {
            if (eval(jump.cond, store).isTrue) {
                jump.ifTrue
            } else {
                jump.ifFalse
            }
        }
        is Jump.Return -> {
            return eval(jump.expr, store)
        }
    }
    val nextBB = requireNotNull(bbMap[nextLabel]) { "Label $nextLabel not found" }
    return execute(nextBB, bbMap, store)
}

private val Value.isTrue: Boolean
    get() = !isFalsy

private val Value.isFalsy: Boolean
    get() = this is Value.I && value == 0

private fun eval(expr: Expr, store: Store): Value = when (expr) {
    is Expr.BOp -> {
        when (expr.op) {
            BinaryRator.Add -> doIntBOp(expr, store) { l, r -> l + r }
            BinaryRator.Sub -> doIntBOp(expr, store) { l, r -> l - r }
            BinaryRator.Eqv -> doBOp<Value>(expr, store) { l, r -> toValue(doEqv(l, r)) }
            BinaryRator.Mul -> doIntBOp(expr, store) { l, r -> l * r }
            BinaryRator.Cons -> doBOp<Value>(expr, store) { l, r -> Value.Cons(l, r) }
        }
    }
    is Expr.I -> Value.I(expr.value)
    is Expr.Symbol -> Value.Symbol(expr.value)
    is Expr.UOp -> {
        when (expr.op) {
            UnaryRator.Head -> evalAs<Value.Cons>(expr.arg, store).head
            UnaryRator.Tail -> evalAs<Value.Cons>(expr.arg, store).tail
        }
    }
    is Expr.Var -> store[expr.name] ?: throw Stuck.UnboundVariable(expr.name).intoException()
    is Expr.MkList -> {
        val values = expr.args.map { eval(it, store) }
        values.foldRight(Value.Nil, Value::Cons)
    }
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
    val v = eval(e, store)
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
