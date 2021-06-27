package com.gh.om.iueoc

sealed class Value {
    data class I(val value: Int) : Value()
}

interface Interp {
    fun interp(e0: Expr, env: Env): Trampoline<Value>
}

typealias Env = List<Pair<String, Value>>

private fun Env.assocv(key: String): Value? {
    for ((k, v) in this)  {
        if (k == key) {
            return v
        }
    }
    return null
}

// Open to allow extension
open class InterpVar : Interp {
    override fun interp(e0: Expr, env: Env): Trampoline<Value> = interpInternal(e0 as ExprVar, env)

    private fun interpInternal(e: ExprVar, env: Env) = when (e) {
        is ExprVar.I -> Tr.pure(Value.I(e.value))
        is ExprVar.V -> {
            val value = env.assocv(e.name)
            requireNotNull(value) {
                "Unbound variable: ${e.name}"
            }
            Tr.pure(value)
        }
        is ExprVar.Let -> TODO()
    }
}
