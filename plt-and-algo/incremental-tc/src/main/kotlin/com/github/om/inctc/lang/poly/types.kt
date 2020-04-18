package com.github.om.inctc.lang.poly

sealed class TypeOrScheme
sealed class Type: TypeOrScheme()

object TyInt: Type() {
    override fun toString(): String = "int"
}
object TyBool: Type() {
    override fun toString(): String = "bool"
}
// Not yet specialized.
data class TyVar(val id: Int): Type() {
    override fun toString(): String {
        return "t$id"
    }
}
data class TyArr(val from: Type, val to: Type): Type() {
    override fun toString(): String {
        return "$from -> $to"
    }
}

// Scheme: let-generalized polymorphic type

data class TyScm(val args: List<TyVar>, val body: Type): TypeOrScheme() {
    override fun toString(): String {
        val bindings = args.joinToString()
        return "∀$bindings.$body"
    }
}

val TypeOrScheme.freeTyVars: Sequence<TyVar>
    get() = when (this) {
        is TyVar -> sequenceOf(this)
        is TyArr -> from.freeTyVars + to.freeTyVars
        is TyScm -> body.freeTyVars - args
        else -> emptySequence()
    }

val TypeOrScheme.hasFreeTyVars: Boolean
    get() = freeTyVars.firstOrNull() != null

