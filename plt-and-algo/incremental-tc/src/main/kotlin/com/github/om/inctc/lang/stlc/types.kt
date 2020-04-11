package com.github.om.inctc.lang.stlc

sealed class Type
object TyInt: Type() {
    override fun toString(): String = "TyInt"
}
object TyBool: Type() {
    override fun toString(): String = "TyBool"
}
// Not yet specialized.
data class TyVar(val id: Int): Type()
data class TyArr(val from: Type, val to: Type): Type()

val Type.tyVars: Sequence<TyVar>
    get() = when (this) {
        is TyVar -> sequenceOf(this)
        is TyArr -> from.tyVars + to.tyVars
        else -> emptySequence()
    }

val Type.hasTyVars: Boolean
    get() = tyVars.firstOrNull() != null
