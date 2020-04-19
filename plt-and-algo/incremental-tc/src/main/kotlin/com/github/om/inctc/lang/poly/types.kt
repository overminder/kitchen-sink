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

val TyScm.isTrivial: Boolean
    get() = args.isEmpty()

fun TyScm.alphaEq(o: TyScm): Boolean {
    if (this === o) return true
    if (isTrivial) return o.isTrivial

    val ug = UniqueGen()

    if (args.size != o.args.size) {
        return false
    }

    val fresh = List(args.size) { ug.freshTyVar() }
    return body.applyFrom(args.zip(fresh).toMap()) == o.body.applyFrom(o.args.zip(fresh).toMap())
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


// region Substitution
internal typealias Subst = Map<TyVar, Type>
internal typealias MutableSubst = MutableMap<TyVar, Type>

/*
// Not sure if this works
private fun <A: TypeOrScheme> A.applyFrom(subst: Subst): A = when (this) {
    is TyVar -> this
    else -> this
}
 */

internal fun Type.applyFrom(subst: Subst): Type = when (this) {
    is TyVar -> subst.getOrDefault(this, this)
    is TyArr -> TyArr(from.applyFrom(subst), to.applyFrom(subst))
    else -> this
}

internal fun TyScm.applyFrom(subst: Subst): TyScm {
    // XXX(perf)
    return TyScm(args, body.applyFrom(subst - args))
}

internal fun Subst.applyFrom(subst: Subst): Subst {
    // XXX(perf)
    return mapValues { it.value.applyFrom(subst) } + subst
}

internal fun MutableSubst.applyFrom(subst: Subst) {
    entries.forEach {
        it.setValue(it.value.applyFrom(subst))
    }

    this += subst
}

// endregion

