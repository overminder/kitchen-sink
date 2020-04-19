package com.github.om.inctc.lang.poly

sealed class TypeOrScheme
sealed class Type: TypeOrScheme()

object TyInt: Type() {
    override fun toString(): String = "int"
}

object TyBool: Type() {
    override fun toString(): String = "bool"
}

// Not yet generalized.
data class TyVar(val ref: TvRef): Type() {
    override fun toString(): String = ref.toString()

    companion object {
        fun unbound(id: Int) = TyVar(TvRef.unbound(id))
    }
}

data class TyGen(val id: Int): Type() {
    override fun toString(): String {
        return "t$id"
    }
}

class TvRef(private var content_: Type?, private var id_: Int?) {
    val content: Type?
        get() = content_

    val id: Int?
        get() = id_

    override fun toString(): String {
        return if (content != null) {
            "ref($content)"
        } else {
            "tv$id"
        }
    }

    fun prunedOr(ty: Type): Type {
        content_?.let {
            val p = it.pruned
            return link(p)
        }
        return ty
    }

    fun link(to: Type): Type {
        content_ = to
        id_ = null
        return to
    }

    companion object {
        fun unbound(id: Int): TvRef = TvRef(content_ = null, id_ = id)
    }
}

data class TyArr(val from: Type, val to: Type): Type() {
    override fun toString(): String {
        return "$from -> $to"
    }
}

val Type.freeTyVars: Sequence<Int>
    get() = when (this) {
        is TyVar -> listOfNotNull(ref.id).asSequence()
        is TyArr -> from.freeTyVars + to.freeTyVars
        else -> emptySequence()
    }

val Type.allTyVars: Sequence<TyVar>
    get() = when (this) {
        is TyVar -> sequenceOf(this) + (ref.content?.allTyVars ?: emptySequence())
        is TyArr -> from.allTyVars + to.allTyVars
        else -> emptySequence()
    }

val Type.hasTyVars: Boolean
    get() = allTyVars.firstOrNull() != null


// region Substitution

internal val Type.pruned: Type
    get() = when (this) {
        is TyVar -> ref.prunedOr(this)
        else -> this
    }

internal fun TvRef.occursIn(t: Type): Boolean =
    when (val tp = t.pruned) {
        is TyVar -> this === tp.ref
        is TyArr -> occursIn(tp.from) || occursIn(tp.to)
        else -> false
    }

internal fun Type.inst(instTyGen: () -> Type): Type {
    val subst = mutableMapOf<Int, Type>()
    fun go(t: Type): Type =
        when (t) {
            is TyGen -> subst.getOrPut(t.id, instTyGen)
            is TyVar -> t.ref.content?.let(::go) ?: t
            is TyArr -> TyArr(go(t.from), go(t.to))
            else -> t
        }
    return go(this)
}

// Instantiate tyGens to normalized form.
internal fun Type.normTyGen(): Type {
    val u = UniqueGen()
    return inst { TyGen(u.next()) }
}

internal fun Type.gen(env: Set<Int>): Type {
    fun go(t: Type): Type =
        when (t) {
            is TyVar -> {
                val id = t.ref.id
                val content = t.ref.content
                if (id != null && !env.contains(id)) {
                    TyGen(id)
                } else {
                    content?.gen(env) ?: t
                }
            }
            is TyArr -> TyArr(go(t.from), go(t.to))
            else -> t
        }
    return go(this)
}

// endregion

