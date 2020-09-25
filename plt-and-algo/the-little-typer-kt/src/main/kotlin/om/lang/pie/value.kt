package om.lang.pie

sealed class PiValue {
    object Zero : PiValue()
    data class Succ(val pred: PiValue) : PiValue()
    data class Lam(val arg: String, val env: Env, val body: PiExpr) : PiValue()
    data class Neu(val neu: PiNeu) : PiValue()

    companion object {
        fun fromInt(i: Int): PiValue {
            var res: PiValue = Zero
            repeat(i) {
                res = Succ(res)
            }
            return res
        }
    }
}

sealed class PiType : PiValue() {
    object Nat : PiType()
    object Set : PiType()
    data class Arr(val arg: PiType, val res: PiType) : PiType()
}

sealed class PiNeu {
    data class Var(val name: String, val id: Int, val type: PiType): PiNeu()
    data class Ap(val rator: PiNeu, val rand: PiValue) : PiNeu()
}

val PiValue.asType: PiType
    get() = this as PiType
