package om.lang.pie

// Elaborated core expressions

sealed class PiCore {
    object Zero : PiCore()
    data class Succ(val pred: PiCore) : PiCore()
    data class NatLit(val value: Int) : PiCore()
    data class RecNat(val type: PiCore, val nat: PiCore, val base: PiCore, val step: PiCore) : PiCore()

    data class Var(val name: String) : PiCore()
    data class The(val type: PiCore, val body: PiCore) : PiCore()

    data class Lam(val arg: String, val body: PiCore) : PiCore()
    data class App(val f: PiCore, val args: PiCore) : PiCore()

    object Nat : PiCore()
    object Set : PiCore()
    data class Arr(val arg: PiCore, val res: PiCore) : PiCore()
}