package om.lang.pie

sealed class TopLevel
data class Claim(val name: String, val type: PiExpr) : TopLevel()
data class Define(val name: String, val value: PiExpr) : TopLevel()

sealed class PiExpr {
    object Zero : PiExpr()
    data class Succ(val pred: PiExpr) : PiExpr()
    data class NatLit(val value: Int) : PiExpr()

    data class Var(val name: String) : PiExpr()
    data class The(val type: PiExpr, val body: PiExpr) : PiExpr()

    data class Lam(val args: List<String>, val body: PiExpr) : PiExpr()
    data class App(val f: PiExpr, val args: List<PiExpr>) : PiExpr()

    object Nat : PiExpr()
    object Set : PiExpr()
    data class Arr(val args: List<PiExpr>, val res: PiExpr) : PiExpr()
}


