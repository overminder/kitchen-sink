package om.lang.pie

object Elab {
    fun asType(e: PiExpr): PiCore {
        when (e) {
            PiExpr.Zero -> TODO()
            is PiExpr.Succ -> TODO()
            is PiExpr.NatLit -> TODO()
            is PiExpr.RecNat -> TODO()
            is PiExpr.Var -> TODO()
            is PiExpr.The -> TODO()
            is PiExpr.Lam -> TODO()
            is PiExpr.App -> TODO()
            PiExpr.Nat -> TODO()
            PiExpr.Set -> TODO()
            is PiExpr.Arr -> TODO()
        }
    }
}