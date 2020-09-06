package om.lang.pie

sealed class TopLevel
data class Claim(val name: String, val type: Expr) : TopLevel()
data class Define(val name: String, val value: Expr) : TopLevel()

sealed class Expr

object Zero : Expr()
data class Succ(val pred: Expr) : Expr()

// Marker interface on expr.
interface Type

object Nat : Expr(), Type
object Set : Expr(), Type
