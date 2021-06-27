package com.gh.om.iueoc

// Closed world AST

sealed class Expr

typealias AnnExpr = Ann<SourceLoc, Expr>

sealed class ExprVar : Expr() {
    data class V(val name: String) : ExprVar()
    data class I(val value: Int) : ExprVar()
    data class Let(val vs: List<String>, val es: List<AnnExpr>, val body: AnnExpr) : ExprVar()
}
