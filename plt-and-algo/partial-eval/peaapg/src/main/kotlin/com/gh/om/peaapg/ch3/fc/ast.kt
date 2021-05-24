package com.gh.om.peaapg.ch3.fc

data class Program(val args: List<String>, val bbs: List<BB>)

inline class Label(val name: String)

data class BB(val label: Label, val body: List<Assign>, val last: Jump)

data class Assign(val name: String, val expr: Expr)

sealed class Jump {
    data class Goto(val label: Label) : Jump()
    data class Return(val expr: Expr) : Jump()
    data class If(val cond: Expr, val ifTrue: Label, val ifFalse: Label) : Jump()
}

sealed class Expr {
    data class I(val value: Int) : Expr()
    data class Var(val name: String) : Expr()
    data class Symbol(val name: String) : Expr()
    data class BOp(val op: BinaryRator, val lhs: Expr, val rhs: Expr) : Expr()
    data class UOp(val op: UnaryRator, val arg: Expr) : Expr()
    data class MkList(val args: List<Expr>) : Expr()
}

enum class BinaryRator {
    Add,
    Sub,
    Mul,
    Eqv,
    Cons;
}

enum class UnaryRator {
    Head,
    Tail;
}