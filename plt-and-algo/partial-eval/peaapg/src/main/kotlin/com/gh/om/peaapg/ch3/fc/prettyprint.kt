package com.gh.om.peaapg.ch3.fc

import java.lang.StringBuilder

fun Program.ppr(): String {
    val sb = StringBuilder()
    pprTo(sb)
    return sb.toString()
}

fun Expr.ppr(): String {
    val sb = StringBuilder()
    pprTo(sb)
    return sb.toString()
}

fun Value.ppr(): String {
    val sb = StringBuilder()
    pprTo(sb)
    return sb.toString()
}

private fun Program.pprTo(sb: StringBuilder) {
    sb.append("read")
    if (args.isNotEmpty()) {
        sb.append(" ")
    }
    sb.append(args.joinToString(", "))
    sb.appendLine(";")

    bbs.forEach { it.pprTo(sb) }
}

private fun BB.pprTo(sb: StringBuilder) {
    sb.append(label.name)
    sb.appendLine(":")

    body.forEach {
        sb.append(" ".repeat(INDENT))
        it.pprTo(sb)
        sb.appendLine(";")
    }

    sb.append(" ".repeat(INDENT))
    last.pprTo(sb)
    sb.appendLine(";")
}

private fun Jump.pprTo(sb: StringBuilder) {
    when (this) {
        is Jump.Goto -> {
            sb.append("goto ")
            sb.append(label.name)
        }
        is Jump.If -> {
            sb.append("if ")
            cond.pprTo(sb)
            sb.append(" goto ")
            sb.append(ifTrue.name)
            sb.append(" else ")
            sb.append(ifFalse.name)
        }
        is Jump.Return -> {
            sb.append("return ")
            expr.pprTo(sb)
        }
    }
}

private fun Assign.pprTo(sb: StringBuilder) {
    sb.append(name)
    sb.append(" = ")
    expr.pprTo(sb)
}

private fun Expr.pprTo(sb: StringBuilder) {
    when (this) {
        is Expr.BOp -> {
            lhs.pprTo(sb, true)
            sb.append(" ")
            op.pprTo(sb)
            sb.append(" ")
            rhs.pprTo(sb, autoAddParen = true)
        }
        is Expr.I -> sb.append(value)
        is Expr.Symbol -> {
            sb.append("'")
            sb.append(value)
        }
        is Expr.UOp -> {
            op.pprTo(sb)
            sb.append(" ")
            arg.pprTo(sb, true)
        }
        is Expr.Var -> sb.append(name)
        is Expr.MkList -> {
            sb.append("[")
            args.forEachIndexed { index, arg ->
                if (index != 0) {
                    sb.append(", ")
                }
                arg.pprTo(sb)
            }
            sb.append("]")
        }
    }
}

private fun Expr.pprTo(sb: StringBuilder, autoAddParen: Boolean) {
    maybeAddParen(sb, autoAddParen && isComplex) {
        pprTo(sb)
    }
}

private fun UnaryRator.pprTo(sb: StringBuilder) {
    val op = when (this) {
        UnaryRator.Head -> "head"
        UnaryRator.Tail -> "tail"
    }
    sb.append(op)
}

private fun maybeAddParen(sb: StringBuilder, addParen: Boolean, over: () -> Unit) {
    if (addParen) {
        sb.append("(")
    }
    over()
    if (addParen) {
        sb.append(")")
    }
}

private fun BinaryRator.pprTo(sb: StringBuilder) {
    val op = when (this) {
        BinaryRator.Add -> "+"
        BinaryRator.Sub -> "-"
        BinaryRator.Mul -> "*"
        BinaryRator.Eqv -> "=="
        BinaryRator.Cons -> "::"
    }
    sb.append(op)
}

private val Expr.isAtom: Boolean
    get() = when (this) {
        is Expr.I, is Expr.Symbol, is Expr.Var, is Expr.MkList -> true
        is Expr.BOp, is Expr.UOp -> false
    }

private val Expr.isComplex: Boolean
    get() = !isAtom

private fun Value.pprTo(sb: StringBuilder) {
    when (this) {
        is Value.Cons -> pprTo(sb, true)
        is Value.I -> sb.append(value)
        is Value.Symbol -> {
            sb.append("'")
            sb.append(name)
        }
        Value.Nil -> sb.append("[]")
    }
}

private tailrec fun Value.Cons.pprTo(sb: StringBuilder, isFirst: Boolean) {
    if (isFirst) {
        sb.append("[")
    } else {
        sb.append(", ")
    }
    head.pprTo(sb)

    when (tail) {
        is Value.Cons -> tail.pprTo(sb, false)
        is Value.Nil -> sb.append("]")
        else -> {
            sb.append("; ")
            tail.pprTo(sb)
            sb.append("]")
        }
    }
}

private const val INDENT = 4