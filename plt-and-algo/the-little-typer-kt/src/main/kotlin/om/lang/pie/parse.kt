package om.lang.pie

import java.io.EOFException
import java.lang.NumberFormatException

sealed class SExpr
data class SSymbol(val s: String): SExpr()
data class SList(val ss: List<SExpr>): SExpr()

fun SExpr.ppr(): String {
    return when (this) {
        is SSymbol -> s
        is SList -> ss.joinToString(separator = " ", prefix = "(", postfix = ")", transform = SExpr::ppr)
    }
}

object SExprToProgram {
    fun topLevel(se: SExpr): TopLevel {
        val (head, rest) = expectListAndHead(se)
        return when (head) {
            "define" -> {
                assert(rest.size == 2)
                val (name, value) = rest
                Define(expectSymbol(name), expr(value))
            }
            "claim" -> {
                assert(rest.size == 2)
                val (name, value) = rest
                Claim(expectSymbol(name), expr(value))
            }
            else -> error("Unknown toplevel syntax: $head")
        }
    }

    private fun expectSymbol(s: SExpr): String {
        return (s as? SSymbol)?.s ?: error("Not a symbol: $s")
    }

    private fun expectListAndHead(s: SExpr): Pair<String, List<SExpr>> {
        if (s is SList) {
            val ss = s.ss
            val head = ss.firstOrNull() ?: error("Empty list")
            val rest = ss.drop(1)
            return expectSymbol(head) to rest
        }
        error("Not a list: $s")
    }

    fun expr(se: SExpr): Expr {
        return when (se) {
            is SSymbol -> {
                val s = se.s
                try {
                    val ival = Integer.valueOf(s)
                    var nat: Expr = Zero
                    repeat(ival) {
                        nat = Succ(nat)
                    }
                    return nat
                } catch (ignored: NumberFormatException) {
                }

                when (se.s) {
                    "Nat" -> Nat
                    "Set" -> Set
                    else -> error("Unknown symbol: $s")
                }
            }
            is SList -> {
                val (head, rest) = expectListAndHead(se)
                when (head) {
                    "add1" -> {
                        assert(rest.size == 1)
                        Succ(expr(rest[0]))
                    }
                    else -> error("Unexpected head: $head")
                }
            }
        }
    }
}

class SExprParser private constructor(private val s: String) {
    private var ix: Int = 0

    companion object {
        fun parseOne(source: String) = SExprParser(source).parseOne()
        fun parseMany(source: String) = SExprParser(source).parseMany()
    }

    fun parseMany(): List<SExpr> {
        val res = mutableListOf<SExpr>()
        while (true) {
            val c = next() ?: return res
            ix -= 1
            res += parseOne()
        }
    }

    fun parseOne(): SExpr {
        while (true) {
            val c = next() ?: throw EOFException()

            if (c.isWhitespace()) {
                continue
            }

            when (c) {
                '(' -> {
                    val es = mutableListOf<SExpr>()
                    while (true) {
                        val n = next() ?: throw EOFException()
                        if (n == ')') {
                            return SList(es)
                        } else {
                            ix -= 1
                            es += parseOne()
                        }
                    }
                }
                else -> {
                    val sb = StringBuilder()
                    sb.append(c)
                    while (true) {
                        val nc = next() ?: break
                        if (nc.isWhitespace() || nc == ')' || nc == '(') {
                            ix -= 1
                            break
                        }
                        sb.append(nc)
                    }
                    return SSymbol(sb.toString())
                }
            }
        }
    }

    private fun next(): Char? {
        return s.getOrNull(ix)?.also {
            ix += 1
        }
    }
}