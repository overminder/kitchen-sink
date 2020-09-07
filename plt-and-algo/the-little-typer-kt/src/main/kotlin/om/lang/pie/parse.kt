package om.lang.pie

import java.io.EOFException
import java.lang.NumberFormatException

sealed class SExpr {
    companion object {
        fun of(s: Any): SExpr {
            return when (s) {
                is String -> SSymbol(s)
                is SExpr -> s
                is List<*> -> SList(s.map { of(requireNotNull(it)) })
                else -> error("Unexpected: $s")
            }
        }
    }
}

data class SSymbol(val s: String) : SExpr()
data class SList(val ss: List<SExpr>) : SExpr() {
    companion object {
        fun of(vararg ss: Any): SList {
            return SList(ss.map(SExpr::of))
        }
    }
}

fun SExpr.ppr(): String {
    return when (this) {
        is SSymbol -> s
        is SList -> ss.joinToString(separator = " ", prefix = "(", postfix = ")", transform = SExpr::ppr)
    }
}

fun PiExpr.ppr(): String {
    return ProgramToSExpr.expr(this).ppr()
}

fun TopLevel.ppr(): String {
    return ProgramToSExpr.topLevel(this).ppr()
}

object ProgramToSExpr {
    fun expr(e: PiExpr): SExpr {
        return when (e) {
            PiExpr.Zero -> SSymbol("zero")
            // | Note that the conversion for sexpr->expr is not injective, e.g. both "1" and
            // "(add1 0)" are converted into S(O).
            is PiExpr.Succ -> SList.of("add1", expr(e.pred))
            PiExpr.Nat -> SSymbol("Nat")
            PiExpr.Set -> SSymbol("Set")
            is PiExpr.Var -> SSymbol(e.name)
            is PiExpr.Lam -> SList.of(
                "lam",
                SList(e.args.map(::SSymbol)),
                expr(e.body)
            )
            is PiExpr.Arr -> {
                val rs = mutableListOf<SExpr>(SSymbol("->"))
                e.args.mapTo(rs, ::expr)
                rs += expr(e.res)
                SList(rs)
            }
            is PiExpr.NatLit -> SSymbol(e.value.toString())
            is PiExpr.The -> SList.of("the", expr(e.type), expr(e.body))
            is PiExpr.App -> SList(e.args.mapTo(mutableListOf(expr(e.f)), ::expr))
        }
    }

    fun topLevel(t: TopLevel): SExpr {
        return when (t) {
            is Claim -> SList.of("claim", t.name, expr(t.type))
            is Define -> SList.of("define", t.name, expr(t.value))
        }
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

    private fun expectSymbolList(s: SExpr): List<String> {
        if (s !is SList) {
            error("Not a list: $s")
        }

        return s.ss.map(::expectSymbol)
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

    fun expr(se: SExpr): PiExpr {
        return when (se) {
            is SSymbol -> {
                val s = se.s
                try {
                    val ival = Integer.valueOf(s)
                    return PiExpr.NatLit(ival)
                } catch (ignored: NumberFormatException) {
                }

                when (se.s) {
                    "Nat" -> PiExpr.Nat
                    "Set" -> PiExpr.Set
                    "zero" -> PiExpr.Zero
                    else -> PiExpr.Var(se.s)
                }
            }
            is SList -> {
                val head = se.ss.firstOrNull() ?: error("Empty list")
                if (head is SSymbol) {
                    builtinApp(se)?.let {
                        return it
                    }
                }
                val exprs = se.ss.map(::expr)
                PiExpr.App(exprs.first(), exprs.drop(1))
            }
        }
    }

    private fun builtinApp(se: SList): PiExpr? {
        val (head, rest) = expectListAndHead(se)
        return when (head) {
            "add1" -> {
                assert(rest.size == 1)
                PiExpr.Succ(expr(rest[0]))
            }
            "lam" -> {
                assert(rest.size == 2)
                val (args, body) = rest
                PiExpr.Lam(expectSymbolList(args), expr(body))
            }
            "->" -> {
                // (-> a b c) is the same as a -> b -> c
                assert(rest.size >= 2)
                val resTy = expr(rest.last())
                val argTypes = rest.subList(0, rest.size - 1).map(::expr)
                PiExpr.Arr(argTypes, resTy)
            }
            else -> null
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
            if (c.isWhitespace()) {
                continue
            }
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