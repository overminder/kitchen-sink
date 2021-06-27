package com.gh.om.iueoc

import com.gh.om.iueoc.SexprGrammar.getValue
import com.gh.om.iueoc.SexprGrammar.provideDelegate
import com.github.h0tk3y.betterParse.combinators.map
import com.github.h0tk3y.betterParse.combinators.oneOrMore
import com.github.h0tk3y.betterParse.combinators.optional
import com.github.h0tk3y.betterParse.combinators.or
import com.github.h0tk3y.betterParse.combinators.times
import com.github.h0tk3y.betterParse.combinators.unaryMinus
import com.github.h0tk3y.betterParse.combinators.use
import com.github.h0tk3y.betterParse.combinators.zeroOrMore
import com.github.h0tk3y.betterParse.grammar.Grammar
import com.github.h0tk3y.betterParse.grammar.parser
import com.github.h0tk3y.betterParse.lexer.TokenMatch
import com.github.h0tk3y.betterParse.lexer.literalToken
import com.github.h0tk3y.betterParse.lexer.noneMatched
import com.github.h0tk3y.betterParse.lexer.regexToken
import com.github.h0tk3y.betterParse.parser.Parser

// Convert strings to sexprs, and also ~`!@#$%^&*_-+=<>,.'?/

// S: source information
sealed class Sexpr<out S> {
    data class Sym<S>(val name: String) : Sexpr<S>()
    data class Fx<S>(val value: Int) : Sexpr<S>()
    data class Flo<S>(val value: Double) : Sexpr<S>()
    data class Cons<S>(val cars: List<AnnSexpr<S>>, val cdr: AnnSexpr<S>?, val paren: ParenShape) : Sexpr<S>()
    data class Quote<S>(val kind: QuoteKind, val value: AnnSexpr<S>): Sexpr<S>()
    class Nil(val paren: ParenShape) : Sexpr<Nothing>()

    enum class ParenShape(val start: String, val end: String) {
        Round("(", ")"),
        Square("[", "]"),
        Curly("{", "}")
    }

    enum class QuoteKind(val repr: String) {
        Quote("'"),
        QuasiQuote("`"),
        Unquote(","),
        UnquoteSplicing(",@"),
    }
}

// Source annotations

data class Ann<out A, out B>(val ann: A, val unwrap: B)

typealias AnnSexpr<A> = Ann<A, Sexpr<A>>
typealias SexprWithLoc = AnnSexpr<SourceLoc>

data class SourceLoc(val col: Int, val row: Int, val offset: Int)

private fun TokenMatch.annotate(expr: Sexpr<SourceLoc>): SexprWithLoc = Ann(SourceLoc(column, row, offset), expr)
private val TokenMatch.parenShape: Sexpr.ParenShape
    get() = when (text.first()) {
        '(' -> Sexpr.ParenShape.Round
        '[' -> Sexpr.ParenShape.Square
        '{' -> Sexpr.ParenShape.Curly
        else -> error("Not starting with a parenthesis: $text")
    }

// Reader
object SexprGrammar : Grammar<SexprWithLoc>() {
    // Tokens
    val tokLparen by literalToken("(")
    val tokRparen by literalToken(")")
    val tokLbracket by literalToken("[")
    val tokRbracket by literalToken("]")
    val tokLbrace by literalToken("{")
    val tokRbrace by literalToken("}")
    val tokInt by regexToken("-?\\d+")
    val tokId by regexToken("[a-zA-Z0-9~!@#$%^&*_\\-+=<>.|\\\\?/\"]+")
    val tokQuote by literalToken("'")
    val tokQuasiquote by literalToken("`")
    val tokUnquoteSplicing by literalToken(",@")
    val tokUnquote by literalToken(",")
    val tokDot by literalToken(".")
    val tokWs by regexToken("\\s+", ignore = true)

    // Helpers
    inline fun <reified A> paren(noinline x: () -> Parser<A>) = tokLparen * parser(x) * -tokRparen
    inline fun <reified A> bracket(noinline x: () -> Parser<A>) = tokLbracket * parser(x) * -tokRbracket
    inline fun <reified A> brace(noinline x: () -> Parser<A>) = tokLbrace * parser(x) * -tokRbrace
    inline fun <reified A> anyWrapped(noinline x: () -> Parser<A>) = paren(x) or bracket(x) or brace(x)

    // Terms
    object P {
        val fx = tokInt.map { it.annotate(Sexpr.Fx(it.text.toInt())) }
        val sym = tokId.map { it.annotate(Sexpr.Sym(it.text)) }
        val nil = ((tokLparen * -tokRparen) or (tokLbracket * -tokRbracket) or (tokLbrace * -tokRbrace)).map {
            it.annotate(Sexpr.Nil(it.parenShape))
        }
        val pair = anyWrapped {
            oneOrMore(sexpr) * optional(-tokDot * sexpr)
        }.map { (paren, body) ->
            paren.annotate(Sexpr.Cons(body.t1, body.t2, paren.parenShape))
        }
        val quoted = ((tokQuote or tokQuasiquote or tokUnquote or tokUnquoteSplicing) * parser(::sexpr)).map {
            val kind = when (it.t1.text) {
                "'" -> Sexpr.QuoteKind.Quote
                "`" -> Sexpr.QuoteKind.QuasiQuote
                "," -> Sexpr.QuoteKind.Unquote
                ",@" -> Sexpr.QuoteKind.UnquoteSplicing
                else -> error("Not a quote: ${it.t1.text}")
            }
            it.t1.annotate(Sexpr.Quote(kind, it.t2))
        }
        val sexpr: Parser<SexprWithLoc> = pair or nil or quoted or fx or sym
        val sexprs = oneOrMore(sexpr)
    }

    override val rootParser = P.sexpr
}

// Pretty printer

// Print without annotations.
fun Sexpr<*>.ppr(): String = when (this) {
    is Sexpr.Cons -> {
        val head = cars.joinToString(separator = " ") { it.unwrap.ppr() }
        val body = cdr?.let {
            head + " . " + it.unwrap.ppr()
        } ?: head
        paren.start + body + paren.end
    }
    is Sexpr.Flo -> value.toString()
    is Sexpr.Fx -> value.toString()
    is Sexpr.Nil -> paren.start + paren.end
    is Sexpr.Sym -> name
    is Sexpr.Quote -> kind.repr + value.unwrap.ppr()
}
