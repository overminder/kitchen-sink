package com.gh.om.peaapg.ch3.fc

import com.github.h0tk3y.betterParse.combinators.leftAssociative
import com.github.h0tk3y.betterParse.combinators.map
import com.github.h0tk3y.betterParse.combinators.oneOrMore
import com.github.h0tk3y.betterParse.combinators.or
import com.github.h0tk3y.betterParse.combinators.rightAssociative
import com.github.h0tk3y.betterParse.combinators.separatedTerms
import com.github.h0tk3y.betterParse.combinators.times
import com.github.h0tk3y.betterParse.combinators.unaryMinus
import com.github.h0tk3y.betterParse.combinators.use
import com.github.h0tk3y.betterParse.combinators.zeroOrMore
import com.github.h0tk3y.betterParse.grammar.Grammar
import com.github.h0tk3y.betterParse.grammar.parseToEnd
import com.github.h0tk3y.betterParse.grammar.parser
import com.github.h0tk3y.betterParse.lexer.literalToken
import com.github.h0tk3y.betterParse.lexer.regexToken
import com.github.h0tk3y.betterParse.parser.Parser

class ProgramGrammar : Grammar<Program>() {
    // Tokens are parsed in the declaration order. So if int is after ident (which subsumes int), int will never
    // get parsed.
    val tokRead by literalToken("read")
    val tokGoto by literalToken("goto")
    val tokIf by literalToken("if")
    val tokElse by literalToken("else")
    val tokReturn by literalToken("return")
    val tokHead by literalToken("head")
    val tokTail by literalToken("tail")
    val tokInt by regexToken("\\d+")
    val tokId by regexToken("[a-zA-Z_][a-zA-Z0-9_]*")
    val tokPlus by literalToken("+")
    val tokMinus by literalToken("-")
    val tokTimes by literalToken("*")

    val tokEq2 by literalToken("==")
    val tokEq by literalToken("=")
    val tokColon2 by literalToken("::")
    val tokColon by literalToken(":")
    val tokSemi by literalToken(";")
    val tokComma by literalToken(",")
    val tokLpar by literalToken("(")
    val tokRpar by literalToken(")")
    val tokLsquare by literalToken("[")
    val tokRsquare by literalToken("]")
    val tokWs by regexToken("\\s+", ignore = true)

    inline fun <reified A> par(noinline x: () -> Parser<A>) = -tokLpar * parser(x) * -tokRpar
    inline fun <reified A> square(noinline x: () -> Parser<A>) = -tokLsquare * parser(x) * -tokRsquare

    val identString by tokId use { text }

    // term ::= <ident> | <int> | '(' <term> ')'
    val term: Parser<Expr> by identString.map(Expr::Var) or
        (tokInt use { Expr.I(text.toInt()) }) or
        par(this::expr) or
        square(this::exprList).map(Expr::MkList)

    val consChain by rightAssociative(term, tokColon2) { l, _, r -> Expr.BOp(BinaryRator.Cons, l, r) }

    val mulChain by leftAssociative(consChain, tokTimes) { l, _, r -> Expr.BOp(BinaryRator.Mul, l, r) }

    val plusChain by leftAssociative(mulChain, tokPlus or tokMinus) { l, tokOp, r ->
        val rator = if (tokOp.text == "+") {
            BinaryRator.Add
        } else {
            BinaryRator.Sub
        }
        Expr.BOp(rator, l, r)
    }

    val eqvChain by leftAssociative(plusChain, tokEq2) { l, _, r -> Expr.BOp(BinaryRator.Eqv, l, r) }

    val expr by eqvChain

    // exprList ::= <expr> (',' <expr>)*
    val exprList: Parser<List<Expr>> by separatedTerms(expr, tokComma, acceptZero = true)

    val label: Parser<Label> by identString.map(::Label)

    val assign: Parser<Assign> by (identString * -tokEq * expr * -tokSemi).map { (name, body) ->
        Assign(name, body)
    }

    val goto: Parser<Jump.Goto> by (-tokGoto * label).map(Jump::Goto)
    val ifGoto: Parser<Jump.If> by (-tokIf * expr * -tokGoto * label * -tokElse * label).map { (cond, t, f) ->
        Jump.If(cond, t, f)
    }
    val ret: Parser<Jump.Return> by (-tokReturn * expr).map(Jump::Return)
    val jump by goto or ifGoto or ret

    val identList by separatedTerms(identString, tokComma, acceptZero = true)

    val bb: Parser<BB> by (label * -tokColon * zeroOrMore(assign) * jump * -tokSemi).map { (label, body, last) ->
        BB(label, body, last)
    }

    val program: Parser<Program> by (-tokRead * identList * -tokSemi * oneOrMore(bb)).map { (args, body) ->
        Program(args, body)
    }

    override val rootParser: Parser<Program>
        get() = program
}

fun main() {
    val g = ProgramGrammar()
    val program = g.parseToEnd("""
        read a, b;
        foo:
            b = a :: b;
            a = a + 1;
            goto bar;
        bar:
            if a == 10 goto baz else foo; 
        baz:
            return b;
    """.trimIndent())
    println(program.ppr())

    val args = listOf(Value.I(0), Value.Nil)
    val result = program.execute(args)
    println(result.ppr())
}