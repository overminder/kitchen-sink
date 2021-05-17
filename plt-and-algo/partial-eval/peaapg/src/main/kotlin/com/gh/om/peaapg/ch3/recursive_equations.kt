package com.gh.om.peaapg.ch3

import com.github.h0tk3y.betterParse.combinators.leftAssociative
import com.github.h0tk3y.betterParse.combinators.map
import com.github.h0tk3y.betterParse.combinators.oneOrMore
import com.github.h0tk3y.betterParse.combinators.or
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
import com.github.h0tk3y.betterParse.parser.parseToEnd
import java.lang.Exception
import kotlin.reflect.KClass

sealed class Expr {
    data class I(val value: Int) : Expr()
    object Bot : Expr()
    data class Var(val name: String) : Expr()
    data class App(val f: Expr, val arg: Expr) : Expr()
    data class Add(val lhs: Expr, val rhs: Expr) : Expr()
    data class Lam(val name: String, val body: Expr) : Expr()

    companion object {
        fun parseToEnd(src: String): Expr {
            return ExprGrammar().parseToEnd(src)
        }
    }
}

class ExprGrammar : Grammar<Expr>() {
    // Tokens are parsed in the declaration order. So if int is after ident (which subsumes int), int will never
    // get parsed.
    val bot by literalToken("bot")
    val int by regexToken("\\d+")
    val ident by regexToken("\\w+")
    val plus by literalToken("+")
    // To separate toplevel definitions -- Just to be lazy...
    val eq by literalToken("=")
    val semi by literalToken(";")
    val comma by literalToken(",")
    val lpar by literalToken("(")
    val rpar by literalToken(")")
    val bslash by literalToken("\\")
    val arrow by literalToken("->")
    val ws by regexToken("\\s+", ignore = true)

    inline fun <reified A> par(noinline x: () -> Parser<A>) = -lpar * parser(x) * -rpar

    val identString by ident use { text }

    val term: Parser<Expr> by identString.map(Expr::Var) or
        (int use { Expr.I(text.toInt()) }) or
        (bot.map { Expr.Bot }) or
        parser(this::lam) or
        par(this::expr)

    val lam: Parser<Expr> by (-bslash * oneOrMore(identString) * -arrow * parser(this::expr)).map { (args, body) ->
        args.foldRight(body, Expr::Lam)
    }

    val exprList: Parser<List<Expr>> by separatedTerms(parser(this::expr), comma)

    val callChain: Parser<Expr> by (term * zeroOrMore(par(this::exprList))).map { (f, args) ->
        args.flatten().fold(f, Expr::App)
    }

    val plusChain by leftAssociative(callChain, plus) { l, _, r -> Expr.Add(l, r) }

    val expr by plusChain

    val toplevelEquation: Parser<ToplevelEquation> by (oneOrMore(identString) * -eq * expr * -semi).map { (names, body) ->
        val name = names.first()
        val args = names.drop(1)
        ToplevelEquation(name, args.foldRight(body, Expr::Lam))
    }

    val program: Parser<Program> by (zeroOrMore(toplevelEquation) * expr).map { (defns, body) ->
        Program(defns, body)
    }

    override val rootParser: Parser<Expr>
        get() = expr
}

object ExprExamples {
    val add = Expr.Add(Expr.I(40), Expr.I(2))
}

data class Program(val defns: List<ToplevelEquation>, val body: Expr) {
    companion object {
        fun parseToEnd(src: String): Program {
            val p = ExprGrammar()
            return p.program.parseToEnd(p.tokenizer.tokenize((src)))
        }
    }
}

// "ScDefn" in Simon's funimpl book
data class ToplevelEquation(val name: String, val body: Expr)

class Env<V : Any>(private val here: Map<String, V>, private val outer: Env<V>? = null) {
    operator fun get(name: String): V? {
        return here[name] ?: outer?.get(name)
    }

    fun extend(name: String, value: V): Env<V> {
        return Env(mapOf(name to value), this)
    }

    fun getBound(name: String): V {
        return this[name] ?: throw Stuck.UnboundVariable(name)
    }
}

sealed class Stuck(msg: String) : Exception(msg) {
    class Bottom() : Stuck("Bottom evaluated")
    class UnboundVariable(val varName: String) : Stuck("Unbound variable: $varName")
    class Loop(val msg: String) : Stuck(msg)
    class IncorrectType(val expr: Expr, val result: Any /* hmm */, val type: KClass<*>) :
        Stuck("$expr evaluates to $result which is not a ${type.simpleName}")
}

object Cbv {
    sealed class Value {
        data class I(val value: Int) : Value()

        // Represents an uninitialized rhs of an equation
        object Uninitialized : Value()
        data class Lam(val arg: String, val body: Expr, val env: Env<Value>) : Value()
    }

    fun run(program: Program): Value {
        val (defns, body) = program
        // First: make toplevel env from all defns
        val toplevelBindings = defns.map {
            it.name to Value.Uninitialized
        }.toMap(mutableMapOf<String, Value>())
        val env = Env(toplevelBindings)
        defns.forEach {
            toplevelBindings[it.name] = eval(it.body, env)
        }
        return eval(body, env)
    }

    private fun eval(expr: Expr, env: Env<Value>): Value {
        return when (expr) {
            is Expr.Var -> {
                val value = env.getBound(expr.name)
                if (value is Value.Uninitialized) {
                    throw Stuck.Loop("Toplevel equation ${expr.name} used before it's initialized")
                }
                value
            }
            is Expr.App -> {
                val f = evalAs<Value.Lam>(expr.f, env)
                val arg = eval(expr.arg, env)
                eval(f.body, f.env.extend(f.arg, arg))
            }
            is Expr.Add -> {
                val lhs = evalAs<Value.I>(expr.lhs, env)
                val rhs = evalAs<Value.I>(expr.rhs, env)
                Value.I(lhs.value + rhs.value)
            }
            is Expr.Lam -> Value.Lam(expr.name, expr.body, env)
            is Expr.I -> Value.I(expr.value)
            Expr.Bot -> throw Stuck.Bottom()
        }
    }

    private inline fun <reified A> evalAs(expr: Expr, env: Env<Value>): A {
        val result = eval(expr, env)
        if (result !is A) {
            throw Stuck.IncorrectType(expr, result, A::class)
        }
        return result
    }
}

// Call-by-name
object Cbn {
    sealed class Value {
        data class I(val value: Int) : Value()
        data class Ind(var thunk: Thunk) : Value()
        data class Lam(val arg: String, val body: Expr, val env: Env<Value>) : Value()

        companion object {
            fun mkInd(expr: Expr, env: Env<Value>): Ind {
                return Ind(Thunk.Lazy(expr, env))
            }
        }
    }

    sealed class Thunk {
        data class Lazy(val expr: Expr, val env: Env<Value>) : Thunk()
        object Forcing : Thunk()
        data class Forced(val value: Value) : Thunk()
    }

    fun run(program: Program): Value {
        val (defns, body) = program
        // First: make empty toplevel env
        val toplevelBindings = mutableMapOf<String, Value>()
        val env = Env(toplevelBindings)
        // Then: fill in the env with lazy values
        defns.forEach {
            toplevelBindings[it.name] = Value.mkInd(it.body, env)
        }
        return eval(body, env)
    }

    private fun eval(expr: Expr, env: Env<Value>): Value {
        return when (expr) {
            is Expr.I -> Value.I(expr.value)
            Expr.Bot -> throw Stuck.Bottom()
            is Expr.Var -> {
                val value = env.getBound(expr.name)
                if (value is Value.Ind) {
                    unwrapInd(value)
                } else {
                    value
                }
            }
            is Expr.App -> {
                val f = evalAs<Value.Lam>(expr.f, env)
                val arg = Value.mkInd(expr.arg, env)
                eval(f.body, f.env.extend(f.arg, arg))
            }
            is Expr.Add -> {
                val lhs = evalAs<Value.I>(expr.lhs, env)
                val rhs = evalAs<Value.I>(expr.rhs, env)
                Value.I(lhs.value + rhs.value)
            }
            is Expr.Lam -> Value.Lam(expr.name, expr.body, env)
        }
    }

    private inline fun <reified A> evalAs(expr: Expr, env: Env<Value>): A {
        val result = eval(expr, env)
        if (result !is A) {
            throw Stuck.IncorrectType(expr, result, A::class)
        }
        return result
    }

    private fun unwrapInd(ind: Value.Ind): Value {
        return when (val thunk = ind.thunk) {
            is Thunk.Lazy -> {
                ind.thunk = Thunk.Forcing
                val result = eval(thunk.expr, thunk.env)
                ind.thunk = Thunk.Forced(result)
                result
            }
            Thunk.Forcing -> throw Stuck.Loop("Re-forcing a thunk")
            is Thunk.Forced -> thunk.value
        }
    }
}
