package com.github.om.inctc.lang.stlc

import com.github.om.inctc.parse.Parser
import com.github.om.inctc.parse.ParserCombinators0
import com.github.om.inctc.parse.ap
import com.github.om.inctc.parse.curried

sealed class Exp
data class Var(val ident: Ident): Exp()
data class Lam(var args: List<Ident>, val body: Exp): Exp()
data class LitI(val value: Int): Exp()
data class If(val cond: Exp, val then: Exp, val else_: Exp): Exp()
data class App(val func: Exp, val arg: Exp): Exp()
data class BOp(val op: BRator, val left: Exp, val right: Exp): Exp()

enum class BRator {
    LT,
    PLUS,
    MINUS,
}

sealed class Decl
// Could possibly support reexport (pub use) as well.
data class Import(val moduleName: ModuleName, val ident: Ident): Decl()
data class Define(val ident: Ident, val visibility: Visibility, val body: Exp): Decl()

data class Module(val name: ModuleName, val decls: List<Decl>)

inline class ModuleName(val name: String)
inline class Ident(val name: String)

enum class Visibility {
    Public,
    Internal,
}

data class FqName(val moduleName: ModuleName, val ident: Ident) {
    companion object {
        fun parse(s: String): FqName {
            val xs = s.split(".")
            assert(xs.size == 2)
            return FqName(ModuleName(xs[0]), Ident(xs[1]))
        }
    }
}

enum class Keyword(val token: String) {
    FUN("fun"),
    IN("in"),
    END("end"),
    DEF("def"),
    IF("if"),
    THEN("then"),
    ELSE("else"),
    PUB("pub"),
    USE("use"),
}

object StlcParser {
    private val p = ParserCombinators0
    val keywords: List<String> = Keyword.values().map { it.token }

    // name ::= <letter> (<letter> | <digit>)*
    // and name is not one of the keywords
    // Note that currently name is a bit problematic (need to add one lookahead to avoid partial parse)
    val name0: Parser<String> = p.andThen(p.letter(), p.many(p.orElse(p.letter(), p.digit()))).fmap {
        val (head, tail) = it
        (listOf(head) + tail).joinToString("")
    }
    val name: Parser<String> = ignoreLeftSpaces(name0).filter {
        !keywords.contains(it)
    }.ignoreRight(p.peekIf {
        // XXX need to write this better
        it == null || !(it.isLetter() || it.isDigit())
    })

    fun <A> ignoreLeftSpaces(pa: Parser<A>): Parser<A> = p.many(p.space()).ignoreLeft(pa)

    fun keyword(s: Keyword) = ignoreLeftSpaces(p.string(s.token))
    fun token(s: String) = ignoreLeftSpaces(p.string(s))
    fun <A: Any> tokenChoice(choices: Map<CharSequence, A>): Parser<A> {
        val lengths = choices.keys.map { it.length }.toSet().sortedDescending()
        return ignoreLeftSpaces(p.choice(lengths.map {
            p.stringThat(it, choices::containsKey).fmap {
                requireNotNull(choices[it])
            }
        }))
    }

    fun <A> parenthesized(p: Parser<A>): Parser<A> = token("(").ignoreLeft(p).ignoreRight(token(")"))

    val ident: Parser<Ident> = name.fmap(::Ident)
    val moduleName: Parser<ModuleName> = name.fmap(::ModuleName)

    val var_: Parser<Var> = ident.fmap(::Var)
    // lam ::= 'fun' arg+ 'in' exp 'end'
    val lam: Parser<Lam> by lazy {
        val args = keyword(Keyword.FUN).ignoreLeft(p.many1(ident)).ignoreRight(keyword(Keyword.IN))
        val exp_ = exp.ignoreRight(keyword(Keyword.END))
        p.pure(::Lam.curried()).ap(args).ap(exp_)
    }

    val int: Parser<Int> = ignoreLeftSpaces(p.many1(p.digit()).fmap { it.joinToString("").toInt() })
    val litI: Parser<LitI> = int.fmap(::LitI)

    val ifExp: Parser<If> by lazy {
        val cond = keyword(Keyword.IF).ignoreLeft(exp)
        val then = keyword(Keyword.THEN).ignoreLeft(exp)
        val else_ = keyword(Keyword.ELSE).ignoreLeft(exp).ignoreRight(keyword(Keyword.END))
        p.pure(::If.curried()).ap(cond).ap(then).ap(else_)
    }

    private fun mkApp(f: Exp, args: List<Exp>) = args.fold(f, ::App)

    private val tokenMap: Map<CharSequence, BRator> = mapOf(
            "<" to BRator.LT,
            "-" to BRator.MINUS,
            "+" to BRator.PLUS
    )

    val bexp: Parser<Exp> = p.makeLazy {
        val left = appOrAtom
        // (This assumes that all these binops are left-assoc.
        val right = p.many(p.andThen(tokenChoice(tokenMap), exp))

        fun mkBOps(left: Exp, right: List<Pair<BRator, Exp>>): Exp {
            return right.fold(left) { left, right ->
                BOp(right.first, left, right.second)
            }
        }

        p.pure(::mkBOps.curried()).ap(left).ap(right)
    }

    val appOrAtom: Parser<Exp> = p.makeLazy {
        val f = atom
        // Essentially treating x(y, z) the same as x(y)(z)
        val args = p.many(parenthesized(p.sepBy1(exp, token(",")))).fmap {
            it.flatten()
        }
        p.pure(::mkApp.curried()).ap(f).ap(args)
    }

    val exp: Parser<Exp> = bexp

    val atom: Parser<Exp> = p.choice(listOf(lam, ifExp, var_, litI, p.makeLazy { parenthesized(bexp) }))

    // Decls

    val import: Parser<Import> by lazy {
        val mod = keyword(Keyword.USE).ignoreLeft(moduleName)
        val id = token(".").ignoreLeft(ident)
        p.pure(::Import.curried()).ap(mod).ap(id)
    }

    val def: Parser<Define> by lazy {
        val vis = p.optional(keyword(Keyword.PUB)).fmap {
            if (it != null) {
                Visibility.Public
            } else {
                Visibility.Internal
            }
        }
        val name = keyword(Keyword.DEF).ignoreLeft(ident)
        val body = token("=").ignoreLeft(exp)
        fun mkDef(vis: Visibility, name: Ident, body: Exp) = Define(name, vis, body)
        p.pure(::mkDef.curried()).ap(vis).ap(name).ap(body)
    }

    val decl: Parser<Decl> = p.orElse(def, import)

    fun file(name: ModuleName): Parser<Module> = p.pure(::Module.curried()(name)).ap(p.many(decl)).ignoreRight(p.eof())
}
