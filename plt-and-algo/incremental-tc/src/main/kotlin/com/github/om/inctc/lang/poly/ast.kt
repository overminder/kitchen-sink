package com.github.om.inctc.lang.poly

import com.github.om.inctc.parse.Parser
import com.github.om.inctc.parse.ParserCombinators0
import com.github.om.inctc.parse.ap
import com.github.om.inctc.parse.curried

sealed class Exp
data class Var(val ident: Ident): Exp()
data class Lam(var args: List<Ident>, val body: Exp): Exp()
// Actually let* (non-recursive, each binding can refer to all the previous bindings)
data class Let(var bindings: List<Pair<Ident, Exp>>, val body: Exp): Exp()
data class LitI(val value: Int): Exp()
data class If(val cond: Exp, val then: Exp, val else_: Exp): Exp()
// Consider make arg a list to improve perf.
data class App(val func: Exp, val arg: Exp): Exp()
data class BOp(val op: BRator, val left: Exp, val right: Exp): Exp()

enum class BRator(val token: String) {
    LT("<"),
    PLUS("+"),
    MINUS("-"),
}

sealed class Decl {
    abstract val ident: Ident
}
// Could possibly support reexport (pub use) as well.
data class Import(val moduleName: ModuleName, override val ident: Ident): Decl()
data class ValueDef(override val ident: Ident, val visibility: Visibility, val body: Exp): Decl()
data class TypeDef(override val ident: Ident, val visibility: Visibility, val body: TypeSpec): Decl()

// Q: Do we want anonymous sum / record types, or even full structural types? Or we can simply treat complex
// type combinators as second class citizens... If we go the anonymous route, what about access modifiers to the
// fields? Module systems are indeed complex and no doubt people want a unified theory of modules...
sealed class TypeSpec
data class SumOfRecordsSpec(val args: List<Ident>, val sumOf: List<RecordSpec>): TypeSpec()
data class TypealiasSpec(val args: List<Ident>, val body: TypeExp): TypeSpec()

data class RecordSpec(val name: Ident, val fields: List<RecordField>)
data class RecordField(val name: Ident, val type: TypeExp)

sealed class TypeExp
data class TypeIdent(val id: Ident): TypeExp()
data class TypeApp(val func: TypeExp, val args: List<TypeExp>): TypeExp()

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

val Import.defSite: FqName
    get() = FqName(moduleName, ident)

enum class Keyword(val token: String) {
    FUN("fun"),
    IN("in"),
    END("end"),
    DEF("def"),
    LET("let"),
    IF("if"),
    THEN("then"),
    ELSE("else"),
    PUB("pub"),
    USE("use"),
    DATA("data"),
    TYPE("type"),
}

object PolyLangParser {
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

    fun <A> parenthesized(p: Parser<A>, open: String = "(", close: String = ")"): Parser<A> =
        token(open).ignoreLeft(p).ignoreRight(token(close))

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

    // let (v = e)+ in e end
    val letExp: Parser<Let> by lazy {
        val binding = p.andThen(ident, token("=").ignoreLeft(exp))
        p.pure(::Let.curried())
            .ap(keyword(Keyword.LET).ignoreLeft(p.many1(binding)))
            .ap(keyword(Keyword.IN).ignoreLeft(exp).ignoreRight(keyword(Keyword.END)))
    }

    private fun mkApp(f: Exp, args: List<Exp>) = args.fold(f, ::App)
    private fun mkTypeApp(f: TypeExp, args: List<TypeExp>) =
        if (args.isEmpty()) {
            f
        } else {
            TypeApp(f, args)
        }

    private val tokenMap: Map<CharSequence, BRator> = BRator.values().map {
        it.token to it
    }.toMap()

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

    val atom: Parser<Exp> = p.choice(listOf(lam, ifExp, letExp, var_, litI, p.makeLazy { parenthesized(bexp) }))

    // Decls

    val import: Parser<Import> by lazy {
        val mod = keyword(Keyword.USE).ignoreLeft(moduleName)
        val id = token(".").ignoreLeft(ident)
        p.pure(::Import.curried()).ap(mod).ap(id)
    }

    val maybeVis: Parser<Visibility> =
        p.optional(keyword(Keyword.PUB)).fmap {
            if (it != null) {
                Visibility.Public
            } else {
                Visibility.Internal
            }
        }

    val valueDef: Parser<ValueDef> by lazy {
        val name = keyword(Keyword.DEF).ignoreLeft(ident)
        val body = token("=").ignoreLeft(exp)
        fun mkDef(vis: Visibility, name: Ident, body: Exp) = ValueDef(name, vis, body)
        p.pure(::mkDef.curried()).ap(maybeVis).ap(name).ap(body)
    }

    // Do we want "Type Arg", "Type<Arg>", "Type(Arg)", "Type[Arg]"? Parenthesis does help with parsing...
    // Okay so for now we choose Type(Arg).
    val typeExp: Parser<TypeExp> by lazy {
        val f = ident.fmap(::TypeIdent)
        // Essentially treating x(y, z) the same as x(y)(z)
        val args = p.makeLazy {
            p.many(parenthesized(p.sepBy1(typeExp, token(",")))).fmap {
                it.flatten()
            }
        }
        p.pure(::mkTypeApp.curried()).ap(f).ap(args)
    }

    val typealiasDef: Parser<TypeDef> by lazy {
        val typeNameAndArgs = keyword(Keyword.TYPE).ignoreLeft(p.many1(ident)).ignoreRight(token("="))
        fun mk(vis: Visibility, head: List<Ident>, body: TypeExp): TypeDef {
            val name = head.first()
            val args = head.drop(1)
            return TypeDef(name, vis, TypealiasSpec(args, body))
        }
        p.pure(::mk.curried()).ap(maybeVis).ap(typeNameAndArgs).ap(typeExp)
    }

    val recordSpec: Parser<RecordSpec> by lazy {
        // Name ({ (name: type)* })?
        val rawFields = p.many(
            p.andThen(ident.ignoreRight(token(":")), typeExp).fmap {
                RecordField(it.first, it.second)
            })
        val fields = p.orElse(parenthesized(rawFields, "{", "}"), p.pure(emptyList()))
        p.pure(::RecordSpec.curried()).ap(ident).ap(fields)
    }

    val dataDef: Parser<TypeDef> by lazy {
        val typeNameAndArgs = keyword(Keyword.DATA).ignoreLeft(p.many1(ident)).ignoreRight(token("="))
        fun mk(vis: Visibility, head: List<Ident>, body: List<RecordSpec>): TypeDef {
            val name = head.first()
            val args = head.drop(1)
            return TypeDef(name, vis, SumOfRecordsSpec(head.drop(1), body))
        }
        // Could also consider allowing zero ctor
        val records = p.sepBy1(recordSpec, token("|"))
        p.pure(::mk.curried()).ap(maybeVis).ap(typeNameAndArgs).ap(records)
    }

    val typeDef: Parser<TypeDef> by lazy {
        p.orElse(typealiasDef, dataDef)
    }

    val decl: Parser<Decl> = p.choice(listOf(valueDef, import, typeDef))

    fun file(name: ModuleName): Parser<Module> = p.pure(::Module.curried()(name)).ap(p.many(decl)).ignoreRight(p.eof())
}

// XXX This can be quadratic for large exps.
fun Exp.freeVariables(localEnv: List<Ident> = listOf()): List<Ident> = when (this) {
    is Var -> if (localEnv.contains(ident)) {
        emptyList()
    } else {
        listOf(ident)
    }
    is Let -> {
        val uses = mutableListOf<Ident>()
        val moarEnv = localEnv.toMutableList()
        for ((ident, rhs) in bindings) {
            uses.addAll(rhs.freeVariables(moarEnv))
            moarEnv += ident
        }
        uses.addAll(body.freeVariables(moarEnv))
        uses
    }
    is Lam -> body.freeVariables(localEnv + args)
    is LitI -> emptyList()
    is If -> listOf(cond, then, else_).flatMap { it.freeVariables(localEnv) }
    is App -> listOf(func, arg).flatMap { it.freeVariables(localEnv) }
    is BOp -> listOf(left, right).flatMap { it.freeVariables(localEnv) }
}
