package com.gh.om.pl.cwai

data class SourceLoc(
    val fileName: String,
    val line: Int,
    val column: Int,
)

/**
 * Raw s-expression
 */
sealed class SExp() {
    abstract val sourceLoc: SourceLoc

    data class SSym(
        val value: String,
        override val sourceLoc: SourceLoc,
    ) : SExp()

    data class SList(
        val value: List<SExp>,
        override val sourceLoc: SourceLoc,
    ) : SExp()

    data class SInt(
        val value: Int,
        override val sourceLoc: SourceLoc,
    ) : SExp()

    companion object {
        fun parse(
            source: String,
            fileName: String = "<input>",
        ): SExp {

            return SExpParser(
                source,
                fileName,
            ).parseTop()
        }
    }
}

private class SExpParser(
    private val input: String,
    private val fileName: String,
) {
    private var i = 0
    private var line = 1
    private var col = 1
    private val n = input.length

    private fun eof(): Boolean =
        i >= n

    private fun peek(): Char? =
        if (i < n) input[i] else null

    private fun isWhitespace(c: Char): Boolean =
        c == ' ' || c == '\t' || c == '\r' || c == '\n'

    private fun isDigit(c: Char): Boolean =
        c in '0'..'9'

    private fun isParen(c: Char): Boolean =
        c == '(' || c == ')' || c == '[' || c == ']'

    private fun isLetter(c: Char): Boolean =
        (c in 'a'..'z') || (c in 'A'..'Z')

    private fun isPunctSym(c: Char): Boolean =
        when (c) {
            '!', '@', '#', '$', '%', '^', '&', '*', '_', '+', '{', '}', '|', ':', '<', '>', '?', '/', '\\', '-', '=', '.' -> true
            else -> false
        }

    private fun isSymStart(c: Char): Boolean =
        isLetter(c) || isPunctSym(c)

    private fun isSymPart(c: Char): Boolean =
        isSymStart(c) || isDigit(c)

    private fun advance(): Char {
        val c = input[i++]
        if (c == '\n') {
            line += 1
            col = 1
        } else {
            col += 1
        }
        return c
    }

    private fun errorAt(msg: String): Nothing {
        throw IllegalArgumentException("$msg at $fileName:$line:$col")
    }

    private fun skipSpaceAndComments() {
        while (true) {
            // skip whitespace
            while (!eof() && peek()?.let { isWhitespace(it) } == true) advance()
            // skip comments starting with ';' to end of line
            if (!eof() && peek() == ';') {
                while (!eof()) {
                    val c = advance()
                    if (c == '\n') break
                }
                continue
            }
            break
        }
    }

    private fun parseList(open: Char): SExp.SList {
        val startLine = line
        val startCol = col
        // consume opener
        val opener = advance()
        val closer = when (opener) {
            '(' -> ')'
            '[' -> ']'
            else -> errorAt("internal parser error: invalid list opener '$opener'")
        }
        val items = mutableListOf<SExp>()
        while (true) {
            skipSpaceAndComments()
            val c = peek() ?: errorAt("unexpected end of input: expected '$closer'")
            if (c == closer) {
                advance()
                return SExp.SList(
                    items,
                    SourceLoc(
                        fileName,
                        startLine,
                        startCol,
                    ),
                )
            }
            if (c == ')' || c == ']') {
                // mismatched closing bracket
                errorAt("mismatched closing '$c', expected '$closer'")
            }
            items.add(parseExp())
        }
    }

    private fun parseInt(): SExp.SInt {
        val startLine = line
        val startCol = col
        val sb = StringBuilder()
        // optional leading '-'
        if (!eof() && peek() == '-') {
            sb.append(advance())
        }
        // must have at least one digit
        if (eof() || !isDigit(peek()!!)) {
            errorAt("expected digit after '-' for integer literal")
        }
        while (!eof() && peek()?.let { isDigit(it) } == true) {
            sb.append(advance())
        }
        // If immediately followed by a symbol-start char without delimiter, that's invalid like 123abc
        val nxt = peek()
        if (nxt != null && isSymStart(nxt)) {
            errorAt("invalid character '$nxt' after integer literal; expecting delimiter")
        }
        val v = try {
            sb.toString().toInt()
        } catch (e: NumberFormatException) {
            errorAt("integer literal out of range")
        }
        return SExp.SInt(
            v,
            SourceLoc(
                fileName,
                startLine,
                startCol,
            ),
        )
    }

    private fun parseSym(): SExp.SSym {
        val startLine = line
        val startCol = col
        val sb = StringBuilder()
        // first char must be sym-start
        val first = peek() ?: errorAt("unexpected end of input while parsing symbol")
        if (!isSymStart(first)) errorAt("invalid symbol start '$first'")
        sb.append(advance())
        while (!eof()) {
            val c = peek()!!
            if (isSymPart(c) && !isParen(c) && !isWhitespace(c) && c != ';') {
                sb.append(advance())
            } else {
                break
            }
        }
        return SExp.SSym(
            sb.toString(),
            SourceLoc(
                fileName,
                startLine,
                startCol,
            ),
        )
    }

    private fun parseExp(): SExp {
        skipSpaceAndComments()
        val c = peek() ?: errorAt("unexpected end of input")
        return when {
            c == '(' || c == '[' -> parseList(c)
            isDigit(c) -> parseInt()
            // negative integer if '-' followed by digit; otherwise it's a symbol
            c == '-' && (i + 1 < n) && isDigit(input[i + 1]) -> parseInt()
            isSymStart(c) -> parseSym()
            c == ')' || c == ']' -> errorAt("unexpected closing '$c'")
            else -> errorAt("unexpected character '$c'")
        }
    }

    fun parseTop(): SExp {
        val e = parseExp()
        skipSpaceAndComments()
        if (!eof()) {
            errorAt("unexpected tokens after expression")
        }
        return e
    }
}

/**
 * Simple scheme AST
 */
sealed class Exp {
    abstract val sourceLoc: SourceLoc

    /**
     * Integer literal
     */
    data class EInt(
        val value: Int,
        override val sourceLoc: SourceLoc,
    ) : Exp()

    /**
     * Boolean literal, e.g. #t or #f
     */
    data class EBool(
        val value: Boolean,
        override val sourceLoc: SourceLoc,
    ) : Exp()

    /**
     * Primitive operation, i.e. (+# 1 2)
     */
    data class EPrimOp(
        val op: PrimOp,
        val args: List<Exp>,
        override val sourceLoc: SourceLoc,
    ) : Exp()

    /**
     * Symbolic variable
     */
    data class ESym(
        val name: String,
        override val sourceLoc: SourceLoc,
    ) : Exp()

    /**
     * Let binding, i.e. (let ([name1 value1] [name2 value2]) body).
     */
    data class ELet(
        val bindings: List<Pair<String, Exp>>,
        val body: Exp,
        /**
         * When true, this is for recursive let (letrec ([name1 value1] [name2 value2]) body).
         * When false, this is for non-recursive let (let ([x 1]) body)
         */
        val isRec: Boolean,
        override val sourceLoc: SourceLoc,
    ) : Exp()

    /**
     * If expression, i.e. (if condition true-branch false-branch).
     */
    data class EIf(
        val condition: Exp,
        val trueBranch: Exp,
        val falseBranch: Exp,
        override val sourceLoc: SourceLoc,
    ) : Exp()

    /**
     * Lambda abstraction, i.e. (lambda (arg1 arg2) body).
     */
    data class EAbs(
        val args: List<String>,
        val body: Exp,
        override val sourceLoc: SourceLoc,
    ) : Exp()

    /**
     * Function application, i.e. (callee arg1 arg2).
     */
    data class EApp(
        val callee: Exp,
        val args: List<Exp>,
        override val sourceLoc: SourceLoc,
    ) : Exp()

    companion object {
        fun fromSExp(sexp: SExp): Exp {
            return ExpParser.parse(sexp)
        }
    }
}

private object ExpParser {
    fun reportError(
        loc: SourceLoc,
        msg: String,
    ): Nothing {
        throw IllegalArgumentException("$msg at ${loc.fileName}:${loc.line}:${loc.column}")
    }

    fun primOpFrom(name: String): PrimOp? =
        when (name) {
            "+#" -> PrimOp.INT_ADD
            "-#" -> PrimOp.INT_SUB
            "<#" -> PrimOp.INT_LT
            else -> null
        }

    fun parse(e: SExp): Exp =
        when (e) {
            is SExp.SInt -> Exp.EInt(
                e.value,
                e.sourceLoc,
            )

            is SExp.SSym -> when (e.value) {
                "#t" -> Exp.EBool(
                    true,
                    e.sourceLoc,
                )

                "#f" -> Exp.EBool(
                    false,
                    e.sourceLoc,
                )

                else -> Exp.ESym(
                    e.value,
                    e.sourceLoc,
                )
            }

            is SExp.SList -> {
                if (e.value.isEmpty()) {
                    reportError(
                        e.sourceLoc,
                        "empty list is not a valid expression",
                    )
                }
                val head = e.value.first()
                if (head is SExp.SSym) {
                    when (head.value) {
                        "let" -> {
                            // (let ([name1 val1] [name2 val2]) body)
                            val elems = e.value
                            if (elems.size != 3) reportError(
                                e.sourceLoc,
                                "let expects exactly a bindings list and a body",
                            )
                            val bindsS = elems[1]
                            val bodyS = elems[2]
                            if (bindsS !is SExp.SList) reportError(
                                bindsS.sourceLoc,
                                "let bindings must be a list",
                            )
                            val binds = mutableListOf<Pair<String, Exp>>()
                            for (b in bindsS.value) {
                                if (b !is SExp.SList) reportError(
                                    b.sourceLoc,
                                    "let binding must be a list [name value]",
                                )
                                if (b.value.size != 2) reportError(
                                    b.sourceLoc,
                                    "let binding must have exactly 2 elements",
                                )
                                val nameS = b.value[0]
                                val valS = b.value[1]
                                if (nameS !is SExp.SSym) reportError(
                                    nameS.sourceLoc,
                                    "let binding name must be a symbol",
                                )
                                binds.add(nameS.value to parse(valS))
                            }
                            Exp.ELet(
                                bindings = binds,
                                body = parse(bodyS),
                                isRec = false,
                                sourceLoc = e.sourceLoc,
                            )
                        }

                        "letrec" -> {
                            // (letrec ([name1 val1] [name2 val2]) body)
                            val elems = e.value
                            if (elems.size != 3) reportError(
                                e.sourceLoc,
                                "letrec expects exactly a bindings list and a body",
                            )
                            val bindsS = elems[1]
                            val bodyS = elems[2]
                            if (bindsS !is SExp.SList) reportError(
                                bindsS.sourceLoc,
                                "letrec bindings must be a list",
                            )
                            val binds = mutableListOf<Pair<String, Exp>>()
                            for (b in bindsS.value) {
                                if (b !is SExp.SList) reportError(
                                    b.sourceLoc,
                                    "letrec binding must be a list [name value]",
                                )
                                if (b.value.size != 2) reportError(
                                    b.sourceLoc,
                                    "letrec binding must have exactly 2 elements",
                                )
                                val nameS = b.value[0]
                                val valS = b.value[1]
                                if (nameS !is SExp.SSym) reportError(
                                    nameS.sourceLoc,
                                    "letrec binding name must be a symbol",
                                )
                                binds.add(nameS.value to parse(valS))
                            }
                            Exp.ELet(
                                bindings = binds,
                                body = parse(bodyS),
                                isRec = true,
                                sourceLoc = e.sourceLoc,
                            )
                        }

                        "if" -> {
                            // (if condition true-branch false-branch)
                            val elems = e.value
                            if (elems.size != 4) reportError(
                                e.sourceLoc,
                                "if expects exactly 3 arguments: condition, true-branch, false-branch",
                            )
                            val condS = elems[1]
                            val thenS = elems[2]
                            val elseS = elems[3]
                            Exp.EIf(
                                parse(condS),
                                parse(thenS),
                                parse(elseS),
                                e.sourceLoc,
                            )
                        }

                        "lambda" -> {
                            // (lambda (arg1 arg2) body)
                            val elems = e.value
                            if (elems.size != 3) reportError(
                                e.sourceLoc,
                                "lambda expects exactly a parameter list and a body",
                            )
                            val paramsS = elems[1]
                            if (paramsS !is SExp.SList) reportError(
                                paramsS.sourceLoc,
                                "lambda parameter list must be a list",
                            )
                            val params = paramsS.value.map {
                                if (it !is SExp.SSym) reportError(
                                    it.sourceLoc,
                                    "lambda parameters must be symbols",
                                )
                                it.value
                            }
                            val bodyS = elems[2]
                            Exp.EAbs(
                                params,
                                parse(bodyS),
                                e.sourceLoc,
                            )
                        }

                        else -> {
                            val op = primOpFrom(head.value)
                            if (op != null) {
                                val argsS = e.value.drop(1)
                                if (argsS.size != op.arity) reportError(
                                    e.sourceLoc,
                                    "primitive '${head.value}' expects ${op.arity} args, got ${argsS.size}",
                                )
                                Exp.EPrimOp(
                                    op,
                                    argsS.map { parse(it) },
                                    e.sourceLoc,
                                )
                            } else {
                                // Application
                                val callee = parse(head)
                                val args = e.value.drop(1).map { parse(it) }
                                Exp.EApp(
                                    callee,
                                    args,
                                    e.sourceLoc,
                                )
                            }
                        }
                    }
                } else {
                    // Head is not a symbol; still treat as application
                    val callee = parse(head)
                    val args = e.value.drop(1).map { parse(it) }
                    Exp.EApp(
                        callee,
                        args,
                        e.sourceLoc,
                    )
                }
            }
        }

}

enum class PrimOp(val arity: Int) {
    INT_ADD(2),
    INT_SUB(2),
    INT_LT(2);
}
