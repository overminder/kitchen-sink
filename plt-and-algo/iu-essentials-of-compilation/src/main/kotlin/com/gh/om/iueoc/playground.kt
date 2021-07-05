package com.gh.om.iueoc

import com.gh.om.iueoc.son.GraphBuilder
import com.gh.om.iueoc.son.GraphVerifier
import com.gh.om.iueoc.son.graphToDot
import com.gh.om.iueoc.son.interp
import com.github.h0tk3y.betterParse.grammar.parseToEnd
import com.github.h0tk3y.betterParse.parser.AlternativesFailure
import com.github.h0tk3y.betterParse.parser.ErrorResult
import com.github.h0tk3y.betterParse.parser.MismatchedToken
import com.github.h0tk3y.betterParse.parser.NoMatchingToken
import com.github.h0tk3y.betterParse.parser.ParseException
import com.github.h0tk3y.betterParse.parser.UnexpectedEof
import com.github.h0tk3y.betterParse.parser.UnparsedRemainder
import java.io.FileWriter

private const val LET_ADD = """
(let ([x 41]
      [y 1])
  (let ([z (#fx+ x y)]
        [zz (#fx< (#fx+ x y) (#fx+ x y))])
    zz))
"""

private const val LAM_AP = """
(let ([add1 (lambda [x] (#fx+ x 1))])
  (add1 41))
"""

private const val LET_IF = """
(let ([x 40]
      [y 8])
  (if (#fx< x y)
      1
      2))
"""

fun showEocError(e: EocError, source: String, header: String = "Error") {
    println("$header: ${e.message} at ${e.where}")
    // XXX Does lineSequence have the same implementation as better-parse?
    if (e.where != null) {
        val (line, pointer) = formatSourceWithLoc(source, e.where)
        println(line)
        println(pointer)
    }
}

private fun formatSourceWithLoc(source: String, loc: SourceLoc): Pair<String, String> {
    val line = source.lineSequence().drop(loc.row - 1).iterator().next()
    return line to " ".repeat(loc.col - 1) + "^"
}

fun showParseError(e: ErrorResult, source: String) {
    println("Parse error:")
    for ((where, msg) in formatParseError(e, 100)) {
        println("$msg at $where")
        if (where != null) {
            val (line, pointer) = formatSourceWithLoc(source, where)
            println(line)
            println(pointer)
        }
    }
}

private fun formatParseError(e: ErrorResult, remainingDepth: Int): List<Pair<SourceLoc?, String>> {
    val res = when (e) {
        is UnparsedRemainder -> {
            e.startsWith.toSourceLoc() to "UnparsedRemainder"
        }
        is MismatchedToken -> {
            e.found.toSourceLoc() to "MismatchedToken, expecting ${e.expected.name}"
        }
        is NoMatchingToken -> {
            e.tokenMismatch.toSourceLoc() to "NoMatchingToken"
        }
        is UnexpectedEof -> {
            val msg = "UnexpectedEof, expecting ${e.expected.name}"
            null to msg
        }
        is AlternativesFailure -> {
            return if (remainingDepth <= 0) {
                emptyList()
            } else {
                e.errors.flatMap {
                    formatParseError(it, remainingDepth - 1)
                }
            }
        }
        else -> error("Unknown ErrorResult: $e")
    }
    return listOf(res)
}

fun runProgram(source: String): Value {
    val program = try {
        SexprGrammar.parseToEnd(source)
    } catch (e: ParseException) {
        showParseError(e.errorResult, source)
        throw e
    }

    val expr = try {
        SexprToExpr.toExpr(program)
    } catch (e: EocError) {
        showEocError(e, source, "SexprToExpr error")
        throw e
    }

    val exprInterpResult = try {
        InterpLam().interpToplevel(expr)
    } catch (e: EocError) {
        showEocError(e, source, "Interp error")
        throw e
    }

    val gb = GraphBuilder()
    try {
        gb.doFunctionBody(expr)
        GraphVerifier(gb).verifyFullyBuilt()
    } catch (e: EocError) {
        showEocError(e, source, "GraphBuilder error")
        throw e
    }
    FileWriter("tools/out.dot").use {
        graphToDot(gb, it)
    }
    val graphInterpResult = interp(gb.start, gb.nodes)
    require(exprInterpResult == graphInterpResult)
    return graphInterpResult
}

private fun main() {
    val result = runProgram(LET_IF)
    println("Ok: $result")
}