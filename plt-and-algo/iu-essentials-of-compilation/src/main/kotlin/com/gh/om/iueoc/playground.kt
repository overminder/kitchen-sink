package com.gh.om.iueoc

import com.gh.om.iueoc.son.MultiGraphBuilder
import com.gh.om.iueoc.son.graphsToDot
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

private const val LET_SEQ = """
(let* ([x 1]
       [y 2]
       [z (#fx+ x y)]
       [x (#fx+ x z)]
       [y (#fx+ y x)])
  y)
"""

private const val LAM_AP = """
(let*
  ([add1 (lambda [x] (#fx+ x 1))]
   [add2 (lambda [x] add1)])
  add2)
"""

private const val LET_IF = """
(let ([x 40]
      [y 8])
  (if (#fx< x y)
      1
      2))
"""

private const val BOX_IF = """
(let* ([b (#box 42)]
       [_ (if b
              (#box-set! b 1)
              (#box-set! b 0))])
  (#box-get b))
"""

private const val BOX_SEMANTICS = """
(lambda [b x]
  (let ([b0 (#box-get b)]
        [_ (#box-set! b 1)]
        [b1 (#box-get b)])
    (#fx+ b0 b1)))
"""

private object EffectTests {
    // Only one branch updates effect, and the join point needs an effect phi.
    // (#box 0) is evaluated by the effectPhi at the join point.
    const val CASE_1 = """
    (let* ([b (#box 0)])
      (if #t
          (#box-set! b 1)
          0)
      (#box-get b))
    """

    // b is used before the control split. Here the value->effect dependence causes the effect to be evaluated.
    const val CASE_2 = """
    (let* ([b (#box 0)])
      (if b
          (#box-set! b 1)
          0)
      (#box-get b))
    """

    // Although b is unused, its effect is consumed by the return node, and b must be evaluated.
    const val CASE_3 = """
    (let* ([b (#box 0)])
      0)
    """

    // Assuming that there's a while expr. This one seems hard...
    // start: B-1:
    //   start -> e0
    //   (e1, b) <- #box e0 0
    //   J B-2
    // B-2:
    //   e2 <- effectPhi e1 e5
    //   (cond, e3) <- (#box-get e2 b)
    //   CondJump cond [ifT -> B-3, ifF -> B-4]
    // B-3:
    //   bv, e4 <- #box-get e3 b
    //   _, e5 <- #box-set! e4 b (+ bv 1)
    //   J B-2
    // B-4:
    //   e6, bv <- #box-get e3 b
    //   ret (e5, bv)
    //
    // Note that e3 dominates both B-3 and B-4, so that there's an effect split.
    // This illustrates that effect propagation also needs to be demand-based (call-by-need).
    const val WHILE_1 = """
    (let* ([b (#box 0)])
      (while (#fx< (#box-get b) 10)
             (#box-set! b (#fx+ (#box-get b) 1)))
      (#box-get b))
    """

    const val WHILE_2 = """
    (let* ([b 0])
      (while (#fx< 0 b)
             0)
      b)
    """

    // Sum from 1 to n. The graph starts to get too big to be viewed...
    const val WHILE_3 = """
    (let* ([s (#box 0)]
           [n (#box 10)])
      (while (#fx< 0 (#box-get n))
        (#box-set! s (#fx+ (#box-get s) (#box-get n)))
        (#box-set! n (#fx- (#box-get n) 1)))
      (#box-get s))
    """

    // Sum from 1 to n. The graph starts to get too big to be viewed...
    const val WHILE_4 = """
    (let* ([s 0]
           [n 10])
      (while (#fx< 0 n)
        (set! s (#fx+ s n))
        (set! n (#fx- n 1)))
      s)
    """
}

private object LambdaTests {
    const val ID = """
    (let* ([id (lambda (x) x)])
      (id 0))
    """

    const val SUM = """
    (let ([loop
            (lambda (n s loop)
              (if (#fx< 0 n)
                (loop (#fx- n 1)
                      (#fx+ n s)
                      loop)
                s))])
      (loop 10 0 loop))          
    """
}

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
        interpToplevel(expr)
    } catch (e: EocError) {
        showEocError(e, source, "Interp error")
        throw e
    }
    println("Interp -> $exprInterpResult")

    val gs = MultiGraphBuilder()
    val gb = try {
        gs.build(null, "<main>", emptyList(), listOf(expr), expr.ann)
    } catch (e: EocError) {
        showEocError(e, source, "GraphBuilder error")
        throw e
    }
    FileWriter("tools/out.dot").use {
        graphsToDot(gs, it)
    }
    val graphInterpResult = interp(gs, gb.id)
    println("Graph -> $graphInterpResult")
    require(exprInterpResult == graphInterpResult) {
        "Expr and graph results differ"
    }
    return graphInterpResult
}

private fun main() {
    val result = runProgram(LambdaTests.SUM)
    println("Ok: $result")
}