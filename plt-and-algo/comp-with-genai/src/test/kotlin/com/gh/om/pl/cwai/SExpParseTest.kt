package com.gh.om.pl.cwai

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test

class SExpParseTest {
    @Test
    fun testParseIntSimple() {
        val e = SExp.parse("123")
        assertTrue(e is SExp.SInt)
        e as SExp.SInt
        assertEquals(123, e.value)
        assertEquals(SourceLoc("<input>", 1, 1), e.sourceLoc)
    }

    @Test
    fun testParseSymSimple() {
        val e = SExp.parse("foo")
        assertTrue(e is SExp.SSym)
        e as SExp.SSym
        assertEquals("foo", e.value)
        assertEquals(SourceLoc("<input>", 1, 1), e.sourceLoc)
    }

    @Test
    fun testParseListOfInts() {
        val e = SExp.parse("(123 456)")
        assertTrue(e is SExp.SList)
        e as SExp.SList
        assertEquals(SourceLoc("<input>", 1, 1), e.sourceLoc)
        assertEquals(2, e.value.size)
        val a = e.value[0] as SExp.SInt
        val b = e.value[1] as SExp.SInt
        assertEquals(123, a.value)
        assertEquals(456, b.value)
        assertEquals(SourceLoc("<input>", 1, 2), a.sourceLoc)
        assertEquals(SourceLoc("<input>", 1, 6), b.sourceLoc)
    }

    @Test
    fun testParseNestedDefine() {
        val e = SExp.parse("(define x (+# 1 2))") as SExp.SList
        assertEquals(3, e.value.size)
        val symDefine = e.value[0] as SExp.SSym
        val symX = e.value[1] as SExp.SSym
        val plusCall = e.value[2] as SExp.SList
        assertEquals("define", symDefine.value)
        assertEquals("x", symX.value)
        assertEquals(3, plusCall.value.size)
        val plusSym = plusCall.value[0] as SExp.SSym
        val one = plusCall.value[1] as SExp.SInt
        val two = plusCall.value[2] as SExp.SInt
        assertEquals("+#", plusSym.value)
        assertEquals(1, one.value)
        assertEquals(2, two.value)
    }

    @Test
    fun testParseBracketsSquare() {
        val e = SExp.parse("[1 2]") as SExp.SList
        assertEquals(2, e.value.size)
        val one = e.value[0] as SExp.SInt
        val two = e.value[1] as SExp.SInt
        assertEquals(1, one.value)
        assertEquals(2, two.value)
        assertEquals(SourceLoc("<input>", 1, 2), one.sourceLoc)
        assertEquals(SourceLoc("<input>", 1, 4), two.sourceLoc)
    }

    @Test
    fun testParseWithComments() {
        val src = """
            (123 ; comment here
             456)
        """.trimIndent()
        val e = SExp.parse(src) as SExp.SList
        assertEquals(2, e.value.size)
        val a = e.value[0] as SExp.SInt
        val b = e.value[1] as SExp.SInt
        assertEquals(123, a.value)
        assertEquals(456, b.value)
        assertEquals(SourceLoc("<input>", 1, 2), a.sourceLoc)
        assertEquals(SourceLoc("<input>", 2, 2), b.sourceLoc)
    }

    @Test
    fun testUnexpectedClosingToken() {
        assertThrows(IllegalArgumentException::class.java) {
            SExp.parse(")")
        }
    }

    @Test
    fun testMismatchedBrackets() {
        assertThrows(IllegalArgumentException::class.java) {
            SExp.parse("(]")
        }
    }

    @Test
    fun testTrailingTokensRejected() {
        assertThrows(IllegalArgumentException::class.java) {
            SExp.parse("123 456")
        }
    }

    @Test
    fun testInvalidIntFollowedByLetters() {
        assertThrows(IllegalArgumentException::class.java) {
            SExp.parse("123foo")
        }
    }

    @Test
    fun testEmptyListAndSourceLoc() {
        val e = SExp.parse("()") as SExp.SList
        assertTrue(e.value.isEmpty())
        assertEquals(SourceLoc("<input>", 1, 1), e.sourceLoc)
    }

    @Test
    fun testSymbolAllowedPunct() {
        val e = SExp.parse("a+b/c\\d.e-=") as SExp.SSym
        assertEquals("a+b/c\\d.e-=", e.value)
    }

    @Test
    fun testParseNegativeIntSimple() {
        val e = SExp.parse("-123")
        assertTrue(e is SExp.SInt)
        e as SExp.SInt
        assertEquals(-123, e.value)
        assertEquals(SourceLoc("<input>", 1, 1), e.sourceLoc)
    }

    @Test
    fun testParseListWithNegativeInts() {
        val e = SExp.parse("(-1 2 -3)") as SExp.SList
        assertEquals(3, e.value.size)
        val a = e.value[0] as SExp.SInt
        val b = e.value[1] as SExp.SInt
        val c = e.value[2] as SExp.SInt
        assertEquals(-1, a.value)
        assertEquals(2, b.value)
        assertEquals(-3, c.value)
        assertEquals(SourceLoc("<input>", 1, 2), a.sourceLoc) // starts at '-'
        assertEquals(SourceLoc("<input>", 1, 5), b.sourceLoc)
        assertEquals(SourceLoc("<input>", 1, 7), c.sourceLoc)
    }

    @Test
    fun testMinusAloneIsSymbol() {
        val e = SExp.parse("-") as SExp.SSym
        assertEquals("-", e.value)
        assertEquals(SourceLoc("<input>", 1, 1), e.sourceLoc)
    }

    @Test
    fun testInvalidNegativeIntFollowedByLetters() {
        assertThrows(IllegalArgumentException::class.java) {
            SExp.parse("-123foo")
        }
    }
}
