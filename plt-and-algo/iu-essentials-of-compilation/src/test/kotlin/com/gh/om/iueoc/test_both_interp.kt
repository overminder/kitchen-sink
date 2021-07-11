package com.gh.om.iueoc

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory

class TestBothInterp {
    @TestFactory
    fun testCases(): List<DynamicTest> {
        return AllPlaygroundTests.ALL.flatMap { suite ->
            val suiteName = suite.name.lowercase()
            suite.get().map {
                val testName = "$suiteName.${it.name.lowercase()}"
                val source = it.get()
                DynamicTest.dynamicTest(testName) {
                    val ir = RunBothInterp.parse(source)
                    RunBothInterp.opt(ir)
                    val (exprResult, graphResult) = RunBothInterp.run(ir)
                    assertEquals(exprResult, graphResult, "Interp and graph result mismatch")
                }
            }
        }
    }
}