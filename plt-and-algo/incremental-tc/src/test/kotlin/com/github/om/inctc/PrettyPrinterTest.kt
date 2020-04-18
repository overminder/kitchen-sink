package com.github.om.inctc

import com.github.om.inctc.lang.poly.ModuleName
import com.github.om.inctc.lang.poly.PprState
import com.github.om.inctc.lang.poly.PolyLangParser
import com.github.om.inctc.lang.poly.ppr
import org.junit.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull

class PrettyPrinterTest {
    @Test
    fun testSome() {
        assertPpr("def foo = fun x in if 5 then 1 else 2 end end")
        assertPpr("""
            def foo = 5
            def bar = fun x in x < 5 end
            def baz = fun y in if baz(3, 6) then foo else 8 end end
        """.trimIndent())
    }

    private fun assertPpr(source: String) {
        val m = assertNotNull(PolyLangParser.file(ModuleName("test")).run(source))
        val st = PprState()
        m.ppr(st)
        val printed = st.output
        assertEquals(source, printed)
    }
}