package yux.ktcpg

import org.jetbrains.kotlin.psi.*
import org.jetbrains.kotlin.psi.psiUtil.isPublic

object DetektLibCodeMustType {
    fun detektLookAtFunction() {
        val f = parseToKtFile("fun foo() = 5")
        val fst = f.declarations.first() as KtNamedFunction
        DetektLibCodeMustType.runCheck(fst)
    }

    fun detektLookAtObjectMethod() {
        val f = parseToKtFile(objLits)
        DetektLibCodeMustType.checkContentDecls(f)
    }

    fun checkContentDecls(of: KtClassOrObject) {
        println("Checking classOrObject ${of.name}")
        for (decl in of.declarations) {
            val f = decl as? KtNamedFunction ?: continue
            runCheck(f)
        }
    }

    fun checkContentDecls(of: KtFile) {
        for (decl in of.declarations) {
            when (decl) {
                is KtClassOrObject -> checkContentDecls(decl)
                is KtProperty -> {
                    // Allow val foo = object: ...
                    (decl.initializer as? KtObjectLiteralExpression)?.let { init ->
                        println("Checking val ${decl.name}")
                        checkContentDecls(init.objectDeclaration)
                    }
                }
            }
        }
    }

    // Helpers

    private val KtNamedFunction.hasExpressionBodyWithoutExplicitReturnType: Boolean
        get() = equalsToken != null && !hasDeclaredReturnType()

    fun runCheck(f: KtNamedFunction) {
        val notPassed = !f.isLocal && f.isPublic && f.hasExpressionBodyWithoutExplicitReturnType
        val flags = listOf(
                if (f.isLocal) "L" else "nl",
                if (f.isPublic) "P" else "np",
                if (f.hasExpressionBodyWithoutExplicitReturnType) "E" else "ne",
                if (KtPsiUtil.isLocal(f)) "PsiL" else "nPsiL"
        )
        println("${f.name} passed: ${!notPassed}, flags: $flags")
    }
}

private val twoObjects = """
    object Foo {
        fun f1() = 5
        private fun f2() = 5
    }
    
    private object Bar {
        fun f1() = 5
        private fun f2() = 5
    }
""".trimIndent()

private val objLits = """
    interface Foo {
        fun f1(): Int
    }
    
    val foo = object: Foo {
        override fun f1() = 5
    }
    
    private object Baz: Foo {
        override fun f1() = 5
    }
""".trimIndent()
