package om.lang.pie

import java.lang.RuntimeException

/**
 * Instead of doing a global type inference (undecidable), Pie uses a simpler inference algorithm.
 * It alternates between two modes: check and infer. `check` type-checks an [Expr] against a
 * type, while `infer` infers a given [Expr].
 */

fun check(e: Expr, ty: Type) {
    val inferred = infer(e)
    if (inferred != null) {
        if (ty != inferred) {
            throw UnexpectedInferredType(e, inferred, ty)
        }
    }
}

/**
 * @return The inferred type, or null if [e] can't be type checked.
 */
fun infer(e: Expr): Type? {
    return when (e) {
        is Zero -> Nat
        is Succ -> {
            check(e.pred, Nat)
            Nat
        }
        is Type -> Set
        // ^ I.e. Set's type is also Set, which can be troublesome
        else -> error("Unreachable")
    }
}

data class UnexpectedInferredType(val e: Expr, val expected: Type, val inferred: Type) : RuntimeException()
