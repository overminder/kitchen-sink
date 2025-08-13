package com.gh.om.gamemacros.scratch

/*

object MapRegexGen {
    enum class QuantType {
        General,
        Map,
        Currency,
        Scarab;
    }

    enum class BOpType {
        /**
         * Conjunction
         */
        And,

        /**
         * Disjunction
         */
        Or;
    }

    sealed class Term {
        data class Quant(
            val type: QuantType,
            val gte: Int
        ) : Term()

        data class BOp(
            val type: BOpType,
            val lhs: Term,
            val rhs: Term
        ) : Term()
    }

    data class PoeTopLevelRegex(val conjunctions: List<PoeRegexTerm>)
    data class PoeRegexTerm(val disjunctions: List<Quant>)

    fun List<Term>.orStar(): Term {
        return drop(1).fold(first()) { lhs, rhs ->
            BOp(BOpType.Or, lhs, rhs)
        }
    }

    fun transformToPoe(input: Term): PoeTopLevelRegex {
        // Step 1: Transform to POE normal form.
        // POE Normal Form refers to "conjunction of disjunction", or "a list of
        // toplevel terms connected by AND, while each sub-term can be
        // connected by OR.

        fun toPnf(input: Term): Term {
            when (input) {
                is BOp -> {
                    when (input.type) {
                        BOpType.And -> input.copy(
                            lhs = toPnf(input.lhs),
                            rhs = toPnf(input.rhs),
                        )

                        BOpType.Or -> TODO()
                    }
                }

                is Quant -> input
            }
        }
    }

    val highCurrency = Quant(
        QuantType.Currency,
        150
    )

    val highScarab = Quant(
        QuantType.Scarab,
        120
    )

    val mixedCurrencyScarab1 = BOp(
        BOpType.And,
        Quant(
            QuantType.Currency,
            100
        ),
        Quant(
            QuantType.Scarab,
            50
        ),
    )

    val mixedCurrencyScarab2 = BOp(
        BOpType.And,
        Quant(
            QuantType.Currency,
            50
        ),
        Quant(
            QuantType.Scarab,
            70
        ),
    )
}


 */
