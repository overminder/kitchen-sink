package com.gh.om.shuati.bigint

import kotlin.math.absoluteValue
import kotlin.math.max
import kotlin.math.sqrt
import kotlin.random.Random

fun main() {
    val a = 0
    val b = 5

    val bigInt = (BigInt.from(a) + -b)
    val digits = bigInt.digits()

    shouldBeEqual(
        actual = digits,
        expected = (a.toLong() + -b.toLong()).toString(),
        "$a + -$b"
    )
}

fun main0() {
    shouldBeEqual(BigInt.from(10, radix = 2).digits(), "1010")
    shouldBeEqual(BigInt.from(-123, radix = 10).digits(), "-123")
    shouldBeEqual((BigInt.from(-123, radix = 10) + 124).digits(), "1")
    shouldBeEqual((BigInt.from(3) * 6).digits(), "18")
    shouldBeEqual((BigInt.from(3) * -6).digits(), "-18")
    println(BigInt.from(100).power(100).digits())

    val rng = Random(1234)
    repeat(1000) {
        randomTest(rng)
    }
}

fun randomTest(rng: Random) {
    val a = rng.nextInt()
    val b = rng.nextInt()
    shouldBeEqual(
        actual = (BigInt.from(a) * b).digits(),
        expected = (a.toLong() * b.toLong()).toString(),
        "$a * $b"
    )
    shouldBeEqual(
        actual = (BigInt.from(a) * -b).digits(),
        expected = (a.toLong() * -b.toLong()).toString(),
        "$a * -$b"
    )
    shouldBeEqual(
        actual = (BigInt.from(a) + b).digits(),
        expected = (a.toLong() + b.toLong()).toString(),
        "$a + $b"
    )
    shouldBeEqual(
        actual = (BigInt.from(a) + -b).digits(),
        expected = (a.toLong() + -b.toLong()).toString(),
        "$a + -$b"
    )
}

fun <A> shouldBeEqual(actual: A, expected: A, message: String? = null) {
    if (actual != expected) {
        error("Not equal ($message): expecting $expected != actual $actual")
    }
}

data class BigInt(
    /**
     * Least-significant words first.
     */
    val words: List<Int>,
    /**
     * Must be smaller than sqrt(Int.MAX_VALUE), so addition and multiplication won't overflow
     */
    val radix: Int,
    val sign: Sign,
) {
    init {
        assert(words.all {
            it in 0..<radix
        })
        assert(radix > 1 && radix < sqrt(Int.MAX_VALUE.toDouble()))
    }

    fun digits(): String {
        return if (words.isEmpty()) {
            "0"
        } else {
            val sign = when (sign) {
                Sign.Positive -> ""
                Sign.Negative -> "-"
            }
            words.asReversed().joinToString(prefix = sign, separator = "")
        }
    }

    operator fun plus(other: BigInt): BigInt {
        return addInternal(other.withRadix(radix))
    }

    operator fun times(other: BigInt): BigInt {
        return multiplyInternal(other.withRadix(radix))
    }

    // Naive version
    fun power(other: BigInt): BigInt {
        var product = BigInt.from(1, radix)
        other.repeatCountTimes {
            product *= this
        }
        return product
    }

    fun repeatCountTimes(f: () -> Unit) {
        fun go(wordIndex: Int) {
            if (wordIndex >= words.size) {
                return
            }
            repeat(words[wordIndex]) {
                f()
            }
            repeat(radix) {
                go(wordIndex + 1)
            }
        }
        go(0)
    }

    private fun withRadix(newRadix: Int): BigInt {
        if (radix == newRadix) {
            return this
        }

        // Iteratively.
        TODO()
    }

    private fun multiplyInternal(other: BigInt): BigInt {
        /**
         * idea:
         *            ab
         *          * cd
         *          ----
         *       a*d b*d
         * + a*c b*c
         * -------------
         */
        var sum = from(0, radix)
        for (ow in other.words.withIndex()) {
            for (w in words.withIndex()) {
                val sumBefore = sum
                sum += from(w.value * ow.value, radix).shiftLeft(w.index + ow.index)
            }
        }
        return sum.copy(sign = sign * other.sign)
    }

    fun shiftLeft(by: Int): BigInt {
        return BigInt(List(by) { 0 } + words, radix, sign)
    }

    private fun addInternal(other: BigInt): BigInt {
        var carryOver = 0

        val outputs = mutableListOf<Int>()
        for (wordIndex in 0 until max(words.size, other.words.size)) {
            val word = words.getOrElse(wordIndex) { 0 }.applySign(sign)
            val otherWord = other.words.getOrElse(wordIndex) { 0 }.applySign(other.sign)
            var sum = word + otherWord + carryOver
            if (sum >= radix) {
                carryOver = 1
                sum -= radix
            } else if (sum < 0) {
                carryOver = -1
                sum += radix
            } else {
                carryOver = 0
            }
            outputs += sum
        }
        val sign = if (carryOver != 0) {
            outputs += carryOver.absoluteValue
            carryOver.sign
        } else {
            Sign.Positive
        }
        // Norm
        val normed = outputs.asReversed().dropWhile { it == 0 }.reversed()
        return BigInt(normed, radix, sign)
    }

    operator fun plus(other: Int) = this + from(other, radix)
    operator fun times(other: Int) = this * from(other, radix)
    fun power(other: Int) = power(from(other, radix))

    enum class Sign {
        Positive,
        Negative;

        operator fun times(other: Sign): Sign {
            return if (this == other) {
                Positive
            } else {
                Negative
            }
        }
    }

    companion object {
        fun from(
            value: Int,
            radix: Int = 10
        ): BigInt {
            var valueIter = value.absoluteValue
            val words = mutableListOf<Int>()
            while (valueIter != 0) {
                val rem = valueIter % radix
                valueIter /= radix
                words += rem
            }
            return BigInt(words, radix, value.sign)
        }

        private val Int.sign: Sign
            get() = if (this < 0) {
                Sign.Negative
            } else {
                Sign.Positive
            }

        private fun Int.applySign(sign: Sign) = when (sign) {
            Sign.Positive -> this
            Sign.Negative -> -this
        }
    }
}
