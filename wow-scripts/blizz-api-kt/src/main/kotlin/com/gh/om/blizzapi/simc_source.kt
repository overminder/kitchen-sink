package com.gh.om.blizzapi

import java.io.File
import java.io.FileInputStream
import java.io.InputStreamReader
import javax.inject.Inject

/**
 * Accessing Simc's generated static data tables.
 */
object SimcSource {
    // Modeled from simc's random_prop_data_t.
    data class RandomProp(
        val ilevel: Int,
        val epic: List<Double>,
        val rare: List<Double>,
        val uncommon: List<Double>,
    ) {
        companion object {
            internal fun fromNested(nested: Nested): RandomProp {
                require(nested is Nested.NArray)
                require(nested.values.size == 6)
                val ilevel = nested.values[0] as Nested.NDouble
                val epic = nested.values[3] as Nested.NArray
                val rare = nested.values[4] as Nested.NArray
                val uncommon = nested.values[5] as Nested.NArray
                return RandomProp(
                    ilevel.value.toInt(),
                    epic.asDoubleList(),
                    rare.asDoubleList(),
                    uncommon.asDoubleList()
                )
            }
        }
    }

    class Reader(private val rootDir: File) {
        private fun openForRead(relPath: String): InputStreamReader {
            return InputStreamReader(FileInputStream(File(rootDir, relPath)), Charsets.UTF_8)
        }

        private fun pathForGenerated(fileName: String): String {
            return "engine/dbc/generated/$fileName.inc"
        }

        fun getRandPropPoints(): List<RandomProp> {
            val nv = openForRead(pathForGenerated("rand_prop_points")).useLines { lines ->
                val tokens = lines
                    .dropWhile { !it.contains("__rand_prop_points_data") }
                    .drop(1)
                    .takeWhile { !it.contains("} };") }
                    .flatMap(::tokenize)

                NestedReader(wrapWithBraces(tokens)).readTop()
            }
            return (nv as Nested.NArray).values.map(RandomProp::fromNested)
        }

        fun getCrmTable(): Map<ItemScaling.CrmType, List<Double>> {
            val nv = openForRead(pathForGenerated("sc_scale_data")).useLines { lines ->
                val tokens = lines
                    .dropWhile { !it.contains("__combat_ratings_mult_by_ilvl") }
                    .drop(1)
                    .takeWhile { !it.contains("};") }
                    .flatMap(::tokenize)
                NestedReader(wrapWithBraces(tokens)).readTop()
            }
            val vs = (nv as Nested.NArray).values
            return ItemScaling.CrmType.values().map {
                it to (vs[it.ordinal] as Nested.NArray).asDoubleList()
            }.toMap()
        }

        private fun tokenize(line: String): List<Pair<TokenReader.Token, String>> {
            val tr = TokenReader(line)
            tr.tokenizeAll()
            return tr.tokens
        }

        private fun wrapWithBraces(xs: Sequence<Pair<TokenReader.Token, String>>): Sequence<Pair<TokenReader.Token, String>> {
            val lbrace = sequenceOf(TokenReader.Token.LBRACE to "")
            val rbrace = sequenceOf(TokenReader.Token.RBRACE to "")
            return lbrace + xs + rbrace
        }
    }
}

internal class TokenReader(line: String) {
    private val tline = line.trim()
    private var ix = 0

    enum class Token {
        LBRACE,
        RBRACE,
        COMMA,
        NUMBER;
    }

    private val out = mutableListOf<Pair<Token, String>>()

    val tokens: List<Pair<Token, String>>
        get() = out

    fun tokenizeAll() {
        while (!eof()) {
            skip()
            readOnce()
        }
    }

    private fun readOnce() {
        val c = tline[ix++]
        when {
            c == '{' -> {
                out += Token.LBRACE to "{"
            }
            c == '}' -> {
                out += Token.RBRACE to "}"
            }
            c == ',' -> {
                out += Token.COMMA to ","
            }
            c == '/' -> {
                if (tline[ix] == '/') {
                    // Is comment: skip until end.
                    ix = tline.length
                } else {
                    throw NestedReader.ReadError("Unexpected char: $c at $ix (${tline.take(100)}")
                }
            }
            c.isDigit() -> {
                readNumber(c)
            }
            else -> {
                throw NestedReader.ReadError("Unexpected char: $c at $ix (${tline.take(100)}")
            }
        }
    }

    private fun readNumber(init: Char) {
        val buf = StringBuilder(init.toString())
        while (!eof()) {
            val c = tline[ix++]
            if (c.isDigit() || c == '.') {
                buf.append(c)
            } else if (c.isWhitespace()) {
                break
            } else if (c == '{' || c == ',' || c == '}') {
                ix -= 1
                break
            } else {
                throw NestedReader.ReadError("Unexpected char: $c")
            }
        }
        out += Token.NUMBER to buf.toString()
    }

    private fun eof(): Boolean = ix >= tline.length

    private fun skip() {
        while (ix < tline.length && tline[ix].isWhitespace()) {
            ix += 1
        }
    }
}

internal sealed class Nested {
    data class NArray(val values: List<Nested>) : Nested() {
        fun asDoubleList(): List<Double> {
            return values.map {
                (it as NDouble).value
            }
        }
    }

    data class NDouble(val value: Double) : Nested()
}

private class NestedReader(tokenSeq: Sequence<Pair<TokenReader.Token, String>>) {
    private val tokens = tokenSeq.iterator()

    class ReadError(message: String) : RuntimeException(message)

    fun readTop(): Nested {
        return readSome()
    }

    private fun takeNext(): Pair<TokenReader.Token, String> {
        return tokens.next()
    }

    private fun eof() = tokens.hasNext()

    private fun readSome(given: Pair<TokenReader.Token, String>? = null): Nested {
        val c = given ?: takeNext()
        return when (c.first) {
            TokenReader.Token.LBRACE -> readArray()
            TokenReader.Token.NUMBER -> readNumber(c.second)
            else -> throw ReadError("Unexpected token: $c")
        }
    }

    private fun readNumber(value: String): Nested.NDouble {
        return Nested.NDouble(value.toDouble())
    }

    private fun readArray(): Nested.NArray {
        val out = mutableListOf<Nested>()
        var canBeComma = false
        while (true) {
            val c = takeNext()
            when (c.first) {
                TokenReader.Token.RBRACE -> return Nested.NArray(out)
                else -> {
                    if (canBeComma) {
                        require(c.first == TokenReader.Token.COMMA)
                        canBeComma = false
                        continue
                    }
                    out += readSome(c)
                    canBeComma = true
                }
            }
        }
    }
}

class Simc @Inject constructor(reader: SimcSource.Reader) {
    val randPropPoints by lazy { reader.getRandPropPoints() }
    val crmTable by lazy { reader.getCrmTable() }
}
