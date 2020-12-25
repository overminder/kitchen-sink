package com.gh.om.blizzapi

import com.gh.om.blizzapi.base.Bapi
import com.gh.om.blizzapi.base.Simc
import com.gh.om.blizzapi.geardrops.is2hWeapon
import java.io.File
import java.io.FileInputStream
import java.io.InputStreamReader
import javax.inject.Inject

/**
 * Accessing Simc's generated static data tables.
 */
class SimcCxxSourceReaderImpl(private val rootDir: File) : Simc.CxxSourceReader {
    private fun openForRead(relPath: String): InputStreamReader {
        return InputStreamReader(FileInputStream(File(rootDir, relPath)), Charsets.UTF_8)
    }

    private fun pathForGenerated(fileName: String): String {
        return "engine/dbc/generated/$fileName.inc"
    }

    override fun getRandPropPoints(): List<Simc.RandomProp> {
        val nv = openForRead(pathForGenerated("rand_prop_points")).useLines { lines ->
            val tokens = lines
                .dropWhile { !it.contains("__rand_prop_points_data") }
                .drop(1)
                .takeWhile { !it.contains("} };") }
                .flatMap(::tokenize)

            NestedReader(wrapWithBraces(tokens)).readTop()
        }
        return (nv as Nested.NArray).values.map { it.toRandomProp() }
    }

    override fun getCrmTable(): Map<Simc.CrmType, List<Double>> {
        return getScaleDataTable("__combat_ratings_mult_by_ilvl")
    }

    override fun getStamCrmTable(): Map<Simc.CrmType, List<Double>> {
        return getScaleDataTable("__stamina_mult_by_ilvl")
    }

    private fun getScaleDataTable(tableName: String): Map<Simc.CrmType, List<Double>> {
        val nv = openForRead(pathForGenerated("sc_scale_data")).useLines { lines ->
            val tokens = lines
                .dropWhile { !it.contains(tableName) }
                .drop(1)
                .takeWhile { !it.contains("};") }
                .flatMap(::tokenize)
            NestedReader(wrapWithBraces(tokens)).readTop()
        }
        val vs = (nv as Nested.NArray).values
        return Simc.CrmType.values().map {
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

class SimcLangReaderImpl @Inject constructor(
    private val bapi: Bapi
) : Simc.Lang.Reader {
    override suspend fun readItems(source: String): List<Simc.Lang.Item> {
        return source.lines().mapNotNull {
            val tline = it.trim()
            if (tline.isNotEmpty()) {
                parseLine(tline)
            } else {
                null
            }
        }
    }

    private suspend fun parseLine(line: String): Simc.Lang.Item {
        var slot: Simc.Slot? = null
        var id: String? = null
        var bonusIds: List<String>? = null
        var gemIds: List<String>? = null
        line.split(",").forEachIndexed { ix, attr ->
            val (name, values) = attr.split("=")
            if (ix == 0) {
                slot = Simc.Slot.valueOf(name.toUpperCase())
                require(values.isEmpty())
            } else {
                val valueIds = values.split("/")
                when (name) {
                    "id" -> {
                        require(valueIds.size == 1)
                        id = valueIds[0]
                    }
                    "bonus_id" -> bonusIds = valueIds
                    "gem_id" -> gemIds = valueIds
                    else -> {
                        // Ignore
                    }
                }
            }
        }

        val res = Simc.Lang.Item(
            slot = slot!!,
            id = id!!,
            bonusIds = bonusIds.orEmpty(),
            gemIds = gemIds.orEmpty(),
            is2hWeapon = bapi.getItem(id!!).is2hWeapon,
        )
        // Sanity check
        if (res.is2hWeapon) {
            require(res.slot == Simc.Slot.MAIN_HAND)
        }
        return res
    }
}

class SimcDBImpl @Inject constructor(reader: Simc.CxxSourceReader) : Simc.DB {
    private val randPropPoints by lazy { reader.getRandPropPoints() }
    override val randPropPointsByIlevel by lazy {
        randPropPoints.map {
            it.ilevel to it
        }.toMap()
    }
    override val crmTable by lazy { reader.getCrmTable() }
    override val stamCrmTable by lazy { reader.getStamCrmTable() }

    override fun inventoryToSlot(inventory: Item.Inventory): Simc.SlotCombination? {
        val res = when (inventory) {
            Item.Inventory.NON_EQUIP -> null
            Item.Inventory.HEAD -> Simc.Slot.HEAD
            Item.Inventory.NECK -> Simc.Slot.NECK
            Item.Inventory.SHOULDER -> Simc.Slot.SHOULDER
            Item.Inventory.BODY -> null
            Item.Inventory.CHEST -> Simc.Slot.CHEST
            Item.Inventory.WAIST -> Simc.Slot.WAIST
            Item.Inventory.LEGS -> Simc.Slot.LEGS
            Item.Inventory.FEET -> Simc.Slot.FEET
            Item.Inventory.WRIST -> Simc.Slot.WRIST
            Item.Inventory.HAND -> Simc.Slot.HANDS
            Item.Inventory.FINGER -> return Simc.SlotCombination.Or(listOf(Simc.Slot.FINGER1, Simc.Slot.FINGER2))
            Item.Inventory.TRINKET -> return Simc.SlotCombination.Or(listOf(Simc.Slot.TRINKET1, Simc.Slot.TRINKET2))
            Item.Inventory.WEAPON -> Simc.Slot.MAIN_HAND // Is this true?
            Item.Inventory.SHIELD -> TODO()
            Item.Inventory.RANGED -> TODO()
            Item.Inventory.CLOAK -> Simc.Slot.BACK
            Item.Inventory.TWOHWEAPON -> return Simc.SlotCombination.And(
                listOf(Simc.Slot.MAIN_HAND, Simc.Slot.OFF_HAND)
            )
            Item.Inventory.BAG -> null
            Item.Inventory.TABARD -> TODO()
            Item.Inventory.ROBE -> Simc.Slot.CHEST
            Item.Inventory.WEAPONMAINHAND -> Simc.Slot.MAIN_HAND
            Item.Inventory.WEAPONOFFHAND -> Simc.Slot.OFF_HAND
            Item.Inventory.HOLDABLE -> Simc.Slot.OFF_HAND
            Item.Inventory.AMMO -> TODO()
            Item.Inventory.THROWN -> TODO()
            Item.Inventory.RANGEDRIGHT -> TODO()
            Item.Inventory.QUIVER -> TODO()
            Item.Inventory.RELIC -> TODO()
        }
        return res?.let(Simc.SlotCombination::Just)
    }

    override fun tryTradeGearToken(itemId: String): List<String>? {
        return when (itemId) {
            "183898" -> listOf("184261", "184259")
            "183895" -> listOf("184258")
            "183888" -> listOf("184246")
            "183891" -> listOf("184249", "184247")
            else -> null
        }
    }
}

private fun Nested.toRandomProp(): Simc.RandomProp {
    require(this is Nested.NArray)
    require(values.size == 6)
    val ilevel = values[0] as Nested.NDouble
    val epic = values[3] as Nested.NArray
    val rare = values[4] as Nested.NArray
    val uncommon = values[5] as Nested.NArray
    return Simc.RandomProp(
        ilevel.value.toInt(),
        epic.asDoubleList(),
        rare.asDoubleList(),
        uncommon.asDoubleList()
    )
}
