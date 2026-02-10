package com.gh.om.ks.arpgmacro.core

import java.util.regex.Pattern

object PoeItemParser {
    val klassPat: Pattern = Pattern.compile("Item Class: (.+)")
    val rarityPat: Pattern =
        Pattern.compile("Rarity: (Normal|Magic|Rare|Unique)")
    val explicitModPat: Pattern =
        Pattern.compile("""(?<pos>Prefix|Suffix) Modifier "(?<name>.+?)"(?: \(Tier: (?<tier>\d+)\))?""")
    val qualPatV2: Pattern = Pattern.compile(
        "(?<name>" +
                PoeRollableItem.QualName.nameMap.keys
                    .joinToString("|") {
                        it.replace("(", "\\(").replace(")", "\\)")
                    } +
                """): \+(?<pct>\d+)%"""
    )
    val stackSizePat: Pattern = Pattern.compile("""Stack Size: ([0-9,]+)/""")

    fun parseAsRollable(ad: String): PoeRollableItem {
        val item = parse(ad)
        require(item is PoeRollableItem) {
            "Expecting rollable item, got $item from:\n$ad"
        }
        return item
    }

    fun getSpecialCaseKlass(
        ad: String,
        klass: PoeItem.Klass?,
        rawKlass: String,
    ): PoeItem.Klass? {
        if (klass.isMapLike()) {
            return if (T17 in ad) {
                PoeItem.Map(PoeItem.MapTier.T17)
            } else if (ZANA_INFLUENCED in ad) {
                PoeItem.Map(PoeItem.MapTier.T16_5)
            } else {
                PoeItem.Map(PoeItem.MapTier.Other)
            }
        }

        // In POE1, all weapons have APS.
        if ("Attacks per Second:" in ad && "Weapon Range:" in ad) {
            return PoeItem.Weapon(rawKlass)
        }

        if (rawKlass in POE2_WEAPON_TYPES) {
            return PoeItem.Weapon(rawKlass)
        }

        PoeItem.NonWeapon.fromRepr(rawKlass)?.let {
            return it
        }

        return null
    }

    fun parse(ad: String): PoeItem? {
        val rawKlass = matchGroup(ad, klassPat)
        var klass = rawKlass?.let(PoeItem.Klass::fromRepr)
        if (klass == PoeItem.ConstKlass.Currency) {
            return parseCurrency(ad)
        }
        val rarity = getRarity(ad) ?: return null
        val mods = findAllExplicitMods(ad)

        klass = rawKlass?.let {
            getSpecialCaseKlass(ad, klass, it)
        } ?: klass

        val quals = findQualities(ad)
        return PoeRollableItem(
            klass = klass,
            rarity = rarity,
            explicitMods = mods,
            qualities = quals,
            originalDescription = ad,
        )
    }

    private fun parseCurrency(ad: String): PoeCurrency? {
        val stackSize =
            matchGroup(ad, stackSizePat)?.replace(",", "")?.toIntOrNull()
                ?: return null
        val lines = ad.lines()
        // The 3rd line usually has the currency name
        val name = lines.getOrNull(2)
        val type = if (name == null) {
            PoeCurrency.UnknownType("")
        } else {
            // 1. Is that a tiered currency?
            parseTieredCurrency(name)
                ?: parseKnownCurrency(name)
                ?: PoeCurrency.UnknownType(name)
        }
        return PoeCurrency(type, stackSize)
    }

    private fun parseTieredCurrency(currencyName: String): PoeCurrency.Type? {
        val type = PoeCurrency.CanHaveTier.entries.firstOrNull { cht ->
            currencyName.endsWith(cht.repr)
        } ?: return null
        val tier = PoeCurrency.Tier.entries.firstOrNull { tier ->
            currencyName.startsWith(tier.name)
        }
        return PoeCurrency.TieredType(type, tier)
    }

    private fun parseKnownCurrency(currencyName: String): PoeCurrency.Type? {
        return PoeCurrency.KnownType.entries.firstOrNull { cty ->
            cty.repr == currencyName
        }
    }

    private fun matchGroup(
        input: String,
        pattern: Pattern,
        groupIx: Int = 1,
    ): String? {
        val m = pattern.matcher(input)
        return if (m.find()) {
            m.group(groupIx)
        } else {
            null
        }
    }

    private fun getRarity(ad: String): PoeRollableItem.Rarity? {
        return matchGroup(ad, rarityPat)?.let(PoeRollableItem.Rarity::valueOf)
    }

    private fun splitIntoBlocks(ad: String): List<String> {
        return ad.split("--------")
    }

    private fun findChunksOfExplicitMods(lines: List<String>): Sequence<Pair<String, String>> {
        return sequence {
            var modName: String? = null
            val descriptions = mutableListOf<String>()

            suspend fun SequenceScope<Pair<String, String>>.tryEmit() {
                modName?.let {
                    yield(it to descriptions.joinToString("; "))
                    modName = null
                    descriptions.clear()
                }
            }

            for (line in lines) {
                if (explicitModPat.matcher(line).find()) {
                    tryEmit()
                    modName = line
                } else {
                    descriptions += line
                }
            }
            tryEmit()
        }
    }

    private fun findAllExplicitMods(ad: String): List<PoeRollableItem.ExplicitMod> {
        val modsBlock = splitIntoBlocks(ad).firstOrNull {
            explicitModPat.matcher(it).find()
        } ?: return emptyList()

        return findChunksOfExplicitMods(modsBlock.trim().lines()).map {
            val (modName, modContent) = it
            val m = explicitModPat.matcher(modName)
            require(m.find()) {
                "Failed to parse mod: $modName"
            }
            val pos = m.group("pos")
            val name = m.group("name")
            val tier = m.group("tier")?.toIntOrNull()
            PoeRollableItem.ExplicitMod(
                loc = PoeRollableItem.ExplicitModLocation.valueOf(pos),
                name = name,
                tier = tier,
                description = modContent,
            )
        }.toList()
    }

    private fun findQualities(ad: String): List<PoeRollableItem.Quality> {
        val m = qualPatV2.matcher(ad)
        return generateSequence {
            if (m.find()) {
                val rawPct = m.group("pct")
                val value =
                    rawPct.toIntOrNull() ?: error("Unknown qual pct: $rawPct")
                val name = m.group("name")
                val qualName = PoeRollableItem.QualName.fromName(name)
                    ?: error("Unknown qual type: $name")
                PoeRollableItem.Quality(
                    name = qualName,
                    value = value,
                )
            } else {
                null
            }
        }.toList()
    }
}

private const val ZANA_INFLUENCED = "Area is Influenced by the Originator's Memories"
private const val T17 = "Map Tier: 17"

private val POE2_WEAPON_TYPES = listOf(
    "Staves",
    "Wands",
)
