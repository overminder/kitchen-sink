package com.gh.om.gamemacros.complex

import com.gh.om.gamemacros.MouseHooks
import com.gh.om.gamemacros.complex.CraftDecisionMaker.IntStackClusterAllowSingleRes.byDesiredOneSideMods
import com.gh.om.gamemacros.complex.PoeAltAugRegal.brandClusterDescription
import com.gh.om.gamemacros.complex.PoeAltAugRegal.lightningClusterForBrandDescriptions
import com.gh.om.gamemacros.complex.PoeItem.Klass.MiscMap
import com.gh.om.gamemacros.isPoeAndTriggerKeyEnabled
import com.gh.om.gamemacros.safeDelayK
import com.github.kwhat.jnativehook.mouse.NativeMouseEvent
import java.awt.Point
import java.util.regex.Pattern
import kotlin.math.min
import kotlin.text.contains
import kotlin.time.Duration.Companion.milliseconds

// More comprehensive crafting: transmute, alt, aug, regal, exalt.

sealed interface PoeItem {
    enum class Klass(val repr: String) {
        Currency("Stackable Currency"),
        Map("Maps"),
        MiscMap("Misc Map Items"),
        Jewels("Jewels");

        companion object {
            fun fromRepr(repr: String): Klass? {
                return entries.firstOrNull { it.repr == repr }
            }
        }
    }
}

fun PoeItem.Klass?.isMapLike(): Boolean {
    return when (this) {
        PoeItem.Klass.Map, MiscMap -> true

        else -> false
    }
}


fun interface PoeAffixMatcher {
    fun matches(affix: PoeRollableItem.ExplicitMod): Boolean

    companion object {
        private val digitsMatcher = Regex("""(\d+)""")

        fun byName(name: String): PoeAffixMatcher = PoeAffixMatcher {
            it.name == name
        }

        fun byNumericDescr(
            name: String,
            check: (numberInDescr: Int) -> Boolean,
        ): PoeAffixMatcher = object : PoeAffixMatcher {
            override fun matches(affix: PoeRollableItem.ExplicitMod): Boolean {
                if (affix.name != name) {
                    return false
                }
                val m = digitsMatcher.find(affix.description) ?: return false
                val number = m.groups[1]?.value?.toIntOrNull() ?: return false
                return check(number)
            }
        }
    }
}

data class PoeCurrency(
    val type: Type,
    val stackSize: Int,
) : PoeItem {
    interface Type

    enum class KnownType(val repr: String) : Type {
        Chaos("Chaos Orb"),
        Scour("Orb of Scouring"),
        Alch("Orb of Alchemy"),
    }

    object UnknownType : Type
}

data class PoeRollableItem(
    val klass: PoeItem.Klass?,
    val rarity: Rarity,
    val explicitMods: List<ExplicitMod>,
    val qualities: List<Quality>,
) : PoeItem {

    enum class Rarity {
        Normal,
        Magic,
        Rare,
    }

    enum class ExplicitModLocation {
        Prefix,
        Suffix,
    }

    // TODO add fractured
    data class ExplicitMod(
        val loc: ExplicitModLocation,
        // E.g. "of the Meteor"
        val name: String,
        val tier: Int?,
        val description: String,
    )

    data class Quality(
        val name: QualName,
        /**
         * Percentage
         */
        val value: Int,
    )

    sealed class QualName {
        data class Chisel(val ty: MapAug) : QualName()
        data class Native(val ty: MapAug) : QualName()

        companion object {
            val nameMap = mapOf(
                "Item Quantity" to Native(MapAug.Quant),
                "Item Rarity" to Native(MapAug.Rarity),
                "Monster Pack Size" to Native(MapAug.Pack),
                "More Currency" to Native(MapAug.Currency),
                "More Divination Cards" to Native(MapAug.DivCard),
                "More Maps" to Native(MapAug.Map),
                "More Scarabs" to Native(MapAug.Scarab),
                "Quality" to Chisel(MapAug.Quant),
                "Quality (Rarity)" to Chisel(MapAug.Rarity),
                "Quality (Pack Size)" to Chisel(MapAug.Pack),
                "Quality (Currency)" to Chisel(MapAug.Currency),
                "Quality (Divination Cards)" to Chisel(MapAug.DivCard),
                // Lol I don't think this exists
                "Quality (Maps)" to Chisel(MapAug.Map),
                "Quality (Scarabs)" to Chisel(MapAug.Scarab),
            )

            fun fromName(name: String) = nameMap[name]
        }
    }

    enum class MapAug {
        Quant, Rarity, Pack, Map, Currency, Scarab, DivCard
    }
}

fun PoeRollableItem.getAffix(name: String): PoeRollableItem.ExplicitMod? {
    return explicitMods.firstOrNull {
        it.name == name
    }
}

fun PoeRollableItem.hasAffix(name: String): Boolean {
    return getAffix(name) != null
}

fun PoeRollableItem.hasAffixThat(
    predicate: (PoeRollableItem.ExplicitMod) -> Boolean,
): Boolean {
    return explicitMods.any(predicate)
}

object PoeAltAugRegal {
    val sharedBaseJewelResMods = listOf(
        // single res, harvest swappable
        "of the Dragon",
        "of the Beast",
        "of Grounding",
        // fire-cold res
        "of the Hearth",
        // all res
        "of Resistance",
    )

    // 50% to avoid shock
    val SHOCK_AVOID = "of the Lightning Rod"

    // 6-8% phasing
    val PHASING = "of Phasing"

    val baseIntStackAbyss = listOf(
        // t1 & t2 ES
        "Resplendent",
        "Incandescent",
        // Int or str-int
        "of Intelligence",
        "of Spirit",
        // crit multi
        "of Potency",
        // movement speed
        "of Momentum",
        // AS when crit (why is this also on hypnotic?)
        "of Opportunity",
        // Searching only
        // AS
        "of Berserking",
        // Lightning attack damage
        "of Arcing",
        // t1 & t2 bow or wand lighting attack damage
        "Electrocuting",
        "Discharging",
    ) + sharedBaseJewelResMods

    val shockAvoidPhasingAbyss = baseIntStackAbyss + SHOCK_AVOID + PHASING

    val wanderCobalt = listOf(
        // Prefixes
        "Battlemage's", // shield spell inc
        "Jinxing", // wand AS
        "Charging", // shield AS
        "Shimmering", // ES%
        // Suffixes
        "of Zeal", // hybrid AS
        "of Berserking", // AS
        "of Intelligence", // int
        "of Spirit", // str-int
        "of Potency", // crit multi
        "of the Phoenix", // max fire res
        "of the Kraken", // max cold res
        "of the Leviathan", // max lightning res
    ) + sharedBaseJewelResMods

    val intStackCluster = listOf(
        // 12 ES
        "Glowing",
        // 35% inc effect
        "Powerful",
        // 8 int
        "of the Prodigy",
    )

    fun notableOf(names: List<String>) = names.map {
        "1 Added Passive Skill is $it"
    }

    val lightningClusterForBrandDescriptions = notableOf(
        listOf(
            "Inspired Oppression",
            "Remarkable",
            "Overshock",
            "Prismatic Heart",
            "Sadist",
            "Thunderstruck",
            "Disorienting Display",
            "Doryani's Lesson",
            "Widespread Destruction"
        )
    )

    val brandClusterDescription = notableOf(
        listOf(
            "Grand Design",
            "Remarkable",
        )
    )

    val gemLevelAmulet = listOf(
        // All +1
        "Exalter's",
    )

    suspend fun main() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            val crafter = RealCrafterOnCurrencyTab()
            repeat(2000) {
                if (!isPoe.value) {
                    return
                }
                if (craftOnce(crafter)) {
                    return
                }
            }
        }
        LEADER_KEY.isEnabled("07").collect(::handle)
    }

    private suspend fun craftOnce(crafter: RealCrafterOnCurrencyTab): Boolean {
        val before = crafter.getCurrentItem()
        val decision = CraftMethods.altAugRegalExaltOnce(
            c = crafter,
            // CraftDecisionMaker.IntStackClusterAllowSingleRes,
            // CraftDecisionMaker.ByDesiredMods(intStackCluster, 2),
            // CraftDecisionMaker.ByDesiredMods(gemLevelAmulet, 1),
            CraftDecisionMaker.lightningClusterForBrand,
        )
        // println("$decision on $before")
        return decision.done
    }
}

object PoeHarvestReforge {
    val itemInHarvestBench = Point(1287, 608)
    val harvestCraftButton = Point(1295, 814)

    val spellShield = listOf(
        // T1 Spell Inc
        "Runic",
    )

    suspend fun main() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            repeat(100) {
                if (!isPoe.value) {
                    return
                }
                if (getAndCheckStat(spellShield)) {
                    return
                }
                harvestOnce()
            }
        }
        LEADER_KEY.isEnabled("10").collect(::handle)
    }

    private suspend fun getAndCheckStat(checklist: List<String>): Boolean {
        MouseHooks.moveTo(itemInHarvestBench)
        safeDelayK(50.milliseconds)

        val ad = PoeInteractor.getAdvancedDescriptionOfItemUnderMouse() ?: ""
        val item = PoeItemParser.parseAsRollable(ad)
        val allMatch = checklist.any { desired ->
            item.explicitMods.any { it.name == desired }
        }
        val isGood = item.explicitMods.count {
            it.tier == 1
        } >= 3
        return allMatch || isGood
    }

    private suspend fun harvestOnce() {
        MouseHooks.postClick(
            point = harvestCraftButton,
            moveFirst = true,
        )
        safeDelayK(50.milliseconds)
    }
}

object PoeItemParser {
    val klassPat = Pattern.compile("Item Class: (.+)")
    val rarityPat =
        Pattern.compile("Rarity: (Normal|Magic|Rare)")
    val explicitModPat =
        Pattern.compile("""(?<pos>Prefix|Suffix) Modifier "(?<name>.+?)"(?: \(Tier: (?<tier>\d+)\))?""")
    val qualPat = Pattern.compile("""(?<name>[a-zA-Z ()]+): \+(?<pct>\d+)%""")
    val stackSizePat = Pattern.compile("""Stack Size: ([0-9,]+)/""")

    fun parseAsRollable(ad: String): PoeRollableItem {
        val item = parse(ad)
        require(item is PoeRollableItem) {
            "Expecting rollable item, got $item from:\n$ad"
        }
        return item
    }

    /**
     * @param ad Advanced description of an item
     */
    fun parse(ad: String): PoeItem? {
        val klass =
            matchGroup(ad, klassPat)?.let(PoeItem.Klass::fromRepr)
        if (klass == PoeItem.Klass.Currency) {
            return parseCurrency(ad)
        }
        val rarity = getRarity(ad) ?: return null
        val mods = findAllExplicitMods(ad)
        val quals = if (klass.isMapLike()) {
            // XXX fix this (cluster "added grant: 3%" also matched)
            findQualities(ad)
        } else {
            emptyList()
        }
        return PoeRollableItem(
            klass = klass,
            rarity = rarity,
            explicitMods = mods,
            qualities = quals
        )
    }

    private fun parseCurrency(ad: String): PoeCurrency? {
        val stackSize =
            matchGroup(ad, stackSizePat)?.replace(",", "")?.toIntOrNull()
                ?: return null
        val type = ad.lines().asSequence().mapNotNull { line ->
            PoeCurrency.KnownType.entries.firstOrNull { cty ->
                cty.repr == line
            }
        }.firstOrNull() ?: PoeCurrency.UnknownType
        return PoeCurrency(type, stackSize)
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

    // POE item description is delimited by dashes.
    // Explicit modifiers specifically occupy two lines, so identifying
    // the blocks first help.
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
                    // Found new mod. Finish previous mod
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
                description = modContent
            )
        }.toList()
    }

    private fun findQualities(ad: String): List<PoeRollableItem.Quality> {
        // XXX qualPat need to be stricter, or it may match things from the
        // explicit block.
        val m = qualPat.matcher(ad)
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

object PoeCurrencyTab {
    val item = Point(452, 609)

    val transmute = Point(62, 355)
    val alch = Point(654, 364)
    val alt = Point(146, 361)
    val aug = Point(302, 432)
    val chaos = Point(730, 356)
    val regal = Point(574, 352)
    val scour = Point(576, 678)
    val exalt = Point(397, 359)
    val annul = Point(226, 360)
}

object PoeAutoAlt {

    val intStackWandWiderAffixes = listOf(
        "per 1",
        "Runic",
        "Acclaim",
        "Incision",
        "Destruction",
        "Vapourising",
    )

    val intStackWandPrefixes = listOf(
        // Includes both spell per 16 and lightning per 10
        "per 1",
        // T1 Spell%
        "Runic",
        // T1 Lightning attack#
        "Vapourising",
    )

    val intShield = listOf(
        "Runic",
        // T1 ES
        "Incandescent",
        // T1 ES%
        "Unfaltering",
        // T1 Hybrid ES%
        "Seraphim",
        // T1 Int
        "of the Genius"
    )

    val intShield86 = listOf(
        "Runic",
        // T1 ES%
        "Unfaltering",
        // T1 Int
        "of the Genius"
    )

    suspend fun play() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            repeat(500) {
                if (!isPoe.value) {
                    return
                }
                if (getAndCheckStat(intShield)) {
                    return
                }
                altOnceToItemInCurrencyTab()
            }
        }
        LEADER_KEY.isEnabled("04").collect(::handle)
    }

    private suspend fun getAndCheckStat(checklist: List<String>): Boolean {
        val stat = getItemStatFromCurrencyTab() ?: return false
        val found = checklist.firstOrNull {
            stat.contains(it, ignoreCase = true)
        }
        if (found != null) {
            println("Found $found")
        }
        return found != null
    }

    private suspend fun altOnceToItemInCurrencyTab() {
        MouseHooks.postClick(
            point = PoeCurrencyTab.alt,
            moveFirst = true,
            button = NativeMouseEvent.BUTTON2
        )
        safeDelayK(30.milliseconds)
        MouseHooks.postClick(
            point = PoeCurrencyTab.item,
            moveFirst = true,
            button = NativeMouseEvent.BUTTON1
        )
        safeDelayK(30.milliseconds)
    }

    private suspend fun getItemStatFromCurrencyTab(): String? {
        MouseHooks.moveTo(PoeCurrencyTab.item)
        safeDelayK(30.milliseconds)

        return PoeInteractor.getDescriptionOfItemUnderMouse()
    }
}

/**
 * Shared interface between the actual crafting interface and the simulator.
 */
interface PoeItemCrafter {
    suspend fun getCurrentItem(): PoeRollableItem

    suspend fun transmute()
    suspend fun alternate()
    suspend fun augment()
    suspend fun regal()
    suspend fun exalt()
    suspend fun scour()
    suspend fun annul()
    suspend fun chaos()
    suspend fun alch()
}

private class RealCrafterOnCurrencyTab : PoeItemCrafter {
    // Cached when there's no operation.
    private var cachedCurrentItem: PoeRollableItem? = null

    override suspend fun getCurrentItem(): PoeRollableItem {
        cachedCurrentItem?.let { return it }

        MouseHooks.moveTo(PoeCurrencyTab.item)
        safeDelayK(50.milliseconds)

        val ad = PoeInteractor.getAdvancedDescriptionOfItemUnderMouse() ?: ""
        val parsed = PoeItemParser.parseAsRollable(ad)
        cachedCurrentItem = parsed
        return parsed
    }

    private suspend fun useCurrency(currencyPosition: Point) {
        // Invalidate
        cachedCurrentItem = null

        MouseHooks.postClick(
            currencyPosition,
            NativeMouseEvent.BUTTON2,
            moveFirst = true
        )

        safeDelayK(30.milliseconds)

        MouseHooks.postClick(
            PoeCurrencyTab.item,
            NativeMouseEvent.BUTTON1,
            moveFirst = true
        )

        safeDelayK(30.milliseconds)
    }

    override suspend fun transmute() {
        useCurrency(PoeCurrencyTab.transmute)
    }

    override suspend fun alternate() {
        useCurrency(PoeCurrencyTab.alt)
    }

    override suspend fun augment() {
        useCurrency(PoeCurrencyTab.aug)
    }

    override suspend fun regal() {
        useCurrency(PoeCurrencyTab.regal)
    }

    override suspend fun exalt() {
        useCurrency(PoeCurrencyTab.exalt)
    }

    override suspend fun scour() {
        useCurrency(PoeCurrencyTab.scour)
    }

    override suspend fun annul() {
        useCurrency(PoeCurrencyTab.annul)
    }

    override suspend fun chaos() {
        useCurrency(PoeCurrencyTab.chaos)
    }

    override suspend fun alch() {
        useCurrency(PoeCurrencyTab.alch)
    }
}

private fun interface CraftDecisionMaker {
    fun getDecision(item: PoeRollableItem): Decision

    data class Decision(
        val type: DecisionType,
        val why: String,
    ) {
        val done: Boolean
            get() = type == DecisionType.Done
    }

    enum class DecisionType {
        Done,
        Reset,
        Proceed,
        GoBack;
    }

    object IntStackClusterAllowSingleRes : CraftDecisionMaker {
        val mustHave = listOf(
            // 12 ES
            "Glowing",
            // 35% inc effect
            "Powerful",
        )
        val oneOfAttr = listOf(
            // 8 int
            "of the Prodigy",
            // 4 attr
            "of the Meteor",
            // 3 AS (attack or shield cluster)
            "of Mastery",
        )
        val oneOfRes = listOf<String>(
            // 4 res
            "of the Kaleidoscope",
            // Elem res
            "of the Drake",
            "of the Penguin",
            "of the Storm",
        )
        val desiredModCount = 4

        override fun getDecision(item: PoeRollableItem): Decision {
            require(item.klass == PoeItem.Klass.Jewels) {
                "$item is not jewels"
            }
            val nMustHave = item.explicitMods.count {
                it.name in mustHave
            }
            var nRes = min(item.explicitMods.count { it.name in oneOfRes }, 1)
            val nAttr = min(item.explicitMods.count { it.name in oneOfAttr }, 2)
            if (item.rarity == PoeRollableItem.Rarity.Magic) {
                // Ignore res suffix on magic to save regal -- we want
                // int on magic such that regal has a high chance to land.
                nRes = 0
            }
            return byMatches(
                matches = nMustHave + nRes + nAttr,
                desiredModCount = desiredModCount,
                nMods = item.explicitMods.size
            )
        }
    }

    fun byDesiredMods(
        desiredModNames: List<String>,
        desiredModCount: Int,
    ): CraftDecisionMaker = ByDesiredModsEx(
        desiredModCount = desiredModCount,
    ) {
        it.name in desiredModNames
    }

    class ByDesiredModsEx(
        private val desiredModCount: Int,
        private val doesModMatch: (PoeRollableItem.ExplicitMod) -> Boolean,
    ) : CraftDecisionMaker {
        override fun getDecision(item: PoeRollableItem): Decision {
            val matches = item.explicitMods.count(doesModMatch)

            return byMatches(
                matches = matches,
                desiredModCount = desiredModCount,
                nMods = item.explicitMods.size
            )
        }
    }

    fun byDesiredOneSideMods(
        desiredModNames: List<String>,
        side: PoeRollableItem.ExplicitModLocation,
    ): CraftDecisionMaker {
        return ByDesiredOneSideModsEx(side = side, desiredModCount = desiredModNames.size) { mods ->
            mods.count {
                it.name in desiredModNames
            }
        }
    }

    // For alt-aug-regal, where regal can land on either side
    class ByDesiredOneSideModsEx(
        private val side: PoeRollableItem.ExplicitModLocation,
        private val desiredModCount: Int,
        private val getMatchedMods: (List<PoeRollableItem.ExplicitMod>) -> Int,
    ) : CraftDecisionMaker {
        override fun getDecision(item: PoeRollableItem): Decision {
            val modsOnSide = item.explicitMods.filter { it.loc == side }
            val matches = getMatchedMods(modsOnSide)
            if (item.rarity == PoeRollableItem.Rarity.Rare &&
                matches < desiredModCount
            ) {
                return Decision(
                    type = DecisionType.Reset,
                    why = "Only $matches matches after regal"
                )
            }

            return byMatches(
                matches = matches,
                desiredModCount = desiredModCount,
                nMods = modsOnSide.size
            )
        }
    }

    companion object {
        val gloveTwoEs = byDesiredOneSideMods(
            listOf(
                "Seething",
                "Unassailable",
            ),
            PoeRollableItem.ExplicitModLocation.Prefix
        )

        fun matchesDescription(mod: PoeRollableItem.ExplicitMod, descriptions: List<String>): Boolean {
            return descriptions.any { it in mod.description }
        }

        val brandCluster = ByDesiredOneSideModsEx(
            PoeRollableItem.ExplicitModLocation.Prefix,
            2,
        ) { mods ->
            mods.count { mod ->
                matchesDescription(mod, brandClusterDescription)
            }
        }

        val lightningClusterForBrand = ByDesiredModsEx(3) {
            matchesDescription(it, lightningClusterForBrandDescriptions)
        }

        /**
         * @param matches The number of matched affixes on the current item
         * @param desiredModCount The number of desired affixes on a
         * fully crafted item
         * @param nMods The number of mods on the current item
         */
        private fun byMatches(
            matches: Int,
            desiredModCount: Int,
            nMods: Int,
        ): Decision {
            val type: DecisionType
            val why: String
            when {
                matches >= desiredModCount -> {
                    type = DecisionType.Done
                    why =
                        "Matches $matches mods is more than desired $desiredModCount"
                }

                matches == nMods -> {
                    type = DecisionType.Proceed
                    why = "All $nMods mods match"
                }

                matches == nMods - 1 && nMods == 4 -> {
                    type = DecisionType.GoBack
                    why = "All $nMods but 1 mod match"
                }

                else -> {
                    type = DecisionType.Reset
                    why = "Only $matches matches within $nMods"
                }
            }
            return Decision(type, why)
        }
    }
}

/**
 * Every execution advances one step. Returns True if crafting is done.
 */
private object CraftMethods {
    suspend fun scourAlchOnce(
        c: PoeItemCrafter,
        dm: CraftDecisionMaker,
    ): CraftDecisionMaker.Decision {
        val item = c.getCurrentItem()

        val decision = dm.getDecision(item)

        if (decision.type == CraftDecisionMaker.DecisionType.Done) {
            return decision
        }

        val why: String

        when (item.rarity) {
            PoeRollableItem.Rarity.Normal -> {
                why = "alch because normal"
                c.alch()
            }

            PoeRollableItem.Rarity.Magic -> {
                why = "scour - alch because magic"
                c.scour()
                c.alch()
            }

            PoeRollableItem.Rarity.Rare -> {
                why = "chaos because rare"
                c.scour()
                c.alch()
            }
        }
        return decision.copy(why = decision.why + ", impl = " + why)
    }

    suspend fun chaosOnce(
        c: PoeItemCrafter,
        dm: CraftDecisionMaker,
    ): CraftDecisionMaker.Decision {
        val item = c.getCurrentItem()

        val decision = dm.getDecision(item)

        if (decision.type == CraftDecisionMaker.DecisionType.Done) {
            return decision
        }

        val why: String

        when (item.rarity) {
            PoeRollableItem.Rarity.Normal -> {
                why = "alch because normal"
                c.alch()
            }

            PoeRollableItem.Rarity.Magic -> {
                why = "scour - alch because magic"
                c.scour()
                c.alch()
            }

            PoeRollableItem.Rarity.Rare -> {
                why = "chaos because rare"
                c.chaos()
            }
        }
        return decision.copy(why = decision.why + ", impl = " + why)
    }

    suspend fun altAugRegalExaltOnce(
        c: PoeItemCrafter,
        dm: CraftDecisionMaker,
    ): CraftDecisionMaker.Decision {
        val item = c.getCurrentItem()

        val decision = dm.getDecision(item)

        if (decision.type == CraftDecisionMaker.DecisionType.Done) {
            return decision
        }

        val shouldProceed =
            decision.type == CraftDecisionMaker.DecisionType.Proceed
        val shouldGoBack =
            decision.type == CraftDecisionMaker.DecisionType.GoBack

        val why: String

        when (item.rarity) {
            PoeRollableItem.Rarity.Normal -> {
                require(!shouldGoBack)
                why = "transmute because normal"
                c.transmute()
            }

            PoeRollableItem.Rarity.Magic -> {
                require(!shouldGoBack)
                // Check mod

                when (val nmods = item.explicitMods.size) {
                    0 -> {
                        why = "aug because 0 mod magic item"
                        // This can't happen, but let's augment.
                        c.augment()
                    }

                    1 -> {
                        if (shouldProceed) {
                            why = "aug 1 mod to 2 mods"
                            c.augment()
                        } else {
                            why = "alt to reset"
                            c.alternate()
                        }
                    }

                    2 -> {
                        // Check if both mods are okay.
                        if (shouldProceed) {
                            why = "regal magic to rare"
                            // Proceed
                            c.regal()
                        } else {
                            why = "alt to reset magic item"
                            c.alternate()
                        }
                    }

                    else -> {
                        error("Shouldn't happen: magic item has $nmods mods")
                    }
                }
            }

            PoeRollableItem.Rarity.Rare -> {
                if (shouldProceed) {
                    c.exalt()
                    why = "exalt to add mod"
                } else if (shouldGoBack) {
                    // Try to save alt by annul and exalt again.
                    c.annul()
                    why = "annul to go back"
                } else {
                    c.scour()
                    why = "scour to reset"
                }
            }
        }
        return decision.copy(why = decision.why + ", impl = " + why)
    }
}


fun Number.fmt(): String {
    return String.format("%.2f", this)
}

fun main() {
    val toParse = """
        Item Class: Jewels
        Rarity: Rare
        Kraken Star
        Medium Cluster Jewel
        --------
        Requirements:
        Level: 54
        --------
        Item Level: 83
        --------
        Adds 5 Passive Skills (enchant)
        (Added Passive Skills are never considered to be in Radius by other Jewels) (enchant)
        (All Added Passive Skills are Small unless otherwise specified) (enchant)
        1 Added Passive Skill is a Jewel Socket (enchant)
        Added Small Passive Skills grant: 12% increased Brand Damage (enchant)
        (Passive Skills that are not Notable, Masteries, Keystones, or Jewel Sockets are Small) (enchant)
        --------
        { Prefix Modifier "Glimmering" (Tier: 2) — Defences, Energy Shield }
        Added Small Passive Skills also grant: +7(6-9) to Maximum Energy Shield
        { Prefix Modifier "Notable" (Tier: 1) — Caster, Speed }
        1 Added Passive Skill is Remarkable — Unscalable Value
        { Suffix Modifier "of the Crystal" (Tier: 3) — Elemental, Resistance }
        Added Small Passive Skills also grant: +2% to all Elemental Resistances
        --------
        Place into an allocated Medium or Large Jewel Socket on the Passive Skill Tree. Added passives do not interact with jewel radiuses. Right click to remove from the Socket.


    """.trimIndent()
}
