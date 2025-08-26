package com.gh.om.gamemacros.complex

import com.gh.om.gamemacros.MouseHooks
import com.gh.om.gamemacros.complex.PoeDumpBag.bagColumns
import com.gh.om.gamemacros.complex.PoeDumpBag.bagRows
import com.gh.om.gamemacros.complex.PoeDumpBag.mapStashColumns
import com.gh.om.gamemacros.complex.PoeDumpBag.mapStashRows
import com.gh.om.gamemacros.complex.PoeRollableItem.MapAug
import com.gh.om.gamemacros.isPoeAndTriggerKeyEnabled
import com.gh.om.gamemacros.safeDelayK
import com.github.kwhat.jnativehook.mouse.NativeMouseEvent
import java.awt.Point
import java.util.regex.Pattern
import kotlin.math.min
import kotlin.time.Duration.Companion.milliseconds

// More comprehensive crafting: transmute, alt, aug, regal, exalt.

sealed interface PoeItem {
    enum class Klass(val repr: String) {
        Currency("Stackable Currency"),
        Map("Maps");

        companion object {
            fun fromRepr(repr: String): Klass? {
                return entries.firstOrNull { it.repr == repr }
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
        Chaos("Chaos Orb")
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
                "Quality (Rarity)" to Native(MapAug.Rarity),
                "Quality (Pack Size)" to Native(MapAug.Pack),
                "Quality (Currency)" to Native(MapAug.Currency),
                "Quality (Divination Cards)" to Native(MapAug.DivCard),
                "Quality (Maps)" to Native(MapAug.Map),
                "Quality (Scarabs)" to Native(MapAug.Scarab),
            )

            fun fromName(name: String) = nameMap[name]
        }
    }

    enum class MapAug {
        Quant, Rarity, Pack, Map, Currency, Scarab, DivCard
    }
}

fun PoeRollableItem.hasAffix(name: String): Boolean {
    return explicitMods.any {
        it.name == name
    }
}

object PoeRollMap {
    val modsToAvoid = listOf(
        // 78% scarab is nice but volatile is too annoying
        "Volatile",
        // 15% pack is too insignificant for eye strain or difficulty
        "of Desolation",
        "Searing",
        "Decaying",
        "Hungering",
        // -37% res is too bad
        "of Exposure",
        // 56% rarity is a joke
        "Cycling",
    )

    suspend fun main() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            rollMapsUntilDone(isPoe::value)
        }
        LEADER_KEY.isEnabled("11").collect(::handle)
    }

    /**
     * @return Rolled map, or null if map is not good
     */
    suspend fun checkAndRollOnce(
        mapSlot: Point,
        chaosSlot: Point,
    ): PoeRollableItem? {
        MouseHooks.moveTo(mapSlot)
        safeDelayK(30.milliseconds)

        val ad = PoeInteractor.getAdvancedDescriptionOfItemUnderMouse() ?: ""
        val item = PoeItemParser.parseAsRollable(ad)
        if (item.rarity != PoeRollableItem.Rarity.Rare) {
            println("Found non-rare item, skip")
            return item
        }
        val score = getMapScoreForAbyss(item)
        if (score >= 10 && !modsToAvoid.any(item::hasAffix)) {
            // Good enough!
            return item
        }

        // Reroll once
        MouseHooks.postClick(
            point = chaosSlot,
            button = NativeMouseEvent.BUTTON2,
            moveFirst = true
        )
        safeDelayK(30.milliseconds)
        MouseHooks.postClick(
            point = mapSlot,
            button = NativeMouseEvent.BUTTON1,
            moveFirst = true
        )
        safeDelayK(30.milliseconds)
        return null
    }

    suspend fun rollMapsUntilDone(shouldContinue: () -> Boolean) {
        val rolledMaps = mutableListOf<PoeRollableItem>()
        var chaosUsed = 0
        val mapsToRoll = mapStashSlots().toMutableList()
        val bagSlots = bagSlots()
        // We'll pop rolled maps from the list
        mapsToRoll.reverse()

        fun report() {
            val scores = rolledMaps.map(::getMapScoreForAbyss)
            val avgCost = (chaosUsed.toDouble() / scores.size).fmt()
            val lines = listOf(
                "Rolled ${scores.size} maps using ${chaosUsed}c. Avg ${avgCost}c",
                "Average score ${scores.average().fmt()}, each: ${
                    scores.map(Number::fmt)
                }",
            )
            lines.forEach(::println)
        }

        for (bagSlot in bagSlots) {
            // Check stack count of chaos
            var count = getChaosCountAt(bagSlot)
            while (count > 0) {
                if (mapsToRoll.isEmpty() || !shouldContinue()) {
                    // We are done
                    report()
                    return
                }
                val mapSlot = mapsToRoll.last()
                val rolledMap = checkAndRollOnce(mapSlot, bagSlot)
                if (rolledMap != null) {
                    // Check only without rolling
                    mapsToRoll.removeLast()
                    rolledMaps.add(rolledMap)
                } else {
                    count -= 1
                    chaosUsed += 1
                }
            }
        }

        report()
    }

    private suspend fun getChaosCountAt(point: Point): Int {
        MouseHooks.moveTo(point)
        safeDelayK(30.milliseconds)

        val d = PoeInteractor.getDescriptionOfItemUnderMouse() ?: ""
        val currency = PoeItemParser.parse(d) as? PoeCurrency
        return if (currency?.type == PoeCurrency.KnownType.Chaos) {
            currency.stackSize
        } else {
            0
        }
    }

    fun getMapScoreForAbyss(item: PoeRollableItem): Double {
        // We use a weighted sum of currency + scarab.
        // 120 quant + 45 pack + 170 currency -> 10 points (good enough)
        // 130 quant + 38 pack + 120 currency + 90 scarab -> 14 points (great)
        // Cutoffs: 9 without filter requires ~10 rolls.
        // 11 + filter requires ~40 rolls. maybe 9.5 or 10 is more economic.
        require(item.klass == PoeItem.Klass.Map)

        val currency = getRealPctValue(item.qualities, MapAug.Currency)
        val scarab = getRealPctValue(item.qualities, MapAug.Scarab)
        val quant = getRealPctValue(item.qualities, MapAug.Quant)
        val pack = getRealPctValue(item.qualities, MapAug.Pack)

        val atlasMulti = 1.88
        // Also increase the weight when both are present because qual affects
        // both.. Or maybe simply also consider pack and qual? Basically
        // *1.88 of qual and maybe treat pack as 40% eff due to abyss.
        val packMulti = ((pack.toDouble() / 100) * atlasMulti * 0.4) + 1
        val quantMulti = ((quant.toDouble() / 100) * atlasMulti) + 1
        val dropMulti = packMulti * quantMulti
        val currencyMulti = ((currency.toDouble() / 100) * atlasMulti) + 1
        val scarabMulti = ((scarab.toDouble() / 100) * atlasMulti) + 1
        // /3 to normalize
        return (currencyMulti + scarabMulti * 2) * dropMulti / 3
    }

    fun getRealPctValue(
        quals: List<PoeRollableItem.Quality>,
        aug: MapAug,
    ): Int {
        // Each quality improves by
        val chiselMulti = when (aug) {
            MapAug.Quant -> 1
            MapAug.Rarity -> 3
            MapAug.Pack -> 1
            MapAug.Map -> 5
            MapAug.Currency -> 5
            MapAug.Scarab -> 5
            MapAug.DivCard -> 5
        }
        val fromChisel = quals.firstOrNull {
            val name = it.name
            name is PoeRollableItem.QualName.Chisel && name.ty == aug
        }
        var nativeQual = quals.firstOrNull {
            val name = it.name
            name is PoeRollableItem.QualName.Native && name.ty == aug
        }?.value ?: 0
        if (fromChisel != null) {
            nativeQual -= fromChisel.value * chiselMulti
        }
        return nativeQual
    }

    private suspend fun bagSlots(): List<Point> {
        val grids = PoeGraphicConstants.allGrids(
            start = PoeGraphicConstants.firstItemInBag,
            rows = bagRows,
            columns = bagColumns,
            gridSize = PoeGraphicConstants.bagGridSize,
        )
        return PoeGraphicConstants.filterHasItem(grids)
    }

    private suspend fun mapStashSlots(): List<Point> {
        val grids = PoeGraphicConstants.allGrids(
            start = PoeGraphicConstants.firstItemInMapStash,
            rows = mapStashRows,
            columns = mapStashColumns,
            gridSize = PoeGraphicConstants.mapGridSize,
        )
        return PoeGraphicConstants.filterHasItem(grids)
    }
}

object PoeAltAugRegal {

    val intStackCluster = listOf(
        // 12 ES
        "Glowing",
        // 35% inc effect
        "Powerful",
        // 4 attr
        "of the Meteor",
        // 8 int
        "of the Prodigy",
        // 4 res
        "of the Kaleidoscope",
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
        val decision = craftClusterOnce(
            c = crafter,
            CraftDecisionMaker.IntStackClusterAllowSingleRes
        )
        println("$decision on $before")
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
    val stackSizePat = Pattern.compile("""Stack Size: (\d+)/""")

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
        val quals = findQualities(ad)
        return PoeRollableItem(
            klass = klass,
            rarity = rarity,
            explicitMods = mods,
            qualities = quals
        )
    }

    private fun parseCurrency(ad: String): PoeCurrency? {
        val stackSize =
            matchGroup(ad, stackSizePat)?.toIntOrNull() ?: return null
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

    private fun findAllExplicitMods(ad: String): List<PoeRollableItem.ExplicitMod> {
        val m = explicitModPat.matcher(ad)
        return generateSequence {
            if (m.find()) {
                val pos = m.group("pos")
                val name = m.group("name")
                val tier = m.group("tier")?.toIntOrNull()
                PoeRollableItem.ExplicitMod(
                    loc = PoeRollableItem.ExplicitModLocation.valueOf(pos),
                    name = name,
                    tier = tier,
                )
            } else {
                null
            }
        }.toList()
    }

    private fun findQualities(ad: String): List<PoeRollableItem.Quality> {
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
    val alt = Point(146, 361)
    val aug = Point(302, 432)
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
            // 8 int
            "of the Prodigy",
        )
        val oneOfSuffixes = listOf(
            // 4 res
            "of the Kaleidoscope",
            // Elem res
            "of the Drake",
            "of the Penguin",
            "of the Storm",
        )
        val desiredModCount = mustHave.size + 1

        override fun getDecision(item: PoeRollableItem): Decision {
            val nMustHave = item.explicitMods.count {
                it.name in mustHave
            }
            var nOneOf = min(
                item.explicitMods.count {
                    it.name in oneOfSuffixes
                }, 1
            )
            if (item.rarity == PoeRollableItem.Rarity.Magic) {
                // Ignore res suffix on magic to save regal -- we want
                // int on magic such that regal has a high chance to land.
                nOneOf = 0
            }
            return byMatches(
                matches = nMustHave + nOneOf,
                desiredModCount = desiredModCount,
                nMods = item.explicitMods.size
            )
        }
    }

    class ByDesiredMods(
        private val desiredModNames: List<String>,
        private val desiredModCount: Int,
    ) : CraftDecisionMaker {
        override fun getDecision(item: PoeRollableItem): Decision {
            val matches = item.explicitMods.count {
                it.name in desiredModNames
            }

            return byMatches(
                matches = matches,
                desiredModCount = desiredModCount,
                nMods = item.explicitMods.size
            )
        }
    }

    companion object {
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
 * Recipe to craft a cluster (so 4 mods max). Every execution advances one step.
 * @param desiredModCount 3 (for fracture) or 4 (fully crafted)
 * @return True if crafting is done.
 */
private suspend fun craftClusterOnce(
    c: PoeItemCrafter,
    dm: CraftDecisionMaker,
): CraftDecisionMaker.Decision {
    val item = c.getCurrentItem()

    val decision = dm.getDecision(item)

    if (decision.type == CraftDecisionMaker.DecisionType.Done) {
        return decision
    }

    val shouldProceed = decision.type == CraftDecisionMaker.DecisionType.Proceed
    val shouldGoBack = decision.type == CraftDecisionMaker.DecisionType.GoBack

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

fun main() {
    val input = """
Item Class: Maps
Rarity: Rare
Agony Sepulchre
Sanctuary Map
--------
Map Tier: 17
Item Quantity: +124% (augmented)
Item Rarity: +105% (augmented)
Monster Pack Size: +38% (augmented)
More Maps: +50% (augmented)
More Scarabs: +53% (augmented)
More Currency: +109% (augmented)
--------
Item Level: 84
--------
Monster Level: 84
--------
{ Prefix Modifier "Parasitic" (Tier: 1) }
15% of Damage Players' Totems take from Hits is taken from their Summoner's Life instead
{ Prefix Modifier "Empowered" — Elemental, Fire, Cold, Lightning, Ailment }
Monsters have a 20% chance to Ignite, Freeze and Shock on Hit
{ Prefix Modifier "Savage" (Tier: 1) }
40(30-40)% increased Monster Damage
{ Suffix Modifier "of Domination" (Tier: 1) }
Unique Monsters have a random Shrine Buff
{ Suffix Modifier "of Defiance" (Tier: 1) }
Debuffs on Monsters expire 100% faster
{ Suffix Modifier "of Stasis" — Life, Mana, Defences, Energy Shield }
Players cannot Regenerate Life, Mana or Energy Shield — Unscalable Value
--------
Travel to this Map by using it in a personal Map Device. Maps can only be used once.
--------
Modifiable only with Chaos Orbs, Vaal Orbs, Delirium Orbs and Chisels


        """

    val output = PoeItemParser.parseAsRollable(input)
    println(output)
    println(PoeRollMap.getMapScoreForAbyss(output).fmt())
}

private fun Number.fmt(): String {
    return String.format("%.2f", this)
}
