package com.gh.om.gamemacros.complex

import com.gh.om.gamemacros.MouseHooks
import com.gh.om.gamemacros.complex.CraftDecisionMaker.IntStackClusterEx.byDesiredOneSideMods
import com.gh.om.gamemacros.complex.PoeAltAugRegal.brandClusterDescription
import com.gh.om.gamemacros.complex.PoeAltAugRegal.intStackCluster
import com.gh.om.gamemacros.complex.PoeAltAugRegal.lightningClusterForBrandDescriptions
import com.gh.om.gamemacros.complex.PoeAltAugRegal.notableOf
import com.gh.om.gamemacros.complex.PoeAutoAlt.intShieldMods
import com.gh.om.gamemacros.complex.PoeAutoAlt.spellIncShieldMods
import com.gh.om.gamemacros.isPoeAndTriggerKeyEnabled
import com.gh.om.gamemacros.safeDelayK
import com.github.kwhat.jnativehook.mouse.NativeMouseEvent
import java.awt.Point
import kotlin.math.min
import kotlin.time.Duration.Companion.milliseconds

// More comprehensive crafting: transmute, alt, aug, regal, exalt.

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
        // 3 AS
        "of Mastery",
        // 4 all res
        "of the Kaleidoscope",
        // 4 attr
        "of the Meteor",
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

    suspend fun craftInCurrencyTab() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            val crafter = RealCrafterOnCurrencyTab()
            repeat(1000) {
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

    suspend fun multiRoll() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            val dm = CraftDecisionMaker.intStackCluster4
            val crafter = CrafterAsRerollProvider(5000, dm, CraftMethods::altAugRegalExaltOnce)
            PoeMultiRoll.rollItems(
                checker = dm.asItemChecker(),
                itemsToRoll = bagSlots().toList(),
                rerollProvider = crafter,
                shouldContinue = isPoe::value,
            )
        }
        LEADER_KEY.isEnabled("15").collect(::handle)
    }

    private suspend fun craftOnce(crafter: RealCrafterOnCurrencyTab): Boolean {
        val before = crafter.getCurrentItem()
        val decision = CraftMethods.altAugRegalExaltOnce(
            c = crafter,
            // CraftDecisionMaker.IntStackClusterAllowSingleRes,
            // CraftDecisionMaker.byDesiredMods(intStackCluster, 4),
            // CraftDecisionMaker.ByDesiredMods(gemLevelAmulet, 1),
            CraftDecisionMaker.intStackAmulet,
            // CraftDecisionMaker.intStackWeapon,
        )
        // println("$decision on $before")
        return decision.done
    }

    suspend fun bagSlots(): List<Point> {
        val grids = PoeGraphicConstants.allGrids(
            start = PoeGraphicConstants.firstItemInBag,
            rows = PoeDumpBag.bagRows,
            // Roll 5x2 items at a time
            columns = 10,
            gridSize = PoeGraphicConstants.bagGridSize,
        )
        return PoeGraphicConstants.safeCaptureThenFilterHasItem(grids)
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

object PoeCurrencyTab {
    val item = Point(452, 609)

    val transmute = Point(62, 355)
    val alch = Point(654, 364)
    val binding = Point(221, 609)
    // So we can choose between binding or alch depending on the amount
    val bindingOrAlch = binding
    val alt = Point(146, 361)
    val aug = Point(302, 432)
    val chaos = Point(730, 356)
    val regal = Point(574, 352)
    val scour = Point(576, 678)
    val exalt = Point(397, 359)
    val annul = Point(226, 360)
    val whetstone = Point(501, 277)
    val armourScrap = Point(572, 273)
}

object PoeAutoAlt {

    val intStackWandPrefixes = listOf(
        "with this Weapon per 10 Intelligence",
        // "Spell Damage per 16 Intelligence",
        // T1 Spell%
        // "Runic",
        // T1 Lightning attack#
        "Vapourising",
    )

    val intStackWandWiderAffixes = intStackWandPrefixes + listOf(
        "Acclaim",
        "Incision",
        "Destruction",
    )

    val spellIncShieldMods = listOf(
        // T1 & T2 spell
        "Runic",
        "Glyphic",
    )

    val intShieldMods = spellIncShieldMods + listOf(
        // T1 ES
        "Incandescent",
        // T1 ES%
        "Unfaltering",
        // T1 Hybrid ES%
        // "Seraphim",
        // T1 Int
        "of the Genius",
    )

    suspend fun play() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            repeat(3000) {
                if (!isPoe.value) {
                    return
                }
                if (getAndCheckStat(intStackWandPrefixes)) {
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
    suspend fun armourerScrap()
    suspend fun whetstone()
}

abstract class BaseRelocatableCrafter : PoeItemCrafter {
    // Cached when there's no operation.
    var cachedCurrentItem: PoeRollableItem? = null

    abstract val itemSlot: Point

    override suspend fun getCurrentItem(): PoeRollableItem {
        cachedCurrentItem?.let { return it }

        MouseHooks.moveTo(itemSlot)
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
            itemSlot,
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
        // useCurrency(PoeCurrencyTab.alch)
        useCurrency(PoeCurrencyTab.bindingOrAlch)
    }

    override suspend fun armourerScrap() {
        useCurrency(PoeCurrencyTab.armourScrap)
    }

    override suspend fun whetstone() {
        useCurrency(PoeCurrencyTab.whetstone)
    }
}

class CurrencyApplierMixin : BaseRelocatableCrafter() {
    private var mutItemSlot: Point? = null

    override var itemSlot: Point
        set(value) {
            mutItemSlot = value
        }
        get() = requireNotNull(mutItemSlot) {
            "Item slot not set"
        }
}

private class CrafterAsRerollProvider(
    private var fuel: Int = 100,
    private val dm: CraftDecisionMaker,
    private val craftMethod: suspend (
        PoeItemCrafter,
        CraftDecisionMaker
    ) -> CraftDecisionMaker.Decision = CraftMethods::altAugRegalExaltOnce
) : RerollProvider {

    val applier = CurrencyApplierMixin()

    override suspend fun hasMore(): Boolean {
        return fuel > 0
    }

    override suspend fun applyTo(itemSlot: Point, item: PoeRollableItem) {
        applier.itemSlot = itemSlot
        applier.cachedCurrentItem = item

        fuel -= 1
        craftMethod(applier, dm)
    }
}

private class RealCrafterOnCurrencyTab : BaseRelocatableCrafter() {
    override val itemSlot = PoeCurrencyTab.item
}

private fun interface CraftDecisionMaker {
    fun getDecision(item: PoeRollableItem): Decision

    data class Decision(
        val type: DecisionType,
        val why: String,
    ) : PoeMultiRoll.CheckResult {
        val done: Boolean
            get() = type == DecisionType.Done

        override val isGood: Boolean
            get() = done
    }

    enum class DecisionType {
        Done,
        Reset,
        Proceed,
        GoBack;
    }

    object IntStackClusterEx : CraftDecisionMaker {
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
            require(item.klass == PoeItem.ConstKlass.Jewels) {
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
        desiredModCount: Int = desiredModNames.size,
        nameGetter: (PoeRollableItem.ExplicitMod) -> String = { it.name },
        extraCheck: (PoeRollableItem.ExplicitMod) -> Boolean = { true }
    ): CraftDecisionMaker {
        return ByDesiredOneSideModsEx(side = side, desiredModCount = desiredModCount) { mods ->
            mods.count {
                nameGetter(it) in desiredModNames && extraCheck(it)
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

        val esIntBoot = byDesiredMods(
            listOf(
                "Seething",
                "Unassailable",
                "of the Genius",
            ),
            1,
        )

        val evEsBody = byDesiredOneSideMods(
            listOf(
                "Incorporeal",
                "Hummingbird's",
                "Phantasm's",
            ),
            side = PoeRollableItem.ExplicitModLocation.Prefix,
            desiredModCount = 1,
        )

        val evEsBodyForFrac = byDesiredOneSideMods(
            listOf(
                "of Nullification",
            ),
            side = PoeRollableItem.ExplicitModLocation.Suffix,
            desiredModCount = 1,
        ) {
            // Only looking for max roll for fracturing
            "+22" in it.description
        }

        val intSuffixForFrac = byDesiredOneSideMods(
            listOf(
                "of the Genius",
            ),
            side = PoeRollableItem.ExplicitModLocation.Suffix,
            desiredModCount = 1,
        )

        fun matchesDescription(mod: PoeRollableItem.ExplicitMod, descriptions: List<String>): Boolean {
            return descriptions.any { it in mod.description }
        }

        val magebloodFlask = byDesiredMods(
            listOf(
                // Effect
                "Abecedarian's",
                "Dabbler's",
                "Alchemist's",
                // Suffix
                // "of the Armadillo", // armor%
                "of the Impala",  // EV%
                "of the Cheetah", // MS
                "of the Rainbow", // all res
                "of Incision",    // crit
                "of Tenaciousness",  // avoid stun
                "of the Owl",     // reduce curse
                "of Bog Moss",    // avoid shock
                "of Plume Moss", // t2 avoid shock is also fine
                "of Tooth Moss", // t3 avoid shock is also okay
            ),
            2,
        )

        val namelessSeerMap = ByDesiredOneSideModsEx(
            PoeRollableItem.ExplicitModLocation.Prefix,
            1,
        ) { mods ->
            mods.count { mod ->
                matchesDescription(mod, listOf("variety", "inhabited"))
            }
        }

        val moreRareMap = ByDesiredOneSideModsEx(
            PoeRollableItem.ExplicitModLocation.Prefix,
            1,
        ) { mods ->
            mods.count { mod ->
                matchesDescription(mod, listOf("number of Rare"))
            }
        }

        val brandCluster = ByDesiredOneSideModsEx(
            PoeRollableItem.ExplicitModLocation.Prefix,
            2,
        ) { mods ->
            mods.count { mod ->
                matchesDescription(mod, brandClusterDescription)
            }
        }

        val spellIncShieldPrefix = byDesiredOneSideMods(spellIncShieldMods, side = PoeRollableItem.ExplicitModLocation.Prefix, 1)
        val intShieldPrefix = byDesiredOneSideMods(intShieldMods, side = PoeRollableItem.ExplicitModLocation.Prefix, 1)
        val intShieldBoth = byDesiredMods(intShieldMods, 1)

        val intStackCluster2 = byDesiredMods(intStackCluster, 2)
        val intStackCluster3 = byDesiredMods(intStackCluster, 3)
        val intStackCluster4 = byDesiredMods(intStackCluster, 4)

        val intStackWeapon = ByDesiredOneSideModsEx(
            PoeRollableItem.ExplicitModLocation.Prefix,
            1,
        ) { mods ->
            mods.count { mod ->
                PoeAutoAlt.intStackWandPrefixes.any { it in mod.description || it in mod.name }
            }
        }

        val intStackRing = byDesiredMods(
            listOf(
                "Resplendent",
                "Electrocuting",
                "Vaporous",
                "Overpowering",
                "of the Genius",
                "of Ephij",
                "of the Rainbow",
            ),
        1)

        val intStackAmulet = ByDesiredOneSideModsEx(
            PoeRollableItem.ExplicitModLocation.Suffix,
            1,
        ) { mods ->
            mods.count { mod ->
                val hasInt = "increased Intelligence" in mod.description
                        || "increased Attr" in mod.description
                mod.tier == 1 && hasInt
            }
        }

        val lightningClusterForBrand = ByDesiredModsEx(3) {
            matchesDescription(it, lightningClusterForBrandDescriptions)
        }

        val critClusterForKboc = ByDesiredOneSideModsEx(
            PoeRollableItem.ExplicitModLocation.Prefix,
            desiredModCount = 1,
        ) { mods ->
            mods.count { mod ->
                matchesDescription(mod, notableOf(listOf("Overwhelming Malice")))
            }
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

        fun byDesiredMods(
            desiredModNames: List<String>,
            desiredModCount: Int,
        ): CraftDecisionMaker = ByDesiredModsEx(
            desiredModCount = desiredModCount,
        ) {
            it.name in desiredModNames
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

            PoeRollableItem.Rarity.Unique -> {
                error("Can't roll unique")
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

            PoeRollableItem.Rarity.Unique -> {
                error("Can't roll unique")
            }
        }
        return decision.copy(why = decision.why + ", impl = " + why)
    }

    /**
     * Useful for 1 prefix + 1 suffix recomb, where we want to avoid augmenting the other side.
     */
    suspend fun altOnce(
        c: PoeItemCrafter,
        dm: CraftDecisionMaker,
    ): CraftDecisionMaker.Decision = altAugRegalExaltOnceEx(c = c, dm = dm, altOnly = true)

    suspend fun altAugRegalExaltOnce(
        c: PoeItemCrafter,
        dm: CraftDecisionMaker,
    ): CraftDecisionMaker.Decision = altAugRegalExaltOnceEx(c = c, dm = dm, altOnly = false)

    private suspend fun altAugRegalExaltOnceEx(
        c: PoeItemCrafter,
        dm: CraftDecisionMaker,
        altOnly: Boolean,
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

        if (altOnly && shouldProceed) {
            require(item.explicitMods.isEmpty()) {
                "altOnly should only target 1 mod items (i.e. should not proceed on item with ${item.explicitMods.size} mods)"
            }
        }

        val why: String
        val isHeistSpecialBase = "Simplex Amulet" in item.originalDescription

        when (item.rarity) {
            PoeRollableItem.Rarity.Normal -> {
                require(!shouldGoBack)

                if (isHeistSpecialBase) {
                    why = "alch because heist special base"
                    c.alch()
                } else {
                    why = "transmute because normal"
                    c.transmute()
                }
            }

            PoeRollableItem.Rarity.Magic -> {
                require(!shouldGoBack)
                // Check mod

                if (isHeistSpecialBase) {
                    c.regal()
                    why = "regal because magic heist special base can't have any mods"
                } else {
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

            PoeRollableItem.Rarity.Unique -> {
                error("Can't roll unique")
            }
        }
        return decision.copy(why = decision.why + ", impl = " + why)
    }
}


fun Number.fmt(): String {
    return String.format("%.2f", this)
}

private fun CraftDecisionMaker.asItemChecker(): PoeMultiRoll.ItemChecker<CraftDecisionMaker.Decision> {
    return object: PoeMultiRoll.ItemChecker<CraftDecisionMaker.Decision> {
        override fun evaluate(item: PoeRollableItem): CraftDecisionMaker.Decision {
            return getDecision(item)
        }

        override fun generateReport(results: List<CraftDecisionMaker.Decision>): String {
            return "Ok"
        }
    }
}

object PoeQualityChecker: PoeMultiRoll.ItemChecker<PoeMultiRoll.SimpleResult> {
    override fun evaluate(item: PoeRollableItem): PoeMultiRoll.SimpleResult {
        val quality = item.qualities.firstOrNull {
            it.name == PoeRollableItem.QualName.FromCurrency(PoeRollableItem.AugType.Generic)
        }
        val done = (quality?.value ?: 0) >= 20
        return PoeMultiRoll.SimpleResult(done)
    }

    override fun generateReport(results: List<PoeMultiRoll.SimpleResult>): String {
        return "Ok"
    }
}

class PoeQualityApplier : RerollProvider {
    val currency = CurrencyApplierMixin()

    override suspend fun hasMore(): Boolean = true

    override suspend fun applyTo(itemSlot: Point, item: PoeRollableItem) {
        currency.itemSlot = itemSlot
        currency.cachedCurrentItem = item

        when (item.klass) {
            is PoeItem.Armor -> {
                currency.armourerScrap()
            }
            is PoeItem.Weapon -> {
                currency.whetstone()
            }
            else -> {
                error("Unsupported class: ${item.klass}")
            }
        }
    }

    companion object {
        suspend fun main() {
            val isPoe = isPoeAndTriggerKeyEnabled()

            suspend fun handle(pressed: Boolean) {
                if (!pressed) {
                    return
                }
                PoeMultiRoll.rollItems(
                    checker = PoeQualityChecker,
                    itemsToRoll = PoeAltAugRegal.bagSlots().toList(),
                    rerollProvider = PoeQualityApplier(),
                    shouldContinue = isPoe::value,
                )
            }
            LEADER_KEY.isEnabled("18").collect(::handle)
        }
    }

}

fun main() {
    val toParse = """
        Item Class: Utility Flasks
        Rarity: Magic
        Jade Flask of the Armadillo
        --------
        Lasts 6 Seconds
        Consumes 30 of 60 Charges on use
        Currently has 0 Charges
        +1500 to Evasion Rating
        --------
        Requirements:
        Level: 67
        --------
        Item Level: 85
        --------
        { Suffix Modifier "of the Armadillo" (Tier: 1) — Defences, Armour }
        58(56-60)% increased Armour during Effect

        --------
        Right click to drink. Can only hold charges while in belt. Refills as you kill monsters.

    """.trimIndent()
    val item = PoeItemParser.parseAsRollable(toParse)
    val d = CraftDecisionMaker.magebloodFlask.getDecision(item)
    println(d)
}

