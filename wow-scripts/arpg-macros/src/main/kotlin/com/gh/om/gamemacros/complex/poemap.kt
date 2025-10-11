package com.gh.om.gamemacros.complex

import com.gh.om.gamemacros.MouseHooks
import com.gh.om.gamemacros.complex.PoeRollMap.bagSlots
import com.gh.om.gamemacros.complex.PoeRollMap.rollMapsUntilDoneEx
import com.gh.om.gamemacros.complex.PoeRollableItem.Rarity.*
import com.gh.om.gamemacros.isPoeAndTriggerKeyEnabled
import com.gh.om.gamemacros.safeDelayK
import java.awt.Point
import kotlin.math.min
import kotlin.time.Duration.Companion.milliseconds

interface PoeMapScorer {
    fun isGoodMap(map: PoeRollableItem): Boolean
    fun getScore(map: PoeRollableItem): Double

    companion object {
        fun anyGood(
            xs: List<PoeMapScorer>,
        ): PoeMapScorer {
            return object : PoeMapScorer {
                override fun isGoodMap(map: PoeRollableItem): Boolean {
                    return xs.any { it.isGoodMap(map) }
                }

                override fun getScore(map: PoeRollableItem): Double {
                    return xs.firstOrNull {
                        it.isGoodMap(map)
                    }?.getScore(map) ?: 0.0
                }
            }
        }
    }
}

// TODO also consider extra quality?
class PoeMapScorerImpl(
    private val packSizeWeight: Double,
    private val quantWeight: Double = 1.0,
    private val rarityWeight: Double = 0.0,
    private val currencyWeight: Double,
    private val scarabWeight: Double,
    private val mapWeight: Double = 0.0,
    private val genericWeight: Double = 0.0,
    private val atlasMulti: Double = 1.88,
    val threshold: Double,
    val hasBadMods: (PoeRollableItem) -> Boolean = { false },
    val extraScorer: (PoeRollableItem) -> Double = { 1.0 },
    private val weightDivider: Double? = null,
) : PoeMapScorer {
    private val totalWeight: Double = sequenceOf(
        genericWeight,
        currencyWeight,
        scarabWeight,
        mapWeight,
        rarityWeight,
    ).sum()

    override fun isGoodMap(map: PoeRollableItem): Boolean {
        val score = getScore(map)
        val hasBadMods = hasBadMods(map)
        // println("score = ${score.fmt()}, threshold = ${scorer.threshold}, badMods = $hasBadMods")
        return score >= threshold && !hasBadMods
    }

    init {
        require(totalWeight > 0) {
            "totalWeight must be > 0, got $totalWeight"
        }
    }

    override fun getScore(input: PoeRollableItem): Double {
        require(input.klass.isMapLike())

        val currency =
            getRealPctValue(input.qualities, PoeRollableItem.MapAug.Currency)
        val scarab =
            getRealPctValue(input.qualities, PoeRollableItem.MapAug.Scarab)
        val quant =
            getRealPctValue(input.qualities, PoeRollableItem.MapAug.Quant)
        val rarity =
            getRealPctValue(input.qualities, PoeRollableItem.MapAug.Rarity)
        val pack = getRealPctValue(input.qualities, PoeRollableItem.MapAug.Pack)
        val map = getRealPctValue(input.qualities, PoeRollableItem.MapAug.Map)

        // Also increase the weight when both are present because qual affects
        // both.. Or maybe simply also consider pack and qual? Basically
        // *1.88 of qual and maybe treat pack as 40% eff due to abyss.
        val packMulti =
            ((pack.toDouble() / 100) * atlasMulti * packSizeWeight) + 1
        val quantMulti =
            ((quant.toDouble() / 100) * atlasMulti * quantWeight) + 1
        val dropMulti = packMulti * quantMulti
        val currencyMulti = ((currency.toDouble() / 100) * atlasMulti) + 1
        val scarabMulti = ((scarab.toDouble() / 100) * atlasMulti) + 1
        val rarityMulti = ((rarity.toDouble() / 100) * atlasMulti) + 1
        val mapMulti = ((map.toDouble() / 100) * atlasMulti) + 1
        val weightedSum = genericWeight + currencyMulti * currencyWeight +
                scarabMulti * scarabWeight + mapMulti * mapWeight +
                rarityMulti * rarityWeight
        // normalize by weightDivider
        val normScore = weightedSum * dropMulti / (weightDivider ?: totalWeight)
        return normScore * extraScorer(input)
    }

    fun getRealPctValue(
        quals: List<PoeRollableItem.Quality>,
        aug: PoeRollableItem.MapAug,
    ): Int {
        // Each quality improves by
        val chiselMulti = when (aug) {
            PoeRollableItem.MapAug.Quant -> 1
            PoeRollableItem.MapAug.Rarity -> 3
            PoeRollableItem.MapAug.Pack -> 1
            PoeRollableItem.MapAug.Map -> 5
            PoeRollableItem.MapAug.Currency -> 5
            PoeRollableItem.MapAug.Scarab -> 5
            PoeRollableItem.MapAug.DivCard -> 5
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

    companion object {

        val ABYSS = PoeMapScorerImpl(
            packSizeWeight = 0.4,
            currencyWeight = 0.4,
            scarabWeight = 1.0,
            genericWeight = 0.3,
            mapWeight = 0.05,
            rarityWeight = 0.1,
            // WD=1, PS=0.4, scarab=0.66, c=0.33:
            // 10.5 for single target reroll, 14 for multiple target
            threshold = 11.5,
            hasBadMods = ::hasBadModsForAbyss,
        )

        val abyssModWithDescriptionToAvoid = listOf(
            // -37% res is too bad. However this also matches t16 -12% res,
            // so a description check is needed to disambiguate.
            "of Exposure" to "-20%"
        )

        val mobDamageMods = listOf<Pair<PoeAffixMatcher, Number>>(
            // T17 double crit
            PoeAffixMatcher.byNumericDescr("of Deadliness") {
                it > 400
            } to 2.5,
            // T17 -max res
            PoeAffixMatcher.byNumericDescr("of Exposure") {
                it >= 20
            } to 2.5,
            // T17 area + proj
            PoeAffixMatcher.byName("Magnifying") to 2,
            // T17 -defence
            PoeAffixMatcher.byName("of Miring") to 2,
            // T17 phys as 200% extra elem
            PoeAffixMatcher.byName("Prismatic") to 2,
            // T17 remove -- this is still dangerous
            PoeAffixMatcher.byName("Equalising") to 2,
            // Shaper touched adds lots of damage
            PoeAffixMatcher.byName("Valdo's") to 1.5,
            // M4D is simply 50% more
            PoeAffixMatcher.byName("Retributive") to 1.5,
            // Meteor is usually fine, unless coupled with something else
            PoeAffixMatcher.byName("of Imbibing") to 2,
            // 15% pen
            PoeAffixMatcher.byName("of Penetration") to 2,
            // Ignites (immunity would be nice)
            PoeAffixMatcher.byName("Afflicting") to 2,
            PoeAffixMatcher.byName("Conflagrating") to 2,
        )

        val mobDefenseMods = listOf<Pair<PoeAffixMatcher, Number>>(
            // ES
            PoeAffixMatcher.byNumericDescr("Buffered") {
                it >= 40
            } to 2.4,
            // Life
            PoeAffixMatcher.byNumericDescr("Fecund") {
                it >= 70
            } to 2.6,
            // Crit reduction
            PoeAffixMatcher.byNumericDescr("of Toughness") {
                it >= 35
            } to 2.2,
            // AOE reduction
            PoeAffixMatcher.byNumericDescr("of Impotence") {
                it >= 25
            } to 1.5,
            // Resistance
            PoeAffixMatcher.byName("Protected") to 1.2,
        )

        val alwaysAvoidMods = listOf(
            // 78% scarab is nice but volatile is too annoying
            "Volatile",
            // 56% rarity is a joke, compared to the 3 seconds lag
            "Cycling",
        )

        val alwaysAnnoyingMods = listOf(
            // Tentacles make mapping much slower
            "Decaying",
        ) + alwaysAvoidMods

        val alvaModsToAvoid = listOf(
            // Buff expiration means shrine buff will be gone faster
            "of Transience",
            // Awakener rune can spawn in incursion which is really bad
            // due to lagging
            "of Desolation",
            // Lagging + drowning orb is bad combination. Runegraft of warp
            // will make the debuff go faster so reaction time is even shorter.
            "Hungering",
        ) + alwaysAnnoyingMods

        val moreDropMods = listOf(
            PoeAffixMatcher.byNumericDescr("Antagonist's") {
                it >= 35
            },
            PoeAffixMatcher.byName("Valdo's"),
        )

        val abyssModsToAvoid = listOf(
            // 2 degens
            // 15% pack is too insignificant for eye strain or difficulty
            "of Desolation",
            "Searing",
            // Abyss requires standing still, so drowning orbs are bad
            "Hungering",
        ) + alwaysAnnoyingMods

        fun hasBadModsForAbyss(map: PoeRollableItem): Boolean {
            val shouldAvoid = abyssModsToAvoid.any(map::hasAffix)
            val shouldAvoidSpecific =
                abyssModWithDescriptionToAvoid.any { (name, descr) ->
                    map.getAffix(name)?.description?.contains(descr) == true
                }
            return shouldAvoid || shouldAvoidSpecific
        }

        fun hasBadModsForAlva(item: PoeRollableItem): Boolean {
            val mobDamageMulti = mobDamageMods.filter { (m, _) ->
                item.hasAffixThat(m::matches)
            }.map {
                it.second.toDouble()
            }.fold(1.0, Double::times)
            val mobDefenseMulti = mobDefenseMods.filter { (m, _) ->
                item.hasAffixThat(m::matches)
            }.map {
                it.second.toDouble()
            }.fold(1.0, Double::times)

            return alvaModsToAvoid.any(item::hasAffix) ||
                    mobDamageMulti > 9 || mobDefenseMulti > 3.5
        }

        val ALVA = PoeMapScorerImpl(
            packSizeWeight = 1.0,
            rarityWeight = 0.4,
            currencyWeight = 1.0,
            scarabWeight = 0.0,
            // default WD: 20-22 for t16.5, 28 for t17
            threshold = 20.0,
            // weightDivider = 1.0,
            hasBadMods = ::hasBadModsForAlva,
            extraScorer = { item ->
                val countOfMoreDropMods = item.explicitMods.count { mod ->
                    moreDropMods.any { it.matches(mod) }
                }
                1 + countOfMoreDropMods * 0.05
            }
        )

        val MAP = PoeMapScorerImpl(
            packSizeWeight = 1.0,
            mapWeight = 1.0,
            currencyWeight = 0.0,
            scarabWeight = 0.0,
            threshold = 12.0,
        )

        val AWAKEN_HARVEST = PoeMapScorerImpl(
            packSizeWeight = 0.5,
            quantWeight = 0.5,
            currencyWeight = 0.0,
            scarabWeight = 0.0,
            genericWeight = 1.0,
            // 3.0: around 110 IIQ, 52 Pack. Need 23c for single rolling
            // 3.4 is also fine when multi-rolling (~50c?)
            threshold = 3.4,
            hasBadMods = { item ->
                alwaysAvoidMods.any(item::hasAffix)
            }
        )

        // TODO: need a way to auto-categorize the results.
        val ANY = PoeMapScorer.anyGood(
            listOf(
                AWAKEN_HARVEST,
                ABYSS,
                // MAP,
                // ALVA,
            )
        )

        val INVITATION = PoeMapScorerImpl(
            packSizeWeight = 0.0,
            quantWeight = 1.0,
            currencyWeight = 0.0,
            scarabWeight = 0.0,
            genericWeight = 1.0,
            atlasMulti = 1.0,
            threshold = 1.8,
        )
    }
}

fun main() {
    val input = """
Item Class: Misc Map Items
Rarity: Rare
Otherworldly Inscription
Screaming Invitation
--------
Item Quantity: +71% (augmented)
Item Rarity: +42% (augmented)
--------
Item Level: 84
--------
{ Implicit Modifier }
Modifiers to Item Quantity affect the amount of rewards dropped by the boss (implicit)
--------
{ Prefix Modifier "Mirrored" (Tier: 1) — Damage, Elemental }
Monsters reflect 18% of Elemental Damage
{ Prefix Modifier "Burning" (Tier: 1) — Damage, Physical, Elemental, Fire }
Monsters deal 110(90-110)% extra Physical Damage as Fire
{ Suffix Modifier "of Drought" (Tier: 1) }
Players gain 50% reduced Flask Charges
{ Suffix Modifier "of Impotence" (Tier: 1) }
Players have 25% less Area of Effect
{ Suffix Modifier "of Exposure" (Tier: 1) — Elemental, Resistance }
Players have -10(-12--9)% to all maximum Resistances
--------
From the heart of the Tangle, the Eater of Worlds
reaches out for control of the Atlas.
--------
Open portals to Absence of Symmetry and Harmony by using this item in a personal Map Device.

        """

    val output = PoeItemParser.parseAsRollable(input)
    println(output)
    val scorer = PoeMapScorerImpl.INVITATION
    val score = scorer.getScore(output).fmt()
    val bad = scorer.hasBadMods(output)
    println("score = $score, bad = $bad")
}

interface RerollProvider {
    suspend fun hasMore(): Boolean
    suspend fun applyTo(
        itemSlot: Point,
        item: PoeRollableItem,
    )
}

@Suppress("unused")
class ChaosRerollProvider(private val fuel: Int = 100) : RerollProvider {
    private var cachedChaosCount: Int? = null
    private var useCount = 0

    private suspend fun getChaosCount(): Int {
        cachedChaosCount?.let {
            return it
        }
        safeDelayK(30.milliseconds)
        val count = PoeInteractor.getCountAt(
            PoeCurrencyTab.chaos,
            PoeCurrency.KnownType.Chaos
        )
        println("chaos = $count")
        cachedChaosCount = count
        return count
    }

    override suspend fun hasMore(): Boolean {
        return fuel > useCount && getChaosCount() > useCount
    }

    override suspend fun applyTo(
        itemSlot: Point,
        item: PoeRollableItem,
    ) {
        require(hasMore())
        useCount += 1
        when (item.rarity) {
            Magic -> {
                // Scour first then alc
                PoeInteractor.applyCurrencyTo(
                    currency = PoeCurrencyTab.scour,
                    item = itemSlot
                )
                PoeInteractor.applyCurrencyTo(
                    currency = PoeCurrencyTab.alch,
                    item = itemSlot
                )
            }

            Normal -> {
                // Alc is enough
                PoeInteractor.applyCurrencyTo(
                    currency = PoeCurrencyTab.alch,
                    item = itemSlot
                )
            }

            Rare -> {
                PoeInteractor.applyCurrencyTo(
                    currency = PoeCurrencyTab.chaos,
                    item = itemSlot
                )
            }
        }
    }
}

class ScourAlchRerollProvider(private val fuel: Int = 100) : RerollProvider {
    private var cachedAlcAndScourCount: Int? = null
    private var useCount = 0

    private suspend fun getAlcAndScourCount(): Int {
        cachedAlcAndScourCount?.let {
            return it
        }
        safeDelayK(30.milliseconds)
        val scourCount = PoeInteractor.getCountAt(
            PoeCurrencyTab.scour,
            PoeCurrency.KnownType.Scour
        )
        val alcCount = PoeInteractor.getCountAt(
            PoeCurrencyTab.alch,
            PoeCurrency.KnownType.Alch
        )
        println("alc = $alcCount, scour = $scourCount")
        val res = min(scourCount, alcCount)
        cachedAlcAndScourCount = res
        return res
    }

    override suspend fun hasMore(): Boolean {
        return fuel > useCount && getAlcAndScourCount() > useCount
    }

    override suspend fun applyTo(
        itemSlot: Point,
        item: PoeRollableItem,
    ) {
        require(hasMore())
        useCount += 1
        if (item.rarity != Normal) {
            // Scour first
            PoeInteractor.applyCurrencyTo(
                currency = PoeCurrencyTab.scour,
                item = itemSlot
            )
        }
        // Then alch
        PoeInteractor.applyCurrencyTo(
            currency = PoeCurrencyTab.alch,
            item = itemSlot
        )
    }
}

object PoeRollMap {

    suspend fun main() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            // rollMapsUntilDone(isPoe::value)
            rollMapsUntilDoneEx(
                scorer = PoeMapScorerImpl.INVITATION,
                mapsToRoll = bagSlots().toList(),
                // rerollProvider = ChaosRerollProvider(1000),
                rerollProvider = ScourAlchRerollProvider(1500),
                shouldContinue = isPoe::value,
            )
        }
        LEADER_KEY.isEnabled("11").collect(::handle)
    }

    suspend fun sortInStash() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            val scorer = PoeMapScorerImpl.ALVA
            val (inputs, tempStorage) = stashItemsAndNext()
            doSortInStash(
                scorer = scorer,
                shouldContinue = isPoe::value,
                inputs = inputs,
                outputs = stashSlots().toList()
            )
        }
        LEADER_KEY.isEnabled("14").collect(::handle)
    }

    /**
     * @return Map at [mapSlot]
     */
    suspend fun getMapAt(mapSlot: Point): PoeRollableItem {
        MouseHooks.moveTo(mapSlot)
        safeDelayK(30.milliseconds)

        val ad = PoeInteractor.getAdvancedDescriptionOfItemUnderMouse() ?: ""
        return PoeItemParser.parseAsRollable(ad)
    }

    suspend fun rollMapsUntilDoneEx(
        scorer: PoeMapScorer,
        mapsToRoll: List<Point>,
        rerollProvider: RerollProvider,
        shouldContinue: () -> Boolean,
    ) {
        val rolledMaps = mutableListOf<PoeRollableItem>()
        var rerollCount = 0
        val mutMapRemaining = mapsToRoll.toMutableList()
        // We'll pop rolled maps from the list
        mutMapRemaining.reverse()

        fun report() {
            val scores = rolledMaps.map(scorer::getScore)
            val avgCost = (rerollCount.toDouble() / scores.size).fmt()
            val lines = listOf(
                "Rolled ${scores.size} maps in $rerollCount tries. Avg $avgCost tries",
                "Average score ${scores.average().fmt()}, each: ${
                    scores.map(Number::fmt)
                }",
            )
            lines.forEach(::println)
        }

        while (true) {
            if (mutMapRemaining.isEmpty() || !shouldContinue()) {
                break
            }
            val mapSlot = mutMapRemaining.last()
            val map = getMapAt(mapSlot)
            require(map.klass.isMapLike()) {
                "Not a map: $map"
            }
            if (scorer.isGoodMap(map)) {
                mutMapRemaining.removeLast()
                rolledMaps.add(map)
            } else {
                if (rerollProvider.hasMore()) {
                    rerollCount += 1
                    rerollProvider.applyTo(mapSlot, map)
                } else {
                    // Not enough currency left
                    break
                }
            }
        }

        report()
    }

    private suspend fun doSortInStash(
        scorer: PoeMapScorer,
        shouldContinue: () -> Boolean,
        inputs: List<Point>,
        outputs: List<Point>
    ) {
        val scoredPoints = mutableListOf<Pair<Point, Double>>()
        for (input in inputs) {
            if (!shouldContinue()) {
                return
            }
            MouseHooks.moveTo(input)
            safeDelayK(30.milliseconds)
            val ad = PoeInteractor.getAdvancedDescriptionOfItemUnderMouse() ?: ""
            val item = PoeItemParser.parseAsRollable(ad)
            scoredPoints += input to scorer.getScore(item)
        }
        // Sort score by high to low
        scoredPoints.sortBy { -it.second }
        val scoresDisplay = scoredPoints.map { it.second.fmt() }
        val scoresAvg = scoredPoints.map { it.second }.average().fmt()
        println("${scoredPoints.size} maps, avg score ${scoresAvg}, each: $scoresDisplay")

        // In-place sort require cycle detection: Find sccs, then for each scc do circular
        // move. Oh I realized this is similar to register allocation on phi nodes.
        // If we relax the space requirement a bit, it's a lot easier: just move them to bags first.

        for ((point, _) in scoredPoints) {
            if (!shouldContinue()) {
                return
            }
            PoeInteractor.withControlPressed {
                MouseHooks.postClick(point, delayMs = 30, moveFirst = true)
            }
        }

        val bagSlots = PoeGraphicConstants.allGrids(
            start = PoeGraphicConstants.firstItemInBag,
            rows = PoeDumpBag.bagRows,
            columns = 10,
            gridSize = PoeGraphicConstants.bagGridSize,
        ).take(inputs.size)
        for (slot in bagSlots) {
            if (!shouldContinue()) {
                return
            }
            PoeInteractor.withControlShiftPressed {
                MouseHooks.postClick(slot, delayMs = 30, moveFirst = true)
            }
        }
    }

    private suspend fun bagSlots(): List<Point> {
        val grids = PoeGraphicConstants.allGrids(
            start = PoeGraphicConstants.firstItemInBag,
            rows = PoeDumpBag.bagRows,
            // Roll 20 maps at a time
            columns = 4,
            gridSize = PoeGraphicConstants.bagGridSize,
        )
        return PoeGraphicConstants.safeCaptureThenFilterHasItem(grids)
    }

    private fun stashSlots(): Sequence<Point> {
        return PoeGraphicConstants.allGrids(
            start = PoeGraphicConstants.firstItemInRegularStash,
            rows = 12,
            // Sort half stash at a time
            columns = 6,
            gridSize = PoeGraphicConstants.bagGridSize,
        )
    }

    /**
     * @return The stash slots with items, and the next slot
     */
    private suspend fun stashItemsAndNext(): Pair<List<Point>, Point> {
        val grids = stashSlots()
        val hasItem = PoeGraphicConstants.safeCaptureThenFilterHasItem(grids)
        val gridList = grids.toList()
        val lastItemIx = gridList.indexOf(hasItem.last())
        return hasItem to gridList[lastItemIx + 1]
    }
}

