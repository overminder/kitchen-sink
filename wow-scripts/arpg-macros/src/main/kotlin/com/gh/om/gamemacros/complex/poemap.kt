package com.gh.om.gamemacros.complex

import PoeMapDifficulty
import com.gh.om.gamemacros.MouseHooks
import com.gh.om.gamemacros.complex.PoeMapScorer.Output
import com.gh.om.gamemacros.complex.PoeRollableItem.Rarity.*
import com.gh.om.gamemacros.isPoeAndTriggerKeyEnabled
import com.gh.om.gamemacros.safeDelayK
import getMapDifficulty
import java.awt.Point
import kotlin.math.min
import kotlin.time.Duration.Companion.milliseconds

interface PoeMapScorer : PoeMultiRoll.ItemChecker<PoeMapScorer.Output> {
    override fun generateReport(results: List<Output>): String {
        return generateReportImpl(results)
    }

    data class Output(
        val scorer: String,
        val score: Double,
        val scoreThreshold: Double,
        val difficulty: PoeMapDifficulty,
        val easyEnough: Boolean,
        val badMods: List<PoeRollableItem.ExplicitMod>,
    ): PoeMultiRoll.CheckResult {
        override val isGood: Boolean get() {
            return score >= scoreThreshold && easyEnough && badMods.isEmpty()
        }
    }

    companion object {
        fun bestOf(
            xs: List<PoeMapScorer>,
        ): PoeMapScorer {
            require(xs.isNotEmpty())

            return object : PoeMapScorer {
                override fun evaluate(item: PoeRollableItem): Output {
                    val outputs = xs.mapTo(mutableListOf()) { it.evaluate(item) }
                    // Sort by best to worst
                    outputs.sortByDescending {
                        it.score / it.scoreThreshold
                    }
                    return outputs.first()
                }
            }
        }

    }
}

// TODO also consider extra quality?
class PoeMapScorerImpl(
    private val name: String,
    private val packSizeWeight: Double,
    private val quantWeight: Double = 1.0,
    private val rarityWeight: Double = 0.0,
    private val currencyWeight: Double,
    private val scarabWeight: Double,
    private val mapWeight: Double = 0.0,
    private val genericWeight: Double = 0.0,
    private val atlasMulti: Double = 1.56,
    private val maxDifficulty: PoeMapDifficulty? = null,
    /**
     * Map is good only if it has a score >= [threshold].
     */
    val threshold: Double,
    /**
     * Modifier to [threshold] and [maxDifficulty] (inversely) when the map is a zana influenced (originator) map.
     * This is often <1 as a discount, since it's harder to roll zana maps.
     */
    private val zanaInfluenceMulti: Double = 0.8,
    val getBadMods: (PoeRollableItem) -> List<PoeRollableItem.ExplicitMod> = PoeMapMods::getBadMods,
    val extraScorer: (PoeRollableItem) -> Double = { 1.0 },
    private val weightDivider: Double? = null,
) : PoeMapScorer, PoeMultiRoll.ItemChecker<PoeMapScorer.Output> {
    private val totalWeight: Double = sequenceOf(
        genericWeight,
        currencyWeight,
        scarabWeight,
        mapWeight,
        rarityWeight,
    ).sum()

    override fun evaluate(item: PoeRollableItem): PoeMapScorer.Output {
        val score = getScore(item)
        val difficulty = getMapDifficulty(item)
        val actualThreshold: Double
        val actualMaxDifficulty: PoeMapDifficulty?
        if (item.klass == PoeItem.Map(PoeItem.MapTier.T16_5)) {
            actualThreshold = threshold * zanaInfluenceMulti
            actualMaxDifficulty = maxDifficulty?.times(1 / zanaInfluenceMulti)
        } else {
            actualThreshold = threshold
            actualMaxDifficulty = maxDifficulty
        }
        val easyEnough = if (actualMaxDifficulty != null) {
            difficulty.strictlyLessOrEqualTo(actualMaxDifficulty)
        } else {
            true
        }
        // println("score = ${score.fmt()}, threshold = ${scorer.threshold}, badMods = $hasBadMods")
        return PoeMapScorer.Output(
            scorer = name,
            score = score,
            scoreThreshold = actualThreshold,
            difficulty = difficulty,
            easyEnough = easyEnough,
            badMods = getBadMods(item),
        )
    }

    init {
        require(totalWeight > 0) {
            "totalWeight must be > 0, got $totalWeight"
        }
    }

    private fun getScore(input: PoeRollableItem): Double {
        require(input.klass.isMapLike())

        val currency =
            getRealPctValue(input.qualities, PoeRollableItem.AugType.Currency)
        val scarab =
            getRealPctValue(input.qualities, PoeRollableItem.AugType.Scarab)
        val quant =
            getRealPctValue(input.qualities, PoeRollableItem.AugType.Generic)
        val rarity =
            getRealPctValue(input.qualities, PoeRollableItem.AugType.Rarity)
        val pack = getRealPctValue(input.qualities, PoeRollableItem.AugType.Pack)
        val map = getRealPctValue(input.qualities, PoeRollableItem.AugType.Map)

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
        aug: PoeRollableItem.AugType,
    ): Int {
        // Each quality improves by
        val chiselMulti = when (aug) {
            PoeRollableItem.AugType.Generic -> 1
            PoeRollableItem.AugType.Rarity -> 3
            PoeRollableItem.AugType.Pack -> 1
            PoeRollableItem.AugType.Map -> 5
            PoeRollableItem.AugType.Currency -> 5
            PoeRollableItem.AugType.Scarab -> 5
            PoeRollableItem.AugType.DivCard -> 5
        }
        val fromChisel = quals.firstOrNull {
            val name = it.name
            name is PoeRollableItem.QualName.FromCurrency && name.ty == aug
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
        // 3.27: 6 is really good. Maybe use 4 for now.
        // 5 is slightly strict when paired with early game difficulty + lots of bad mods
        // 6 is fine on midGame + fewer bad mods (e.g. refl ok)
        val SCARAB = PoeMapScorerImpl(
            "scarab",
            packSizeWeight = 0.6,
            currencyWeight = 0.3,
            scarabWeight = 1.0,
            genericWeight = 0.3,
            mapWeight = 0.05,
            rarityWeight = 0.1,
            // maxDifficulty = PoeMapDifficulty.lateGame,
            threshold = 6.8,
            // T16.5 scarab/currency drop is bad so we have an equal bar
            zanaInfluenceMulti = 0.8,
        )

        // 3.26 only
        val ALVA = PoeMapScorerImpl(
            "alva",
            packSizeWeight = 1.0,
            rarityWeight = 0.4,
            currencyWeight = 1.0,
            scarabWeight = 0.0,
            // default WD: 20-22 for t16.5, 28 for t17
            threshold = 20.0,
            // weightDivider = 1.0,
        )

        // 3.27: 9 is okay (100% map, 90 quant).
        val MAP = PoeMapScorerImpl(
            "map",
            packSizeWeight = 1.0,
            mapWeight = 1.0,
            currencyWeight = 0.0,
            scarabWeight = 0.0,
            maxDifficulty = PoeMapDifficulty.lateGame,
            threshold = 10.0,
            // T16.5 map drop is okay so we have a lower bar
            zanaInfluenceMulti = 0.7,
        )

        val AWAKEN_HARVEST = PoeMapScorerImpl(
            "harvest",
            packSizeWeight = 0.5,
            quantWeight = 0.5,
            currencyWeight = 0.0,
            scarabWeight = 0.0,
            genericWeight = 1.0,
            // 3.0: around 110 IIQ, 52 Pack. Need 23c for single rolling
            // 3.4 is also fine when multi-rolling (~50c?)
            threshold = 2.5,
        )

        // TODO: need a way to auto-categorize the results.
        val ANY = PoeMapScorer.bestOf(
            listOf(
                // AWAKEN_HARVEST,
                SCARAB,
                MAP,
                // ALVA,
            )
        )

        val INVITATION = PoeMapScorerImpl(
            "invitation",
            packSizeWeight = 0.0,
            quantWeight = 1.0,
            currencyWeight = 0.0,
            scarabWeight = 0.0,
            genericWeight = 1.0,
            atlasMulti = 1.0,
            // Heard that melding is not affected by IIQ, so threshold is whatever.
            threshold = 1.7,
        )

        val SCARAB_OR_MAP = object : PoeMapScorer {
            override fun evaluate(item: PoeRollableItem): Output {
                return when (item.klass) {
                    PoeItem.Map(PoeItem.MapTier.T17) -> SCARAB.evaluate(item)
                    PoeItem.Map(PoeItem.MapTier.T16_5) -> MAP.evaluate(item)
                    else -> error("Can't evaluate ${item.klass}")
                }
            }
        }
    }
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
                    currency = PoeCurrencyTab.bindingOrAlch,
                    item = itemSlot
                )
            }

            Normal -> {
                // Alc is enough
                PoeInteractor.applyCurrencyTo(
                    currency = PoeCurrencyTab.bindingOrAlch,
                    item = itemSlot
                )
            }

            Rare -> {
                PoeInteractor.applyCurrencyTo(
                    currency = PoeCurrencyTab.chaos,
                    item = itemSlot
                )
            }

            Unique -> {
                error("Can't roll unique")
            }
        }
    }
}

/**
 * Uses chaos to roll T17, and alchemy to roll T16 and below.
 */
class ChaosOrAlchMapRerollProvider(fuel: Int = 100) : RerollProvider {
    private val alch = ScourAlchRerollProvider(fuel)
    private val chaos = ChaosRerollProvider(fuel)

    override suspend fun hasMore(): Boolean {
        return alch.hasMore() && chaos.hasMore()
    }

    override suspend fun applyTo(itemSlot: Point, item: PoeRollableItem) {
        require(item.klass.isMapLike())
        val provider = if (item.klass == PoeItem.Map(PoeItem.MapTier.T17)) {
            chaos
        } else {
            alch
        }
        provider.applyTo(itemSlot, item)
    }
}

@Suppress("unused")
class ScourAlchRerollProvider(
    private val fuel: Int = 100,
    private val scourSlot: Point = PoeCurrencyTab.scour,
    private val alchSlot: Point = PoeCurrencyTab.bindingOrAlch,
) : RerollProvider {
    private var cachedAlcAndScourCount: Int? = null
    private var useCount = 0

    private suspend fun getAlcAndScourCount(): Int {
        cachedAlcAndScourCount?.let {
            return it
        }
        safeDelayK(30.milliseconds)
        val scourCount = PoeInteractor.getCountAt(
            scourSlot,
            PoeCurrency.KnownType.Scour
        )
        val alcCount = PoeInteractor.getCountAt(
            alchSlot,
            listOf(PoeCurrency.KnownType.Alch, PoeCurrency.KnownType.Binding),
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
                currency = scourSlot,
                item = itemSlot
            )
        }
        // Then alch
        PoeInteractor.applyCurrencyTo(
            currency = alchSlot,
            item = itemSlot
        )
    }
}

object PoeRollMap {
    val kiracInvitationSlot = Point(792, 638)

    suspend fun main() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            PoeMultiRoll.rollItems(
                checker = PoeMapScorerImpl.SCARAB_OR_MAP,
                itemsToRoll = bagSlots().toList(),
                rerollProvider = ChaosOrAlchMapRerollProvider(500),
                shouldContinue = isPoe::value,
            )
        }
        LEADER_KEY.isEnabled("11").collect(::handle)
    }

    suspend fun kiracInvitation() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            PoeMultiRoll.rollItems(
                checker = PoeMapScorerImpl.INVITATION,
                itemsToRoll = listOf(kiracInvitationSlot),
                rerollProvider = ScourAlchRerollProvider(
                    100,
                    scourSlot = PoeGraphicConstants.firstItemInBag,
                    alchSlot = PoeGraphicConstants.secondItemInBag,
                ),
                shouldContinue = isPoe::value,
            )
        }
        LEADER_KEY.isEnabled("17").collect(::handle)
    }

    suspend fun sortInStash() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            val scorer = PoeMapScorerImpl.SCARAB
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
            scoredPoints += input to scorer.evaluate(item).score
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

private fun generateReportImpl(results: List<PoeMapScorer.Output>): String {
    val scores = results.map { it.score }
    return "Average score ${scores.average().fmt()}, each: ${
        results.map {
            "${it.scorer} ${it.score.fmt()} ${it.difficulty.fmt()}"
        }
    }"
}
