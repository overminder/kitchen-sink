package com.gh.om.gamemacros.complex

import com.gh.om.gamemacros.MouseHooks
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
    private val currencyWeight: Double,
    private val scarabWeight: Double,
    private val mapWeight: Double = 0.0,
    private val genericWeight: Double = 0.0,
    private val atlasMulti: Double = 1.88,
    val threshold: Double,
    val hasBadMods: (PoeRollableItem) -> Boolean = { false },
    val extraScorer: (PoeRollableItem) -> Double = { 1.0 },
) : PoeMapScorer {
    private val totalWeight = sequenceOf(
        genericWeight,
        currencyWeight,
        scarabWeight,
        mapWeight,
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
        require(input.klass == PoeItem.Klass.Map)

        val currency =
            getRealPctValue(input.qualities, PoeRollableItem.MapAug.Currency)
        val scarab =
            getRealPctValue(input.qualities, PoeRollableItem.MapAug.Scarab)
        val quant =
            getRealPctValue(input.qualities, PoeRollableItem.MapAug.Quant)
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
        val mapMulti = ((map.toDouble() / 100) * atlasMulti) + 1
        val weightedSum = genericWeight + currencyMulti * currencyWeight +
                scarabMulti * scarabWeight + mapMulti * mapWeight
        // normalize by weight = 1
        val normScore = weightedSum * dropMulti / totalWeight
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
            currencyWeight = 0.8,
            scarabWeight = 1.8,
            mapWeight = 0.4,
            threshold = 10.5,
            hasBadMods = ::hasBadModsForAbyss,
        )

        val abyssModWithDescriptionToAvoid = listOf(
            // -37% res is too bad. However this also matches t16 -12% res,
            // so a descriptin check is needed to disambiguate.
            "of Exposure" to "-20%"
        )

        val mobDefenseMods = listOf(
            PoeAffixMatcher.byNumericDescr("Buffered") {
                it >= 40
            },
            PoeAffixMatcher.byNumericDescr("Fecund") {
                it >= 70
            },
            PoeAffixMatcher.byNumericDescr("of Toughness") {
                it >= 35
            },
            PoeAffixMatcher.byNumericDescr("of Impotence") {
                it >= 25
            }
        )

        val alwaysAnnoyingMods = listOf(
            // 78% scarab is nice but volatile is too annoying
            "Volatile",
            // 56% rarity is a joke, compared to the 3 seconds lag
            "Cycling",
            // Tentacles make mapping much slower
            "Decaying",
        )

        val alvaModsToAvoid = listOf(
            // Buff expiration means shrine buff will be gone faster
            "of Transience",
            // Awakener rune can spawn in incursion which is really bad
            // due to lagging
            "of Desolation",
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

        val ALVA = PoeMapScorerImpl(
            packSizeWeight = 1.0,
            currencyWeight = 1.0,
            scarabWeight = 0.0,
            threshold = 20.0,
            hasBadMods = { item ->
                alvaModsToAvoid.any(item::hasAffix) ||
                        mobDefenseMods.count { matcher ->
                            item.hasAffixThat(matcher::matches)
                        } > 1
            },
            extraScorer = { item ->
                val countOfMoreDropMods = item.explicitMods.count { mod ->
                    moreDropMods.any { it.matches(mod) }
                }
                1 + countOfMoreDropMods * 0.08
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
            // 3.0: around 110 IIQ, 52 Pack. Need 23c
            threshold = 3.0,
        )

        val ANY = PoeMapScorer.anyGood(
            listOf(
                ABYSS,
                AWAKEN_HARVEST,
                MAP,
                ALVA,
            )
        )
    }
}

fun main() {
    val input = """
Item Class: Maps
Rarity: Rare
Exposed Turf
City Square Map
--------
Map Tier: 16
Item Quantity: +109% (augmented)
Item Rarity: +66% (augmented)
Monster Pack Size: +40% (augmented)
More Maps: +50% (augmented)
More Currency: +196% (augmented)
--------
Item Level: 85
--------
Monster Level: 83
--------
{ Implicit Modifier }
Area is Influenced by the Originator's Memories — Unscalable Value (implicit)
--------
{ Prefix Modifier "Equalising" (Tier: 1) }
Rare and Unique Monsters remove 5% of Life, Mana and Energy Shield from Players or their Minions on Hit
{ Prefix Modifier "Fecund" (Tier: 1) }
98(90-100)% more Monster Life
{ Suffix Modifier "of Desolation" (Tier: 1) }
Area has patches of Awakeners' Desolation
{ Suffix Modifier "of Endurance" (Tier: 1) }
Monsters have +1 to Maximum Endurance Charges
Monsters gain an Endurance Charge when hit
{ Suffix Modifier "of Fatigue" }
Players have 40% less Cooldown Recovery Rate
--------
Travel to this Map by using it in a personal Map Device. Maps can only be used once.



        """

    val output = PoeItemParser.parseAsRollable(input)
    println(output)
    val scorer = PoeMapScorerImpl.ALVA
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
                scorer = PoeMapScorerImpl.ANY,
                mapsToRoll = bagSlots().toList(),
                // rerollProvider = ChaosRerollProvider(1000),
                rerollProvider = ScourAlchRerollProvider(1000),
                shouldContinue = isPoe::value,
            )
        }
        LEADER_KEY.isEnabled("11").collect(::handle)
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
            require(map.klass == PoeItem.Klass.Map) {
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

}
