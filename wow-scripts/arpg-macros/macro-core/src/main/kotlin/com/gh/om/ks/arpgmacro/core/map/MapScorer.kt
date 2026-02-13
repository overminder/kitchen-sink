package com.gh.om.ks.arpgmacro.core.map

import com.gh.om.ks.arpgmacro.core.item.PoeItem
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem
import com.gh.om.ks.arpgmacro.core.item.isMapLike

/**
 * Evaluates whether a rolled map meets acceptance criteria.
 */
interface MapScorer {
    fun evaluate(item: PoeRollableItem): MapScorerOutput

    companion object {
        /**
         * Composite scorer that picks the best result from multiple scorers.
         */
        fun bestOf(scorers: List<MapScorer>): MapScorer {
            require(scorers.isNotEmpty())
            return object : MapScorer {
                override fun evaluate(item: PoeRollableItem): MapScorerOutput {
                    return scorers
                        .map { it.evaluate(item) }
                        .maxBy { it.score / it.scoreThreshold }
                }
            }
        }
    }
}

data class MapScorerOutput(
    val scorerName: String,
    val score: Double,
    val scoreThreshold: Double,
    val difficulty: PoeMapDifficulty,
    val easyEnough: Boolean,
    val badMods: List<PoeRollableItem.ExplicitMod>,
) {
    val isGood: Boolean
        get() = score >= scoreThreshold && easyEnough && badMods.isEmpty()
}

/**
 * Configurable map scorer with weighted quality scoring and difficulty checking.
 */
class MapScorerImpl(
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
    val threshold: Double,
    private val zanaInfluenceMulti: Double = 0.8,
    val getBadMods: (PoeRollableItem) -> List<PoeRollableItem.ExplicitMod> = PoeMapMods::getBadMods,
    val extraScorer: (PoeRollableItem) -> Double = { 1.0 },
    private val weightDivider: Double? = null,
) : MapScorer {
    private val totalWeight: Double = sequenceOf(
        genericWeight, currencyWeight, scarabWeight, mapWeight, rarityWeight,
    ).sum()

    init {
        require(totalWeight > 0) { "totalWeight must be > 0, got $totalWeight" }
    }

    override fun evaluate(item: PoeRollableItem): MapScorerOutput {
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
        return MapScorerOutput(
            scorerName = name,
            score = score,
            scoreThreshold = actualThreshold,
            difficulty = difficulty,
            easyEnough = easyEnough,
            badMods = getBadMods(item),
        )
    }

    private fun getScore(input: PoeRollableItem): Double {
        require(input.klass.isMapLike())

        val currency = getRealPctValue(input.qualities, PoeRollableItem.AugType.Currency)
        val scarab = getRealPctValue(input.qualities, PoeRollableItem.AugType.Scarab)
        val quant = getRealPctValue(input.qualities, PoeRollableItem.AugType.Generic)
        val rarity = getRealPctValue(input.qualities, PoeRollableItem.AugType.Rarity)
        val pack = getRealPctValue(input.qualities, PoeRollableItem.AugType.Pack)
        val map = getRealPctValue(input.qualities, PoeRollableItem.AugType.Map)

        val packMulti = ((pack.toDouble() / 100) * atlasMulti * packSizeWeight) + 1
        val quantMulti = ((quant.toDouble() / 100) * atlasMulti * quantWeight) + 1
        val dropMulti = packMulti * quantMulti
        val currencyMulti = ((currency.toDouble() / 100) * atlasMulti) + 1
        val scarabMulti = ((scarab.toDouble() / 100) * atlasMulti) + 1
        val rarityMulti = ((rarity.toDouble() / 100) * atlasMulti) + 1
        val mapMulti = ((map.toDouble() / 100) * atlasMulti) + 1
        val weightedSum = genericWeight + currencyMulti * currencyWeight +
                scarabMulti * scarabWeight + mapMulti * mapWeight +
                rarityMulti * rarityWeight
        val normScore = weightedSum * dropMulti / (weightDivider ?: totalWeight)
        return normScore * extraScorer(input)
    }

    companion object {
        private fun getRealPctValue(
            quals: List<PoeRollableItem.Quality>,
            aug: PoeRollableItem.AugType,
        ): Int {
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

        val SCARAB = MapScorerImpl(
            "scarab",
            packSizeWeight = 0.6,
            currencyWeight = 0.3,
            scarabWeight = 1.0,
            genericWeight = 0.3,
            mapWeight = 0.05,
            rarityWeight = 0.1,
            threshold = 6.8,
            zanaInfluenceMulti = 0.8,
        )

        val MAP = MapScorerImpl(
            "map",
            packSizeWeight = 1.0,
            mapWeight = 1.0,
            currencyWeight = 0.0,
            scarabWeight = 0.0,
            maxDifficulty = PoeMapDifficulty.lateGame,
            threshold = 10.0,
            zanaInfluenceMulti = 0.7,
        )

        val INVITATION = MapScorerImpl(
            "invitation",
            packSizeWeight = 0.0,
            quantWeight = 1.0,
            currencyWeight = 0.0,
            scarabWeight = 0.0,
            genericWeight = 1.0,
            atlasMulti = 1.0,
            threshold = 1.7,
        )

        val SCARAB_OR_MAP = object : MapScorer {
            override fun evaluate(item: PoeRollableItem): MapScorerOutput {
                return when (item.klass) {
                    PoeItem.Map(PoeItem.MapTier.T17) -> SCARAB.evaluate(item)
                    PoeItem.Map(PoeItem.MapTier.T16_5) -> MAP.evaluate(item)
                    else -> error("Can't evaluate ${item.klass}")
                }
            }
        }
    }
}

fun generateMapReport(results: List<MapScorerOutput>): String {
    val scores = results.map { it.score }
    return "Average score ${scores.average().fmt()}, each: ${
        results.map {
            "${it.scorerName} ${it.score.fmt()} ${it.difficulty.fmt()}"
        }
    }"
}
