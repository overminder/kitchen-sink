package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.CheckResult
import com.gh.om.ks.arpgmacro.core.ItemChecker
import com.gh.om.ks.arpgmacro.core.map.MapScorer
import com.gh.om.ks.arpgmacro.core.map.MapScorerOutput
import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem
import com.gh.om.ks.arpgmacro.core.map.generateMapReport

class MapScorerCheckResult(
    val output: MapScorerOutput,
) : CheckResult {
    override val isGood: Boolean get() = output.isGood
}

class MapScorerItemChecker(
    private val scorer: MapScorer,
) : ItemChecker<MapScorerCheckResult> {
    override fun evaluate(item: PoeRollableItem): MapScorerCheckResult {
        return MapScorerCheckResult(scorer.evaluate(item))
    }

    override fun generateReport(results: List<MapScorerCheckResult>): String {
        return generateMapReport(results.map { it.output })
    }
}
