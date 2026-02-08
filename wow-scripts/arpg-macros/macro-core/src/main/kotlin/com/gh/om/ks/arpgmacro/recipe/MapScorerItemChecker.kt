package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.CheckResult
import com.gh.om.ks.arpgmacro.core.ItemChecker
import com.gh.om.ks.arpgmacro.core.MapScorer
import com.gh.om.ks.arpgmacro.core.MapScorerOutput
import com.gh.om.ks.arpgmacro.core.PoeRollableItem
import com.gh.om.ks.arpgmacro.core.generateMapReport

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
