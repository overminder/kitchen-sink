package com.gh.om.blizzapi.geardrops

import com.gh.om.blizzapi.RaidDifficulty
import com.gh.om.blizzapi.base.BonusRollDecisionMaker
import com.gh.om.blizzapi.base.Boss
import com.gh.om.blizzapi.base.CharacterState
import com.gh.om.blizzapi.base.GearDropSimulatorHelper
import com.gh.om.blizzapi.base.ShadowlandsGearDrops
import java.util.function.Supplier
import javax.inject.Inject

class GreedyBonusRollDecisionMaker @Inject constructor(
    private val slDrops: ShadowlandsGearDrops,
    private val simulatorHelper: GearDropSimulatorHelper,
) : BonusRollDecisionMaker {
    override fun shouldRollOn(
        cs: CharacterState,
        thisBoss: Boss, thisDifficulty: RaidDifficulty,
        // Not including the current (just defeated) one.
        restOfBosses: Supplier<List<Pair<Boss, RaidDifficulty>>>,
    ): Boolean {
        if (cs.bonusRollCount <= 0) {
            return false
        }

        val baseScore = simulatorHelper.score(cs.equipments)
        val bosses = listOf(thisBoss to thisDifficulty) + restOfBosses.get()
        // For all the rest of the bosses, calculate the average improvement.
        val indexedScores = bosses.mapIndexedTo(mutableListOf()) { ix, (boss, difficulty) ->
            val ilevel = slDrops.translateRaidIlevel(difficulty) + slDrops.ilevelMod(boss)
            val effects = slDrops.getDrop(boss).itemIds.map {
                simulatorHelper.scoreAnyDrop(it, ilevel, cs.equipments, baseScore)
            }
            // Average of the positive scores
            ix to (effects.filter { it.scoreIncr > 0 }.sumByDouble { it.scoreIncr } / effects.size)
        }
        // Sort so that we can check if this boss is among the N bests. (N = number of bonus rolls left)
        indexedScores.sortByDescending { it.second }
        return indexedScores.take(cs.bonusRollCount).find {
            it.first == 0
        } != null
    }
}
