package com.gh.om.blizzapi.geardrops

import com.gh.om.blizzapi.Item
import com.gh.om.blizzapi.base.GearDropSimReport
import com.gh.om.blizzapi.base.GearDropSimulatorHelper
import com.gh.om.blizzapi.base.LootDistribution
import com.gh.om.blizzapi.base.ShadowlandsInstance
import com.gh.om.blizzapi.base.Simc
import com.tylerthrailkill.helpers.prettyprint.pp

fun GearDropSimReport.ppr() {
    if (this is GearDropSimReport.Raid) {
        println("Average from ${bosses.size} bosses: $averageIncr")
        bosses.forEach {
            it.ppr()
        }
    } else {
        println("Average: $averageIncr")
        pp(sortedEffects.map { it.scoreIncr to it.apiItem.name })
    }
}

val ShadowlandsInstance.isDungeon: Boolean
    get() = ShadowlandsInstance.dungeons.contains(this)

fun GearDropSimulatorHelper.score(equipmentState: Simc.EquipmentState): Double {
    return scoreStats(sumStats(equipmentState.items))
}

val Item.is2hWeapon: Boolean
    get() = inventory.type == Item.Inventory.TWOHWEAPON

val Simc.Lang.Item.weaponKind: Simc.Lang.WeaponKind?
    get() {
        return when {
            is2hWeapon -> {
                Simc.Lang.WeaponKind.TWO_HAND
            }
            slot == Simc.Slot.MAIN_HAND -> {
                Simc.Lang.WeaponKind.MAIN_HAND
            }
            slot == Simc.Slot.OFF_HAND -> {
                Simc.Lang.WeaponKind.OFF_HAND
            }
            else -> {
                null
            }
        }
    }

data class DropChances(
    val endOfDungeon: Double,
    val endOfRaidBoss: Double,
    // Null means that we don't have bonus roll in this expansion
    val bonusRoll: Double?,
) {
    companion object {
        val bfa = DropChances(
            endOfDungeon = 0.6,
            endOfRaidBoss = 0.25,
            bonusRoll = 0.4,
        )
        val sl = DropChances(
            endOfDungeon = 0.4,
            endOfRaidBoss = 0.15,
            bonusRoll = null,
        )
    }
}

val LootDistribution.chances: DropChances
    get() = when (this) {
        LootDistribution.BFA -> DropChances.bfa
        LootDistribution.SL -> DropChances.sl
    }
