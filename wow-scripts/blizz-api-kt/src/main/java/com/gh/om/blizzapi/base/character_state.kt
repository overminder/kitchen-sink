package com.gh.om.blizzapi.base

import com.gh.om.blizzapi.GreatVaultOption
import com.gh.om.blizzapi.PlayerActivity

interface CharacterStateFactory {
    fun create(
        equipmentState: Simc.EquipmentState,
        lootDistribution: LootDistribution,
    ): CharacterState
}

interface CharacterState {
    val equipments: Simc.EquipmentState
    fun startWeek()
    fun runActivity(activity: PlayerActivity)
    fun finalizeWeeklyChests(): List<GreatVaultOption>

    var bonusRollCount: Int
}
