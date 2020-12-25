package com.gh.om.blizzapi.base

import com.gh.om.blizzapi.Item
import com.gh.om.blizzapi.RaidDifficulty

enum class ShadowlandsInstance {

    TheaterOfPain,
    Plaguefall,
    DeOtherSide,
    Spires,
    HoA,
    SD,
    NecroticWake,
    Mist,
    CastleNathria;

    companion object {
        val raids = setOf(CastleNathria)
        val dungeons = setOf(
            TheaterOfPain,
            Plaguefall,
            DeOtherSide,
            Spires,
            HoA,
            SD,
            NecroticWake,
            Mist
        )
    }

    val bosses: List<Boss>
        get() = when (this) {
            CastleNathria -> listOf(
                Boss.SHRIEK,
                Boss.HUNTER,
                Boss.KAEL,
                Boss.XYMOX,
                Boss.DESTO,
                Boss.DARKVEIN,
                Boss.COUNCIL,
                Boss.SLUDGE,
                Boss.LEGION,
                Boss.DENATH,
            )
            else -> TODO("Not implemented yet")
        }
}

enum class Boss {
    SHRIEK,
    HUNTER,
    KAEL,
    XYMOX,
    DESTO,
    DARKVEIN,
    COUNCIL,
    SLUDGE,
    LEGION,
    DENATH;
}

data class BossWithDrop(
    val name: String,
    val itemIds: List<String>,
)

interface GearDropSource {
    val isDungeon: Boolean
    val name: String
    val bosses: List<BossWithDrop>

    // Some bosses have higher ilevel
    fun ilevelMod(boss: BossWithDrop): Int
}

interface ShadowlandsGearDrops {
    val dungeons: List<GearDropSource>
    val raids: List<GearDropSource>

    fun fromInstance(instance: ShadowlandsInstance): GearDropSource
    fun fromBoss(boss: Boss): BossWithDrop
    fun translateKeystoneLevel(keystoneLevel: Int): MythicPlusDungeonDrop
    fun translateRaidIlevel(difficulty: RaidDifficulty): Int
}

data class MythicPlusDungeonDrop(
    val endOfDungeonIlevel: Int,
    val weeklyChestIlevel: Int,
)

interface GearDropSimulatorFactory {
    fun create(
        site: GearDropSource,
        equipmentState: Simc.EquipmentState,
        // Can be further bumped by raid specific ilevel mod (e.g. last two bosses in Castle Nathria)
        newIlevel: Int,
    ): GearDropSimulator
}

interface GearDropSimulator {
    suspend fun run(): GearDropSimReport
}

interface GearDropSimulatorHelper {
    // "Any drop" could either be a piece of gear, or a gear token (e.g. from Castle Nathria).
    suspend fun scoreAnyDrop(
        dropId: String,
        ilevel: Int,
        equipmentState: Simc.EquipmentState,
        baseScore: Double
    ): EffectFromEquip

    suspend fun sumStats(items: Collection<Simc.Lang.Item>): Map<Item.Stat, Int>
    fun scoreStats(stats: Map<Item.Stat, Int>): Double
    suspend fun pprItem(item: Simc.Lang.Item): String
}

data class EffectFromEquip(
    val scoreIncr: Double,
    val apiItem: Item,
    val langItem: Simc.Lang.Item,
)

sealed class GearDropSimReport {
    abstract val averageIncr: Double
    abstract val sortedEffects: List<EffectFromEquip>

    data class OneDrop(
        override val sortedEffects: List<EffectFromEquip>,
        override val averageIncr: Double,
    ) : GearDropSimReport()

    data class Raid(
        val bosses: List<GearDropSimReport>,
        override val sortedEffects: List<EffectFromEquip>,
        override val averageIncr: Double,
    ) : GearDropSimReport()
}
