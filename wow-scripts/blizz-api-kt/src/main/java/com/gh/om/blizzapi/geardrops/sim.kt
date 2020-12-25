package com.gh.om.blizzapi.geardrops

import com.gh.om.blizzapi.Item
import com.gh.om.blizzapi.base.BossWithDrop
import com.gh.om.blizzapi.base.EffectFromEquip
import com.gh.om.blizzapi.base.FastBapi
import com.gh.om.blizzapi.base.GearDropSimReport
import com.gh.om.blizzapi.base.GearDropSimulator
import com.gh.om.blizzapi.base.GearDropSimulatorFactory
import com.gh.om.blizzapi.base.GearDropSimulatorHelper
import com.gh.om.blizzapi.base.GearDropSource
import com.gh.om.blizzapi.base.Simc
import javax.inject.Inject

class GearDropSimulatorFactoryImpl @Inject constructor(
    private val helper: GearDropSimulatorHelper,
) : GearDropSimulatorFactory {
    override fun create(site: GearDropSource, equipmentState: Simc.EquipmentState, newIlevel: Int): GearDropSimulator {
        return GearDropSimulatorImpl(helper, site, equipmentState, newIlevel)
    }
}

private class GearDropSimulatorImpl(
    private val helper: GearDropSimulatorHelper,

    private val site: GearDropSource,
    // Can be further bumped by raid specific ilevel mod (e.g. last two bosses in Castle Nathria)
    private val equipmentState: Simc.EquipmentState,
    private val newIlevel: Int,
) : GearDropSimulator {
    private val equipEffects = mutableListOf<EffectFromEquip>()
    private val baseScore = helper.score(equipmentState)

    override fun run(): GearDropSimReport {
        return if (site.isDungeon) {
            runDungeon()
        } else {
            runRaid()
        }
    }

    // Run a M+ dungeon
    private fun runDungeon(): GearDropSimReport.OneDrop {
        for (boss in site.bossWithDrops) {
            doBoss(boss)
        }
        val totalPossibleDrops = site.bossWithDrops.sumBy { it.itemIds.size }
        val sortedEffects = takeSortedEffects()
        require(totalPossibleDrops == sortedEffects.size)
        val averageIncr = sortedEffects.filter { it.scoreIncr > 0 }.sumByDouble { it.scoreIncr } / totalPossibleDrops
        return GearDropSimReport.OneDrop(
            sortedEffects,
            averageIncr,
        )
    }

    private fun runRaid(): GearDropSimReport.Raid {
        val bossReports = mutableListOf<GearDropSimReport>()
        for (boss in site.bossWithDrops) {
            val totalPossibleDrops = boss.itemIds.size
            doBoss(boss)
            val sortedEffects = takeSortedEffects()
            require(totalPossibleDrops == sortedEffects.size)
            val averageIncr =
                sortedEffects.filter { it.scoreIncr > 0 }.sumByDouble { it.scoreIncr } / totalPossibleDrops
            val bossReport = GearDropSimReport.OneDrop(
                sortedEffects,
                averageIncr,
            )
            bossReports += bossReport
        }
        val allEffects = bossReports.flatMapTo(mutableListOf()) { it.sortedEffects }
        allEffects.sortByDescending { it.scoreIncr }
        val averageIncr = bossReports.sumByDouble { it.averageIncr } / site.bossWithDrops.size
        return GearDropSimReport.Raid(bossReports, allEffects, averageIncr)
    }

    private fun takeSortedEffects(): List<EffectFromEquip> {
        val sorted = equipEffects.sortedByDescending { it.scoreIncr }
        equipEffects.clear()
        return sorted
    }

    private fun doBoss(boss: BossWithDrop) {
        for (dropId in boss.itemIds) {
            val toIlevel = newIlevel + site.ilevelMod(boss)
            equipEffects += helper.scoreAnyDrop(dropId, toIlevel, equipmentState, baseScore)
        }
    }
}

class GearDropSimulatorHelperImpl @Inject constructor(
    private val simc: Simc.DB,
    private val bapi: FastBapi,
    private val itemScaling: Simc.ItemScaling,
) : GearDropSimulatorHelper {
    override fun scoreAnyDrop(
        dropId: Int,
        ilevel: Int,
        equipmentState: Simc.EquipmentState,
        baseScore: Double,
    ): EffectFromEquip {
        // A drop might be a gear token. Here we need to calculate the DPS increase for each possible
        // trade option, and choose the best.
        val dropIds = simc.tryTradeGearToken(dropId) ?: listOf(dropId)
        val bestTradeAndSlot = dropIds
            .map { scoreSingleGear(it, ilevel, equipmentState) to it }
            .maxByOrNull { it.first.first }!!

        val apiItem = bapi.getItem(bestTradeAndSlot.second)
        val slot = bestTradeAndSlot.first.second
        val langItem = createSimcItemWithIlevel(apiItem, slot, ilevel)
        return EffectFromEquip(
            bestTradeAndSlot.first.first - baseScore,
            apiItem,
            langItem
        )
    }

    override fun sumStats(items: Collection<Simc.Lang.Item>): Map<Item.Stat, Int> {
        val totalStats = mutableMapOf<Item.Stat, Int>()
        for (item in items) {
            val apiItem = bapi.getItem(item.id)
            val baseIlevel = apiItem.level
            val ilevelDiff = inferItemLevelDiff(item.bonusIds)
            val ilevel = baseIlevel + ilevelDiff
            val scaledItem = scaleItem(apiItem, ilevel)
            for ((stat, value) in scaledItem) {
                addToCounter(stat, value, totalStats)
            }
        }
        return totalStats
    }

    override fun scoreStats(stats: Map<Item.Stat, Int>): Double {
        // Put your pawn score here.
        return (stats[Item.Stat.INTELLECT] ?: 0) * 3.13 +
            (stats[Item.Stat.HASTE_RATING] ?: 0) * 1.43 +
            (stats[Item.Stat.MASTERY_RATING] ?: 0) * 1.28 +
            (stats[Item.Stat.CRIT_RATING] ?: 0) * 1.25 +
            (stats[Item.Stat.VERSATILITY] ?: 0) * 1.15
    }

    override fun pprItem(item: Simc.Lang.Item): String {
        val apiItem = bapi.getItem(item.id)
        val ilevel = apiItem.level + inferItemLevelDiff(item.bonusIds)
        return "${item.id}($ilevel, ${apiItem.name})"
    }

    private fun scoreSingleGear(
        itemId: Int,
        toIlevel: Int,
        equipmentState: Simc.EquipmentState
    ): Pair<Double, Simc.Slot> {
        // Query item, find its slot, and create simc item, and calculate stats.
        val apiItem = bapi.getItem(itemId)

        return when (val slotComb = simc.inventoryToSlot(apiItem.inventory.type)) {
            is Simc.SlotCombination.Just -> {
                equipAndRescore(apiItem, toIlevel, slotComb.slot, equipmentState) to slotComb.slot
            }
            is Simc.SlotCombination.Or -> {
                // Greedly choose the best slot to equip
                val combs = slotComb.slots.map {
                    equipAndRescore(apiItem, toIlevel, it, equipmentState) to it
                }
                combs.maxByOrNull {
                    it.first
                }!!
            }
            is Simc.SlotCombination.And -> {
                require(apiItem.inventory.type == Item.Inventory.TWOHWEAPON) {
                    "invtype: ${apiItem.inventory}"
                }
                val slot = Simc.Slot.MAIN_HAND
                equipAndRescore(apiItem, toIlevel, slot, equipmentState) to slot
            }
            else -> {
                error("Don't know how to handle $itemId (${apiItem.inventory.type})")
            }
        }
    }

    private fun equipAndRescore(
        apiItem: Item,
        newIlevel: Int,
        slot: Simc.Slot,
        equipmentState: Simc.EquipmentState
    ): Double {
        // blocklist legendary slot / trinkets (hard to sim -- maybe use average improvement?)
        if (setOf(Simc.Slot.WRIST, Simc.Slot.TRINKET1, Simc.Slot.TRINKET2).contains(slot)) {
            return -1.0
        }
        val tryEquip = equipmentState.copy()
        val simcItem = createSimcItemWithIlevel(apiItem, slot, newIlevel)
        tryEquip.equip(simcItem)
        return score(tryEquip)
    }

    private fun scaleItem(item: Item, newIlevel: Int): List<Pair<Item.Stat, Int>> {
        return Item.Stat.combatStats.mapNotNull { stat ->
            item.findStat(stat)?.let { statVal ->
                val statAlloc = itemScaling.normStat(item, stat, statVal.value)
                stat to itemScaling.scaledStat(item, newIlevel, statAlloc, stat)
            }
        }
    }
}

private fun <A : Any> addToCounter(key: A, value: Int, toMap: MutableMap<A, Int>) {
    toMap.compute(key) { _, originalValue ->
        (originalValue ?: 0) + value
    }
}

private fun createSimcItemWithIlevel(apiItem: Item, slot: Simc.Slot, newIlevel: Int): Simc.Lang.Item {
    val baseIlevel = apiItem.level
    val bonusId = 1472 + (newIlevel - baseIlevel)
    val bonusIds = listOf(bonusId)
    require(apiItem.level + inferItemLevelDiff(bonusIds) == newIlevel) {
        val inferred = apiItem.level + inferItemLevelDiff(bonusIds)
        "bonusId = $bonusIds, item = ${apiItem.id}, inferred = $inferred, new = $newIlevel"
    }
    return Simc.Lang.Item(slot, apiItem.id, bonusIds, emptyList(), is2hWeapon = apiItem.is2hWeapon)
}

private fun inferItemLevelDiff(bonusIds: List<Int>): Int {
    var diff = 0
    for (bid in bonusIds) {
        if (bid in 1372..1672) {
            diff += bid - 1472
        } else if (bid in 5846..6245) {
            diff += bid - 5845
        }
    }

    return diff
}
