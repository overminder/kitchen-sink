package com.gh.om.blizzapi.geardrops

import com.gh.om.blizzapi.GreatVaultOption
import com.gh.om.blizzapi.PlayerActivity
import com.gh.om.blizzapi.RaidDifficulty
import com.gh.om.blizzapi.base.Boss
import com.gh.om.blizzapi.base.CharacterState
import com.gh.om.blizzapi.base.CharacterStateFactory
import com.gh.om.blizzapi.base.LootDistribution
import com.gh.om.blizzapi.base.ShadowlandsInstance
import com.gh.om.blizzapi.base.Simc
import javax.inject.Inject
import kotlin.math.min

class EquipmentStateFactoryImpl @Inject constructor() : Simc.EquipmentStateFactory {
    override fun create(): Simc.EquipmentState {
        return EquipmentStateImpl()
    }
}

object CharacterStateFactoryImpl : CharacterStateFactory {
    override fun create(
        equipmentState: Simc.EquipmentState,
        lootDistribution: LootDistribution,
    ) = CharacterStateImpl(equipmentState, lootDistribution)
}

class CharacterStateImpl(
    override val equipments: Simc.EquipmentState,
    private val lootDistribution: LootDistribution
) : CharacterState {
    private val defeatedLastBoss = mutableSetOf<RaidDifficulty>()

    // Keystone levels this week
    private val mythicPlusCompleted = mutableListOf<Int>()

    // Per difficulty this week
    private val raidBossesKilled = mutableMapOf<RaidDifficulty, MutableSet<Boss>>()

    override var bonusRollCount: Int = 0

    override fun startWeek() {
        if (lootDistribution.chances.bonusRoll != null) {
            bonusRollCount = min(5, bonusRollCount + 2)
        }
    }

    override fun runActivity(activity: PlayerActivity) {
        when (activity) {
            is PlayerActivity.Raid -> {
                for (boss in activity.bosses) {
                    raidBossesKilled.compute(activity.difficulty) { _, v ->
                        (v ?: mutableSetOf()).also {
                            it += boss
                        }
                    }
                }
            }
            is PlayerActivity.MythicPlus -> {
                mythicPlusCompleted += activity.keystoneLevel
            }
        }
    }

    override fun finalizeWeeklyChests(): List<GreatVaultOption> {
        val res = when (lootDistribution) {
            LootDistribution.BFA -> generateOptionsForBfa()
            LootDistribution.SL -> generateOptionsForSl()
        }
        mythicPlusCompleted.clear()
        raidBossesKilled.clear()
        return res
    }

    private fun generateOptionsForBfa(): List<GreatVaultOption> {
        // Only count the highest M+
        return listOfNotNull(mythicPlusCompleted.maxOrNull()?.let(GreatVaultOption::MythicPlus))
    }

    private fun generateOptionsForSl(): List<GreatVaultOption> {
        // 1. Update defeatedLastBoss.
        for ((diff, bosses) in raidBossesKilled) {
            if (bosses.contains(Boss.DENATH)) {
                defeatedLastBoss.add(diff)
            }
        }

        // 2. Sort content completed and generate great vault options
        // 2.1 M+
        val keystones = mythicPlusCompleted.sortedDescending()
        val mplusOptions = listOf(1, 4, 10).mapNotNull {
            keystones.getOrNull(it - 1)
        }.map(GreatVaultOption::MythicPlus)

        // 2.2 Raid
        val bossDifficulties = raidBossesKilled.flatMap { entry ->
            List(entry.value.size) { entry.key }
        }.sortedDescending()
        val raidOptions = listOf(3, 7, 10).mapNotNull {
            bossDifficulties.getOrNull(it - 1)
        }.map {
            GreatVaultOption.Raid(
                ShadowlandsInstance.CastleNathria,
                it,
                defeatedLastBoss.contains(it)
            )
        }
        return mplusOptions + raidOptions
    }
}

class EquipmentStateImpl : Simc.EquipmentState {
    private val slots = mutableMapOf<Simc.Slot, Simc.Lang.Item>()
    private var has2hWeapon = false

    // Store the unequipped MH/OH/2H weapons so that we can switch them back
    private val bag = mutableMapOf<Simc.Lang.WeaponKind, Simc.Lang.Item>()

    override val items: Collection<Simc.Lang.Item>
        get() = slots.values

    override fun equip(item: Simc.Lang.Item) {
        val toSlot = item.slot
        val unequipped = if (item.is2hWeapon) {
            require(toSlot == Simc.Slot.MAIN_HAND)
            has2hWeapon = true
            listOfNotNull(slots.remove(Simc.Slot.MAIN_HAND), slots.remove(Simc.Slot.OFF_HAND))
        } else {
            if (has2hWeapon && (toSlot == Simc.Slot.MAIN_HAND || toSlot == Simc.Slot.OFF_HAND)) {
                has2hWeapon = false
                listOfNotNull(slots.remove(Simc.Slot.MAIN_HAND)).also {
                    tryEquipBackTheOtherHand(toSlot)
                }
            } else {
                listOfNotNull(slots.remove(toSlot))
            }
        }
        slots[toSlot] = item
        unequipped.filter { shouldPutBackToBag(item, it) }.forEach {
            bag[it.weaponKind!!] = it
        }
    }

    override fun copy(): Simc.EquipmentState {
        val res = EquipmentStateImpl()
        res.slots += slots
        res.has2hWeapon = has2hWeapon
        res.bag += bag
        return res
    }

    override fun diff(other: Simc.EquipmentState): List<Pair<Simc.Lang.Item?, Simc.Lang.Item?>> {
        val allSlots = slots.keys + other.items.map { it.slot }
        return allSlots.mapNotNull { slot ->
            val mine = slots[slot]
            val theirs = other.items.find { it.slot == slot }
            if (mine != theirs) {
                mine to theirs
            } else {
                null
            }
        }
    }

    private fun shouldPutBackToBag(newItem: Simc.Lang.Item, unequipped: Simc.Lang.Item): Boolean {
        // Only put weapon pieces back to bag.
        val newWK = newItem.weaponKind ?: return false
        val oldWK = unequipped.weaponKind ?: return false
        // If it's the same slot, don't put back
        if (newWK == oldWK) {
            return false
        }
        // If a two-hand weapon is unequipped, don't put it back.
        if (oldWK == Simc.Lang.WeaponKind.TWO_HAND) {
            return false
        }
        // Must be switching from mh+oh to 2h
        require(newWK == Simc.Lang.WeaponKind.TWO_HAND)
        return true
    }

    private fun tryEquipBackTheOtherHand(oneHand: Simc.Slot) {
        val kind = when (oneHand) {
            Simc.Slot.MAIN_HAND -> {
                Simc.Lang.WeaponKind.OFF_HAND
            }
            Simc.Slot.OFF_HAND -> {
                Simc.Lang.WeaponKind.MAIN_HAND
            }
            else -> {
                error("Not a 1h weapon slot: $oneHand")
            }
        }
        bag.remove(kind)?.let {
            slots[it.slot] = it
        }
    }
}
