package com.gh.om.blizzapi.geardrops

import com.gh.om.blizzapi.base.Simc
import javax.inject.Inject

class EquipmentStateFactoryImpl @Inject constructor() : Simc.EquipmentStateFactory {
    override fun create(): Simc.EquipmentState {
        return EquipmentStateImpl()
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
