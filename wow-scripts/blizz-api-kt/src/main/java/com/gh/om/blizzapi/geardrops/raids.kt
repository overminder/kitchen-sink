package com.gh.om.blizzapi.geardrops

import com.gh.om.blizzapi.base.Boss
import com.gh.om.blizzapi.base.BossWithDrop
import com.gh.om.blizzapi.base.GearDropSource

abstract class Raid : GearDropSource {
    override val isDungeon: Boolean = false
    override val name: String
        get() = "Raid(${javaClass.simpleName})"
}

object CastleNathria : Raid() {
    private val shriek = boss("Shriek", 183034, 182979)
    private val hunter = boss("Hunter", 183040, 182996)
    private val kael = boss("Kael", 183033, 182986, 184019)
    private val xymox = boss("Xymox", 183088, 183004, 183038, 184021)
    private val desto = boss("Desto", 183891, 183028)
    private val darkvein = boss("Darkvein", 183021, 183037)
    private val council = boss("Council", 183039, 183011, 183023, 184024)
    private val sludge = boss("Sludge", 183022, 182981)
    private val legion = boss("Legion", 183895, 183032, 182998)
    private val denath = boss("Denath", 183898, 183020, 183036, 184028, 184030)
    override val bossWithDrops: List<BossWithDrop> = listOf(
        shriek, hunter, kael, xymox, desto, darkvein, council, sludge, legion, denath
    )

    override fun ilevelMod(boss: BossWithDrop): Int = when {
        boss === legion || boss === denath -> {
            7
        }
        else -> 0
    }

    val bosses = mapOf(
        Boss.SHRIEK to shriek,
        Boss.HUNTER to hunter,
        Boss.KAEL to kael,
        Boss.XYMOX to xymox,
        Boss.DESTO to desto,
        Boss.DARKVEIN to darkvein,
        Boss.COUNCIL to council,
        Boss.SLUDGE to sludge,
        Boss.LEGION to legion,
        Boss.DENATH to denath,
    )

    fun getDrop(boss: Boss): BossWithDrop {
        return requireNotNull(bosses[boss]) {
            "Unknown boss ($boss) in $name"
        }
    }
}
