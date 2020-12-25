package com.gh.om.blizzapi.geardrops

import com.gh.om.blizzapi.RaidDifficulty
import com.gh.om.blizzapi.base.Boss
import com.gh.om.blizzapi.base.BossWithDrop
import com.gh.om.blizzapi.base.GearDropSource
import com.gh.om.blizzapi.base.MythicPlusDungeonDrop
import com.gh.om.blizzapi.base.ShadowlandsGearDrops
import com.gh.om.blizzapi.base.ShadowlandsInstance

abstract class Dungeon : GearDropSource {
    override val isDungeon: Boolean = true
    override val name: String
        get() = "Dungeon(${javaClass.simpleName})"

    override fun ilevelMod(boss: BossWithDrop): Int = 0
}

internal fun boss(name: String, vararg itemIds: Int): BossWithDrop {
    return BossWithDrop(name, itemIds.toList())
}

object TheaterOfPain : Dungeon() {
    private val aac = boss("AAC", 178803, 178871)
    private val gore = boss("Gorechop", 178806, 178869)
    private val xav = boss("Xav", 178789)
    private val kul = boss("Kul", 178792, 178870, 178809)
    private val mord = boss("Mord", 178868, 178804, 178872)

    override val bossWithDrops: List<BossWithDrop>
        get() = listOf(aac, gore, xav, kul, mord)
}

object Plaguefall : Dungeon() {
    private val glob = boss("Glob", 178753, 178756)
    private val ickus = boss("Ickus", 178759)
    private val domina = boss("Domina", 178930, 178933)
    private val margrave = boss("Margrave", 178755, 178761, 178769)

    override val bossWithDrops: List<BossWithDrop>
        get() = listOf(glob, ickus, domina, margrave)
}

object Mist : Dungeon() {
    private val ingra = boss("Ingra", 178709, 178696, 178704, 178708)
    private val mistcaller = boss("Mistcaller", 178707, 178705)
    private val tred = boss("Tred", 178714, 178693)

    override val bossWithDrops: List<BossWithDrop>
        get() = listOf(ingra, mistcaller, tred)
}

object DeOtherSide : Dungeon() {
    private val hakkar = boss("Hakkar", 179322)
    private val manastorms = boss("Manastorms", 179339, 179335)
    private val xyexa = boss("Xyexa", 179349, 179343, 179350)
    private val mueh = boss("Mueh", 179351, 179355)

    override val bossWithDrops: List<BossWithDrop>
        get() = listOf(hakkar, manastorms, xyexa, mueh)
}

object Spires : Dungeon() {
    private val kin = boss("1", 180115, 180109)
    private val vent = boss("2", 180102)
    private val oryph = boss("3", 180107, 180117)
    private val devos = boss("4", 180123, 180098)

    override val bossWithDrops: List<BossWithDrop>
        get() = listOf(kin, vent, oryph, devos)
}

object HoA : Dungeon() {
    private val halk = boss("1", 178827, 178813)
    private val eche = boss("2", 178833)
    private val aleez = boss("3", 178828, 178822, 178826)
    private val chamb = boss("4", 178829, 178831, 178824)

    override val bossWithDrops: List<BossWithDrop>
        get() = listOf(halk, eche, aleez, chamb)
}

object SD : Dungeon() {
    private val kryx = boss("1", 178844, 178848)
    private val tarv = boss("2", 178859, 178851, 178849)
    private val bery = boss("3", 178852, 178838)
    private val kaal = boss("4", 178860)

    override val bossWithDrops: List<BossWithDrop>
        get() = listOf(kryx, tarv, bery, kaal)
}

object NecroticWake : Dungeon() {
    private val blight = boss("1", 178732, 178736)
    private val amarth = boss("2", 178740)
    private val stitch = boss("3", 178748, 178772)
    private val nalt = boss("4", 178782, 178781)

    override val bossWithDrops: List<BossWithDrop>
        get() = listOf(blight, amarth, stitch, nalt)
}

