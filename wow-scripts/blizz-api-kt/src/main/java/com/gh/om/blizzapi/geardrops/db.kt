import com.gh.om.blizzapi.RaidDifficulty
import com.gh.om.blizzapi.base.Boss
import com.gh.om.blizzapi.base.BossWithDrop
import com.gh.om.blizzapi.base.GearDropSource
import com.gh.om.blizzapi.base.MythicPlusDungeonDrop
import com.gh.om.blizzapi.base.ShadowlandsGearDrops
import com.gh.om.blizzapi.base.ShadowlandsInstance
import com.gh.om.blizzapi.geardrops.CastleNathria
import com.gh.om.blizzapi.geardrops.DeOtherSide
import com.gh.om.blizzapi.geardrops.HoA
import com.gh.om.blizzapi.geardrops.Mist
import com.gh.om.blizzapi.geardrops.NecroticWake
import com.gh.om.blizzapi.geardrops.Plaguefall
import com.gh.om.blizzapi.geardrops.SD
import com.gh.om.blizzapi.geardrops.Spires
import com.gh.om.blizzapi.geardrops.TheaterOfPain

object ShadowlandsGearDropsImpl : ShadowlandsGearDrops {
    override val dungeons: List<GearDropSource>
        get() = ShadowlandsInstance.dungeons.map(::fromInstance)

    override val raids: List<GearDropSource>
        get() = ShadowlandsInstance.raids.map(::fromInstance)

    override fun fromInstance(instance: ShadowlandsInstance): GearDropSource {
        return when (instance) {
            ShadowlandsInstance.TheaterOfPain -> TheaterOfPain
            ShadowlandsInstance.Plaguefall -> Plaguefall
            ShadowlandsInstance.Mist -> Mist
            ShadowlandsInstance.DeOtherSide -> DeOtherSide
            ShadowlandsInstance.Spires -> Spires
            ShadowlandsInstance.HoA -> HoA
            ShadowlandsInstance.SD -> SD
            ShadowlandsInstance.NecroticWake -> NecroticWake
            ShadowlandsInstance.CastleNathria -> CastleNathria
        }
    }

    override fun getDrop(boss: Boss): BossWithDrop {
        return CastleNathria.getDrop(boss)
    }

    override fun bossesFrom(instance: ShadowlandsInstance): Collection<Boss> {
        return when (instance) {
            ShadowlandsInstance.CastleNathria -> CastleNathria.bosses.keys
            else -> TODO()
        }
    }

    override fun translateKeystoneLevel(keystoneLevel: Int): MythicPlusDungeonDrop {
        require(keystoneLevel >= 2)
        val clamped = if (keystoneLevel > 15) {
            15
        } else {
            keystoneLevel
        }
        val ix = (clamped - 2) * 2
        val endOfDungeon = keystoneDrops[ix]
        val weeklyChest = keystoneDrops[ix + 1]
        return MythicPlusDungeonDrop(endOfDungeonIlevel = endOfDungeon, weeklyChestIlevel = weeklyChest)
    }

    override fun translateRaidIlevel(difficulty: RaidDifficulty): Int {
        return when (difficulty) {
            RaidDifficulty.Normal -> 200
            RaidDifficulty.Heroic -> 213
            RaidDifficulty.Mythic -> 226
        }
    }

    override fun ilevelMod(boss: Boss): Int {
        return when (boss) {
            Boss.LEGION, Boss.DENATH -> 7
            else -> 0
        }
    }
}

private val keystoneDrops = ("187 200 190 203 194 207 194 210 197 210 200 " +
    "213 200 216 200 216 203 220 203 220 207 223 207 223 207 226 210 226").split(" ").map {
    it.toInt()
}
