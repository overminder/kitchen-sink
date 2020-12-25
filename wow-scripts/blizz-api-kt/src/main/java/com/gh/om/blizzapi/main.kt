package com.gh.om.blizzapi

import com.gh.om.blizzapi.base.BonusRollDecisionMaker
import com.gh.om.blizzapi.base.Boss
import com.gh.om.blizzapi.base.CharacterState
import com.gh.om.blizzapi.base.CharacterStateFactory
import com.gh.om.blizzapi.base.FastBapi
import com.gh.om.blizzapi.base.GearDropSimulatorFactory
import com.gh.om.blizzapi.base.GearDropSimulatorHelper
import com.gh.om.blizzapi.base.GearDropSource
import com.gh.om.blizzapi.base.LootDistribution
import com.gh.om.blizzapi.base.ShadowlandsGearDrops
import com.gh.om.blizzapi.base.ShadowlandsInstance
import com.gh.om.blizzapi.base.Simc
import com.gh.om.blizzapi.geardrops.chances
import com.gh.om.blizzapi.geardrops.score
import com.google.gson.Gson
import com.tylerthrailkill.helpers.prettyprint.pp
import kotlinx.coroutines.runBlocking
import org.tomlj.Toml
import java.lang.Integer.min
import java.util.function.Supplier
import javax.inject.Inject
import javax.inject.Singleton
import kotlin.random.Random

fun createApp(): App {
    val config = Gson().fromJson(
        Toml.parse(Any::class.java.getResourceAsStream("/config.toml")).toJson(),
        AppConfig::class.java
    )
    val random = Random(12345678L)
    val app = DaggerAppComponent.builder()
        .configModule(ConfigModule(config, random))
        .build()
    runBlocking {
        app.bapi.configure()
    }
    return app
}

fun main() {
    val app = createApp()
    val t0 = System.nanoTime()
    runBlocking {
        app.fastBapi.init()
        app.gearDropSimPresets.init()
    }
    // app.gearDropSimPresets.greatVaultFromDungeonOnce()
    // app.gearDropSimPresets.raidOnce()
    // BFA(8, myself) is 688 before bonus roll, 741 after.
    val nWeeks = 1
    val weeklyActivities = List(nWeeks) {
        ActivityPresets.limit(it + 1)
    }
    app.gearDropSimPresets.multipleWeeks(batch = 300, nWeeks = nWeeks, LootDistribution.BFA, weeklyActivities::get)
    app.gearDropSimPresets.multipleWeeks(batch = 1000, nWeeks = nWeeks, LootDistribution.SL, weeklyActivities::get)
    val dt = (System.nanoTime() - t0) / 1_000_000
    println("Time used: $dt")
}

sealed class PlayerActivity {
    data class Raid(
        val difficulty: RaidDifficulty,
        val bosses: List<Boss>,
        val instance: ShadowlandsInstance,
    ) : PlayerActivity()

    data class MythicPlus(
        val keystoneLevel: Int,
        val instance: ShadowlandsInstance,
    ) : PlayerActivity()
}

// Ignore PVP for now.
sealed class GreatVaultOption {
    data class Raid(
        val source: ShadowlandsInstance,
        val difficulty: RaidDifficulty,
        val includingEndBoss: Boolean
    ) : GreatVaultOption()

    data class MythicPlus(val keystoneLevel: Int) : GreatVaultOption()
}

enum class RaidDifficulty {
    Normal,
    Heroic,
    Mythic,
}

@Singleton
class GearDropSimPresets @Inject constructor(
    private val bapi: FastBapi,
    private val scLang: Simc.Lang.Reader,
    private val config: AppConfig,
    private val equipmentStateFactory: Simc.EquipmentStateFactory,
    private val gearDropSimulatorFactory: GearDropSimulatorFactory,
    private val gearDropSimulatorHelper: GearDropSimulatorHelper,
    private val characterStateFactory: CharacterStateFactory,
    private val slDrops: ShadowlandsGearDrops,
    private val randomSupplier: Supplier<Random>,
    private val bonusRollHelper: BonusRollDecisionMaker,
) {
    lateinit var equipmentState: Simc.EquipmentState

    suspend fun init() {
        val rawGears = scLang.readItems(config.profile.gears)
        rawGears.forEach {
            bapi.populateItem(it.id)
        }
        val gears = rawGears.filter {
            // Ignore legendary pieces for now
            it.id != 173249
        }

        equipmentState = equipmentStateFactory.create()
        gears.forEach(equipmentState::equip)
    }

    // Simply calculate average dps incr from one great vault item.
    fun greatVaultFromDungeonOnce() {
        for (ilevel in listOf(216, 220, 223, 226)) {
            val reports = slDrops.dungeons.map { site ->
                val gearDropSim = gearDropSimulatorFactory.create(site, equipmentState, ilevel)
                gearDropSim.run()
            }
            val avg = reports.sumByDouble { it.averageIncr } / reports.size
            println("All dungeon average for $ilevel: $avg")
        }
    }

    // Simply calculate average dps incr by completing one raid.
    fun raidOnce() {
        for (ilevel in listOf(200, 213, 226)) {
            val site = slDrops.raids.first()
            val gearDropSim = gearDropSimulatorFactory.create(site, equipmentState, ilevel)
            val report = gearDropSim.run()
            val totalIncr = report.averageIncr * site.bossWithDrops.size * 0.15
            println("${site.name} average item for $ilevel: ${report.averageIncr}; total (15% drop rate): $totalIncr")
        }
    }

    fun multipleWeeks(
        batch: Int,
        nWeeks: Int,
        lootDistribution: LootDistribution,
        getWeeklyActivity: (Int) -> List<PlayerActivity>,
    ) {
        data class WeeklyDiff(
            val totalIncr: Double,
            val incrFromGreatVault: Double,
            val equipments: Simc.EquipmentState,
        )

        // This inner loop is a bit slow, mostly due to scaleItem (>40%).
        val changess = List(batch) {
            val cs = characterStateFactory.create(equipmentState.copy(), lootDistribution)
            val diffs = mutableListOf<WeeklyDiff>()
            repeat(nWeeks) {
                val base = gearDropSimulatorHelper.score(cs.equipments)
                val incrFromGreatVault = oneWeek(cs, getWeeklyActivity(it), lootDistribution)
                val eqs = cs.equipments
                diffs += WeeklyDiff(
                    totalIncr = gearDropSimulatorHelper.score(eqs) - base,
                    incrFromGreatVault = incrFromGreatVault,
                    equipments = eqs,
                )
            }
            diffs
        }
        // Total of N weeks, average across batches
        val totalAvg = changess.sumByDouble { it.sumByDouble { it.totalIncr } } / batch
        // Average of N weeks, average across batches
        val weeklyAvg = totalAvg / nWeeks
        // Average of each weeks (across batches),
        val avgByWeek = groupAndSum(changess, { it.totalIncr to it.incrFromGreatVault }) { lhs, rhs ->
            lhs.first + rhs.first to lhs.second + rhs.second
        }.map { it.first / batch to it.second / batch }
        println("totalAvg: $totalAvg, weeklyAvg: $weeklyAvg, avgByWeek: $avgByWeek")
        val bestChanges = changess.maxByOrNull { it.sumByDouble { it.totalIncr } }!!
        // State at the end
        val bestChange = bestChanges.last()
        val bestDifference = equipmentState.diff(bestChange.equipments)
        pp("Best: ${bestChanges.sumByDouble { it.totalIncr }}" to bestDifference.map { (from, to) ->
            renderDifference(from, to)
        })
    }

    private fun renderDifference(from: Simc.Lang.Item?, to: Simc.Lang.Item?): String = buildString {
        from?.let {
            append("- ${gearDropSimulatorHelper.pprItem(it)}")
        }
        to?.let {
            append(" + ${gearDropSimulatorHelper.pprItem(it)}")
        }
    }

    // Returns the incr from great vault.
    private fun oneWeek(
        cs: CharacterState,
        activities: List<PlayerActivity>,
        lootDistribution: LootDistribution,
    ): Double {
        // E.g. bonus roll
        cs.startWeek()

        // Run each activity, and randomly get gear.
        // Equip these gears greedily (might need to put offhand upgrades to bag)
        activities.forEachIndexed { ix, activity ->
            runActivity(activity, cs, lootDistribution) { bossIx ->
                // Gather the rest of the raid bosses (so that we know when to bonus roll).
                // XXX This is quadratic (to the number of raid bosses). Fortunately this is only called when needed.
                require(activity is PlayerActivity.Raid)
                val restOfRaids = activities.drop(ix)
                    .filterIsInstance(PlayerActivity.Raid::class.java)
                    .flatMap {
                        it.bosses.drop(bossIx + 1).map { boss -> boss to it.difficulty }
                    }
                restOfRaids
            }
        }

        // At the end, calculate the great vault rewards. Then greedily choose the best upgrade.
        val greatVaultOptions = materializeGreatVaults(cs.finalizeWeeklyChests())
        val baseScore = gearDropSimulatorHelper.score(cs.equipments)
        val scoredChoices = greatVaultOptions.map { (dropId, ilevel) ->
            gearDropSimulatorHelper.scoreAnyDrop(dropId, ilevel, cs.equipments, baseScore)
        }
        // Greedily choose the best among those that makes sense.
        val bestGreatVaultScore = scoredChoices.filter { it.scoreIncr > 0 }.maxByOrNull { it.scoreIncr }?.let {
            cs.equipments.equip(it.langItem)
            it.scoreIncr
        }
        return bestGreatVaultScore ?: 0.0
    }

    private fun materializeGreatVaults(options: List<GreatVaultOption>): List<Pair<Int, Int>> {
        val out = mutableListOf<Pair<Int, Int>>()
        for (option in options) {
            var got = materializeGreatVault(option)
            while (out.find { it.first == got.first } != null) {
                // Reroll if got the same item.
                got = materializeGreatVault(option)
            }
            out += got
        }
        return out
    }

    // (itemId, Ilevel)
    private fun materializeGreatVault(option: GreatVaultOption): Pair<Int, Int> {
        val rand = randomSupplier.get()
        when (option) {
            is GreatVaultOption.Raid -> {
                val baseIlevel = slDrops.translateRaidIlevel(option.difficulty)
                val site = slDrops.fromInstance(option.source)
                val bossesToChoose = if (option.includingEndBoss) {
                    site.bossWithDrops
                } else {
                    // XXX Hardcoded
                    site.bossWithDrops.take(8)
                }
                // Assuming that we first choose boss, and then choose item from boss. This keeps
                // the drop rate consistent (as if we are completing the whole raid).
                val bossToChoose = bossesToChoose.random(rand)
                val ilevel = baseIlevel + site.ilevelMod(bossToChoose)
                val itemId = bossToChoose.itemIds.random(rand)
                return itemId to ilevel
            }
            is GreatVaultOption.MythicPlus -> {
                val ilevel = slDrops.translateKeystoneLevel(option.keystoneLevel).weeklyChestIlevel
                val site = slDrops.dungeons.random(rand)
                // Assuming that we first choose dungeon, and then choose item from the whole drop pool. This keeps
                // the drop rate consistent (as if we are running every dungeon).
                val itemId = site.bossWithDrops.flatMap { it.itemIds }.random(rand)
                return itemId to ilevel
            }
        }
    }

    private fun runActivity(
        activity: PlayerActivity, cs: CharacterState, lootDistribution: LootDistribution,
        getRestOfBosses: (Int) -> List<Pair<Boss, RaidDifficulty>>
    ) {
        cs.runActivity(activity)
        when (activity) {
            is PlayerActivity.Raid -> {
                val site = slDrops.fromInstance(activity.instance)
                val ilevel = slDrops.translateRaidIlevel(activity.difficulty)

                class SingleBossSource(boss: Boss) : GearDropSource by site {
                    override val bossWithDrops = listOf(slDrops.getDrop(boss))
                }
                // Try to get gear upgrades from each boss.
                activity.bosses.forEachIndexed { ix, boss ->
                    tryGetUpgrade(SingleBossSource(boss), ilevel, lootDistribution.chances.endOfRaidBoss, cs)

                    if (bonusRollHelper.shouldRollOn(cs, boss, activity.difficulty) { getRestOfBosses(ix) }) {
                        require(cs.bonusRollCount > 0)
                        cs.bonusRollCount -= 1
                        tryGetUpgrade(SingleBossSource(boss), ilevel, lootDistribution.chances.bonusRoll!!, cs)
                    }
                }
            }

            is PlayerActivity.MythicPlus -> {
                val site = slDrops.fromInstance(activity.instance)
                val ilevel = slDrops.translateKeystoneLevel(activity.keystoneLevel).endOfDungeonIlevel
                tryGetUpgrade(site, ilevel, lootDistribution.chances.endOfDungeon, cs)
            }
        }
    }

    private fun tryGetUpgrade(
        site: GearDropSource,
        ilevel: Int,
        dropChance: Double,
        cs: CharacterState,
    ) {
        val rand = randomSupplier.get()
        val gearDropSim = gearDropSimulatorFactory.create(site, cs.equipments, ilevel)
        val report = gearDropSim.run()

        if (rand.nextDouble() <= dropChance) {
            val randomDrop = report.sortedEffects.random(rand)

            // Greedily take it (equip it if it's an upgrade). XXX: We might need a better way to
            // lookahead on offhand upgrades...
            if (randomDrop.scoreIncr > 0) {
                cs.equipments.equip(randomDrop.langItem)
            }
        }
    }
}

object ActivityPresets {
    fun limit(week: Int): List<PlayerActivity> {
        val activities = mutableListOf<PlayerActivity>()
        activities += ActivityPresets.tenDungeons(15)
        activities += ActivityPresets.raidClear(RaidDifficulty.Mythic)
        return activities
    }

    fun hea(week: Int): List<PlayerActivity> {
        val activities = mutableListOf<PlayerActivity>()
        activities += ActivityPresets.oneDungeon(week + 5)
        if (week < 4) {
            activities += ActivityPresets.raidClear(RaidDifficulty.Normal)
        } else {
            activities += ActivityPresets.raidFor(RaidDifficulty.Heroic, (week - 3) * 2)
        }
        return activities
    }

    fun myself(week: Int): List<PlayerActivity> {
        val activities = mutableListOf<PlayerActivity>()
        // One more keystone level per week (10+8, 11+9, 12+10, until 15+15)
        activities += ActivityPresets.fourDungeons(min(15, week + 9), min(15, week + 7))

        // Heroic: kill 5, 7, 9, 10, ...
        activities += ActivityPresets.raidFor(RaidDifficulty.Heroic, min(10, 3 + week * 2))
        if (week >= 3) {
            // Kill 1 more mythic boss per 2 weeks, starting from week 3
            activities += ActivityPresets.raidFor(RaidDifficulty.Mythic, week / 2)
        }
        return activities
    }

    fun dungeonPfu(week: Int): List<PlayerActivity> {
        return ActivityPresets.tenDungeons(15) + ActivityPresets.tenDungeons(15)
    }

    fun dungeonHea(week: Int): List<PlayerActivity> {
        return ActivityPresets.fourDungeons(min(15, week + 9), min(15, week + 7))
    }

    fun raidPfu(week: Int): List<PlayerActivity> {
        return listOf(
            ActivityPresets.raidClear(RaidDifficulty.Normal),
            ActivityPresets.raidClear(RaidDifficulty.Heroic),
            ActivityPresets.raidFor(RaidDifficulty.Mythic, min(10, week * 2))
        )
    }

    fun raidHea(week: Int): List<PlayerActivity> {
        val allRaids = List(10) { RaidDifficulty.Normal } + List(10) { RaidDifficulty.Heroic }
        val raids = allRaids.drop(min(10, week * 2)).take(10)
        val n = raids.count { it == RaidDifficulty.Normal }
        val h = raids.count { it == RaidDifficulty.Heroic }
        return listOf(
            ActivityPresets.raidFor(RaidDifficulty.Normal, n),
            ActivityPresets.raidFor(RaidDifficulty.Heroic, h),
        )
    }

    fun raidClear(difficulty: RaidDifficulty): PlayerActivity {
        return PlayerActivity.Raid(
            difficulty,
            ShadowlandsInstance.CastleNathria.bosses,
            ShadowlandsInstance.CastleNathria,
        )
    }

    fun raidClearExceptLastThree(difficulty: RaidDifficulty): PlayerActivity {
        return PlayerActivity.Raid(
            difficulty,
            ShadowlandsInstance.CastleNathria.bosses.filter {
                it != Boss.DENATH && it != Boss.LEGION && it != Boss.SLUDGE
            },
            ShadowlandsInstance.CastleNathria,
        )
    }

    fun raidFor(difficulty: RaidDifficulty, nBosses: Int): PlayerActivity {
        return PlayerActivity.Raid(
            difficulty,
            ShadowlandsInstance.CastleNathria.bosses.take(nBosses),
            ShadowlandsInstance.CastleNathria,
        )
    }

    fun raidFirstThree(difficulty: RaidDifficulty): PlayerActivity {
        return PlayerActivity.Raid(
            difficulty,
            listOf(Boss.SHRIEK, Boss.HUNTER, Boss.DESTO),
            ShadowlandsInstance.CastleNathria,
        )
    }

    fun oneDungeon(keystoneLevel: Int): PlayerActivity {
        return PlayerActivity.MythicPlus(keystoneLevel, ShadowlandsInstance.Mist)
    }

    fun fourDungeons(level1: Int, level2: Int): List<PlayerActivity> {
        return List(3) { oneDungeon(level2) } + oneDungeon(level1)
    }

    fun tenDungeons(keystoneLevel: Int): List<PlayerActivity> {
        return ShadowlandsInstance.dungeons.map { PlayerActivity.MythicPlus(keystoneLevel, it) } +
            List(2) { oneDungeon(keystoneLevel) }
    }
}

fun <A, B> groupAndSum(xxs: Iterable<Iterable<A>>, unwrap: (A) -> B, combine: (B, B) -> B): List<B> {
    val out = mutableListOf<B>()
    var firstIter = true
    for (xs in xxs) {
        xs.forEachIndexed { i, x ->
            if (firstIter) {
                out += unwrap(x)
            } else {
                out[i] = combine(out[i], unwrap(x))
            }
        }
        firstIter = false
    }
    return out
}

