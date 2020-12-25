package com.gh.om.blizzapi

import com.gh.om.blizzapi.base.Bapi
import com.gh.om.blizzapi.base.Boss
import com.gh.om.blizzapi.base.GearDropSimulatorFactory
import com.gh.om.blizzapi.base.GearDropSimulatorHelper
import com.gh.om.blizzapi.base.GearDropSource
import com.gh.om.blizzapi.base.ShadowlandsGearDrops
import com.gh.om.blizzapi.base.ShadowlandsInstance
import com.gh.om.blizzapi.base.Simc
import com.gh.om.blizzapi.geardrops.score
import com.google.gson.Gson
import com.tylerthrailkill.helpers.prettyprint.pp
import kotlinx.coroutines.runBlocking
import org.tomlj.Toml
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
    runBlocking {
        println(app.bapi.token)
        val item = app.bapi.getItem("178829")
        // pp(item)
    }

    runBlocking {
        app.gearDropSimPresets.init()
        // app.gearDropSimPresets.greatVaultFromDungeonOnce()
        // app.gearDropSimPresets.raidOnce()
        app.gearDropSimPresets.manyOneWeeks()
    }
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
    private val scLang: Simc.Lang.Reader,
    private val config: AppConfig,
    private val equipmentStateFactory: Simc.EquipmentStateFactory,
    private val bapi: Bapi,
    private val gearDropSimulatorFactory: GearDropSimulatorFactory,
    private val gearDropSimulatorHelper: GearDropSimulatorHelper,
    private val slDrops: ShadowlandsGearDrops,
    private val randomSupplier: Supplier<Random>,
) {
    lateinit var equipmentState: Simc.EquipmentState

    suspend fun init() {
        val rawGears = scLang.readItems(config.profile.gears)
        val gears = rawGears.filter {
            // Ignore legendary pieces for now
            it.id != "173249"
        }

        equipmentState = equipmentStateFactory.create()
        gears.forEach(equipmentState::equip)
    }

    // Simply calculate average dps incr from one great vault item.
    suspend fun greatVaultFromDungeonOnce() {
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
    suspend fun raidOnce() {
        for (ilevel in listOf(200, 213, 226)) {
            val site = slDrops.raids.first()
            val gearDropSim = gearDropSimulatorFactory.create(site, equipmentState, ilevel)
            val report = gearDropSim.run()
            val totalIncr = report.averageIncr * site.bosses.size * 0.15
            println("${site.name} average item for $ilevel: ${report.averageIncr}; total (15% drop rate): $totalIncr")
        }
    }

    suspend fun manyOneWeeks() {
        val base = gearDropSimulatorHelper.score(equipmentState)
        // This loop is slow.
        val changes = List(20) {
            val changed = oneWeek()
            val diff = gearDropSimulatorHelper.score(changed) - base
            diff to changed
        }
        val avg = changes.sumByDouble { it.first } / changes.size
        println("Average: $avg")
        val bestChange = changes.maxByOrNull { it.first }!!
        val bestDifference = equipmentState.diff(bestChange.second)
        pp("Best: ${bestChange.first}" to bestDifference.map { (from, to) ->
            renderDifference(from, to)
        })
    }

    suspend fun renderDifference(from: Simc.Lang.Item?, to: Simc.Lang.Item?): String = buildString {
        from?.let {
            append("- ${gearDropSimulatorHelper.pprItem(it)}")
        }
        to?.let {
            append(" + ${gearDropSimulatorHelper.pprItem(it)}")
        }
    }

    suspend fun oneWeek(): Simc.EquipmentState {
        val cs = CharacterState(equipmentState.copy())
        val ws = WeeklyState()
        val activities = listOf(
            // I'm lazy so I only run mist.
            PlayerActivity.MythicPlus(10, ShadowlandsInstance.Mist),
            PlayerActivity.MythicPlus(8, ShadowlandsInstance.Mist),
            PlayerActivity.MythicPlus(8, ShadowlandsInstance.Mist),
            PlayerActivity.MythicPlus(8, ShadowlandsInstance.Mist),

            PlayerActivity.Raid(
                RaidDifficulty.Normal,
                ShadowlandsInstance.CastleNathria.bosses,
                ShadowlandsInstance.CastleNathria
            ),
            PlayerActivity.Raid(
                RaidDifficulty.Heroic,
                listOf(
                    Boss.SHRIEK,
                    Boss.HUNTER,
                    Boss.DESTO,
                    Boss.XYMOX,
                    Boss.KAEL,
                ), ShadowlandsInstance.CastleNathria
            ),
        )
        // Run each activity, and randomly get gear.
        // Equip these gears greedily (might need to put offhand upgrades to bag)
        for (activity in activities) {
            runActivity(activity, cs, ws)
        }

        // At the end, calculate the great vault rewards. Then greedily choose the best upgrade.
        val greatVaultOptions = ws.finalizeThisWeek(cs).map(::materializeGreatVault)
        val baseScore = gearDropSimulatorHelper.score(cs.equipmentState)
        val scoredChoices = greatVaultOptions.map { (dropId, ilevel) ->
            gearDropSimulatorHelper.scoreAnyDrop(dropId, ilevel, cs.equipmentState, baseScore)
        }
        // Greedily choose the best among those that makes sense.
        scoredChoices.filter { it.scoreIncr > 0 }.maxByOrNull { it.scoreIncr }?.let {
            cs.equipmentState.equip(it.langItem)
        }
        return cs.equipmentState
    }

    private fun materializeGreatVault(option: GreatVaultOption): Pair<String, Int> {
        val rand = randomSupplier.get()
        when (option) {
            is GreatVaultOption.Raid -> {
                val baseIlevel = slDrops.translateRaidIlevel(option.difficulty)
                val site = slDrops.fromInstance(option.source)
                val bossesToChoose = if (option.includingEndBoss) {
                    site.bosses
                } else {
                    // XXX Hardcoded
                    site.bosses.take(8)
                }
                // Assuming that we first choose boss, and then choose item from boss. This keeps
                // the drop rate consistent (as if we are completing the whole raid).
                val bossToChoose = bossesToChoose.random(rand)
                val ilevel = site.ilevelMod(bossToChoose)
                val itemId = bossToChoose.itemIds.random(rand)
                return itemId to ilevel
            }
            is GreatVaultOption.MythicPlus -> {
                val ilevel = slDrops.translateKeystoneLevel(option.keystoneLevel).weeklyChestIlevel
                val site = slDrops.dungeons.random(rand)
                // Assuming that we first choose dungeon, and then choose item from the whole drop pool. This keeps
                // the drop rate consistent (as if we are running every dungeon).
                val itemId = site.bosses.flatMap { it.itemIds }.random(rand)
                return itemId to ilevel
            }
        }
    }

    private suspend fun runActivity(activity: PlayerActivity, cs: CharacterState, ws: WeeklyState) {
        when (activity) {
            is PlayerActivity.Raid -> {
                val site = slDrops.fromInstance(activity.instance)
                val ilevel = slDrops.translateRaidIlevel(activity.difficulty)

                class SingleBossSource(boss: Boss) : GearDropSource by site {
                    override val bosses = listOf(slDrops.fromBoss(boss))
                }
                // Try to get gear upgrades from each boss.
                for (boss in activity.bosses) {
                    tryGetUpgrade(SingleBossSource(boss), ilevel, 0.15, cs)
                    ws.raidBossesKilled.compute(activity.difficulty) { _, v ->
                        (v ?: mutableSetOf()).also {
                            it += boss
                        }
                    }
                }
            }

            is PlayerActivity.MythicPlus -> {
                val site = slDrops.fromInstance(activity.instance)
                val ilevel = slDrops.translateKeystoneLevel(activity.keystoneLevel).endOfDungeonIlevel
                tryGetUpgrade(site, ilevel, 0.4, cs)
                ws.mythicPlusCompleted += activity.keystoneLevel
            }
        }
    }

    private suspend fun tryGetUpgrade(
        site: GearDropSource,
        ilevel: Int,
        dropChance: Double,
        cs: CharacterState,
    ) {
        val rand = randomSupplier.get()
        val gearDropSim = gearDropSimulatorFactory.create(site, cs.equipmentState, ilevel)
        val report = gearDropSim.run()

        if (rand.nextDouble() <= dropChance) {
            val randomDrop = report.sortedEffects.random(rand)

            // Greedily take it (equip it if it's an upgrade). XXX: We might need a better way to
            // lookahead on offhand upgrades...
            if (randomDrop.scoreIncr > 0) {
                cs.equipmentState.equip(randomDrop.langItem)
            }
        }
    }
}

class CharacterState(val equipmentState: Simc.EquipmentState) {
    val defeatedLastBoss = mutableSetOf<RaidDifficulty>()
}

class WeeklyState {
    // Keystone levels
    val mythicPlusCompleted = mutableListOf<Int>()

    // Per difficulty
    val raidBossesKilled = mutableMapOf<RaidDifficulty, MutableSet<Boss>>()

    fun finalizeThisWeek(characterState: CharacterState): List<GreatVaultOption> {
        // 1. Update defeatedLastBoss.
        for ((diff, bosses) in raidBossesKilled) {
            if (bosses.contains(Boss.DENATH)) {
                characterState.defeatedLastBoss.add(diff)
            }
        }

        // 2. Sort content completed and generate great vault options
        // 2.1 M+
        val keystones = mythicPlusCompleted.sortedDescending()
        val mplusOptions = listOf(1, 4, 10).mapNotNull {
            keystones.getOrNull(it - 1)
        }.map(GreatVaultOption::MythicPlus)

        // 2.2 Raid
        val bossDifficulties = raidBossesKilled.map { it.key }.sortedDescending()
        val raidOptions = listOf(3, 7, 10).mapNotNull {
            bossDifficulties.getOrNull(it - 1)
        }.map {
            GreatVaultOption.Raid(
                ShadowlandsInstance.CastleNathria,
                it,
                characterState.defeatedLastBoss.contains(it)
            )
        }
        return mplusOptions + raidOptions
    }
}
