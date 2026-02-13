package com.gh.om.ks.arpgmacro.core.map

import com.gh.om.ks.arpgmacro.core.item.PoeRollableItem
import com.gh.om.ks.arpgmacro.core.item.isMapLike

data class PoeMapDifficulty(
    val playerDamageTaken: Double,
    val monsterEhp: Double,
) {
    fun fmt(): String {
        return "(${playerDamageTaken.fmt()}p, ${monsterEhp.fmt()}m)"
    }

    fun strictlyLessOrEqualTo(other: PoeMapDifficulty): Boolean {
        return playerDamageTaken <= other.playerDamageTaken && monsterEhp <= other.monsterEhp
    }

    operator fun times(other: Double) =
        PoeMapDifficulty(playerDamageTaken * other, monsterEhp * other)

    companion object {
        val earlyGame = PoeMapDifficulty(2.2, 3.0)
        val midGame = PoeMapDifficulty(4.0, 6.0)
        val lateGame = PoeMapDifficulty(20.0, 20.0)
    }
}

fun Number?.fmt(): String = if (this == null) {
    "null"
} else {
    String.format("%.2f", this)
}

data class MapModDescriptor(
    val keywords: List<String>,
    val variableIndex: Int? = null,
    val variableRange: IntRange? = null,
    val morePlayerDamageTakenMultiForVariable: Double? = null,
    val morePlayerDamageTakenMulti: Double? = null,
    val moreMonsterHpMultiForVariable: Double? = null,
    val moreMonsterHpMulti: Double? = null,
)

private val rangePat = """\([0-9]+-[0-9]+\)""".toRegex()
private val variablePat = """(-?[0-9]+)""".toRegex()

fun getVariableForMod(mod: PoeRollableItem.ExplicitMod, variableIndex: Int): Int? {
    val descWithoutRange = mod.description.replace(rangePat, "")
    return variablePat
        .findAll(descWithoutRange)
        .elementAtOrNull(variableIndex)
        ?.value
        ?.toInt()
}

fun findMatchingDescriptor(mod: PoeRollableItem.ExplicitMod): MapModDescriptor {
    val matches = PoeMapMods.ALL.filter {
        it.keywords.all { kw -> mod.description.contains(kw, ignoreCase = true) }
    }
    if (matches.isEmpty()) {
        error("Didn't find `${mod.description}`")
    }
    if (matches.size > 1) {
        if (matches.any(overlappingT17Mods::contains)) {
            // Known case with overlapping descriptions between T16/T17
        } else {
            error("Found multiple descriptors for `${mod.description}`: $matches")
        }
    }
    return matches.first()
}

private val overlappingT17Mods = setOf(
    T16Mods.punishing,
    T16Mods.unwavering,
    T17Mods.ofVenom,
    T17Mods.ofCurses,
    T17Mods.magnifying,
    T17Mods.ofPower,
    T17Mods.ofFrenzy,
    T17Mods.ofEndurance,
    T17Mods.protected,
)

fun getMapDifficulty(map: PoeRollableItem, atlasMulti: Double = 1.56): PoeMapDifficulty {
    require(map.klass.isMapLike())
    var playerDamageTaken = 1.0
    var monsterHp = 1.0
    val descriptors = map.explicitMods.map(::findMatchingDescriptor)

    for ((mod, d) in map.explicitMods.zip(descriptors)) {
        if (d.variableIndex != null) {
            val variable = getVariableForMod(mod, d.variableIndex)
            if (variable == null) {
                error("Didn't find variable[${d.variableIndex}] in `${mod.description}`")
            }
            d.moreMonsterHpMultiForVariable?.let { hpMulti ->
                monsterHp *= (1 + hpMulti * variable * atlasMulti / 100)
            }
            d.morePlayerDamageTakenMultiForVariable?.let { damageTakenMulti ->
                playerDamageTaken *= (1 + damageTakenMulti * variable * atlasMulti / 100)
            }
        }
        d.moreMonsterHpMulti?.let {
            monsterHp *= 1 + it / 100
        }
        d.morePlayerDamageTakenMulti?.let {
            playerDamageTaken *= 1 + it / 100
        }
    }
    return PoeMapDifficulty(playerDamageTaken = playerDamageTaken, monsterEhp = monsterHp)
}

// -- T16 Mod Definitions --

object T16Mods {
    val fecund = MapModDescriptor(
        keywords = listOf("% more Monster Life"),
        variableIndex = 0,
        variableRange = IntRange(40, 100),
        moreMonsterHpMultiForVariable = 1.0,
    )
    val savage = MapModDescriptor(
        keywords = listOf("% increased Monster Damage"),
        variableIndex = 0,
        variableRange = IntRange(22, 40),
        morePlayerDamageTakenMultiForVariable = 1.0,
    )
    val chaining = MapModDescriptor(
        keywords = listOf("Monsters' skills Chain ", " additional times"),
        variableIndex = 0,
        variableRange = IntRange(2, 3),
    )
    val splitting = MapModDescriptor(
        keywords = listOf("Monsters fire ", " additional Projectiles"),
        variableIndex = 0,
        variableRange = IntRange(2, 2),
        morePlayerDamageTakenMultiForVariable = 5.0,
    )
    val ofGiants = MapModDescriptor(
        keywords = listOf("Monsters have ", "% increased Area of Effect"),
        variableIndex = 0,
        variableRange = IntRange(100, 100),
        morePlayerDamageTakenMultiForVariable = 0.05,
    )
    val ofDeadliness = MapModDescriptor(
        keywords = listOf(
            "Monsters have ", "% increased Critical Strike Chance",
            "% to Monster Critical Strike Multiplier",
        ),
        variableIndex = 1,
        variableRange = IntRange(41, 75),
        morePlayerDamageTakenMultiForVariable = 0.76,
    )
    val punishing = MapModDescriptor(
        keywords = listOf("Monsters reflect ", "% of Physical Damage"),
        variableIndex = 0,
        variableRange = IntRange(18, 20),
    )
    val mirrored = MapModDescriptor(
        keywords = listOf("Monsters reflect ", "% of Elemental Damage"),
        variableIndex = 0,
        variableRange = IntRange(18, 18),
    )
    val armoured = MapModDescriptor(
        keywords = listOf("% Monster Physical Damage Reduction"),
        variableIndex = 0,
        variableRange = IntRange(40, 40),
    )
    val resistant = MapModDescriptor(
        keywords = listOf(
            "% Monster Chaos Resistance",
            "% Monster Elemental Resistances",
        ),
        variableIndex = 1,
        variableRange = IntRange(40, 40),
    )
    val oppressive = MapModDescriptor(
        keywords = listOf("Monsters have +", "% chance to Suppress Spell Damage"),
        variableIndex = 0,
        variableRange = IntRange(60, 100),
    )
    val insulation = MapModDescriptor(
        keywords = listOf("Monsters have ", "% chance to Avoid Elemental Ailments"),
        variableIndex = 0,
        variableRange = IntRange(70, 70),
    )
    val impervious = MapModDescriptor(
        keywords = listOf(
            "Monsters have a ",
            "% chance to avoid Poison, Impale, and Bleeding",
        ),
        variableIndex = 0,
        variableRange = IntRange(50, 50),
    )
    val impaling = MapModDescriptor(
        keywords = listOf("Monsters' Attacks have ", "% chance to Impale on Hit"),
        variableIndex = 0,
        variableRange = IntRange(60, 60),
        morePlayerDamageTakenMultiForVariable = 0.1,
    )
    val empowered = MapModDescriptor(
        keywords = listOf("Monsters have a ", "% chance to Ignite, Freeze and Shock on Hit"),
        variableIndex = 0,
        variableRange = IntRange(20, 20),
        morePlayerDamageTakenMultiForVariable = 0.5,
    )
    val burning = MapModDescriptor(
        keywords = listOf("Monsters deal ", "% extra Physical Damage as Fire"),
        variableIndex = 0,
        variableRange = IntRange(90, 110),
        morePlayerDamageTakenMultiForVariable = 1.0,
    )
    val freezing = MapModDescriptor(
        keywords = listOf("Monsters deal ", "% extra Physical Damage as Cold"),
        variableIndex = 0,
        variableRange = IntRange(90, 110),
        morePlayerDamageTakenMultiForVariable = 1.0,
    )
    val shocking = MapModDescriptor(
        keywords = listOf("Monsters deal ", "% extra Physical Damage as Lightning"),
        variableIndex = 0,
        variableRange = IntRange(90, 110),
        morePlayerDamageTakenMultiForVariable = 1.0,
    )
    val profane = MapModDescriptor(
        keywords = listOf("Monsters gain ", "% of their Physical Damage as Extra Chaos Damage"),
        variableIndex = 0,
        variableRange = IntRange(31, 100),
    )
    val buffered = MapModDescriptor(
        keywords = listOf("Monsters gain ", "% of Maximum Life as Extra Maximum Energy Shield"),
        variableIndex = 0,
        variableRange = IntRange(40, 80),
    )
    val overlords = MapModDescriptor(
        keywords = listOf(
            "Unique Boss deals ", "% increased Damage",
            "Unique Boss has ", "% increased Attack and Cast Speed",
        ),
        variableIndex = 0,
        variableRange = IntRange(25, 25),
        morePlayerDamageTakenMultiForVariable = 1.0,
    )
    val titans = MapModDescriptor(
        keywords = listOf(
            "Unique Boss has ", "% increased Life",
            "Unique Boss has ", "% increased Area of Effect",
        ),
        variableIndex = 0,
        variableRange = IntRange(35, 35),
        moreMonsterHpMultiForVariable = 1.0,
    )
    val smothering = MapModDescriptor(
        keywords = listOf("Players have ", "% less Recovery Rate of Life and Energy Shield"),
        variableIndex = 0,
        variableRange = IntRange(60, 60),
        morePlayerDamageTakenMultiForVariable = 1.0,
    )
    val drought = MapModDescriptor(
        keywords = listOf("Players gain ", "% reduced Flask Charges"),
        variableIndex = 0,
        variableRange = IntRange(50, 50),
    )
    val ofStasis = MapModDescriptor(
        keywords = listOf("Players cannot Regenerate Life, Mana or Energy Shield"),
        morePlayerDamageTakenMulti = 100.0,
    )
    val ofBalance = MapModDescriptor(
        keywords = listOf("Players cannot inflict Exposure"),
    )
    val ofExposure = MapModDescriptor(
        keywords = listOf("Players have ", "% to all maximum Resistances"),
        variableIndex = 0,
        variableRange = IntRange(-20, -9),
        morePlayerDamageTakenMultiForVariable = -10.0,
    )
    val ofFatigue = MapModDescriptor(
        keywords = listOf("Players have ", "% less Cooldown Recovery Rate"),
        variableIndex = 0,
        variableRange = IntRange(40, 40),
        moreMonsterHpMultiForVariable = 1.2,
    )
    val ofTransience = MapModDescriptor(
        keywords = listOf("Buffs on Players expire ", "% faster"),
        variableIndex = 0,
        variableRange = IntRange(70, 100),
    )
    val ofDoubt = MapModDescriptor(
        keywords = listOf("Players have ", "% reduced effect of Non-Curse Auras from Skills"),
        variableIndex = 0,
        variableRange = IntRange(60, 60),
    )
    val ofImprecision = MapModDescriptor(
        keywords = listOf("Players have ", "% less Accuracy Rating"),
        variableIndex = 0,
        variableRange = IntRange(25, 25),
        morePlayerDamageTakenMultiForVariable = 0.2,
    )
    val ofImpotence = MapModDescriptor(
        keywords = listOf("Players have ", "% less Area of Effect"),
        variableIndex = 0,
        variableRange = IntRange(25, 30),
        moreMonsterHpMultiForVariable = 0.2,
    )
    val ofMiring = MapModDescriptor(
        keywords = listOf(
            "Monsters have ", "% increased Accuracy Rating",
            "Players have ", "% to amount of Suppressed Spell Damage Prevented",
        ),
        variableIndex = 1,
        variableRange = IntRange(-20, -20),
        morePlayerDamageTakenMultiForVariable = -1.0,
    )
    val rust = MapModDescriptor(
        keywords = listOf(
            "Players have ", "% less Armour",
            "Players have ", "% reduced Chance to Block",
        ),
        variableIndex = 1,
        variableRange = IntRange(40, 40),
        morePlayerDamageTakenMultiForVariable = 1.5,
    )
    val ofFrenzy = MapModDescriptor(
        keywords = listOf("Monsters gain a Frenzy Charge on Hit"),
    )
    val ofEndurance = MapModDescriptor(
        keywords = listOf("Monsters gain an Endurance Charge on Hit"),
    )
    val ofPower = MapModDescriptor(
        keywords = listOf("Monsters gain a Power Charge on Hit"),
    )
    val ofElementalWeakness = MapModDescriptor(
        keywords = listOf("Players are Cursed with Elemental Weakness"),
    )
    val ofVulnerability = MapModDescriptor(
        keywords = listOf("Players are Cursed with Vulnerability"),
    )
    val ofEnfeeblement = MapModDescriptor(
        keywords = listOf("Players are Cursed with Enfeeble"),
    )
    val ofTemporalChains = MapModDescriptor(
        keywords = listOf("Players are Cursed with Temporal Chains"),
    )
    val ofFlames = MapModDescriptor(
        keywords = listOf("Area has patches of Burning Ground"),
    )
    val ofIce = MapModDescriptor(
        keywords = listOf("Area has patches of Chilled Ground"),
    )
    val ofLightning = MapModDescriptor(
        keywords = listOf("Area has patches of Shocked Ground"),
    )
    val ofDesecration = MapModDescriptor(
        keywords = listOf("Area has patches of Desecrated Ground"),
    )
    val ofConsecration = MapModDescriptor(
        keywords = listOf("Area has patches of Consecrated Ground"),
    )
    val hexproof = MapModDescriptor(
        keywords = listOf("Monsters are Hexproof"),
    )
    val hexwarded = MapModDescriptor(
        keywords = listOf("% less effect of Curses on Monsters"),
        variableIndex = 0,
        variableRange = IntRange(60, 60),
        moreMonsterHpMultiForVariable = 0.1,
    )
    val conflagrating = MapModDescriptor(
        keywords = listOf("All Monster Damage from Hits always Ignites"),
        morePlayerDamageTakenMulti = 10.0,
    )
    val unstoppable = MapModDescriptor(
        keywords = listOf(
            "Monsters cannot be Taunted",
            "Monsters' Action Speed cannot be modified to below Base Value",
            "Monsters' Movement Speed cannot be modified to below Base Value",
        ),
    )
    val ofCongealment = MapModDescriptor(
        keywords = listOf("Monsters cannot be Leeched from"),
        morePlayerDamageTakenMulti = 100.0,
    )
    val ofBlinding = MapModDescriptor(
        keywords = listOf("Monsters Blind on Hit"),
    )
    val ofCarnage = MapModDescriptor(
        keywords = listOf("Monsters Maim on Hit with Attacks"),
    )
    val ofImpedance = MapModDescriptor(
        keywords = listOf("Monsters Hinder on Hit with Spells"),
    )
    val ofEnervation = MapModDescriptor(
        keywords = listOf("Monsters steal Power, Frenzy and Endurance charges on Hit"),
        morePlayerDamageTakenMulti = 13.6,
        moreMonsterHpMulti = 74.0,
    )
    val ofVenom = MapModDescriptor(
        keywords = listOf("Monsters Poison on Hit"),
    )
    val fleet = MapModDescriptor(
        keywords = listOf(
            "% increased Monster Movement Speed",
            "% increased Monster Attack Speed",
            "% increased Monster Cast Speed",
        ),
        variableIndex = 1,
        variableRange = IntRange(35, 45),
        morePlayerDamageTakenMultiForVariable = 0.2,
    )
    val abhorrent = MapModDescriptor(
        keywords = listOf("Area is inhabited by Abominations"),
    )
    val ceremonial = MapModDescriptor(
        keywords = listOf("Area contains many Totems"),
    )
    val skeletal = MapModDescriptor(
        keywords = listOf("Area is inhabited by Skeletons"),
    )
    val ofBloodlines = MapModDescriptor(
        keywords = listOf("% increased Magic Monsters"),
        variableIndex = 0,
        variableRange = IntRange(20, 30),
    )
    val capricious = MapModDescriptor(
        keywords = listOf("Area is inhabited by Goatmen"),
    )
    val slithering = MapModDescriptor(
        keywords = listOf("Area is inhabited by Sea Witches and their Spawn"),
    )
    val undead = MapModDescriptor(
        keywords = listOf("Area is inhabited by Undead"),
    )
    val emanant = MapModDescriptor(
        keywords = listOf("Area is inhabited by ranged monsters"),
    )
    val feral = MapModDescriptor(
        keywords = listOf("Area is inhabited by Animals"),
    )
    val demonic = MapModDescriptor(
        keywords = listOf("Area is inhabited by Demons"),
    )
    val bipedal = MapModDescriptor(
        keywords = listOf("Area is inhabited by Humanoids"),
    )
    val solar = MapModDescriptor(
        keywords = listOf("Area is inhabited by Solaris fanatics"),
    )
    val lunar = MapModDescriptor(
        keywords = listOf("Area is inhabited by Lunaris fanatics"),
    )
    val haunting = MapModDescriptor(
        keywords = listOf("Area is inhabited by Ghosts"),
    )
    val feasting = MapModDescriptor(
        keywords = listOf("Area is inhabited by Cultists of Kitava"),
    )
    val multifarious = MapModDescriptor(
        keywords = listOf("Area has increased monster variety"),
    )
    val twinned = MapModDescriptor(
        keywords = listOf("Area contains two Unique Bosses"),
    )
    val unwavering = MapModDescriptor(
        keywords = listOf("% more Monster Life", "Monsters cannot be Stunned"),
        variableIndex = 0,
        variableRange = IntRange(25, 30),
        moreMonsterHpMultiForVariable = 1.0,
    )

    val ALL = listOf(
        fecund, savage, chaining, splitting, ofGiants, ofDeadliness,
        punishing, mirrored, armoured, resistant, oppressive, insulation,
        impervious, impaling, empowered, burning, freezing, shocking,
        profane, buffered, overlords, titans, smothering, drought,
        ofStasis, ofBalance, ofExposure, ofFatigue, ofTransience, ofDoubt,
        ofImprecision, ofImpotence, ofMiring, rust, ofFrenzy, ofEndurance,
        ofPower, ofElementalWeakness, ofVulnerability, ofEnfeeblement,
        ofTemporalChains, ofFlames, ofIce, ofLightning, ofDesecration,
        ofConsecration, hexproof, hexwarded, conflagrating, unstoppable,
        ofCongealment, ofBlinding, ofCarnage, ofImpedance, ofEnervation,
        ofVenom, fleet, ofBloodlines, ceremonial, skeletal, capricious,
        slithering, undead, emanant, feral, demonic, bipedal, solar,
        lunar, haunting, feasting, multifarious, abhorrent, twinned,
        unwavering,
    )
}

// -- T17 Mod Definitions --

object T17Mods {
    val ofPower = MapModDescriptor(
        keywords = listOf(
            "Monsters have +", " to Maximum Power Charges",
            "Monsters gain a Power Charge on Hit",
        ),
        variableIndex = 0,
        variableRange = IntRange(1, 1),
        morePlayerDamageTakenMultiForVariable = 10.0,
    )
    val ofFrenzy = MapModDescriptor(
        keywords = listOf(
            "Monsters have +", " to Maximum Frenzy Charges",
            "Monsters gain a Frenzy Charge on Hit",
        ),
        variableIndex = 0,
        variableRange = IntRange(1, 1),
        morePlayerDamageTakenMultiForVariable = 10.0,
    )
    val ofEndurance = MapModDescriptor(
        keywords = listOf(
            "Monsters have +", " to Maximum Endurance Charges",
            "Monsters gain an Endurance Charge when hit",
        ),
        variableIndex = 0,
        variableRange = IntRange(1, 1),
    )
    val volatile = MapModDescriptor(
        keywords = listOf("Rare Monsters have Volatile Cores"),
        morePlayerDamageTakenMulti = 100.0,
    )
    val enthralled = MapModDescriptor(
        keywords = listOf("Unique Bosses are Possessed"),
    )
    val grasping = MapModDescriptor(
        keywords = listOf("Monsters inflict ", " Grasping Vines on Hit"),
        variableIndex = 0,
        variableRange = IntRange(2, 2),
    )
    val ofPetrification = MapModDescriptor(
        keywords = listOf("Area contains Petrification Statues"),
    )
    val ofToughness = MapModDescriptor(
        keywords = listOf("Monsters take ", "% reduced Extra Damage from Critical Strikes"),
        variableIndex = 0,
        variableRange = IntRange(35, 45),
    )
    val cycling = MapModDescriptor(
        keywords = listOf(
            "Players and their Minions deal no damage for ",
            " out of every ",
            " seconds",
        ),
        variableIndex = 0,
        variableRange = IntRange(3, 3),
    )
    val magnifying = MapModDescriptor(
        keywords = listOf(
            "Monsters have ",
            "% increased Area of Effect",
            "Monsters fire ",
            " additional Projectiles",
        ),
        variableIndex = 0,
        variableRange = IntRange(100, 100),
        morePlayerDamageTakenMultiForVariable = 0.3,
    )
    val ofVenom = MapModDescriptor(
        keywords = listOf(
            "Monsters Poison on Hit",
            "All Damage from Monsters' Hits can Poison",
            "Monsters have ", "% increased Poison Duration",
        ),
        variableIndex = 0,
        variableRange = IntRange(100, 100),
    )
    val stalwart = MapModDescriptor(
        keywords = listOf("Monsters have +", "% Chance to Block Attack Damage"),
        variableIndex = 0,
        variableRange = IntRange(50, 50),
    )
    val ofCongealment = MapModDescriptor(
        keywords = listOf("Players have ", "% reduced Maximum total Life, Mana and Energy Shield Recovery per second from Leech"),
        variableIndex = 0,
        variableRange = IntRange(50, 60),
        morePlayerDamageTakenMultiForVariable = 0.3,
    )
    val ofCurses = MapModDescriptor(
        keywords = listOf(
            "Players are Cursed with Vulnerability",
            "Players are Cursed with Temporal Chains",
            "Players are Cursed with Elemental Weakness",
        ),
    )
    val antagonists = MapModDescriptor(
        keywords = listOf(
            "% increased number of Rare Monsters",
            "Rare Monsters each have ", " additional Modifier",
        ),
        variableIndex = 0,
        variableRange = IntRange(35, 45),
    )
    val ofDomination = MapModDescriptor(
        keywords = listOf("Unique Monsters have a random Shrine Buff"),
    )
    val prismatic = MapModDescriptor(
        keywords = listOf("Monsters gain ", "% of their Physical Damage as Extra Damage of a random Element"),
        variableIndex = 0,
        variableRange = IntRange(180, 200),
        morePlayerDamageTakenMultiForVariable = 1.0,
    )
    val ultimate = MapModDescriptor(
        keywords = listOf("Players are assaulted by Bloodstained Sawblades"),
    )
    val ofTheJuggernaut = MapModDescriptor(
        keywords = listOf(
            "Monsters cannot be Stunned",
            "Monsters' Action Speed cannot be modified to below Base Value",
            "Monsters' Movement Speed cannot be modified to below Base Value",
        ),
    )
    val ofImbibing = MapModDescriptor(
        keywords = listOf("Players are targeted by a Meteor when they use a Flask"),
    )
    val ofMiring = MapModDescriptor(
        keywords = listOf("Players have ", "% less Defences"),
        variableIndex = 0,
        variableRange = IntRange(25, 30),
        morePlayerDamageTakenMultiForVariable = 2.0,
    )
    val hungering = MapModDescriptor(
        keywords = listOf("Area contains Drowning Orbs"),
    )
    val protected = MapModDescriptor(
        keywords = listOf(
            "% Monster Physical Damage Reduction",
            "% Monster Chaos Resistance",
            "% Monster Elemental Resistances",
        ),
        variableIndex = 0,
        variableRange = IntRange(50, 50),
    )
    val afflicting = MapModDescriptor(
        keywords = listOf(
            "All Monster Damage can Ignite, Freeze and Shock",
            "Monsters Ignite, Freeze and Shock on Hit",
        ),
        morePlayerDamageTakenMulti = 10.0,
    )
    val ofPenetration = MapModDescriptor(
        keywords = listOf("Monster Damage Penetrates ", "% Elemental Resistances"),
        variableIndex = 0,
        variableRange = IntRange(15, 15),
        morePlayerDamageTakenMultiForVariable = 10.0,
    )
    val ofDeceleration = MapModDescriptor(
        keywords = listOf("Players have ", "% reduced Action Speed for each time they've used a Skill Recently"),
        variableIndex = 0,
        variableRange = IntRange(3, 3),
    )
    val retributive = MapModDescriptor(
        keywords = listOf(
            "Players are Marked for Death for ",
            " seconds",
            "after killing a Rare or Unique monster",
        ),
        variableIndex = 0,
        variableRange = IntRange(10, 10),
        morePlayerDamageTakenMulti = 50.0,
    )
    val equalising = MapModDescriptor(
        keywords = listOf("Rare and Unique Monsters remove ", "% of Life, Mana and Energy Shield from Players or their Minions on Hit"),
        variableIndex = 0,
        variableRange = IntRange(5, 5),
        morePlayerDamageTakenMultiForVariable = 3.0,
    )
    val decaying = MapModDescriptor(
        keywords = listOf("Area contains Unstable Tentacle Fiends"),
    )
    val impaling = MapModDescriptor(
        keywords = listOf(
            "Monsters' Attacks Impale on Hit",
            "When a fifth Impale is inflicted on a Player",
        ),
        morePlayerDamageTakenMultiForVariable = 0.1,
    )
    val ofDesolation = MapModDescriptor(
        keywords = listOf("Area has patches of Awakeners' Desolation"),
    )
    val valdos = MapModDescriptor(
        keywords = listOf("Rare monsters in area are Shaper-Touched"),
        morePlayerDamageTakenMulti = 150.0,
    )
    val sabotaging = MapModDescriptor(
        keywords = listOf(
            "Player Skills which Throw Mines throw ", " fewer Mine",
            "Player Skills which Throw Traps throw ", " fewer Trap",
        ),
        variableIndex = 0,
        variableRange = IntRange(1, 1),
    )
    val ofRevolt = MapModDescriptor(
        keywords = listOf(
            "Players' Minions have ", "% less Attack Speed",
            "Players' Minions have ", "% less Cast Speed",
            "Players' Minions have ", "% less Movement Speed",
        ),
        variableIndex = 0,
        variableRange = IntRange(50, 50),
    )
    val parasitic = MapModDescriptor(
        keywords = listOf("% of Damage Players' Totems take from Hits is taken from their Summoner's Life instead"),
        variableIndex = 0,
        variableRange = IntRange(15, 15),
    )
    val synthetic = MapModDescriptor(
        keywords = listOf("Map Boss is accompanied by a Synthesis Boss"),
    )
    val ofDefiance = MapModDescriptor(
        keywords = listOf("Debuffs on Monsters expire ", "% faster"),
        variableIndex = 0,
        variableRange = IntRange(100, 100),
    )
    val searing = MapModDescriptor(
        keywords = listOf("Area contains Runes of the Searing Exarch"),
    )
    val ofCollection = MapModDescriptor(
        keywords = listOf("The Maven interferes with Players"),
    )
    val ofSplinters = MapModDescriptor(
        keywords = listOf("% chance for Rare Monsters to Fracture on death"),
        variableIndex = 0,
        variableRange = IntRange(25, 25),
    )

    val ALL = listOf(
        ofPower, ofFrenzy, ofEndurance, cycling, magnifying, ofVenom,
        stalwart, ofCongealment, volatile, enthralled, grasping,
        ofPetrification, ofToughness, antagonists, ofDomination,
        prismatic, ultimate, ofTheJuggernaut, ofImbibing, ofMiring,
        hungering, protected, afflicting, ofPenetration, ofDeceleration,
        retributive, equalising, decaying, impaling, ofDesolation,
        valdos, sabotaging, ofRevolt, parasitic, synthetic, ofDefiance,
        searing, ofCollection, ofCurses, ofSplinters,
    )
}

object PoeMapMods {
    val ALL = T17Mods.ALL + T16Mods.ALL

    val alwaysAnnoying = listOf(
        T17Mods.cycling,
        T17Mods.decaying,
        T17Mods.hungering,
        T17Mods.searing,
    )

    val otherBadMods = listOf<MapModDescriptor>()

    val allBadMods = alwaysAnnoying + otherBadMods

    fun getBadMods(item: PoeRollableItem): List<PoeRollableItem.ExplicitMod> {
        val descriptors = item.explicitMods.map {
            findMatchingDescriptor(it)
        }

        val badDescrs = descriptors.filterTo(mutableListOf()) {
            it in allBadMods
        }

        // Special case: volatile + exposure is very dangerous
        if (T17Mods.volatile in descriptors && T16Mods.ofExposure in descriptors) {
            val exposureMod = item.explicitMods.first {
                findMatchingDescriptor(it) == T16Mods.ofExposure
            }
            val variable = getVariableForMod(exposureMod, T16Mods.ofExposure.variableIndex!!) ?: 0
            if (variable <= -20) {
                badDescrs += T17Mods.volatile
                badDescrs += T16Mods.ofExposure
            }
        }
        return item.explicitMods.filter {
            findMatchingDescriptor(it) in badDescrs
        }
    }
}
