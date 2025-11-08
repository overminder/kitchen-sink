import com.gh.om.gamemacros.complex.PoeRollableItem
import com.gh.om.gamemacros.complex.isMapLike

data class MapDifficulty(
    val playerDamageTaken: Double,
    val monsterEhp: Double,
) {
    fun strictlyLessOrEqualTo(other: MapDifficulty): Boolean {
        return playerDamageTaken <= other.playerDamageTaken && monsterEhp <= other.monsterEhp
    }
}

fun getMapDifficulty(map: PoeRollableItem, atlasMulti: Double = 1.56): MapDifficulty {
    require(map.klass.isMapLike())
    var playerDamageTaken = 1.0
    var monsterHp = 1.0
    for (mod in map.explicitMods) {
        val d = findMatchingDescriptor(mod)
        if (d.variableIndex != null) {
            val variable = variablePat
                .findAll(mod.description)
                .elementAtOrNull(d.variableIndex)
                ?.value
                ?.toInt()
            if (variable == null) {
                error("Didn't find variable[${d.variableIndex}] in `${mod.description}`")
            }
            d.moreMonsterHpMultiPercentage?.let { hpMulti ->
                monsterHp *= (1 + hpMulti * variable * atlasMulti / 100)
            }
            d.morePlayerDamageTakenMultiPercentage?.let { damageTakenMulti ->
                playerDamageTaken *= (1 + damageTakenMulti * variable * atlasMulti / 100)
            }
        }
    }
    return MapDifficulty(playerDamageTaken = playerDamageTaken, monsterEhp = monsterHp)
}

private val variablePat = """(-?[0-9]+)""".toRegex()

private fun findMatchingDescriptor(mod: PoeRollableItem.ExplicitMod): MapModDescriptor {
    val matches = PoeMapMods.ALL.filter {
        it.keywords.all(mod.description::contains)
    }
    if (matches.isEmpty()) {
        error("Didn't find `${mod.description}`")
    }
    if (matches.size > 1) {
        if (matches.any(overlappingT17Mods::contains)) {
            // Known case to have multiple matches (because the mod descriptions do overlap)
        } else {
            error("Found multiple descriptors for `${mod.description}`: $matches")
        }
    }
    return matches.first()
}

/**
 * The list of mods that have overlapping descriptions between T16 and T17.
 * - Note: When there are overlapping mods, prefer to add the T17 version to this list.
// - Why: This is necessary to avoid throwing in findMatchingDescriptor.
 */
private val overlappingT17Mods = setOf(
    T16Mods.punishing,
    T16Mods.ofVenom,
    T17Mods.ofCurses,
    T17Mods.magnifying,
    // TODO: Complete this list by including mods from T16 or T17 that have overlapping descriptions.
    //  Example: According to the JSON data, t16 and t17 ofVenom both have the line "Monsters Poison on Hit".
    //  So the t17 ofVenom is added to this list.
)

data class MapModDescriptor(
    /**
     * Fixed part of the mod description, not including any variables.
     *
     * When the mod contains multiple variables, this can contain more than one keyword (because
     * the keywords are separated by variables)
     */
    val keywords: List<String>,
    /**
     * 0-based index of the most important numeric variable in the description.
     * - This is often 0, indicating that the variable is the first one in the description.
     * - When the description has multiple variables, this indicates which one to use.
     * - This should only be null when the mod has no variables.
     */
    val variableIndex: Int? = null,

    /**
     * The range of the variable on [variableIndex]. This is mostly for documentation's purpose.
     */
    val variableRange: IntRange? = null,

    /**
     * The effect of the mod on player damage taken. This is multiplied with the actual variable
     * to get the final result on the player. For instance, if the mod says "50% increased player damage taken",
     * then variable will be 50, and this multi should be 1.0. So 50 * 1% = 0.5, indicating that the player is taking
     * 50% more damage.
     *
     * This is null when it doesn't affect player damage taken.
     */
    val morePlayerDamageTakenMultiPercentage: Double? = null,
    /**
     * The effect of the mod on monster effective health (including resistance and energy shield, which are also
     * counted as effective health). This is multiplied with the actual variable
     * to get the final result on the player. For instance, if the mod says "100% increased monster life",
     * then variable will be 100, and this multi should be 1.0. So 100 * 1% = 1, indicating that monsters have
     * 100% more health.
     *
     * This is null when the mod doesn't affect monster health.
     */
    val moreMonsterHpMultiPercentage: Double? = null,
)

/**
 * Comes from poet16data.json.
 *
 * Note that the ranges of the mods are unioned against the same mods from poet17data.json.
 */
object T16Mods {
    // Monster life/damage
    val fecund = MapModDescriptor(
        keywords = listOf("% more Monster Life"),
        variableIndex = 0,
        variableRange = IntRange(40, 100),
        moreMonsterHpMultiPercentage = 1.0,
    )

    val savage = MapModDescriptor(
        keywords = listOf("% increased Monster Damage"),
        variableIndex = 0,
        variableRange = IntRange(22, 40),
        morePlayerDamageTakenMultiPercentage = 1.0,
    )

    // Projectile/AoE
    val chaining = MapModDescriptor(
        keywords = listOf("Monsters' skills Chain ", " additional times"),
        variableIndex = 0,
        variableRange = IntRange(2, 3),
    )

    val splitting = MapModDescriptor(
        keywords = listOf("Monsters fire ", " additional Projectiles"),
        variableIndex = 0,
        variableRange = IntRange(2, 2),
        morePlayerDamageTakenMultiPercentage = 5.0,
    )

    val ofGiants = MapModDescriptor(
        keywords = listOf("Monsters have ", "% increased Area of Effect"),
        variableIndex = 0,
        variableRange = IntRange(100, 100),
        morePlayerDamageTakenMultiPercentage = 0.05,
    )

    // Crit
    val ofDeadliness = MapModDescriptor(
        keywords = listOf(
            "Monsters have ", "% increased Critical Strike Chance",
            "% to Monster Critical Strike Multiplier",
        ),
        variableIndex = 1,
        variableRange = IntRange(41, 75),
        morePlayerDamageTakenMultiPercentage = 0.5,
    )

    // Reflect
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

    // Resistances/defences
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
        moreMonsterHpMultiPercentage = 0.2,
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

    // On-hit mechanics
    val impaling = MapModDescriptor(
        keywords = listOf("Monsters' Attacks have ", "% chance to Impale on Hit"),
        variableIndex = 0,
        variableRange = IntRange(60, 60),
        morePlayerDamageTakenMultiPercentage = 0.1,
    )

    val empowered = MapModDescriptor(
        keywords = listOf("Monsters have a ", "% chance to Ignite, Freeze and Shock on Hit"),
        variableIndex = 0,
        variableRange = IntRange(20, 20),
        morePlayerDamageTakenMultiPercentage = 0.3,
    )

    // Extra damage conversions
    val burning = MapModDescriptor(
        keywords = listOf("Monsters deal ", "% extra Physical Damage as Fire"),
        variableIndex = 0,
        variableRange = IntRange(90, 110),
        morePlayerDamageTakenMultiPercentage = 1.0,
    )

    val freezing = MapModDescriptor(
        keywords = listOf("Monsters deal ", "% extra Physical Damage as Cold"),
        variableIndex = 0,
        variableRange = IntRange(90, 110),
        morePlayerDamageTakenMultiPercentage = 1.0,
    )

    val shocking = MapModDescriptor(
        keywords = listOf("Monsters deal ", "% extra Physical Damage as Lightning"),
        variableIndex = 0,
        variableRange = IntRange(90, 110),
        morePlayerDamageTakenMultiPercentage = 1.0,
    )

    val profane = MapModDescriptor(
        keywords = listOf("Monsters gain ", "% of their Physical Damage as Extra Chaos Damage"),
        variableIndex = 0,
        variableRange = IntRange(31, 100),
    )

    // Monster ES buffer
    val buffered = MapModDescriptor(
        keywords = listOf("Monsters gain ", "% of Maximum Life as Extra Maximum Energy Shield"),
        variableIndex = 0,
        variableRange = IntRange(40, 80),
        moreMonsterHpMultiPercentage = 1.0,
    )

    // Boss modifiers
    val overlords = MapModDescriptor(
        keywords = listOf(
            "Unique Boss deals ", "% increased Damage",
            "Unique Boss has ", "% increased Attack and Cast Speed",
        ),
        variableIndex = 0,
        variableRange = IntRange(25, 25),
        morePlayerDamageTakenMultiPercentage = 1.0,
    )

    val titans = MapModDescriptor(
        keywords = listOf(
            "Unique Boss has ", "% increased Life",
            "Unique Boss has ", "% increased Area of Effect",
        ),
        variableIndex = 0,
        variableRange = IntRange(35, 35),
        moreMonsterHpMultiPercentage = 1.0,
    )

    // Player debuffs
    val smothering = MapModDescriptor(
        keywords = listOf("Players have ", "% less Recovery Rate of Life and Energy Shield"),
        variableIndex = 0,
        variableRange = IntRange(60, 60),
        morePlayerDamageTakenMultiPercentage = 0.3,
    )

    val drought = MapModDescriptor(
        keywords = listOf("Players gain ", "% reduced Flask Charges"),
        variableIndex = 0,
        variableRange = IntRange(50, 50),
    )

    val ofStasis = MapModDescriptor(
        keywords = listOf("Players cannot Regenerate Life, Mana or Energy Shield"),
    )

    val ofBalance = MapModDescriptor(
        keywords = listOf("Players cannot inflict Exposure"),
    )

    val ofExposure = MapModDescriptor(
        keywords = listOf("Players have ", "% to all maximum Resistances"),
        variableIndex = 0,
        variableRange = IntRange(-20, -9),
        // Since the value is negative
        morePlayerDamageTakenMultiPercentage = -2.5,
    )

    val ofFatigue = MapModDescriptor(
        keywords = listOf("Players have ", "% less Cooldown Recovery Rate"),
        variableIndex = 0,
        variableRange = IntRange(40, 40),
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
        // Hmm this one is harder to estimate
    )

    val ofImprecision = MapModDescriptor(
        keywords = listOf("Players have ", "% less Accuracy Rating"),
        variableIndex = 0,
        variableRange = IntRange(25, 25),
        morePlayerDamageTakenMultiPercentage = 0.2,
    )

    val ofImpotence = MapModDescriptor(
        keywords = listOf("Players have ", "% less Area of Effect"),
        variableIndex = 0,
        variableRange = IntRange(25, 30),
        moreMonsterHpMultiPercentage = 0.2,
    )

    val ofMiring = MapModDescriptor(
        keywords = listOf(
            "Monsters have ", "% increased Accuracy Rating",
            "Players have ", "% to amount of Suppressed Spell Damage Prevented",
        ),
        variableIndex = 1,
        variableRange = IntRange(-20, -20),
        morePlayerDamageTakenMultiPercentage = -1.0,
    )

    val rust = MapModDescriptor(
        keywords = listOf(
            "Players have ", "% less Armour",
            "Players have ", "% reduced Chance to Block",
        ),
        variableIndex = 1,
        variableRange = IntRange(40, 40),
        // Huge for block builds, not so for other.
        morePlayerDamageTakenMultiPercentage = 0.3,
    )

    // Charge mods (no numeric variables in description)
    val ofFrenzy = MapModDescriptor(
        keywords = listOf("Monsters gain a Frenzy Charge on Hit"),
    )

    val ofEndurance = MapModDescriptor(
        keywords = listOf("Monsters gain an Endurance Charge on Hit"),
    )

    val ofPower = MapModDescriptor(
        keywords = listOf("Monsters gain a Power Charge on Hit"),
    )

    // Curses (no numeric variable)
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

    // Ground effects
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

    

    // Misc no-variable mods
    val hexproof = MapModDescriptor(
        keywords = listOf("Monsters are Hexproof"),
    )

    val hexwarded = MapModDescriptor(
        keywords = listOf("% less effect of Curses on Monsters"),
        variableIndex = 0,
        variableRange = IntRange(60, 60),
        moreMonsterHpMultiPercentage = 0.1,
    )

    val conflagrating = MapModDescriptor(
        keywords = listOf("All Monster Damage from Hits always Ignites"),
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
    )

    val ofVenom = MapModDescriptor(
        keywords = listOf("Monsters Poison on Hit"),
    )

    // Movement/attack/cast speed
    val fleet = MapModDescriptor(
        keywords = listOf("% increased Monster Attack Speed"),
        variableIndex = 1,
        variableRange = IntRange(35, 45),
        morePlayerDamageTakenMultiPercentage = 0.2,
    )

    // No-var descriptive mods
    val abhorrent = MapModDescriptor(
        keywords = listOf("Area is inhabited by Abominations"),
    )

    // Area-inhabited and pack variety mods
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
        moreMonsterHpMultiPercentage = 1.0,
    )

    val ALL = listOf(
        fecund,
        savage,
        chaining,
        splitting,
        ofGiants,
        ofDeadliness,
        punishing,
        mirrored,
        armoured,
        resistant,
        oppressive,
        insulation,
        impervious,
        impaling,
        empowered,
        burning,
        freezing,
        shocking,
        profane,
        buffered,
        overlords,
        titans,
        smothering,
        drought,
        ofStasis,
        ofBalance,
        ofExposure,
        ofFatigue,
        ofTransience,
        ofDoubt,
        ofImprecision,
        ofImpotence,
        ofMiring,
        rust,
        ofFrenzy,
        ofEndurance,
        ofPower,
        ofElementalWeakness,
        ofVulnerability,
        ofEnfeeblement,
        ofTemporalChains,
        ofFlames,
        ofIce,
        ofLightning,
        ofDesecration,
        ofConsecration,
        hexproof,
        hexwarded,
        conflagrating,
        unstoppable,
        ofCongealment,
        ofBlinding,
        ofCarnage,
        ofImpedance,
        ofEnervation,
        ofVenom,
        fleet,
        ofBloodlines,
        ceremonial,
        skeletal,
        capricious,
        slithering,
        undead,
        emanant,
        feral,
        demonic,
        bipedal,
        solar,
        lunar,
        haunting,
        feasting,
        multifarious,
        abhorrent,
        twinned,
        unwavering,
    )
}

/**
 * Comes from poet17data.json, minus any mods that already exist in [T16Mods].
 */
object T17Mods {
    // TODO: Parse poet17data.json and add missing mods into this object.
    //  Note that some mod's name or str (description) were already subsumed by object T16Mods --
    //  these don't need to be added. For example,
    //  - Volatile is missing and its str description doesn't exist in T16Mods. This needs to be added.
    //  - Fecund already exists in T16Mods, so it doesn't need to be added again in T17Mods.

    val ofPower = MapModDescriptor(
        keywords = listOf("Monsters have +", " to Maximum Power Charges"),
        variableIndex = 0,
        variableRange = IntRange(1, 1),
        morePlayerDamageTakenMultiPercentage = 10.0,
    )

    val ofFrenzy = MapModDescriptor(
        keywords = listOf("Monsters have +", " to Maximum Frenzy Charges"),
        variableIndex = 0,
        variableRange = IntRange(1, 1),
        morePlayerDamageTakenMultiPercentage = 10.0,
    )

    val ofEndurance = MapModDescriptor(
        keywords = listOf("Monsters have +", " to Maximum Endurance Charges"),
        variableIndex = 0,
        variableRange = IntRange(1, 1),
    )

    

    val volatile = MapModDescriptor(
        keywords = listOf("Rare Monsters have Volatile Cores"),
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
        morePlayerDamageTakenMultiPercentage = 0.1,
    )

    

    val ofVenom = MapModDescriptor(
        keywords = listOf("Monsters have ", "% increased Poison Duration"),
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
        morePlayerDamageTakenMultiPercentage = 0.3,
    )

    

    val ofCurses = MapModDescriptor(
        keywords = listOf(
            "Players are Cursed with Vulnerability",
            "Players are Cursed with Temporal Chains",
            "Players are Cursed with Elemental Weakness",
        ),
    )

    

    

    val antagonists = MapModDescriptor(
        keywords = listOf("% increased number of Rare Monsters"),
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
        morePlayerDamageTakenMultiPercentage = 1.0,
    )

    val ultimate = MapModDescriptor(
        keywords = listOf("Players are assaulted by Bloodstained Sawblades"),
    )

    val ofTheJuggernaut = MapModDescriptor(
        keywords = listOf("Monsters cannot be Stunned"),
    )

    val ofImbibing = MapModDescriptor(
        keywords = listOf("Players are targeted by a Meteor when they use a Flask"),
    )

    val ofMiring = MapModDescriptor(
        keywords = listOf("Players have ", "% less Defences"),
        variableIndex = 0,
        variableRange = IntRange(25, 30),
        morePlayerDamageTakenMultiPercentage = 0.3,
    )

    val hungering = MapModDescriptor(
        keywords = listOf("Area contains Drowning Orbs"),
    )

    val protectedResists = MapModDescriptor(
        keywords = listOf(
            "% Monster Physical Damage Reduction",
            "% Monster Chaos Resistance",
            "% Monster Elemental Resistances",
        ),
        variableIndex = 0,
        variableRange = IntRange(50, 50),
        moreMonsterHpMultiPercentage = 0.2,
    )

    val afflicting = MapModDescriptor(
        keywords = listOf("All Monster Damage can Ignite, Freeze and Shock"),
    )

    

    val ofPenetration = MapModDescriptor(
        keywords = listOf("Monster Damage Penetrates ", "% Elemental Resistances"),
        variableIndex = 0,
        variableRange = IntRange(15, 15),
        morePlayerDamageTakenMultiPercentage = 1.0,
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
    )

    val equalising = MapModDescriptor(
        keywords = listOf("Rare and Unique Monsters remove ", "% of Life, Mana and Energy Shield from Players or their Minions on Hit"),
        variableIndex = 0,
        variableRange = IntRange(5, 5),
    )

    val decaying = MapModDescriptor(
        keywords = listOf("Area contains Unstable Tentacle Fiends"),
    )

    val impaling = MapModDescriptor(
        keywords = listOf("Monsters' Attacks Impale on Hit"),
        morePlayerDamageTakenMultiPercentage = 0.1,
    )

    val ofDesolation = MapModDescriptor(
        keywords = listOf("Area has patches of Awakeners' Desolation"),
    )

    val valdos = MapModDescriptor(
        keywords = listOf("Rare monsters in area are Shaper-Touched"),
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
        keywords = listOf("Players' Minions have ", "% less Attack Speed"),
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
        ofPower,
        ofFrenzy,
        ofEndurance,
        cycling,
        magnifying,
        ofVenom,
        stalwart,
        ofCongealment,
        volatile,
        enthralled,
        grasping,
        ofPetrification,
        ofToughness,
        
        antagonists,
        ofDomination,
        prismatic,
        ultimate,
        ofTheJuggernaut,
        ofImbibing,
        ofMiring,
        hungering,
        protectedResists,
        afflicting,
        ofPenetration,
        ofDeceleration,
        retributive,
        equalising,
        decaying,
        impaling,
        ofDesolation,
        valdos,
        sabotaging,
        ofRevolt,
        parasitic,
        synthetic,
        ofDefiance,
        searing,
        ofCollection,
        ofCurses,
        ofSplinters,
    )
}

object PoeMapMods {
    val ALL = T17Mods.ALL + T16Mods.ALL

    val alwaysAnnoying = listOf(
        T17Mods.volatile,
        T17Mods.cycling,
        // Floor stuff
        T17Mods.decaying,
        T17Mods.ofDesolation,
        T17Mods.searing,
        T17Mods.hungering,
    )

    val otherBadMods = listOf(
        // Refl
        T16Mods.punishing,
        T16Mods.mirrored,

        // Regen
        T16Mods.smothering,
        T16Mods.ofStasis,
        T17Mods.ofCongealment,
    )

    val allBadMods = alwaysAnnoying + otherBadMods

    fun getBadMods(item: PoeRollableItem): List<PoeRollableItem.ExplicitMod> {
        return item.explicitMods.filter {
            val d = findMatchingDescriptor(it)
            d in allBadMods
        }
    }
}
