package com.gh.om.gamemacros.scratch

import kotlin.random.Random

// Q: To get 3T1 prefix, should I do 2p + 2p, or should I do 2p + 1p?
// Each recomb try is a state transition function (Item, Item, rng) -> (Item, rng)
// where an Item is a List Affix.
// For brevity we assume there are only 3 prefixes.
// We want to record the number of tries, and the distribution of affixes needed.
// We also want to keep track of the stash.
// We can assume infinite input items, but we'll greedily try to balance the
// consumption of all 3 affixes.

private const val DEBUG = false

data class Report(
    val rounds: Int,
    val inputsConsumed: List<Item>,
    val divineCount: Int,
)

data class Stash(
    val items: List<Item> = emptyList(),
)

class StashRef {
    var stash = Stash()
}

class RecombSim(
    private val rng: Random,
    private val stashRef: StashRef? = null
) {
    private var stash = stashRef?.stash ?: Stash()
    private val inputsConsumed = mutableListOf<Item>()
    private var rounds = 0
    private var divineCost = 0

    fun genReportAndWriteBack(): Report {
        stashRef?.stash = stash
        return Report(
            rounds = rounds,
            inputsConsumed = inputsConsumed,
            divineCount = divineCost
        )
    }

    fun advanceOneRound() {
        rounds += 1
    }

    fun takeFromStash(what: (Item) -> Boolean): Item? {
        val item = stash.items.firstOrNull(what) ?: return null
        stash = stash.copy(items = stash.items - item)
        return item
    }

    fun putIntoStash(item: Item) {
        stash = stash.copy(items = stash.items + item)
    }

    fun containsItemWithAffix(
        isPrefix: Boolean,
        what: (Set<Affix>) -> Boolean
    ): Boolean {
        val found = takeFromStash {
            what(it.affixesAt(isPrefix))
        }
        return if (found != null) {
            putIntoStash(found)
            true
        } else {
            false
        }
    }

    fun grab3p2s() =
        takeFromStash { it.prefixes.size == 3 && it.suffixes.size >= 2 }

    fun grab3p() = takeFromStash { it.prefixes.size == 3 }
    fun grab2p() = takeFromStash { it.prefixes.size == 2 }
    fun grab1a(
        affix: Affix? = null,
        isPrefix: Boolean = true
    ): Item? {
        return takeFromStash {
            val lookup = if (isPrefix) {
                it.prefixes
            } else {
                it.suffixes
            }
            val affixMatches = affix == null || affix in lookup
            lookup.size == 1 && affixMatches
        }
    }

    /**
     * @param suchThat1 The single-item filter that's applied first
     * @param suchThat2 The double-item filter that's applied to each pair
     * that satisfies [suchThat1]
     */
    fun grab2x(
        suchThat1: (Item) -> Boolean = { true },
        suchThat2: (Item, Item) -> Boolean
    ): Pair<Item, Item>? {
        val filtered1 = stash.items.filter(suchThat1)

        val found = filtered1.asSequence().flatMapIndexed { i1, item1 ->
            filtered1.asSequence().mapIndexedNotNull { i2, item2 ->
                if (i1 < i2 && suchThat2(item1, item2)) {
                    item1 to item2
                } else {
                    null
                }
            }
        }.firstOrNull()
        if (found != null) {
            takeFromStash { it == found.first }
            takeFromStash { it == found.second }
        }
        return found
    }

    fun grab2x2p(suchThat: (Item, Item) -> Boolean): Pair<Item, Item>? {
        fun is2p(item: Item) = item.prefixes.size == 2
        return grab2x(::is2p, suchThat)
    }

    fun grabOrConjure1a(
        affix: Affix? = null,
        isPrefix: Boolean = true
    ): Item {
        grab1a(affix = affix, isPrefix = isPrefix)?.let { return it }
        // TODO: greedily balance the consumption
        val affixes = setOf(affix ?: Affix.Natural.N1)
        val item = Item(
            prefixes = if (isPrefix) {
                affixes
            } else {
                emptySet()
            },
            suffixes = if (isPrefix) {
                emptySet()
            } else {
                affixes
            },
        )
        inputsConsumed += item
        return item
    }

    fun recombAndPutBack(
        lhs: Item,
        rhs: Item
    ) {
        val output = recomb(lhs, rhs, rng)
        if (DEBUG) {
            println("Recomb $lhs + $rhs -> $output")
        }
        putIntoStash(output)
    }

    fun craftExclusive(item0: Item): Item {
        if (totalExclusiveCount(item0) >= 3) {
            return item0
        }

        var item = item0
        // Ensure canHave3 exists (but avoid recrafting it)
        if (Affix.Exclusive.CanHave3 !in item.suffixes) {
            if (totalExclusiveCount(item) > 0) {
                // Need to remove all crafted mods first
                item = removeCraftedMods(item)
            }
            item =
                item.copy(suffixes = item.suffixes + Affix.Exclusive.CanHave3)
            divineCost += 2
        }
        // Ensure exclusive affixes, prioritizing prefix
        while (totalExclusiveCount(item) < 3) {
            val cmod = requireNotNull(nextAvailableCraftedMod(item))
            if (item.prefixes.size < 3) {
                item = item.copy(prefixes = item.prefixes + cmod)
                continue
            }
            if (item.suffixes.size < 3) {
                item = item.copy(suffixes = item.suffixes + cmod)
                continue
            }
            break
        }
        return item
    }
}

data class Item(
    val prefixes: Set<Affix> = emptySet(),
    val suffixes: Set<Affix> = emptySet(),
) {
    init {
        // Sanity checks
        require(prefixes.size <= 3)
        require(suffixes.size <= 3)

        totalExclusiveCount(this) <= 3
        require(Affix.Exclusive.CanHave3 !in prefixes)
    }
}

// Abstract affixes
sealed interface Affix {
    // Desired natural affixes
    enum class Natural : Affix {
        N1,
        N2,
        N3,
    }

    // For example: metamod, veiled mod
    enum class Exclusive : Affix {
        CanHave3,
        E2,
        E3,
    }
}

// From https://www.reddit.com/r/pathofexile/comments/1exyavx
private val RECOMB_CHANCES = mapOf<Int, List<Number>>(
    1 to listOf(0.41, 0.59, 0, 0),
    2 to listOf(0, 0.67, 0.33, 0),
    3 to listOf(0, 0.39, 0.52, 0.1),
    4 to listOf(0, 0.11, 0.59, 0.31),
    5 to listOf(0, 0, 0.43, 0.57),
    6 to listOf(0, 0, 0.28, 0.72),
)

fun main() {
    val rng = Random(1024)
    val roundss = mutableListOf<Int>()
    val consumeds = mutableListOf<Int>()
    val N_REP = if (DEBUG) 1 else 10000
    repeat(N_REP) {
        val report = run3p2s(rng)
        roundss += report.rounds
        consumeds += report.inputsConsumed.size
    }
    val avgRounds = roundss.sum().toDouble() / N_REP
    val avgConsumed = consumeds.sum().toDouble() / N_REP
    println("Average rounds: $avgRounds, items: $avgConsumed")
    println("Min/max rounds: ${roundss.min()}/${roundss.max()}, min/max items: ${consumeds.min()}/${consumeds.max()}")
}

fun run21(rng: Random): Report {
    val sim = RecombSim(rng)

    while (true) {
        // If we have a 3, we are done
        val threeA = sim.grab3p()
        if (threeA != null) {
            return sim.genReportAndWriteBack()
        }

        sim.advanceOneRound()

        // If we have a 2, recomb with 1
        val twoA = sim.grab2p()
        if (twoA != null) {
            val oneA = sim.grabOrConjure1a(missingAffixOf(twoA.prefixes))
            sim.recombAndPutBack(twoA, oneA)
            continue
        }

        CommonRecombRoutines.recombInto2a(sim)
    }
}

fun run22(
    rng: Random,
    sr: StashRef? = null
): Report {
    val sim = RecombSim(rng, sr)

    while (true) {
        // If we have a 3, we are done
        val threeA = sim.grab3p()
        if (threeA != null) {
            return sim.genReportAndWriteBack()
        }

        sim.advanceOneRound()

        // If we have 2 2a: recomb
        val two2a = sim.grab2x2p { item1, item2 ->
            item1.prefixes.intersect(item2.prefixes).size == 1
        }
        if (two2a != null) {
            sim.recombAndPutBack(two2a.first, two2a.second)
            continue
        }

        // If we have one 2a, recomb 2x1 on the missing side
        val twoA = sim.grab2p()
        if (twoA != null) {
            sim.putIntoStash(twoA)
            sim.recombAndPutBack(
                sim.grabOrConjure1a(missingAffixOf(twoA.prefixes)),
                sim.grabOrConjure1a(twoA.prefixes.first())
            )
            continue
        }

        // Otherwise, recomb any 1 + 1
        val lhs = sim.grabOrConjure1a()
        val rhs = sim.grabOrConjure1a(missingAffixOf(lhs.prefixes))
        sim.recombAndPutBack(lhs, rhs)
    }
}

fun run3p2s(
    rng: Random,
    sr: StashRef? = null,
    fuel: Int = 1000
): Report {
    val sim = RecombSim(rng, sr)

    var fuelUsed = 0
    while (true) {
        if (fuelUsed > fuel) {
            error("Didn't get a result after $fuel rounds")
        }
        fuelUsed += 1

        // If we have a 5, we are done
        val final = sim.grab3p2s()
        if (final != null) {
            return sim.genReportAndWriteBack()
        }

        sim.advanceOneRound()

        // If we have 2 items that compliment each other into 3p2s
        // add exclusive mods and recombine them
        val c3p2s = sim.grab2x { item1, item2 ->
            has3p2s(unionOrganicItemAffixes(item1, item2))
        }

        if (c3p2s != null) {
            val (c1, c2) = c3p2s
            val c1e = sim.craftExclusive(c1)
            val c2e = sim.craftExclusive(c2)
            sim.recombAndPutBack(c1e, c2e)
            continue
        }

        // If we don't: make 3p and 2s items (which are known to compliment each other)

        // If we have 2 2p: recomb into 3p
        fun is2p(item: Item): Boolean {
            return item.prefixes.count {
                it is Affix.Natural
            } == 2
        }

        val two2p = sim.grab2x(::is2p) { item1, item2 ->
            item1.prefixes.intersect(item2.prefixes).size == 1
        }
        if (two2p != null) {
            sim.recombAndPutBack(two2p.first, two2p.second)
            continue
        }

        // If we have one 2p, recomb 2x1 on the missing side
        val twoA = sim.grab2p()
        if (twoA != null) {
            sim.putIntoStash(twoA)
            sim.recombAndPutBack(
                sim.grabOrConjure1a(missingAffixOf(twoA.prefixes)),
                sim.grabOrConjure1a(twoA.prefixes.first())
            )
            continue
        }

        var didRecomb1and1 = false
        for (isPrefix in listOf(false, true)) {
            fun has2(affixes: Set<Affix>) = affixes.count {
                it is Affix.Natural
            } == 2
            // 2 suffixes are fixed so don't proceed if that already exists
            if (!isPrefix && sim.containsItemWithAffix(isPrefix, ::has2)) {
                continue
            }

            // Otherwise, recomb any 1 + 1, prioritizing ones without 2a
            val lhs = sim.grabOrConjure1a(isPrefix = isPrefix)
            val rhs = sim.grabOrConjure1a(
                affix = missingAffixOf(lhs.affixesAt(isPrefix)),
                isPrefix = isPrefix
            )
            sim.recombAndPutBack(lhs, rhs)
            didRecomb1and1 = true
            break
        }

        require(didRecomb1and1)
    }
}

private fun missingAffixOf(affixes: Set<Affix>): Affix {
    return (Affix.Natural.entries.toSet() - affixes).first()
}

private fun recombOneSide(
    lhs: Set<Affix>,
    rhs: Set<Affix>,
    canHaveExclusive: Boolean,
    rng: Random
): Set<Affix> {
    val inputCount = lhs.size + rhs.size
    if (inputCount == 0) {
        return emptySet()
    }
    val chances = requireNotNull(RECOMB_CHANCES[inputCount])

    val outputCount = sampleByChance(chances, rng.nextDouble())
    val outputAffixes = chooseOutputsFromRecomb(
        affixes = lhs.toList() + rhs,
        count = outputCount,
        rng = rng,
        canHaveExclusive = canHaveExclusive
    )
    return outputAffixes
}

fun recomb(
    lhs: Item,
    rhs: Item,
    rng: Random
): Item {
    // Decide to start from prefix or suffix
    return if (rng.nextBoolean()) {
        val ps = recombOneSide(lhs.prefixes, rhs.prefixes, true, rng)
        val ss = recombOneSide(
            lhs.suffixes,
            rhs.suffixes,
            ps.all { it !is Affix.Exclusive },
            rng
        )
        Item(ps, ss)
    } else {
        val ss = recombOneSide(lhs.suffixes, rhs.suffixes, true, rng)
        val ps = recombOneSide(
            lhs.prefixes,
            rhs.prefixes,
            ss.all { it !is Affix.Exclusive },
            rng
        )
        Item(ps, ss)
    }
}

// Returns the index of the chance
private fun sampleByChance(
    chances: List<Number>,
    choice: Double
): Int {
    var s = 0.0
    for ((i, chance) in chances.withIndex()) {
        s += chance.toDouble()
        if (choice < s) {
            return i
        }
    }
    return chances.size - 1
}

private fun chooseOutputsFromRecomb(
    affixes: List<Affix>,
    count: Int,
    rng: Random,
    canHaveExclusive: Boolean
): Set<Affix> {
    val input = affixes.toMutableSet()
    val output = mutableSetOf<Affix>()
    while (output.size < count && input.isNotEmpty()) {
        val choice = input.random(rng)
        input.remove(choice)
        if (!canHaveExclusive && choice is Affix.Exclusive) {
            continue
        }
        output += choice
    }
    return output
}

private fun unionOrganicItemAffixes(
    i1: Item,
    i2: Item
): Item {
    fun naturalOnly(xs: Set<Affix>) = xs.filterTo(mutableSetOf()) {
        it is Affix.Natural
    }
    return Item(
        naturalOnly(i1.prefixes + i2.prefixes),
        naturalOnly(i1.suffixes + i2.suffixes)
    )
}

private fun has3p2s(x: Item): Boolean {
    return x.prefixes.count { it is Affix.Natural } == 3
            && x.suffixes.count { it is Affix.Natural } >= 2
}

private fun is2pOr2s(item: Item): Boolean {
    return item.prefixes.count { it is Affix.Natural } == 2
            || item.suffixes.count { it is Affix.Natural } == 2
}

private fun Item.affixesAt(isPrefix: Boolean): Set<Affix> {
    return if (isPrefix) {
        prefixes
    } else {
        suffixes
    }
}

private fun totalExclusiveCount(x: Item): Int {
    return x.prefixes.count { it is Affix.Exclusive } +
            x.suffixes.count { it is Affix.Exclusive }
}

private fun removeCraftedMods(x: Item): Item {
    return x.filter {
        it is Affix.Natural
    }
}

private fun nextAvailableCraftedMod(x: Item): Affix.Exclusive? {
    val es = (x.prefixes + x.suffixes).filterIsInstance<Affix.Exclusive>()
    return (Affix.Exclusive.entries - es).firstOrNull()
}

private fun Item.filter(by: (Affix) -> Boolean): Item {
    return Item(
        prefixes.filterTo(mutableSetOf(), by),
        suffixes.filterTo(mutableSetOf(), by)
    )
}

object CommonRecombRoutines {
    fun recombInto2a(
        sim: RecombSim,
        isPrefix: Boolean = true
    ) {
        // If we have a 1, recomb with 1
        val lhs = sim.grabOrConjure1a(isPrefix = isPrefix)
        val lookup = if (isPrefix) {
            lhs.prefixes
        } else {
            lhs.suffixes
        }
        val rhs =
            sim.grabOrConjure1a(missingAffixOf(lookup), isPrefix = isPrefix)
        sim.recombAndPutBack(lhs, rhs)
    }
}
