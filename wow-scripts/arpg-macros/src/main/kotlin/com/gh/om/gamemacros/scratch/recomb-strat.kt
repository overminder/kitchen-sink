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
)

data class Stash(
    val items: List<Item> = emptyList(),
)

class StashRef {
    var stash = Stash()
}

class RecombSim(private val rng: Random, private val stashRef: StashRef? = null) {
    private var stash = stashRef?.stash ?: Stash()
    private val inputsConsumed = mutableListOf<Item>()
    private var rounds = 0

    fun genReportAndWriteBack(): Report {
        stashRef?.stash = stash
        return Report(rounds, inputsConsumed)
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

    fun grab3p() = takeFromStash { it.prefixes.size == 3 }
    fun grab2p() = takeFromStash { it.prefixes.size == 2 }
    fun grab1p(affix: Affix? = null): Item? {
        return takeFromStash {
            val affixMatches = affix == null || affix in it.prefixes
            it.prefixes.size == 1 && affixMatches
        }
    }

    fun grab2x2p(suchThat: (Item, Item) -> Boolean): Pair<Item, Item>? {
        val all2A = stash.items.filter { it.prefixes.size == 2 }
        val found = all2A.asSequence().flatMapIndexed { i1, item1 ->
            all2A.asSequence().mapIndexedNotNull { i2, item2 ->
                if (i1 < i2 && suchThat(item1, item2)) {
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

    fun grab2Items() {

    }

    fun grabOrConjure1a(affix: Affix? = null): Item {
        grab1p(affix)?.let { return it }
        // TODO: greedily balance the consumption
        val item = Item(setOf(affix ?: Affix.Natural.N1))
        inputsConsumed += item
        return item
    }

    fun recombAndPutBack(lhs: Item, rhs: Item) {
        val output = recomb(lhs, rhs, rng)
        if (DEBUG) {
            println("Recomb $lhs + $rhs -> $output")
        }
        putIntoStash(output)
    }
}

data class Item(
    val prefixes: Set<Affix> = emptySet(),
    val suffixes: Set<Affix> = emptySet(),
)

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
        E1,
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
        val report = run22(rng)
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

        // If we have a 1, recomb with 1
        val lhs = sim.grabOrConjure1a()
        val rhs = sim.grabOrConjure1a(missingAffixOf(lhs.prefixes))
        sim.recombAndPutBack(lhs, rhs)
    }
}

fun run22(rng: Random, sr: StashRef? = null): Report {
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

private fun missingAffixOf(affixes: Set<Affix>): Affix {
    return (Affix.Natural.entries.toSet() - affixes).first()
}

private fun recombOneSide(lhs: Set<Affix>, rhs: Set<Affix>, canHaveExclusive: Boolean, rng: Random): Set<Affix> {
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

fun recomb(lhs: Item, rhs: Item, rng: Random): Item {
    // Decide to start from prefix or suffix
    return if (rng.nextBoolean()) {
        val ps = recombOneSide(lhs.prefixes, rhs.prefixes, true, rng)
        val ss = recombOneSide(lhs.suffixes, rhs.suffixes, ps.all { it !is Affix.Exclusive }, rng)
        Item(ps, ss)
    } else {
        val ss = recombOneSide(lhs.suffixes, rhs.suffixes, true, rng)
        val ps = recombOneSide(lhs.prefixes, rhs.prefixes, ss.all { it !is Affix.Exclusive }, rng)
        Item(ps, ss)
    }
}

// Returns the index of the chance
private fun sampleByChance(chances: List<Number>, choice: Double): Int {
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
