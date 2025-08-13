package com.gh.om.gamemacros.scratch

import kotlin.random.Random

data class WeightedAffix(
    val name: String,
    val weight: Int
)

fun main() {
    // ALL: 48.55%
    // BLOCK_DEX_STR: 68.25%
    // BLOCK_INT_CURSE: 74.76%
    // BLOCK_ALL_ATTR: 83.72%
    runNumberOfTries(
        available = VeiledAffixes.BLOCK_ALL_ATTR
    )
}

fun runNumberOfTries(
    n: Int = 10000,
    available: Set<WeightedAffix> = VeiledAffixes.ALL,
    rng: Random = Random(1234)
) {
    val total: Int = (0 until n).sumOf {
        if (unveilDesired(
                available = available,
                desired = VeiledAffixes.DD,
                rng
            )
        ) {
            1
        } else {
            0
        }.toInt()
    }
    println("Rate: ${total.toDouble() / n}")
}

fun unveilDesired(
    available: Set<WeightedAffix>,
    desired: Set<WeightedAffix>,
    rng: Random
): Boolean {
    val mutAvailable = available.toMutableSet()
    val choices = buildSet {
        repeat(3) {
            val choice = drawOnce(mutAvailable, rng)
            mutAvailable -= choice
            add(choice)
        }
    }
    return choices.intersect(desired).isNotEmpty()
}

private fun drawOnce(
    pool: Set<WeightedAffix>,
    rng: Random
): WeightedAffix {
    val ordered = pool.toList()
    val totalWeight = pool.sumOf { it.weight }
    val choice = rng.nextInt(totalWeight)
    var weightUpToNow = 0
    for (affix in ordered) {
        weightUpToNow += affix.weight
        if (choice < weightUpToNow) {
            return affix
        }
    }
    // Should not be reachable?
    return ordered.last()
}

object VeiledAffixes {
    val dd = WeightedAffix("DD", 1000)
    val ddf = WeightedAffix("DD while Focused", 1000)
    val curse = WeightedAffix("Curse effect", 3000)
    val dexint = WeightedAffix("Dex Int", 600)
    val strdex = WeightedAffix("Str Dex", 600)
    val strint = WeightedAffix("Str Int", 600)
    val dex = WeightedAffix("Dex", 1000)
    val int = WeightedAffix("Int", 1000)
    val str = WeightedAffix("Str", 1000)
    val coldchaos = WeightedAffix("Cold Chaos Res", 600)
    val firechaos = WeightedAffix("Fire Chaos Res", 600)
    val lightningchaos = WeightedAffix("Lightning Chaos Res", 600)

    val ALL = setOf(
        dd,
        ddf,
        curse,
        dexint,
        strdex,
        strint,
        dex,
        int,
        str,
        coldchaos,
        firechaos,
        lightningchaos
    )

    val DD = setOf(dd, ddf)

    // TODO: better encoding of mutual exclusive groups
    val ALL_ATTR = setOf(dexint, strdex, strint, dex, int, str)
    val ALL_INT = setOf(dexint, strint, int)
    val ALL_DEX_STR = setOf(dexint, strdex, dex, str)

    val BLOCK_ALL_ATTR = ALL - ALL_ATTR
    val BLOCK_DEX_STR = ALL - ALL_DEX_STR
    val BLOCK_INT_CURSE = ALL - ALL_INT - curse
}
