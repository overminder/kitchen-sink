package com.gh.om.gamemacros.complex

fun main() {
    val input = """

Item Class: Maps
Rarity: Rare
Ancient Trap
Fortress Map
--------
Map Tier: 17
Item Quantity: +110% (augmented)
Item Rarity: +54% (augmented)
Monster Pack Size: +40% (augmented)
More Scarabs: +78% (augmented)
More Currency: +140% (augmented)
Quality: +20% (augmented)
--------
Item Level: 84
--------
Monster Level: 84
--------
Delirium Reward Type: Weapons (enchant)
Players in Area are 20% Delirious (enchant)
--------
{ Prefix Modifier "Volatile" (Tier: 1) }
Rare Monsters have Volatile Cores

{ Prefix Modifier "Stalwart" (Tier: 1) }
Monsters have +50% Chance to Block Attack Damage

{ Prefix Modifier "Retributive" (Tier: 1) }
Players are Marked for Death for 10 seconds
after killing a Rare or Unique monster
(Players that are Marked for Death take 50% increased Damage)

{ Suffix Modifier "of Exposure" (Tier: 1) }
Players have -20% to all maximum Resistances

{ Suffix Modifier "of Temporal Chains" — Caster, Curse }
Players are Cursed with Temporal Chains
(Temporal Chains is a Hex which reduces Action Speed by 15%, or 9% on Rare or Unique targets, and makes other effects on the target expire 40% slower. It has 50% less effect on Players and lasts 5 seconds)

{ Suffix Modifier "of Splinters" (Tier: 1) }
25% chance for Rare Monsters to Fracture on death

--------
Travel to this Map by using it in a personal Map Device. Maps can only be used once.
--------
Modifiable only with Chaos Orbs, Vaal Orbs, Delirium Orbs and Chisels



        """

    val parsedMap = PoeItemParser.parseAsRollable(input)
    println(parsedMap)
    val scorer = PoeMapScorerImpl.SCARAB
    val scorerOutput = scorer.evaluate(parsedMap)
    println("$scorerOutput")
}
