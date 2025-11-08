package com.gh.om.gamemacros.complex

fun main() {
    val input = """
Item Class: Maps
Rarity: Rare
Pain Cramp
Fortress Map
--------
Map Tier: 17
Item Quantity: +90% (augmented)
Item Rarity: +134% (augmented)
Monster Pack Size: +34% (augmented)
More Maps: +100% (augmented)
--------
Item Level: 85
--------
Monster Level: 84
--------
{ Prefix Modifier "Prismatic" (Tier: 1) }
Monsters gain 180(180-200)% of their Physical Damage as Extra Damage of a random Element

{ Prefix Modifier "Burning" — Damage, Physical, Elemental, Fire }
Monsters deal 99(90-110)% extra Physical Damage as Fire

{ Prefix Modifier "Magnifying" (Tier: 1) }
Monsters have 100% increased Area of Effect
Monsters fire 2 additional Projectiles

{ Suffix Modifier "of Power" (Tier: 1) }
Monsters have +1 to Maximum Power Charges
Monsters gain a Power Charge on Hit

{ Suffix Modifier "of Impotence" }
Players have 25% less Area of Effect

{ Suffix Modifier "of Endurance" (Tier: 1) }
Monsters have +1 to Maximum Endurance Charges
Monsters gain an Endurance Charge when hit

--------
Travel to this Map by using it in a personal Map Device. Maps can only be used once.
--------
Modifiable only with Chaos Orbs, Vaal Orbs, Delirium Orbs and Chisels


        """

    val parsedMap = PoeItemParser.parseAsRollable(input)
    println(parsedMap)
    val scorer = PoeMapScorerImpl.MAP
    val scorerOutput = scorer.evaluate(parsedMap)
    println("$scorerOutput")
}
