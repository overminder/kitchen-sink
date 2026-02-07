# Map Rolling Macro

## Purpose

In Path of Exile's endgame, players run maps — randomized dungeon instances whose modifiers are determined by currency-crafted affixes. These modifiers simultaneously control **loot rewards** (item quantity, pack size, scarab/currency drop bonuses) and **difficulty** (extra monster damage, life, dangerous mechanics).

Manually rolling a batch of maps is tedious: hover each map, read its mods, decide if the combination is good enough, and if not, apply currency to reroll and repeat. This macro automates that entire loop for a batch of maps in the player's inventory.

## Trigger

Activated by a leader-key chord (similar to vim's leader key). The player presses a leader key combination, then a command sequence, within a short grace period. The macro only runs while Path of Exile is the active foreground window and the global trigger key is enabled.

Releasing the trigger key (or switching windows) stops the macro at any point.

## High-Level Flow

```
TRIGGER
  │
  ▼
SETUP
  • Scan the inventory grid for occupied slots (using pixel color detection).
  • Check available currency supply (by reading stack counts from the currency stash tab).
  • Build the list of maps to process.
  │
  ▼
LOOP (for each map in the batch)
  │
  ├─► READ MAP
  │     Move the mouse to the map's inventory slot and copy the item's
  │     advanced description to the clipboard (Ctrl+Alt+C). Parse the
  │     clipboard text into a structured item representation: rarity,
  │     item class, explicit mods, and quality bonuses.
  │     │
  │     ▼
  │   EVALUATE
  │     Three checks must ALL pass for the map to be accepted:
  │     │
  │     │  1. Reward score ≥ threshold
  │     │     A weighted sum of the map's bonus stats (scarab%, currency%,
  │     │     pack size%, quantity%, map drop%, etc.), scaled by the atlas
  │     │     passive multiplier. Different scoring profiles weight these
  │     │     stats differently depending on the farming strategy.
  │     │
  │     │  2. Difficulty ≤ maximum
  │     │     Each mod's impact on player damage taken and monster effective
  │     │     HP is estimated and multiplied together. The combined difficulty
  │     │     must stay within a configured ceiling.
  │     │
  │     │  3. No blacklisted mods
  │     │     Certain mods are unconditionally rejected regardless of score —
  │     │     typically mods that cause lag, require constant manual attention,
  │     │     or create unavoidable ground hazards. Some blacklist entries are
  │     │     conditional (e.g., volatile cores are only blacklisted when
  │     │     combined with reduced max resistances).
  │     │
  │     ▼
  │   GOOD ──► Accept the map, remove it from the work list, move to next map.
  │     │
  │   BAD ───► REROLL
  │              Apply currency to randomize the map's mods. The currency
  │              strategy depends on map tier and current rarity:
  │
  │              • Higher-tier maps: use Chaos Orbs (rerolls a rare item).
  │              • Lower-tier maps: use Scour + Alchemy (strips mods, then
  │                rerolls as rare). Normal-rarity maps skip the scour step.
  │
  │              Currency is applied by right-clicking the orb in the stash,
  │              then left-clicking the map in the inventory.
  │              │
  │              └──► Loop back to READ MAP (re-inspect the same map slot).
  │
  ▼
REPORT
  Print a summary: number of maps rolled, total reroll attempts,
  average cost per map, and per-map scores with difficulty estimates.
```

## Stop Conditions

The loop exits when any of the following is true:

1. **All maps accepted** — every map in the batch passed evaluation.
2. **Currency exhausted** — the reroll provider has no more orbs (checked against both a configured fuel limit and the actual in-game stack count).
3. **Trigger released** — the player released the activation key or switched away from Path of Exile.

## Scoring Profiles

Different farming strategies call for different scoring weights. The macro supports multiple named profiles, each emphasizing different reward types:

| Profile | Primary focus | Use case |
|---------|--------------|----------|
| Scarab | Scarab drop bonuses, with secondary currency and pack size | T17 maps farmed for scarab drops |
| Map | Map drop bonuses and pack size | Sustaining the map pool (T16.5 influenced maps) |
| Invitation | Raw item quantity | Boss invitation items |

A **composite scorer** can select the best-fitting profile automatically based on map tier (e.g., T17 uses the scarab profile, T16.5 uses the map profile).

Scoring thresholds are reduced for harder-to-roll item types (e.g., originator-influenced maps get a discount multiplier on the threshold).

## Difficulty Model

Each map mod is tagged with its estimated impact on two axes:

- **Player damage taken** — how much more dangerous the map becomes (e.g., "monsters deal 100% extra fire damage" roughly doubles incoming physical-as-fire).
- **Monster effective HP** — how much harder monsters are to kill (e.g., "60% more monster life", curse effect reduction).

These multipliers are compounded across all mods on the map. The result is compared against a difficulty ceiling that varies by game progression stage (early / mid / late game).

## Reroll Strategies

The macro abstracts currency application behind a provider interface, allowing different strategies:

- **Chaos reroll** — uses Chaos Orbs directly (only works on rare items).
- **Scour + Alchemy** — strips the item to normal, then applies an Alchemy Orb. Works regardless of current rarity.
- **Tier-based hybrid** — selects between the above based on map tier (higher tiers use chaos, lower tiers use scour+alch).

Each provider tracks remaining supply and stops when currency runs out.
