# Craft Methods

Status: done
Dependencies: craft-decision-maker.md

## Description

Migrate the `PoeItemCrafter` interface and `CraftMethods` object from `poecraft.kt` into `macro-core`. `CraftMethods` is the crafting state machine that decides which currency to apply based on item rarity and the decision maker's output.

Includes:
- `PoeItemCrafter` interface (suspend functions for each currency type + `getCurrentItem()`)
- `CraftMethods` object with methods: `altAugRegalExaltOnce`, `altOnce`, `scourAlchOnce`, `chaosOnce`
- The private `altAugRegalExaltOnceEx` implementation

## Acceptance Criteria

- [x] `PoeItemCrafter` interface in `macrocore` package
- [x] `CraftMethods` object in `macrocore` package
- [x] All four craft methods migrated (`altAugRegalExaltOnce`, `altOnce`, `scourAlchOnce`, `chaosOnce`)
- [x] Heist special base logic preserved (`Simplex Amulet` check)
- [x] Unit tests with mock `PoeItemCrafter` verifying currency sequences for each rarity
- [x] Unit tests verifying GoBack triggers annul on rare
- [x] Tests pass

## Notes

`CraftMethods` is pure logic — it only calls methods on the `PoeItemCrafter` interface and reads `CraftDecisionMaker.Decision`. No platform coupling.

The `altOnly` flag in `altAugRegalExaltOnceEx` prevents augmenting, useful for 1-prefix + 1-suffix recomb scenarios.
