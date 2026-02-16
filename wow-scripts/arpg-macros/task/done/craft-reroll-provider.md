# Craft Reroll Provider

Status: done
Dependencies: craft-methods.md

## Description

Implement a `RerollProvider` that uses `CraftMethods` + `CraftDecisionMaker` to reroll items via alt/aug/regal crafting. This replaces the old `CrafterAsRerollProvider` + `BaseRelocatableCrafter` + `CurrencyApplierMixin` stack.

The new implementation backs `PoeItemCrafter` with macro-core's `PoeInteractor.applyCurrencyTo()` using a currency slot map (`ScreenPoint` per currency type), eliminating the direct `MouseHooks` dependency.

## Acceptance Criteria

- [x] `CraftRerollProvider` implements `RerollProvider`
- [x] Constructor takes: fuel, `CraftDecisionMaker`, craft method, `PoeInteractor`, currency slot map, `Clock`
- [x] Internal `PoeItemCrafter` delegates each currency call to `PoeInteractor.applyCurrencyTo(slot, itemSlot)`
- [x] `getCurrentItem()` uses `PoeInteractor.getItemDescriptionAt()` + `PoeItemParser`
- [x] Fuel tracking (decrements on each `applyTo`)
- [x] Uses `ScreenPoint` throughout (no `java.awt.Point`)
- [x] Unit tests with `FakePlatform` verifying click sequences
- [x] Unit tests for fuel exhaustion
- [x] Tests pass

## Notes

Currency slot map example:
```kotlin
data class CurrencySlots(
    val transmute: ScreenPoint,
    val alt: ScreenPoint,
    val aug: ScreenPoint,
    val regal: ScreenPoint,
    val exalt: ScreenPoint,
    val scour: ScreenPoint,
    val annul: ScreenPoint,
    val chaos: ScreenPoint,
    val alch: ScreenPoint,
    val armourScrap: ScreenPoint,
    val whetstone: ScreenPoint,
)
```

The old `CurrencyApplierMixin` cached `currentItem` to avoid re-reading after applying currency. The new implementation should preserve this optimization.
