# Refactor Remaining Macros to MacroDef Classes

Status: done
Dependencies: none (builds on existing PrintMousePosMacro pattern)

## Description

Refactor the remaining macro functions in `MacroDefinitions.kt` into `MacroDef`-implementing classes (like `PrintMousePosMacro`), wire them into `MacroDefsComponent`, and launch them from `MainV2.kt`.

## Pattern

The target pattern (established by `PrintMousePosMacro`):
- Class in `macro-core/.../recipe/` with `@Inject constructor`
- Implements `MacroDef` interface (`prepare()` → `Prepared { run() }`)
- Uses `ShouldContinueChecker` for window/stop-key gating
- Triggering (leader key detection + collect) lives in `MainV2.kt`
- Dependencies injected rather than pulled from `AppComponent`

## Macros to Refactor

### 1. MapRollingMacro (leader key "11")

**Dependencies:** `Screen`, `PoeInteractor`, `MultiRollLoop`, `ShouldContinueChecker`, `ConsoleOutput`, `CurrencySlots`

- `prepare()`: get `shouldContinue` from checker
- `run()`: find occupied bag slots, create `ChaosOrAlchMapRerollProvider`, call `multiRollLoop.rollItems()`
- `MapScorerItemChecker` / `MapScorerCheckResult` move to `macro-core` recipe package (currently in `MacroDefinitions.kt`)

### 2. CraftRollingMacro (leader key "15")

**Dependencies:** `Screen`, `PoeInteractor`, `MultiRollLoop`, `ShouldContinueChecker`, `ConsoleOutput`, `CurrencySlots`, `Clock`, `CraftDecisionMaker`

- `prepare()`: get `shouldContinue` from checker
- `run()`: find occupied bag slots (10-column variant), create `CraftRerollProvider`, call `multiRollLoop.rollItems()`
- `CraftDecisionMaker` (the preset) needs to come from somewhere. Options:
  - Inject it (requires a `@Provides` in macro-app for the specific preset)
  - Hardcode in the class (less flexible but simpler)

### 3. SortInStashMacro (leader key "14")

**Dependencies:** `Screen`, `PoeInteractor`, `ShouldContinueChecker`, `ConsoleOutput`

- `prepare()`: get `shouldContinue` from checker
- `run()`: find occupied stash slots, score items, sort, move via bag round-trip
- `doSortInStash` helper becomes a private method

### 4. TownHotkeyMacro (NO leader key — different trigger pattern)

This macro doesn't fit the `MacroDef` pattern since it listens to raw key releases, not leader key chords. Options:
- **(A)** Keep as a standalone class with `suspend fun run()`, launched separately in `MainV2.kt`
- **(B)** Make `MacroDef` more generic (but this would over-complicate the interface for one case)

**Recommendation:** Option A. `TownHotkeyMacro` becomes a class with `@Inject` for shared deps (`KeyboardInput`, `KeyboardOutput`, `ActiveWindowChecker`) but takes window title + hotkey map as constructor params. Two instances created manually in `MainV2.kt` and launched as separate coroutines.

## Wiring Changes

### `CurrencySlots` injection
- Add `@Provides fun currencySlots(): CurrencySlots = CURRENCY_TAB_SLOTS` in `MacroModule`
- `CURRENCY_TAB_SLOTS` val stays in `MacroDefinitions.kt` (or moves to macro-app config)

### `CraftDecisionMaker` injection
- Add `@Provides fun craftDecisionMaker(): CraftDecisionMaker = CraftPresets.intStackCluster4` in `MacroModule`

### `MacroDefsComponent` update
- Add all new `MacroDef` classes as fields

### `MainV2.kt` update
- Add all leader-key macros to `macroAndKeys` list
- Launch `TownHotkeyMacro` instances separately
- Remove commented-out old code block

### `MacroDefinitions.kt` cleanup
- Remove migrated functions (`mapRollingMacro`, `craftRollingMacro`, `printMousePosMacro`, `sortInStashMacro`, `townHotkeyMacro`, `doSortInStash`)
- `MacroConfigImpl` stays (or moves)
- `CURRENCY_TAB_SLOTS` stays
- `MapScorerItemChecker` / `MapScorerCheckResult` move to macro-core

## New Files

1. `macro-core/.../recipe/MapRollingMacro.kt`
2. `macro-core/.../recipe/CraftRollingMacro.kt`
3. `macro-core/.../recipe/SortInStashMacro.kt`
4. `macro-core/.../recipe/TownHotkeyMacro.kt`
5. `macro-core/.../recipe/MapScorerItemChecker.kt` (moved from MacroDefinitions)

## Acceptance Criteria

- [ ] `MapRollingMacro` implements `MacroDef`, triggered by leader key "11"
- [ ] `CraftRollingMacro` implements `MacroDef`, triggered by leader key "15"
- [ ] `SortInStashMacro` implements `MacroDef`, triggered by leader key "14"
- [ ] `TownHotkeyMacro` class handles POE1 and POE2 hotkeys, launched separately
- [ ] All macros wired in `MainV2.kt`
- [ ] Old macro functions removed from `MacroDefinitions.kt`
- [ ] `MacroDefsComponent` includes all `MacroDef` classes
- [ ] `./gradlew build` succeeds
