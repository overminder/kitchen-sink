# Macro App Cleanup

Status: done
Dependencies: macro-main.md

## Description

Address missing features and code issues found during review of the macro-app module.

## Issues

### 1. No cancellation support (`shouldContinue = { true }`)

**Files:** `MacroDefinitions.kt:95, :137`

Both macros pass `shouldContinue = { true }`, so once triggered they run until all items are rolled or currency runs out. There is no way to stop mid-roll.

The old code passes `isPoe::value` (a `StateFlow<Boolean>`) that combines:
- **Active window detection**: `isPoe()` checks if "Path of Exile" is the foreground window title via Win32 API. Alt-tabbing out stops macros.
- **F4 pause**: `isTriggerKeyEnabled()` listens for F4 presses and disables macros for 3 seconds.

This requires:
- A `WindowChecker` interface in macro-core (or macro-app) that can query the active window title
- A pause/disable-key mechanism (F4 with 3-second timeout)
- Combining both into a `StateFlow<Boolean>` and passing `::value` as `shouldContinue`

### 2. `generateReport` returns hardcoded `"Ok"`

**Files:** `MacroDefinitions.kt:50-52`

`MapScorerItemChecker.generateReport()` returns `"Ok"` instead of useful output. The old code returns average score and per-item details. A `generateMapReport()` function already exists in macro-core (`MapScorer.kt:191-198`) that does exactly this, but `MapScorerItemChecker` doesn't use it.

**Fix:** Change `MapScorerItemChecker.generateReport()` to delegate to `macrocore.generateMapReport()` by mapping `MapScorerCheckResult` back to `MapScorerOutput`.

This requires making `MapScorerCheckResult.output` non-private (or internal).

### 3. Unused `mouseOutput()` on AppComponent

**Files:** `AppComponent.kt:20`

`AppComponent.mouseOutput()` is declared but never called. `PoeInteractor` and `MultiRollLoop` receive `MouseOutput` via constructor injection. This is dead API surface.

**Fix:** Remove `mouseOutput()` from `AppComponent`.

### 4. Hardcoded craft mod names with no context

**Files:** `MacroDefinitions.kt:119-125`

The `desiredModNames` list and `desiredModCount` are inlined in `craftRollingMacro()` with no indication of what item/build they target. Extract into a dedicated class (e.g., `CraftPresets` or `CraftRecipes`) that holds named mod combinations with meaningful identifiers.

## Acceptance Criteria

- [x] Macros stop when POE is not the foreground window
- [x] F4 disables macros for 3 seconds (cooperative cancellation via Flow, same as old code)
- [x] `shouldContinue` wired to cancellation StateFlow in both macros
- [x] `MapScorerItemChecker.generateReport()` produces meaningful output (score averages, per-item details)
- [x] Dead `mouseOutput()` removed from `AppComponent`
- [x] Craft mod presets extracted to a named class with meaningful identifiers
- [x] `./gradlew :macro-app:build` still succeeds

## Notes

- F4 disables `shouldContinue` for 3 seconds via a reactive Flow (same as old `isTriggerKeyEnabled`). Since `shouldContinue` is checked cooperatively inside `MultiRollLoop.rollItems()`, a running loop will exit when the flow emits false. The next leader-key trigger starts a fresh `rollItems` call; no explicit reset needed.
- The hardcoded `columns = 10` in `craftRollingMacro` is an intentional carry-over from the old code (different grid width for crafting) and not a bug.
- JNativeHook logger suppression is a nice-to-have but not a regression (old code doesn't suppress either).
- See attachment for more detailed analysis: [macro-app-cleanup-plan.md](attachment/macro-app-cleanup-details.md)