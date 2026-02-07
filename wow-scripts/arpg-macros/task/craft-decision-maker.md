# Craft Decision Maker

Status: done
Dependencies: none

## Description

Migrate the `CraftDecisionMaker` interface and its generic inner classes from `poecraft.kt` into `macro-core`. This is the decision engine that inspects an item's current mods and decides whether to proceed, reset, go back, or declare done.

Includes:
- `CraftDecisionMaker` fun interface
- `Decision` data class (implements `CheckResult`)
- `DecisionType` enum (Done, Reset, Proceed, GoBack)
- `byMatches()` helper
- `ByDesiredModsEx` inner class
- `ByDesiredOneSideModsEx` inner class
- `byDesiredMods()` and `byDesiredOneSideMods()` factory functions
- `.asItemChecker()` bridge extension

Excludes: All preset instances (e.g., `intStackCluster4`, `magebloodFlask`) since they reference game-specific mod lists.

## Acceptance Criteria

- [x] `CraftDecisionMaker` interface in `macrocore` package
- [x] `Decision` implements macro-core's `CheckResult`
- [x] `byMatches()` logic preserved: Done/Proceed/GoBack/Reset thresholds
- [x] `ByDesiredModsEx` and `ByDesiredOneSideModsEx` migrated
- [x] Factory functions `byDesiredMods()` and `byDesiredOneSideMods()` migrated
- [x] `.asItemChecker()` bridge extension migrated
- [x] Unit tests for `byMatches()` state transitions
- [x] Unit tests for `ByDesiredOneSideModsEx` regal-reset behavior
- [x] Tests pass

## Notes

`Decision` currently implements `PoeMultiRoll.CheckResult`. In macro-core it should implement the top-level `CheckResult` interface from `MultiRollLoop.kt`.

The `IntStackClusterEx` inner class is a concrete preset — it can stay in old code or be migrated as an example. Low priority either way.
