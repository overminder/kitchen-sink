# More Macros

Status: done
Dependencies: macro-app-cleanup.md

## Description

Port three more macros from the old codebase into macro-app:

1. **printMousePos** — Debug tool that prints mouse coordinates and pixel color at cursor. Triggered by leader key `Alt+X, 0, 2`.
2. **townHotkey** — Maps function keys (F5/F6/F7) to POE chat commands (`/hideout`, `/kingsmarch`, `/heist`). Parameterized by window title so it works for both POE and POE2.
3. **sortInStash** — Reads items in stash, scores them with MapScorer, then sorts them in-place by moving to bag and back in score order. Triggered by leader key `Alt+X, 1, 4`.

## Acceptance Criteria

- [x] `printMousePos` prints `Mouse(x=..., y=...), color=ScreenColor(...)` on leader key `02`
- [x] `printMousePos` only fires when POE is the foreground window
- [x] `townHotkey` sends `/hideout` on F5, `/kingsmarch` on F6, `/heist` on F7 when POE is active
- [x] `townHotkey` sends `/hideout` on F5 when POE2 is active
- [x] `townHotkey` does nothing when neither game is active
- [x] `sortInStash` scores stash items, sorts by score descending, moves items via bag round-trip
- [x] `sortInStash` respects `shouldContinue` (active window + F4)
- [x] New `KeyboardOutput` extension functions (`postPressRelease`, `postAsciiString`) are in macro-core
- [x] New `JNativeHookMouseInput` implementing `MouseInput` is in macro-app
- [x] `./gradlew :macro-core:test` and `./gradlew :macro-app:build` pass
- [x] All macros wired in Main.kt

## Notes

- `printMousePos`: minimal port — single pixel color only, no average color helpers (can be added later).
- `townHotkey`: single parameterized function launched twice with different window titles and hotkey maps. Not leader-key based — listens to global key releases directly.
- `sortInStash` uses `PoeScreenConstants.firstItemInRegularStash` (already in macro-core) and sorts half the stash (12x6 grid) at a time.
- See [detail plan](attachment/more-macros-details.md) for implementation steps.
