# background macro: visual feedback

Status: done
Dependencies: none

## Description

BackgroundMacroRunner holds various single key triggered macros. I want to add some visual feedback of these macros, so users are aware that the macros are automatically pressing keys. However, the visual feedback should also stay small to avoid blocking too much of the game screen.

## UX idea

Show a concise description of the background macros that were ran recently (e.g. past 15 seconds), similar to a "status line" in CLI.

For example, "flask [2, 3 x3] 00:50" means the flask macro pressed key 3 for 3 times, and 2 for 1 time, and has been running for 50 seconds. "Running" means the macro pressed a key in the past "recently" window.

## Details

See [bg-macro-status-details.md](../attachment/bg-macro-status-details.md) for full design.

Summary of components:
1. **`BgMacroStatusTracker`** — collects events, maintains 15s sliding window, exposes `StateFlow<List<BgMacroStatusLine>>`
2. **`ReportingKeyboardOutput`** — `KeyboardOutput` decorator that intercepts key presses and reports to the tracker
3. **Wiring in `BackgroundMacroRunner`** — creates per-macro decorated `KeyboardOutput` instances (e.g. `"flask"`, `"focus"`) and passes to each macro's `run()`
4. **Macro signature change** — each macro's `run()` accepts a `keyboardOutput` param instead of using the DI-injected field
5. **`BackgroundMacroState` extension** — add `statusLines: StateFlow` for overlay consumption
6. **Overlay status line** — compact, click-through row shown when picker/execution status are not active

## Acceptance Criteria
- [x] `BgMacroEventSink` and `BgMacroStatusTracker` exist in macro-core
- [x] All 4 background macros report key presses to the sink
- [x] `BackgroundMacroState` exposes status lines
- [x] Overlay shows a compact status line for recently active background macros
- [x] Status line disappears after 15s of inactivity
- [x] Status line format: `macroName [key xN, key2] MM:SS`
- [x] Click-through (non-focusable) when shown
- [x] Tests for `BgMacroStatusTracker` (eviction, counts, duration, multi-macro)
- [x] Tests for `ReportingKeyboardOutput` (delegates + reports, postRelease excluded)
- [x] Build and all tests pass