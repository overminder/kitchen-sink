# UX Guardrails — Detailed Spec

## Motivation

From `bug.md` recommendation #2: features and use cases interact with each other, and we need to describe our intention better in our spec.

### Use cases that drive the guardrails

| Use case | What happens | Guardrails involved |
|----------|-------------|---------------------|
| Alt-tab while bg macro runs | Bg macro stays running, overlay hides | G1, G5 |
| Alt-tab while picker is open | Picker auto-cancels, overlay hides | G1, G2 |
| Open picker while bg macro recently ran | Picker works normally, all keys respond | G4, G5 |
| Press leader key twice | First opens, second dismisses | G2 |
| Select macro in picker | Confirmation countdown, then execution | G6, G7 |
| Macro finishes | Overlay returns to idle (or bg status) | G7 |

### Interaction matrix

Pairs of concurrent activities and expected behavior:

| Activity A | Activity B | Expected |
|-----------|-----------|----------|
| Bg macro running | Open picker | Picker works normally |
| Bg macro running | Alt-tab | Bg status hides, macro continues |
| Picker open | Alt-tab | Picker cancels |
| Picker open | Leader key | Picker cancels |
| Macro running | Leader key | No-op |
| Macro running | Alt-tab | Macro continues (game refocused on return) |

## Guardrail enforcement strategies

### G1: Overlay visibility — Structural enforcement

**Current code** (`ComposeOverlayWindow.kt:122`):
```kotlin
val isVisible = pickerVisible || runningMacroName != null || (bgStatusLines.isNotEmpty() && gameInForeground)
```

**Problem:** `pickerVisible` and `runningMacroName` don't check `gameInForeground`.

**Proposed:**
```kotlin
val isVisible = when {
    pickerVisible -> gameInForeground || overlayInForeground
    runningMacroName != null -> gameInForeground
    bgStatusLines.isNotEmpty() -> gameInForeground
    else -> false
}
```

Plus: when `pickerVisible && !gameInForeground && !overlayInForeground`, auto-cancel.

### G2: Leader key toggle — State machine enforcement

**Current:** `Coordinator.onLeaderKey()` returns immediately if `state != Idle`.

**Proposed:** Add explicit handling for `Open` state:
```kotlin
suspend fun onLeaderKey() {
    when (state) {
        CoordinatorState.Idle -> { /* existing open logic */ }
        CoordinatorState.Open -> { overlayController.cancelSelection() }
        CoordinatorState.MacroRunning -> { /* no-op */ }
    }
}
```

Need to expose cancel on `OverlayController` interface.

### G4: Input delivery is non-exclusive — Audit + test

**Audit checklist:**
- [ ] Windows keyboard hook uses `CallNextHookEx` (does not consume events)
- [ ] `KeyboardInput.keyPresses()` is a broadcast flow (multiple collectors don't compete)
- [ ] Overlay `onPreviewKeyEvent` returns `true` only for handled keys (prevents propagation only for keys it cares about)

**Test:** Integration test that:
1. Starts bg macros
2. Opens overlay
3. Sends key "6" via test keyboard input
4. Asserts overlay selects the 6th macro

### G4a: Intentional cross-macro feedback — Documentation + test

Some macros intentionally communicate through the keyboard channel. This is distinct from G4 (delivery isolation): G4 ensures all readers see all events, G4a documents cases where one macro's *output* is deliberately consumed by another macro's *input*.

**Known feedback loops:**

| Sender | Output | Receiver | Input | Why |
|--------|--------|----------|-------|-----|
| Auto-attack | Holds "W" via `KeyboardOutput` | Flask macro | Detects "W" in `keyStates()` | Flasks should stay active during auto-attacks |

**Enforcement:**
- KDoc on both sender and receiver macros documenting the intentional coupling
- Integration test per loop: run auto-attack → assert flask macro activates

### G7: State machine — Sealed class enforcement

Replace `CoordinatorState` enum + ad-hoc transitions with a sealed class that encodes valid transitions:

```kotlin
sealed interface CoordinatorState {
    data object Idle : CoordinatorState
    data class Open(val pendingSelection: CompletableDeferred<OverlaySelection>) : CoordinatorState
    data class MacroRunning(val macroName: String) : CoordinatorState
}
```

Transitions as methods on Coordinator that return the new state, with exhaustive `when` over current state.

## Review Comments

### Overall

Good detail spec. The use-case table and interaction matrix are exactly what the recommendation asked for. Code snippets are accurate (verified against codebase). A few specific notes:

### G1 enforcement

The proposed `isVisible` code is correct but incomplete. It shows what visibility *should be*, but doesn't show the auto-cancel mechanism. When `pickerVisible && !gameInForeground && !overlayInForeground`, who calls cancel? The main plan mentions a `LaunchedEffect` or Coordinator monitoring — this detail spec should pick one and specify it.

### G2 enforcement

The proposed `when` block is clean. Important implementation detail not mentioned: `Coordinator.onLeaderKey()` has a double-check pattern — fast path without lock (line 41) and guarded path with lock (line 44). The `Open → cancel` branch needs to work with this pattern. Specifically, the fast path should let `Open` through to the mutex block (not return early), so the cancel happens under the lock to avoid races.

### G4 enforcement

The audit checklist is good. Consider adding: "verify `keyPresses()` is backed by a `SharedFlow` (not a regular `Flow`), and check its `replay` and `extraBufferCapacity` settings." If it's a cold flow that creates a new collector per `collect` call, multiple consumers should be fine. But if it's a shared hot flow with limited buffer, slow consumers could cause drops.

### G7 enforcement

The sealed class only has 3 states (`Idle`, `Open`, `MacroRunning`), but the state diagram in `ux-guardrails.md` has 4 (`Idle`, `Open`, `Confirming`, `MacroRunning`). Either add `Confirming` to the sealed class, or clarify that `Confirming` is a sub-state of `Open` (i.e., the deferred in `Open` transitions to a countdown phase internally).

### Interaction matrix

Excellent addition. One missing row: **Macro running + Bg macro running**. What happens if a foreground macro is executing while a bg macro is also active? They should be independent (G5), but it's worth stating explicitly.
