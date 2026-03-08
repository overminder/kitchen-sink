# UX guardrails: Intention-based overlay & macro interaction spec

Status: todo
Dependencies: none

## Description

The bugs in `bug.md` stem partly from under-specification: the overlay's behavior was built incrementally without a formal description of intended UX invariants. As features grow (bg macros, more overlay modes), pairwise interactions multiply and bugs slip through.

This task defines **intention-based guardrails** — a set of declarative UX invariants that the system must maintain. These guide both implementation and testing, and serve as a spec for future feature work.

## Plan

See `task/attachment/ux-guardrails-details.md` for the full guardrail spec.

### Phase 1: Define the guardrails

Write a set of UX invariants organized by concern. These are not implementation details — they describe *what should be true* from the user's perspective.

### Phase 2: Audit current code against guardrails

For each guardrail, determine: (a) is it currently satisfied? (b) if not, what's the gap?

### Phase 3: Implement enforcement

Choose the right enforcement mechanism for each guardrail:
- **Structural** (compile-time): Type system, sealed classes, state machine design that makes violations impossible.
- **Runtime** (assertions/checks): Precondition checks at state transitions.
- **Test-based** (regression): Integration tests that exercise multi-feature interaction scenarios.

### Phase 4: Document for future contributors

Add the guardrails as a living doc (e.g. in `doc/` or as KDoc on key interfaces) so future changes are guided by them.

## Proposed guardrails

### G1: Overlay visibility follows focus context

> The overlay (all modes: picker, execution status, bg status) is visible **only** when a game window or the overlay itself is in the foreground.

- Picker auto-cancels if foreground changes to a non-game, non-overlay window.
- Bg status hides when game is not in foreground (already implemented).
- Execution status follows the same rule as bg status.

**Enforcement:** A single `shouldBeVisible` derivation that all modes feed into, incorporating foreground state.

### G2: Leader key is a toggle

> Pressing the leader key when the overlay is **not open** opens it. Pressing it when the overlay **is open** dismisses it. Pressing it during macro execution is a no-op.

**Enforcement:** Coordinator state machine handles all three states explicitly:
- `Idle` → `Open` (open overlay)
- `Open` → `Idle` (cancel and dismiss)
- `MacroRunning` → no-op

### G3: Macro preparation happens at startup, not at trigger time

> `MacroDef.prepare()` is called once during app initialization. `MacroDef.Prepared.run()` is called per session.

This aligns with the documented lifecycle and prevents issues like Bug 2 (stateIn needing a value that isn't available yet).

**Enforcement:** `MacroRunnerImpl` caches `Prepared` instances. `prepare()` takes no arguments that vary per-session.

### G4: Input delivery is non-exclusive

> All keyboard event consumers receive all events. No consumer blocks, consumes, or starves another consumer's delivery.

This is about the *reading* side: multiple listeners (overlay, bg macros, etc.) must all see every key event. Bug 3 is a violation of this guardrail.

Concretely:
- Global hooks must not consume/swallow key events (use `CallNextHookEx` on Windows).
- Overlay key handling (`onPreviewKeyEvent`) is the sole owner of keys while the overlay is focused.
- Background macros must not assume they are the only consumers of keyboard state.

Note: This guardrail does not prohibit intentional **output→input feedback** between macros — see G4a.

**Enforcement:**
- Audit the native hook implementation to ensure non-consuming behavior.
- Integration test: trigger overlay while bg macros are active, verify all picker keys work.

### G4a: Intentional cross-macro feedback is documented

> Some macros intentionally communicate through the keyboard channel: one macro's `KeyboardOutput` produces events that another macro's `KeyboardInput` picks up. These interactions are by design and must be explicitly documented.

Known intentional feedback loops:
- **Auto-attack → flask**: Auto-attack macro holds "W" (via `KeyboardOutput`). Flask macro detects "W" held (via `KeyboardInput.keyStates()`) and activates flasks. This is desired — flasks should be maintained during auto-attacks.

**Enforcement:**
- Each intentional feedback loop is documented in the macro's KDoc (both the sender and receiver).
- Integration test per documented loop to prevent regressions.

### G5: Background macros and foreground macros are independent

> A background macro's state (running, recently ran, enabled/disabled) does not affect the ability to launch and run foreground macros via the leader key overlay.

This is the generalized form of Bug 3.

**Enforcement:**
- Bg macros and fg macros use separate coroutine scopes.
- No shared mutable state between bg macro execution and overlay/coordinator flows (except the read-only status display).
- Integration test: run bg macro → open overlay → select macro → verify it runs.

### G6: Macro confirmation is explicit

> A foreground macro runs only after explicit user confirmation (countdown + enter, or countdown expiry). No macro runs as a side effect of `prepare()`.

**Enforcement:** `prepare()` must be side-effect-free (no I/O, no screen interaction). Only `run()` performs actions.

### G7: Overlay state machine is well-defined

> The overlay has exactly these states and transitions:

```
Idle ──[leader key]──→ Open
Open ──[select macro]──→ Confirming
Open ──[esc / leader key / focus lost]──→ Idle
Confirming ──[countdown / enter]──→ MacroRunning
Confirming ──[esc]──→ Idle  (not back to Open — full cancel)
MacroRunning ──[macro completes]──→ Idle
```

**Enforcement:** Encode as a sealed class / state machine with exhaustive `when` handling. Invalid transitions are compile-time errors.

## Acceptance Criteria

- [ ] Guardrails documented in `doc/ux-guardrails.md` (or similar)
- [ ] Each guardrail has an enforcement strategy (structural, runtime, or test)
- [ ] Key guardrails (G1, G2, G4, G5) have integration tests
- [ ] Coordinator state machine refactored to match G7
- [ ] `MacroDef.prepare()` lifecycle aligned with G3 (or documented exception)
- [ ] Existing tests still pass

## Notes

- This is a larger effort than the immediate bugfix task. It can be done incrementally — start with the guardrails that directly prevent the reported bugs (G1, G2, G4, G5), then add the rest.
- G3 (prepare at startup) may require changes to `MacroDef` interface. Some macros may need per-session context — if so, document the exception and ensure `prepare()` remains side-effect-free (G6).
- G5 (independence) is the hardest to enforce generically. The "quadratic interaction" problem noted in `bug.md` is real. The practical approach is: (a) architectural isolation (separate scopes, no shared mutable state), (b) integration tests for known interaction pairs, (c) accept that not all pairs can be tested upfront.
- Some guardrails overlap with existing conventions (e.g. G6 is partially implied by the `prepare`/`run` split). The value is making them explicit and testable.

## Review Comments

### Overall

This plan is a strong response to the recommendation's call for "intention-based specification." The guardrails are well-organized, each traces back to a specific bug or user concern, and enforcement strategies are concrete. A few observations:

### G1: Overlay visibility follows focus context

Good. Directly addresses recommendation's "overlays should only be visible in games." One gap: the guardrail says "visible only when a game window or the overlay itself is in the foreground" — but what about *execution status*? If a macro is running and I alt-tab, should I still see the execution status when I tab back? The proposed code in the detail spec hides it (`runningMacroName != null -> gameInForeground`), which means the execution status disappears on alt-tab and reappears on tab-back. That's probably fine, but worth stating explicitly as intended behavior.

### G2: Leader key toggle

Clean and well-specified. No issues.

### G3: Macro preparation at startup

This is the right long-term fix. However, it has a tension with the current architecture: `MacroRunnerImpl` calls `prepare()` inside a loop over `targetGameTypes`, meaning `prepare()` may produce different `Prepared` instances per game type. If we cache at startup, we need to handle this. The plan says "prepare() takes no arguments that vary per-session" — verify this is true for all macros, or document exceptions.

### G4: Input delivery is non-exclusive

Good guardrail. The audit checklist is the right approach. However, the recommendation specifically calls out that this is "harder to catch as we add more features" (quadratic growth). The plan's enforcement (audit + one integration test) is good for the known bug, but doesn't address the scaling problem. Consider: could there be a structural enforcement? E.g., a test helper that starts N macros simultaneously and verifies all key events are delivered to all of them. This would catch future violations without needing to enumerate all pairs.

### G4a: Intentional cross-macro feedback

Excellent — this directly addresses the recommendation's point about auto-attack → flask being intentional. The distinction between G4 (delivery isolation) and G4a (intentional coupling) is exactly right. Well done.

### G5: Background vs foreground independence

Good. The "separate coroutine scopes + no shared mutable state" enforcement is the right structural approach. One question: the recommendation notes that defining "independently" is hard. The guardrail says "bg macro's state does not affect the ability to launch fg macros" — but what about the reverse? Can a foreground macro affect a bg macro? E.g., if I run a foreground macro that sends keyboard output, could it confuse a bg macro that's listening? This may be intentional (G4a), but it's worth being explicit about directionality.

### G6: Macro confirmation is explicit

Fine. Note this overlaps with the bugfix-immediate plan's Bug 2 fix. If G3 is implemented (prepare at startup), Bug 2 is automatically fixed, making the immediate fix redundant. The phasing between the two plans should be clarified — if bugfix-immediate ships first, the G3 implementation should remove the Bug 2 workaround.

### G7: Overlay state machine

The state diagram is clear. One issue: it's missing the `Confirming` state from the diagram but the text mentions it. Also, the sealed class in the detail spec doesn't include `Confirming` — it only has `Idle`, `Open`, and `MacroRunning`. If `Confirming` is a real state (countdown before execution), it should be in the sealed class.

### Missing from the plan

The recommendation mentions "use cases" as a driver. The detail spec has a good use-case table and interaction matrix — but the main `ux-guardrails.md` plan doesn't reference specific use cases per guardrail. Consider adding a "covers use cases: ..." note to each guardrail for traceability.

### Phasing concern

The plan says this can be done incrementally, starting with G1, G2, G4, G5. But the plan doesn't specify an order or dependencies between guardrails. G7 (state machine refactor) is foundational — G2 and G1's enforcement depends on the state machine being well-defined. Consider making G7 the first implementation step.
