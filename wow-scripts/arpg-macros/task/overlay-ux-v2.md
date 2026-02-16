# Overlay UX — high-level design (v2)

Status: todo
Dependencies: none
Supersedes: overlay-ux.md (kept for history / implementation notes)

This document focuses on goals, component responsibilities, and communication patterns. Implementation details are deliberately kept brief — see overlay-ux.md for Kotlin-level sketches.

## Goals and invariants

### Invariants

1. **Macro list is immutable at runtime.** After program startup, the set of available macros (and their metadata) is fixed.
2. **One macro runs at a time.** The leader key flow is modal — once a macro starts, the leader key is inactive until it finishes.

### Goals — current iteration

* **G1 (user):** When the leader key is pressed, the overlay shows available macros. When the user types a prefix, unreachable macros are dimmed/hidden and already-typed keys are highlighted.
* **G2 (user):** After a command is fully typed, the overlay shows a detailed description of the selected macro for a confirmation period. The user can confirm (or wait) to execute, or cancel.
* **G3 (user):** The overlay hides promptly on timeout — not on the next keypress.
* **G4 (dev):** Components communicate via observable state, not imperative callbacks. Adding new information to display should not require new callback methods.
* **G5 (dev):** Each macro describes itself: short label (for the picker list), category, which game(s) it applies to, and an optional longer description (for the confirmation view). Crafting macros can generate their description programmatically from their decision maker configuration.
* **G6 (dev):** Trigger keys are assigned in exactly one place.

### Goals — later iterations

* **G7 (user):** While the overlay is active (from leader key through confirmation), keypresses do not reach the game. The overlay intercepts input by temporarily becoming the foreground window.
* **G8 (user):** During macro execution, the overlay stays visible and shows live status: currencies used, time elapsed, progress. After the macro ends, the result stays visible briefly.
* **G9 (dev):** The overlay during macro execution must be click-through (mouse events pass to the game) and must not be captured by the screen-capture routine that macros use for pixel reading.

## Components and responsibilities

### 1. Macro Registry

**What it is:** An immutable list of macro descriptors, created at startup.

**What it knows:**
- For each macro: trigger key, display name, category, game applicability, short and long descriptions, and a factory to create the runnable macro.

**What it does NOT know:** Anything about keyboard input, overlay rendering, or execution state.

**State:** None (immutable data).

### 2. Leader Key Detector

**What it is:** A state machine that processes raw keyboard events and determines what the user is doing with the leader key system.

**What it knows:**
- The leader key chord (e.g., Alt+X).
- The set of registered trigger keys (from the macro registry).
- Timing: timeout duration, confirmation duration.

**What it does NOT know:** What the macros do, how the overlay looks, or how to manage window focus. It doesn't even know macros exist — it only knows about registered *command strings*.

**State (`StateFlow`):** A single continuous value representing the current phase of the leader key interaction:
- **Idle** — nothing happening.
- **Picking(collectedKeys)** — leader key activated, collecting command keys. Includes which keys have been typed so far.
- **Confirming(matchedCommand, descriptor)** — a command was fully typed and matched. Carries the resolved macro descriptor (display name, description) so the overlay can render without looking up the registry. Waiting for confirmation or cancellation.

State transitions are driven by keyboard events and timers. The detector owns the timers (timeout during Picking, countdown during Confirming).

**Execution handshake:** `suspend fun awaitExecution(): String` — suspends until confirmation completes (timer or user confirm). Returns the matched command and transitions state back to Idle. This is not observable state — it's a suspend function consumed by the coordinator only (see Q1 in review responses).

### 3. Overlay

**What it is:** A visual surface that renders information to the user. In the current iteration, it shows the macro picker and confirmation view. In a later iteration, it also shows macro execution status.

**What it knows:**
- The macro registry (for rendering labels, descriptions, categories).
- The leader key detector's state (for deciding what to show).
- Later: the macro execution status (for live progress display).

**What it does NOT know:** How to detect keys, which macro to run, or when to transfer focus. It is a *pure renderer* of observed state.

**State:** Derived entirely from what it observes. The overlay has no independent state machine — it is a function of its inputs:
- Detector Idle → hidden (or showing execution status if a macro is running, see G8).
- Detector Picking(keys) → show macro list, highlight/dim based on prefix.
- Detector Confirming(cmd, descriptor) → show matched macro's description (from descriptor), countdown.
- Macro running → show live status (later iteration, G8).
- Macro finished → show result briefly, then hide.

### 4. Coordinator

**What it is:** The top-level wiring that connects components and handles ordering-sensitive side effects that cannot be expressed as pure observation.

**What it knows:** All the components. It is the only place where imperative sequencing lives.

**Responsibilities:**
- At startup: builds the macro registry, registers commands with the detector, binds the overlay to observable state, starts listening.
- On execution: calls `detector.awaitExecution()` (suspends through confirmation), then performs the **focus handoff** (return focus from overlay to game), then runs the macro.

**Why it exists:** There is one ordering constraint that pure reactive observation cannot express: *focus must return to the game before the macro starts.* The coordinator is the single site where this imperative sequencing happens. Everything else is reactive. The sequencing is expressed as a simple sequential suspend function, not as state observation.

### 5. Focus Manager

**What it is:** An abstraction over window focus transfer. Platform-dependent (Win32 `SetForegroundWindow`/`GetForegroundWindow`).

**What it knows:** How to save the current foreground window, bring a target window to front, and restore the previous window.

**What it does NOT know:** Why or when to transfer focus — that's the coordinator's job.

**Interaction with the overlay (G7):**
- When the detector enters Picking, the overlay (or coordinator) asks the focus manager to bring the overlay to the foreground. From this point, keypresses go to the overlay, not the game.
- When the coordinator acknowledges execution, it asks the focus manager to return focus to the game before running the macro.

### 6. Macro Execution Engine

**What it is:** Runs a selected macro and reports its status.

**What it knows:** The macro's `prepare()` / `run()` lifecycle.

**State (for G8, later iteration):** An observable value representing the current execution status:
- Not running
- Running(macro, startTime, progress: macro-specific data)
- Finished(macro, result summary)

The overlay observes this to show live status during G8. The data model for "progress" is macro-specific — crafting macros report currencies used, generic macros might just report elapsed time.

### 7. Platform Layer

Keyboard input, mouse input, screen capture, window management, clipboard, active window checking. Already exists. The main new addition for this work is focus management (`SetForegroundWindow` binding) and later, click-through window style and per-window screen capture (for G9).

## Communication diagram

```
                    ┌─────────────────────┐
                    │   Macro Registry    │  (immutable data)
                    └─────────┬───────────┘
                              │ read
            ┌─────────────────┼──────────────────┐
            │                 │                  │
            ▼                 ▼                  ▼
   ┌─────────────┐   ┌──────────────┐   ┌──────────────┐
   │  Leader Key  │   │   Overlay    │   │ Coordinator  │
   │  Detector    │   │  (renderer)  │   │   (main)     │
   └──────┬───────┘   └──────▲───────┘   └──────┬───────┘
          │                  │                   │
          │  state(StateFlow)│                   │ observes state
          └──────────────────┘                   │ + awaitExecution()
                                                 │
                                        ┌────────┴────────┐
                                        │  Focus Manager  │  (platform)
                                        └─────────────────┘

    Keyboard ──events──▶ Leader Key Detector
    Coordinator ──awaitExecution()──▶ Leader Key Detector  (suspend, returns command)
    Coordinator ──grabFocus()──▶ Focus Manager  (on Picking)
    Coordinator ──releaseFocus()──▶ Focus Manager  (before macro run)
    Coordinator ──run()──▶ Macro Execution Engine
    Macro Execution Engine ──status(StateFlow)──▶ Overlay  (G8, later)
```

**Data flow summary:**
- **Keyboard → Detector:** raw key events (the only input to the state machine).
- **Detector → Overlay:** observable state (`StateFlow`). Read-only.
- **Coordinator → Detector:** `awaitExecution()` — suspend call that blocks through confirmation and returns matched command. The detector transitions itself to Idle when it returns.
- **Coordinator → Focus Manager:** imperative `grabFocus()` / `releaseFocus()`. Sequenced with macro execution.
- **Coordinator → Macro Engine:** `run()`. Only after focus is returned to game.
- **Macro Engine → Overlay:** observable execution status (`StateFlow`, for G8).
- **Macro Registry → everyone:** immutable data, read at startup and during rendering.

## Key design decisions

### Single observable state, not callbacks

The detector's `StateFlow` is the single source of truth for what the overlay should render. No callback interfaces to extend when adding new information — just add fields to the state.

The coordinator does *not* observe the state for execution. Instead it calls `awaitExecution()`, a suspend function that blocks through the confirmation phase and returns the matched command. This cleanly separates "what to render" (StateFlow, observed by overlay) from "when to act" (suspend function, called by coordinator). No `acknowledgeExecution()` handshake needed — the suspend function return *is* the handshake.

### Overlay is a pure function of observed state

The overlay never mutates shared state. It renders what it sees. This makes it easy to test (snapshot-test the rendering given a state), easy to extend (add new state → add new rendering), and impossible to create feedback loops.

Focus management (G7) is the one wrinkle: the overlay window needs to become focusable/foreground during Picking/Confirming. This is driven by the observed state (Picking → grab focus), but the actual Win32 call goes through the Focus Manager. Whether the overlay or the coordinator drives this is a wiring detail — the important thing is it's triggered by state observation, not a callback.

### Macro self-description

Each macro entry in the registry carries its own metadata. For craft macros, the long description can be generated from the decision maker's structured args (target mods, strategy name, etc.). This is a property of the registry entry, computed once at startup — no runtime introspection needed.

### Execution status as a separate observable (G8)

The detector's state covers the leader-key interaction (idle → picking → confirming → executing). Macro *runtime* status (currencies used, progress, result) is a separate concern with a separate lifecycle. It gets its own observable value, owned by the macro execution engine. The overlay observes both: detector state for the picker, execution status for the live display.

This separation means G8 can be implemented without touching the detector at all.

## Review responses

### Q1: Does Executing earn its keep as a full state?

The reviewer's point: `Executing` is only observed by the coordinator, which immediately acknowledges it, making it effectively a synchronous signal. A `Channel<MatchedCommand>` would be simpler.

**Resolution: drop `Executing` from the detector state. Use a suspend function instead.**

The Confirming → execution transition doesn't need to be observable by the overlay. It's a handshake between two parties (detector + coordinator), not a broadcast. Modeling it as a state pollutes the "what should the overlay show" concern with "when should the coordinator act."

Revised detector API:
```
Detector state: Idle | Picking(collectedKeys) | Confirming(matchedCommand)
Detector method: suspend fun awaitExecution(): String
```

`awaitExecution()` suspends until the confirmation period completes (or user confirms). It returns the matched command string and transitions the detector to Idle internally. The coordinator calls it, gets the command, and runs the macro. The detector never enters a state that only one consumer cares about.

From the overlay's perspective, the lifecycle is: `Idle → Picking → Confirming → Idle`. No `Executing` to render. The "starting..." indicator from the previous design is unnecessary — by the time the coordinator gets the command, the overlay is already transitioning to Idle (or to the execution status view in G8).

This also eliminates the `acknowledgeExecution()` handshake entirely. The suspend function *is* the handshake — when it returns, the coordinator knows confirmation is done and can proceed. Focus release slots naturally into this:

```
// Coordinator:
val command = detector.awaitExecution()   // suspends through confirmation
focusManager.releaseFocusToGame()          // ordered: focus first
macrosByKey[command]?.run()                // then run
```

### Q2: Phase 2 confirmation UX without focus interception

In Phase 2 (before G7), keypresses still reach the game. Confirmation works as:
- **Auto-confirm:** The confirmation countdown timer expires → macro runs. The user just waits.
- **Cancel:** The user presses the leader key chord (Alt+X) again, or any unrecognized key, which resets the detector to Idle. Escape also works (it'll close a game menu, but that's recoverable).

This is intentionally simple. Phase 2 doesn't aim for a polished confirm/cancel UX — it just introduces the concept of a delay + description view. Phase 3 (G7, focus interception) is where Enter/Escape become clean.

### Q3 & Q4: Trigger key location and command→macro mapping

Already addressed in overlay-ux.md:
- Q3: Central list approach (option b). The current `macroMapping` in `MainV2.kt` is already the single source. Add validation at startup.
- Q4: Coordinator holds a `macrosByTriggerKey: Map<String, PreparedMacro>` built from the registry at startup.

### Q5: SetForegroundWindow reliability — needs a PoC

This is the riskiest platform-specific piece. `SetForegroundWindow` has well-known restrictions on Windows — a background process generally cannot steal focus. The workarounds are:

1. **Simulated Alt keypress via `SendInput`** before calling `SetForegroundWindow`. This flags the calling process as eligible. (Used by PowerToys and many other tools.)
2. **`AttachThreadInput`** to the foreground thread, call `SetForegroundWindow`, then detach. Risk: our thread can hang if the attached thread hangs.
3. **`AllowSetForegroundWindow`** — requires cooperation from the foreground process (not applicable here).

In our case, the user *just* pressed Alt+X, so the system may already consider our process eligible (condition: "the calling process received the last input event"). But JNativeHook hooks run on a native thread, so the Java process might not be credited with the input event from the kernel's perspective.

**Even if `SetForegroundWindow` succeeds, it's not instant.** The window manager processes the request asynchronously. There could be a brief window where `GetForegroundWindow()` still returns the old HWND. The focus-then-run ordering in the coordinator needs to account for this.

**Plan: write a minimal PoC to verify the flow.** The PoC should be a standalone `main()` — no Dagger, no macros, no existing infrastructure. Its only goal is to answer:

1. Can we reliably bring a Java/Swing window to the foreground from a JNativeHook callback?
2. Which workaround (SendInput Alt, AttachThreadInput, or none) is needed?
3. Can we reliably return focus to the previous foreground window?
4. What's the latency between `SetForegroundWindow()` and `GetForegroundWindow()` confirming the switch?
5. Is polling `GetForegroundWindow()` sufficient to confirm the switch, or do we need a different signal?

See `task/attachment/focus-poc-spec.md` for the PoC specification.

### Q6: Screen capture exclusion — fallback strategy

The current `Robot`-based (or `BitBlt`-based) capture can be kept as the default. G9 (per-window Windows Graphics Capture) is an enhancement for when the overlay is visible during macro execution. If the overlay is hidden (which it is in Phase 1-3 during macro execution), the existing capture works fine. G9 only becomes necessary when G8 (live overlay during execution) is implemented.

So the practical ordering is: G8 requires click-through overlay (`WS_EX_TRANSPARENT`, straightforward JNA) but can use existing capture *if* the overlay is positioned to not overlap the game area being captured. G9 is only needed if the overlay overlaps the capture region.

### Nits

**LeaderState carrying resolved descriptors vs command strings:** Good idea. `Confirming` should carry the resolved `MacroDescriptor` (or at least display name + description) rather than just the command string. This way the overlay doesn't need to look up the registry. `Picking` still only needs `collectedKeys` — the overlay can filter the registry by prefix itself (it already has the registry for rendering the full list). Updated in the component description below.

**Behavior vs StateFlow terminology:** Sticking with Kotlin terminology (`StateFlow`) going forward. "Behavior" was used to explain the FRP concept in review discussions; the design doc should use `StateFlow` consistently.

## Implementation phases

### Phase 0: Focus interception PoC (de-risks G7)

Standalone `main()` — no Dagger, no macros, no existing infrastructure. A minimal Swing window + JNativeHook + JNA. Answers the questions from Q5: Can we steal/return focus reliably? Which workaround is needed? What's the latency? See `task/attachment/focus-poc-spec.md`.

### Phase 1: StateFlow-driven picker + timeout fix (G1, G3, G4, G5, G6)

Refactor `LeaderKeyDetector` to expose `StateFlow<LeaderState>` (Idle, Picking, Confirming) instead of per-command `isEnabled()` flows and callbacks. Overlay observes state reactively. Proactive timeout via coroutine. Macro registry with descriptions.

### Phase 2: Confirmation step (G2)

Add `Confirming` state with countdown timer. Overlay shows matched macro's description. `awaitExecution()` suspend function for the coordinator. Phase 2 UX: auto-confirm after countdown, cancel by pressing leader key or any unrecognized key.

### Phase 3: Focus interception (G7)

`FocusManager` abstraction. Coordinator grabs focus on Picking, releases before macro run. Win32 `SetForegroundWindow` binding (approach validated by Phase 0 PoC). Enter/Escape handled by overlay while it has focus.

### Phase 4: Live execution status (G8)

Macro execution engine reports status as `StateFlow`. Overlay renders live progress. Click-through window style (`WS_EX_TRANSPARENT` via JNA) so mouse events pass to game.

### Phase 5: Screen capture without overlay (G9)

Per-window capture (Windows Graphics Capture API) so macros don't see the overlay in pixel reads. This is the most platform-heavy phase. The existing `Robot`/`BitBlt`-based capture remains the default fallback — G9 is only needed when the overlay overlaps the capture region during macro execution.
