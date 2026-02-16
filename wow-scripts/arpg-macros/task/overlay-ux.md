# Overlay UX improvements

Status: todo
Dependencies: none

## Design goals and invariants

(From review comments v1)

* **invariant(dev)**: After program starts, the list of macros is known and immutable.
* **goal(dev)**: Avoid imperative interfaces / callbacks. Model leader key state as a `StateFlow` that the overlay observes reactively.
* **goal(dev)**: Each macro should describe itself: short description (for overlay list), which game it applies to, and optionally a longer description (for confirmation view).
* **goal(dev)**: Trigger keys should be assigned in one place. Ideally auto-assigned, or at least centralized (not scattered across files).
* **goal(user)**: Trigger keys should be short and mostly stable when adding new macros.
* **goal(user)**: After a macro is selected, show its detailed description for a few seconds before starting. Let the user cancel if they picked the wrong one.

## Problems (from v1)

### 1. Overlay lingers after logical timeout

The timeout in `LeaderKeyDetector` is **lazy** — it only checks elapsed time when a key arrives (line 70-71 of `LeaderKeyDetector.kt`). If no key is pressed after the timeout duration, the overlay stays visible until the next key event.

### 2. No key feedback in overlay

When the user types the first character of a multi-char command (e.g., "1" of "13"), the overlay gives no visual feedback — no indication that the keypress was registered, no filtering of reachable commands.

### 3. No confirmation step

Currently, the matched macro fires immediately. If the user mistypes or picks the wrong macro, there's no chance to cancel before it starts.

## Proposed architecture

### Core idea: `StateFlow`-driven leader state

Replace the imperative callbacks (`onLeaderActivated`, `onLeaderDeactivated`) with a `StateFlow<LeaderState>` owned by the detector. The overlay and the macro launcher both observe this flow reactively.

```kotlin
sealed class LeaderState {
    /** Leader key not active. Overlay hidden. */
    data object Idle : LeaderState()

    /** Leader active, overlay has focus, waiting for command keys. */
    data class Picking(val collectedKeys: List<String> = emptyList()) : LeaderState()

    /** Command matched, showing confirmation. Overlay still has focus. */
    data class Confirming(val matchedCommand: String) : LeaderState()

    /** Confirmed. Consumer should start the macro and call acknowledgeExecution(). */
    data class Executing(val matchedCommand: String) : LeaderState()
}
```

The `LeaderKeyDetector` exposes:
```kotlin
class LeaderKeyDetector(
    private val leaderKey: Set<String>,
    private val keyboardInput: KeyboardInput,
    private val clock: Clock,
    private val scope: CoroutineScope,
    private val focusManager: FocusManager,
    private val timeout: Duration = 2.seconds,
    private val confirmDuration: Duration = 2.seconds,
) {
    // All registered commands (populated via register() before start)
    val commands: Set<String>

    // Single source of truth (Behavior in FRP terms — always has a value)
    val state: StateFlow<LeaderState>

    fun register(command: String)

    // Releases focus to game, then transitions Executing → Idle.
    // Suspends until game has focus. See "Focus release ordering" section.
    suspend fun acknowledgeExecution()
}
```

**Key changes from v1 design:**
- No more `isEnabled(command): Flow<Boolean>` per-command flows. One shared `state: StateFlow<LeaderState>`.
- No callbacks. No separate `SharedFlow` for events. Single StateFlow is the entire public API (plus `acknowledgeExecution()` handshake for ordering-critical focus release).
- The detector needs a `CoroutineScope` to launch timeout / confirmation timers.
- `FocusManager` dependency for sequenced focus release (see "Focus release ordering" section).

### Proactive timeout

When transitioning to `Picking`, the detector launches a coroutine:
```kotlin
timeoutJob = scope.launch {
    clock.delay(timeout)
    _state.value = LeaderState.Idle
}
```
Cancelled on match, mismatch, or new leader activation.

### Focus interception: overlay steals focus during leader mode

(From open question answers)

Currently the overlay window is `focusable = false` and the game stays in the foreground. This means any key we'd use for confirm/cancel (Enter, Escape) would be sent to the game too.

**Solution:** When the leader key (Alt+X) is detected, bring the overlay window to the foreground and make it focusable. This way:
- The game window becomes inactive — keypresses no longer reach it.
- The overlay can naturally capture Enter (confirm), Escape (cancel), and the command digit keys.
- `ShouldContinueChecker`'s active-window polling won't falsely stop running macros (see below).

**Implementation sketch:**
```kotlin
// New method on OverlayOutput (or a separate WindowFocusManager)
interface OverlayOutput {
    fun start() {}
    fun bind(macros: List<MacroRegistration>, leaderState: StateFlow<LeaderState>)
    fun requestFocus()    // bring overlay to foreground
    fun releaseFocus()    // return focus to previous window (the game)
}
```

On the Win32 side, this requires `User32.SetForegroundWindow(overlayHwnd)` and remembering the previous foreground window HWND to restore later. The JNA `User32` binding already provides `GetForegroundWindow`; we'd add `SetForegroundWindow`. In Compose, the overlay window toggles `focusable` dynamically.

**Active window check interaction:** `ShouldContinueChecker` uses `ActiveWindowChecker.isActiveWindow(gameTitle)` to verify the game is in the foreground before macro execution. When the overlay has focus, this check would return false. Focus must be released **before** the macro starts. See "Focus release ordering" below for how this is guaranteed.

**When to grab focus:** Right when entering `Picking` (i.e., when leader key is detected). This is better than waiting for `Confirming` because even the command digit keys won't reach the game (e.g., pressing "1" in the overlay won't trigger an in-game "1" action).

### Confirmation step

When all command keys match a registered command:
1. Transition to `Confirming(matchedCommand)`.
2. The overlay shows the macro's detailed description.
3. After `confirmDuration` elapses (or user presses Enter), proceed to execution.
4. If user presses Escape, transition back to `Idle`, overlay releases focus, no execution.

Since the overlay has focus during this phase, Enter/Escape are cleanly intercepted without conflicting with game bindings.

### Event vs Behavior: eliminating `executions` SharedFlow

(From review comments v2)

The FRP distinction is real: `state: StateFlow<LeaderState>` is a Behavior (continuous, always has a value, conflated), while a hypothetical `executions: SharedFlow<String>` is an Event (discrete, can be missed if no collector is active, not conflated). Mixing the two under the same `Flow` umbrella forces consumers to understand which semantics apply.

**Revised approach: encode execution as a state transition, not a separate flow.**

Add `Executing` as a transient state:
```kotlin
sealed class LeaderState {
    data object Idle : LeaderState()
    data class Picking(val collectedKeys: List<String> = emptyList()) : LeaderState()
    data class Confirming(val matchedCommand: String) : LeaderState()
    data class Executing(val matchedCommand: String) : LeaderState()
}
```

The detector transitions: `Confirming → Executing → Idle`. The `Executing` state is brief — it exists long enough for the consumer to observe it, then immediately transitions to `Idle`.

**Problem:** `StateFlow` is conflated. If `Executing → Idle` happens before the collector processes `Executing`, the event is lost.

**Solution:** The detector doesn't auto-transition from `Executing` to `Idle`. Instead, the consumer (main) calls an explicit `acknowledgeExecution()` method. This method is also where focus release is sequenced — see below.

### Focus release ordering and `acknowledgeExecution()`

There is a potential race condition: the overlay observes `Executing`/`Idle` and releases focus *concurrently* with the consumer calling `macro.run()`. If the macro starts before focus returns to the game, `ShouldContinueChecker.isActiveWindow(gameTitle)` returns false and the macro exits immediately. Or keystrokes/clicks might go to the overlay instead of the game.

The root cause: focus release is a *side effect* of state observation, and we need it to complete *before* the macro runs. Pure reactive observation across independent collectors can't guarantee that ordering.

**Solution: make `acknowledgeExecution()` a suspend function that handles focus release as an ordered step.** Introduce a `FocusManager` interface:

```kotlin
/**
 * Manages window focus transitions between the overlay and the game.
 */
fun interface FocusManager {
    /**
     * Release overlay focus and return focus to the game window.
     * Suspends until focus transfer is confirmed.
     */
    suspend fun releaseFocusToGame()
}
```

`LeaderKeyDetector` takes a `FocusManager`:
```kotlin
class LeaderKeyDetector(
    ...
    private val focusManager: FocusManager,
) {
    val state: StateFlow<LeaderState>

    fun register(command: String)

    /**
     * Called by consumer after observing Executing state.
     * 1. Releases overlay focus (suspends until game has focus).
     * 2. Transitions state to Idle.
     * Guarantees: when this returns, the game window is in foreground.
     */
    suspend fun acknowledgeExecution() {
        focusManager.releaseFocusToGame()
        _state.value = LeaderState.Idle
    }
}
```

The consumption pattern:
```kotlin
leaderKeyDetector.state
    .filterIsInstance<LeaderState.Executing>()
    .collect { exec ->
        leaderKeyDetector.acknowledgeExecution()  // suspends: releases focus, then Idle
        // Game window is now guaranteed to be in foreground
        val macro = macrosByTriggerKey[exec.matchedCommand] ?: return@collect
        macro.run()
    }
```

**The ordering guarantee:**
1. State becomes `Executing` → overlay still has focus, can show "Running..." briefly.
2. Consumer sees `Executing`, calls `acknowledgeExecution()`.
3. Inside: `focusManager.releaseFocusToGame()` calls `SetForegroundWindow(gameHwnd)` and suspends until the focus transfer is confirmed (e.g., poll `GetForegroundWindow()` briefly).
4. Inside: state transitions to `Idle`. Overlay observes this for rendering (hide window), but focus is already released — no race.
5. `acknowledgeExecution()` returns. Consumer calls `macro.run()` with game guaranteed in foreground.

**Why `FocusManager` is on the detector, not the overlay:** Focus release is a precondition for safe macro execution — it's part of the execution handshake, not a rendering concern. The overlay still observes `state` for rendering (what to show/hide), but the *ordering-critical* focus transfer lives in the imperative path. `FocusManager` is a simple interface that the overlay module implements but the detector calls through, keeping the dependency inverted.

**Why this is better than the two-flow approach:**
- Single `StateFlow` — one source of truth, one type to reason about. No need to understand which flow is an Event vs Behavior.
- No `SharedFlow` with its replay/buffer semantics to configure correctly.
- The `acknowledgeExecution()` handshake prevents both missed events (detector stays in `Executing` until acknowledged) and focus races (focus released before returning).
- The overlay still renders purely from `state`.

**Tradeoff:** `acknowledgeExecution()` is imperative, which slightly contradicts the "no imperative calls" goal. But it's a single, well-scoped suspend call at one site (main), and it solves a real ordering problem that pure observation can't.

### Self-describing macros: `MacroRegistration`

Introduce a data class that bundles everything about a macro into one self-describing unit:

```kotlin
data class MacroRegistration(
    val triggerKey: String,
    val displayName: String,
    val category: String,
    val game: WhichGame,
    val description: String = "",          // longer description for confirmation
    val macroDef: (MacroDefsComponent) -> MacroDef,
)
```

This replaces the current `MacroMapping` in `MainV2.kt`. The key difference is that `description` is now a first-class field. It lives in the centralized macro list — the one place where trigger keys are assigned (as they already are today in `macroMapping`).

**Programmatic descriptions for craft macros:** The `CraftDecisionMakerV2` subclasses have structured `Args` (e.g., `Poe2AugAnnulMagicItem.Args` lists `highPriorityMods`, `Poe2ChaoOnTablet.Args` lists `groups` with `goodMods`). We can add a `describe(): String` method to the DM or its args:
```kotlin
// Example for Poe2AugAnnulMagicItem
fun Poe2AugAnnulMagicItem.describe(): String {
    val modNames = args.highPriorityMods.map { it.displayName }
    return "Aug/annul magic item until ${args.desiredHpModCount} of: ${modNames.joinToString()}"
}
```
This is opt-in — not all macros need generated descriptions. Simple macros (e.g., "Print mouse pos") can use a hand-written string.

### Trigger key assignment

Currently, `macroMapping` in `MainV2.kt` is already the single source of trigger keys — this is good. The old code in `src/` (the non-modularized code) scatters keys across `poe.kt`, `poecraft.kt`, etc., but that's legacy.

Options considered for auto-assignment:
1. **Sequential numbering** (01, 02, 03, ...) — simple, stable if you only append. But inserting a new macro shifts everything.
2. **Category-prefixed** (C1, C2 for crafting; U1, U2 for utility) — meaningful, but requires category alphabet.
3. **Hash-based** — deterministic from macro name, but not human-memorable.

**Recommendation: Keep manual assignment in one place, but validate.** The current `macroMapping` list approach is already centralized. Add a validation step at startup that checks for duplicate keys, key length, and optionally warns about gaps. Auto-assignment adds complexity without strong benefit when there are only ~10 macros.

### OverlayOutput → observe StateFlow + manage focus

Replace the imperative `show`/`hide` interface. The overlay observes `StateFlow<LeaderState>` and manages window focus:

```kotlin
interface OverlayOutput {
    fun start() {}

    /**
     * Bind the overlay to the leader key state and the macro list.
     * The overlay re-renders reactively and manages focus based on state.
     */
    fun bind(
        macros: List<MacroRegistration>,
        leaderState: StateFlow<LeaderState>,
    )
}
```

State-driven rendering and focus:
- `Idle` → window hidden, focus released to game
- `Picking(collectedKeys)` → window visible, **overlay grabs focus**, show macro list with prefix highlighting/dimming
- `Confirming(matchedCommand)` → show the matched macro's `description` with countdown, overlay still has focus (Enter to confirm early, Escape to cancel)
- `Executing(matchedCommand)` → brief "Running..." indicator, focus released back to game

This eliminates `show(entries)`, `hide()`, and any future imperative methods. The overlay is fully driven by the state flow, including its own focus lifecycle.

### Decentralized `isEnabled` → centralized state observation

The current `isEnabled(command): Flow<Boolean>` design creates one flow per command, each with its own state machine. In `MainV2.kt`, the loop `for (mmap in macroMapping) { ... leaderKeyDetector.isEnabled(mmap.triggerKey).collect ... }` launches N coroutines.

Replace with a single collector:
```kotlin
// In main:
leaderKeyDetector.state
    .filterIsInstance<LeaderState.Executing>()
    .collect { exec ->
        leaderKeyDetector.acknowledgeExecution()  // suspends: focus → game, then Idle
        // Game is guaranteed in foreground here
        val macro = macrosByTriggerKey[exec.matchedCommand] ?: return@collect
        macro.run()
    }
```

One collector instead of N. The detector handles command matching internally and the state machine drives everything.

## Changes summary

| File / Area | What changes |
|---|---|
| `LeaderKeyDetector` | Remove callbacks. Add `CoroutineScope` + `FocusManager`. Expose `state: StateFlow<LeaderState>` + `suspend acknowledgeExecution()`. Remove `isEnabled()`, add `register()`. Single internal state machine for all commands. |
| `LeaderState` | New sealed class: `Idle`, `Picking(collectedKeys)`, `Confirming(matchedCommand)`, `Executing(matchedCommand)`. |
| `OverlayOutput` | Replace `show`/`hide` with `bind(macros, leaderState)`. Add focus management (`requestFocus`/`releaseFocus` or driven by state). |
| `ComposeOverlayWindow` | Collect `leaderState`, render list/confirmation view reactively. Toggle `focusable` and call `SetForegroundWindow` based on state. |
| `MacroMapping` → `MacroRegistration` | Add `description` field. Keep trigger key assignment manual and centralized. |
| `MainV2.kt` | Register all macros with `leaderKeyDetector.register()`. Collect `state.filterIsInstance<Executing>()`. Call `acknowledgeExecution()` + run macro. Pass `leaderState` to overlay via `bind()`. |
| `MacroModule` (DI) | Wire `CoroutineScope` into `LeaderKeyDetector`. Remove overlay callbacks. |
| `FocusManager` | New `fun interface` in `macro-core`. Implemented in `macro-overlay` (or `macro-app`) using Win32 `SetForegroundWindow`. Saves/restores previous foreground HWND. Injected into `LeaderKeyDetector`. |
| Win32 bindings | Add `SetForegroundWindow` JNA binding. |
| Craft DMs (optional) | Add `describe()` extension funs for structured craft descriptions. |
| Tests | Update `LeaderKeyDetectorTest` to use `state` flow + `acknowledgeExecution()`. Add timeout, confirmation, and cancel tests. |

## Acceptance criteria

- [ ] Overlay hides within ~100ms of the logical timeout (no waiting for next key)
- [ ] Each command key press updates the overlay to show which macros still match (collected prefix highlight + dimming)
- [ ] After a command matches, overlay shows macro description for a confirmation period before executing
- [ ] During `Picking` and `Confirming`, overlay has focus — keypresses don't reach the game
- [ ] Enter confirms during `Confirming`; Escape cancels and returns to `Idle`
- [ ] Focus returns to game window before macro execution starts
- [ ] Tests cover: timeout-driven hide, confirmation countdown, cancel during confirmation, key prefix feedback
- [ ] No imperative callbacks on `LeaderKeyDetector` — all state via single `StateFlow` (no separate Event flow)
- [ ] Trigger keys assigned in exactly one place (`macroMapping`/`MacroRegistration` list in `MainV2.kt`)
- [ ] Craft macros have programmatic descriptions derived from their decision maker args

## Open questions (resolved)

1. **Confirmation interaction:** → Resolved: Enter to confirm early, countdown to auto-confirm. Overlay steals focus so Enter doesn't reach the game.
2. **Cancel key:** → Resolved: Escape to cancel. No game conflict because overlay has focus during `Picking`/`Confirming`. Focus grab happens right at `Picking` (i.e., right after Alt+X), so even command digit keys don't reach the game.
3. **Auto-assignment:** → Resolved: Manual + validation for now.

## Review comments v2

Another conceptually important (but maybe not as important in concrete implementations) is on flow & compose's reactive system.
- Functional reactive programming (FRP) systems distinguish between Events (discrete signals that happen on discrete times) and Behaviors (continuous values that may change over time).
- Kotlin Flow and friends merge FRP Events and Behaviors, but the blurred boundary can make things harder to model mentally. For example, `LeaderKeyDetector.state: StateFlow<LeaderState>` is Behavior because it's a continuous UI state and will always have a value. OTOH, `LeaderKeyDetector.executions: SharedState<String>` is an Event, since macro executions are discrete signals that happen at certain time.

I think the ways that they are consumed in this doc make sense (e.g. executions is collected to run macros). However, it feels to me that the consumption site have to understand the semantics of the flows to correctly handle them (slightly breaking abstraction). What do you think?

**Response:** Good observation. The revised design eliminates the separate `executions: SharedFlow` entirely. Instead, execution is encoded as a state (`Executing`) in the single `StateFlow<LeaderState>`. The `acknowledgeExecution()` handshake prevents the conflation problem (`StateFlow` would normally drop `Executing` if `Idle` is emitted before the collector runs — but we never auto-transition, so `Executing` persists until the consumer explicitly acknowledges it). This keeps everything as one Behavior with no hidden Event semantics. The tradeoff is one imperative call (`acknowledgeExecution()`), but it's a single well-scoped call at one site, not a proliferating interface. See the "Event vs Behavior" section above for the full rationale.

## Follow-up: overlay during macro execution

See `task/attachment/overlay-while-crafting.md`. The idea is to keep the overlay visible *during* macro execution to show live status (currencies used, time elapsed, etc.). This is orthogonal to the current task but builds on the same overlay infrastructure. Key platform concerns:
- **Click-through**: The overlay must not intercept mouse clicks during macro execution (`WS_EX_TRANSPARENT` extended window style via JNA).
- **Screen capture**: `java.awt.Robot` captures the overlay along with the game. Macros that read pixels (e.g., item parsing) would need per-window capture (Windows Graphics Capture API) to exclude the overlay. This is non-trivial — see the attachment for details.

These can be addressed as a separate task after the current UX improvements land.

## Review comments v1

(Preserved for history)

I'm rethinking the leader key interface, the list of macros, how they interact with the overlay. I'll try to classify my thoughts into: goal (can be user facing or dev facing), invariant (something I believe is always true so our design can depend on), explore (I don't fully know what I want yet)
* goal(dev): avoid imperative interface or callbacks if possible. Currently, the overlayOutput, LeaderKey's start/end callbacks can be hard to maintain if we keep extending them.
  + explore: Brainstorm this. My instinct is maybe model the leader key state with a StateFlow. But feel free to add your idea.
* invariant(dev): At a certain time after program starts, the list of macros is known and immutable.
* goal(dev): Each macro should describe itself: concise description of what it does (to be shown in overlay's list view), which game it applies to, and optionally a longer description on the internal steps (e.g. if it's a crafting macro)
  + explore: maybe we can programmatically generate longer description from craft decision maker subclass + args
* explore: The trigger key is currently manually assigned, but it doesn't have to.
  + goal(user): trigger keys should be short (ideally meaningful, but not a must). They should also be mostly stable for existing macros when we add new ones.
  + goal(dev): it would be good to avoid having to manually assign trigger keys. If we must assign trigger keys manually, do that in one place (instead of scattering around multiple files -- that's too hard to maintain)
* explore(dev): The leader key interface is currently decentralized (see isEnabled method). If this makes the overlay interaction awkward, consider changing that.
* goal(user): once a leader key macro is selected to trigger, show its detailed description in overlay for several seconds, before actually starting. This gives user a chance to double check the action (and cancel if they don't want to proceed)