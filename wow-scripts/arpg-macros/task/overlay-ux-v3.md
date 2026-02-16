# Overlay UX v3 — GUI-first interaction paradigm

Status: todo
Dependencies: none
Supersedes: overlay-ux-v2.md (kept for history and component-level design notes)

## The insight

Phase 0 (an exploration from overlay-ux-v2.md) proved that focus switching is fast (~15ms) and reliable (12/12 against POE2 borderless). This changes the design space fundamentally.

In v2, the overlay was a **passive display**: it showed which keys to press, but all interaction happened through the leader key detector's command-sequence state machine. The user had to memorize trigger key sequences ("13" = tablet rolling), type them blind, and hope they got it right. The overlay helped by showing available options, but the interaction was still "type a code."

With reliable focus stealing, the overlay can become the **primary interaction surface**. Once the leader key is pressed, the overlay grabs focus and becomes a normal interactive window. The user sees buttons, clicks one (or presses a single obvious key), and the macro starts. No memorized sequences. No prefix matching. No multi-character commands.

This is the difference between a CLI and a GUI. v2 was designing a better CLI (with autocomplete and hints). v3 says: just use a GUI.

## What changes from v2

### Eliminated: command-sequence state machine

v2's `LeaderKeyDetector` was a complex state machine:
```
Idle → Picking(collectedKeys) → Confirming(matchedCommand) → Idle
```
It buffered keypresses, matched prefixes, dimmed unreachable options, handled multi-character commands, and managed timeouts on partial sequences.

v3 replaces this with: **leader key opens the GUI, GUI handles selection.** The leader key detector becomes trivial — it just detects Alt+X and signals "open." Everything after that is ordinary GUI interaction on a focused window.

### Eliminated: trigger key assignment

No more `"13"` → tablet rolling. No trigger keys at all in the command-sequence sense. Macros identify themselves by name, category, and description — the GUI renders them as a list of buttons. The user picks visually, not from memory.

Single-key accelerators can still exist (press `1` to select the first item, `t` to jump to the "Tablet" category) but they're **discoverable shortcuts** shown in the GUI, not the primary interaction. Nobody needs to memorize them.

### Simplified: leader state

v2 state:
```kotlin
Idle | Picking(collectedKeys) | Confirming(matchedCommand)
```

v3 state:
```kotlin
Idle | Open | MacroRunning
```

- **Idle**: overlay hidden, leader key listening.
- **Open**: overlay visible and focused, showing the macro list. User browses and selects. Confirmation is an overlay-internal concern — from the coordinator's perspective this is still `Open`.
- **MacroRunning**: macro is executing. Leader key presses are ignored.

`Open` is an explicit coordinator state — not just "the window is visible." This enables the re-entrancy guard: if Alt+X fires while the overlay is already open, the coordinator ignores it.

### Preserved from v2

These v2 components survive mostly unchanged:

| Component | v2 role | v3 role |
|-----------|---------|---------|
| **Focus Manager** | Steal/return focus around picking | Same — steal on leader key, return before macro run |
| **Macro Registry** | Immutable list of macro descriptors | Same — source of truth for what the GUI renders |
| **Coordinator** | Wire components, sequence focus + execution | Same — but simpler (no `awaitExecution()` handshake with detector) |
| **Macro Execution Engine** | Run macros, report status | Unchanged |
| **Self-describing macros** | `MacroRegistration` with name, category, description | Unchanged — now even more important since the GUI shows descriptions directly |

### Changed: who owns interaction

v2: Keyboard → Leader Key Detector (state machine) → Overlay (passive renderer)

v3: Keyboard → Leader Key (just Alt+X) → Overlay (focused, interactive) → Coordinator → Macro

The leader key detector shrinks from a complex state machine to essentially a hotkey listener. The overlay promotes from passive renderer to interactive controller.

## Interaction flow

```
1. User presses Alt+X
2. Coordinator detects leader key, checks state is Idle
3. Coordinator captures ActivationContext (game HWND, window title, cursor position)
4. Coordinator tells Focus Manager: steal focus to overlay
5. Overlay appears with macro list (filtered by ActivationContext, grouped by category)
   - Overlay gates on first-frame render before accepting input
6. User picks a macro:
   - Click a button, OR
   - Arrow keys + Enter, OR
   - Press a displayed shortcut key (e.g., first letter)
7. Overlay shows confirmation view (macro description + countdown)
   - Enter / click "Go" to confirm immediately
   - Escape to cancel → overlay hides, focus returns to game
   - Countdown auto-confirms
8. Coordinator tells Focus Manager: return focus to game (using snapshotted HWND)
9. Macro runs
```

Cancel at any point (step 6 or 7): Escape or clicking outside the overlay → hides, returns focus, no action.

Timeout: if the user doesn't interact within N seconds after step 5, the overlay hides automatically.

## GUI sketch

```
┌─────────────────────────────────────┐
│  Select Macro              [Esc ×]  │
│─────────────────────────────────────│
│                                     │
│  Crafting                           │
│  ┌─────────────────────────────────┐│
│  │ 1  Map rolling         POE1/2  ││
│  │ 2  Craft rolling (v2)  POE2    ││
│  │ 3  Tablet rolling      POE2    ││
│  │ 4  Craft rolling       POE1/2  ││
│  └─────────────────────────────────┘│
│                                     │
│  Utility                            │
│  ┌─────────────────────────────────┐│
│  │ 5  Print mouse pos     Any     ││
│  │ 6  Parse & print item  Any     ││
│  │ 7  Sort in stash       POE1/2  ││
│  └─────────────────────────────────┘│
│                                     │
└─────────────────────────────────────┘
```

The numbers (`1`, `2`, ...) are auto-assigned shortcut keys, displayed for discoverability. They're positional, not semantic — you don't need to memorize them because you're looking at the list.

The confirmation view replaces this content:
```
┌─────────────────────────────────────┐
│  Tablet rolling                     │
│─────────────────────────────────────│
│                                     │
│  Chaos spam on tablets.             │
│  Target: Abyss groups with          │
│  specific good mods.                │
│                                     │
│  Starting in 3s...                  │
│                                     │
│  [Go now]            [Cancel]       │
│                                     │
└─────────────────────────────────────┘
```

## Architecture

### Components

**1. Leader Key Listener** (was: Leader Key Detector)

Drastically simplified. Just a hotkey listener for Alt+X. When detected, signals the coordinator. No state machine, no command parsing, no timer management.

The global keyboard hook remains active while the overlay is focused — both the Compose window and the hook see key events. This is fine: the coordinator's state guard (`if (state != Idle) return`) ensures leader key signals during Open/MacroRunning states are ignored. No need to pause or detach the hook.

Could be as simple as:
```kotlin
keyboardInput.keyReleases()
    .filter { it.matchesChord(leaderChord) }
    .collect { coordinator.onLeaderKey() }
```

**2. Overlay (interactive)**

Promoted from passive renderer to interactive GUI. Compose Desktop window that:
- Renders the macro list from the Macro Registry, filtered by `ActivationContext`
- Handles mouse clicks, keyboard navigation, shortcut keys
- Manages its own UI state (which item is focused, scroll position, etc.)
- Emits a selection event when the user picks a macro
- Owns the confirmation view (countdown, cancel, confirm)
- Gates on first-frame render before accepting input (avoids race where the window has OS focus but hasn't painted yet — Compose first-frame is likely slower than the ~15ms focus steal)

**Window configuration change**: The current overlay is non-focusable (`isFocusableWindow = false`), always-on-top, and click-through. v3 flips this to focusable, interactive, and input-capturing. This is a significant change to the Compose window setup.

The overlay's internal state is UI-local — it doesn't need to be a shared `StateFlow`. The coordinator only cares about two outputs: "user selected macro X" and "user cancelled."

**3. Coordinator**

Sequences the flow:
```kotlin
// State: Idle | Open | MacroRunning
fun onLeaderKey() {
    if (state != Idle) return   // ignore while overlay is open or macro is running

    val context = captureActivationContext()   // HWND, window title, cursor pos
    state = Open
    focusManager.stealFocusToOverlay(context.gameWindow)
    val selection = overlay.awaitSelection(context)   // gates on first-frame render

    when (selection) {
        is Cancel -> {
            focusManager.returnFocusToGame(context.gameWindow)
        }
        is Confirmed(macro) -> {
            focusManager.returnFocusToGame(context.gameWindow)
            state = MacroRunning
            macroEngine.run(macro, context)   // suspends until macro completes
        }
    }
    state = Idle
}
```

The coordinator coroutine is occupied for the full duration (overlay interaction + macro execution). This is intentional — the sequential structure keeps the logic simple, and the `state` guard prevents re-entrancy. `onLeaderKey()` is a no-op when not Idle.

Focus return uses the snapshotted `context.gameWindow` HWND, not "whatever is currently in the foreground." This is reliable even if the user alt-tabs during the confirmation countdown.

**4. ActivationContext**

Captured by the coordinator before stealing focus. Provides context for filtering and execution:
```kotlin
data class ActivationContext(
    val gameWindow: HWND,         // snapshotted for reliable focus return
    val gameTitle: String,        // detected game (POE1/POE2/unknown) → overlay filtering
    val cursorPosition: Point,    // spatial context → macro-specific behavior
)
```

The game title drives macro list filtering (only show POE2 macros when POE2 is running). Cursor position is passed through to macros that can use it — e.g., a crafting macro can target the item under the cursor instead of requiring the user to position it after macro start.

**5. Focus Manager, Macro Registry, Macro Execution Engine** — unchanged from v2.

### Communication

```
Keyboard ──Alt+X──▶ Leader Key Listener ──signal──▶ Coordinator
                                                         │
                                        captureContext()  │  (HWND, title, cursor)
                                              │          │
                                    stealFocus(HWND)     │   returnFocus(HWND)
                                              ▼          │        ▼
                                         Focus Manager ◀─┘──▶ Focus Manager
                                                         │
                                  awaitSelection(ctx)    │   run(macro, ctx)
                                              ▼          │        ▼
                                        Overlay (GUI) ◀──┘──▶ Macro Engine
                                              │
                                              ▼
                                       Macro Registry (read-only)
```

Data flow is mostly imperative suspend calls (coordinator → overlay, coordinator → focus manager), not reactive observation. This is appropriate because the interaction is a linear sequence, not a continuous stream. The coordinator `suspend`s through the whole flow — it's essentially a sequential script.

The one place where reactive observation still matters: **macro execution status** (G8). While a macro runs, the overlay can observe execution progress as a `StateFlow` and render live status. But that's a later concern.

## What about keyboard-only usage?

The GUI doesn't prevent efficient keyboard use — it enables it. With a focused overlay window:

- **Number keys** (`1`-`9`): select by position (auto-assigned, shown in UI)
- **Arrow keys + Enter**: navigate and confirm
- **Escape**: cancel
- **Type to filter**: if the macro list grows large, typing narrows the list (fuzzy search)

This is strictly better than v2's trigger key sequences because:
1. You can see what you're selecting while you select it.
2. Shortcuts are positional and displayed — no memorization.
3. The same shortcuts work without learning them (just read the screen).
4. Mouse is available as a fallback.

## Goals mapping

| v2 Goal | v3 Status |
|---------|-----------|
| G1 (picker with prefix feedback) | **Replaced** — full GUI picker with buttons, no prefix matching needed |
| G2 (confirmation with description) | **Kept** — confirmation view with description and countdown |
| G3 (proactive timeout) | **Kept** — overlay hides on inactivity timeout |
| G4 (observable state, not callbacks) | **Relaxed** — overlay manages its own UI state; coordinator uses suspend calls. Observable state still used for macro execution status (G8). |
| G5 (self-describing macros) | **Kept** — macro registry with descriptions, even more visible in GUI |
| G6 (trigger keys in one place) | **Eliminated** — no trigger keys to assign |
| G7 (focus interception) | **Kept and promoted** — focus interception is now the foundation, not a later-phase enhancement |
| G8 (live execution status) | **Kept** — future phase |
| G9 (screen capture exclusion) | **Kept** — future phase |

## Implementation phases

### Phase 1: Interactive overlay MVP

- Leader key listener (simplified from v2's detector)
- Focus Manager (reuse phase 0 PoC logic: `SendInput` Alt + `SetForegroundWindow`)
- ActivationContext capture (game HWND, window title, cursor position)
- Compose Desktop overlay window: macro list with clickable buttons, keyboard shortcuts, grouped by category, filtered by detected game
- Coordinator wiring: Alt+X → capture context → steal focus → await selection → return focus → run macro
- Cancel via Escape, timeout on inactivity

This is one phase where v2 had three (phases 1-3) because focus interception is no longer a separate concern — it's baked in from the start.

### Phase 2: Confirmation step

- After selection, show macro description + countdown before executing
- Enter / click to confirm immediately, Escape to cancel
- Auto-confirm after countdown

### Phase 3: Live execution status (G8)

- Overlay shows progress during macro execution (click-through mode)
- Macro engine reports status as `StateFlow`

### Phase 4: Screen capture exclusion (G9)

- Per-window capture so macros don't see the overlay in pixel reads

## Resolved decisions

Formerly open questions, resolved during design review.

1. **Overlay framework**: Compose Desktop. Already a dependency, fits the coroutine-heavy style.

2. **Confirmation UX**: Separate confirmation view (full view swap, not tooltip/popover). Optimize for muscle memory — cancel/confirm controls stay in consistent positions across different macro selections. Start simple, iterate after prototyping.

3. **Overlay position and size**: Prototype and iterate. Start with the existing ~320x400dp top-left placement, adjust based on how the GUI feels in practice.

4. **Activation context**: The coordinator captures an `ActivationContext` before stealing focus (see Architecture). This includes game HWND (for reliable focus return + game filtering), window title, and cursor position. Cursor position enables context-sensitive behavior — e.g., if the cursor is on an item, the overlay can prioritize single-item crafting macros over batch-crafting.