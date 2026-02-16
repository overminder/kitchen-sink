Review: overlay-ux-v3.md

Overall Assessment

Strong design doc. The core insight — "Phase 0 proved focus switching works, so just use a GUI" — is
well-motivated and correctly simplifies the architecture. The elimination of the command-sequence state
machine is the right call. The doc reads clearly, the v2→v3 diff is well-explained, and the phasing is
reasonable.

Below are specific observations, grouped by concern.

---
1. The interaction flow has a race condition risk

Lines 169-185, the coordinator pseudocode:

focusManager.stealFocusToOverlay()
val selection = overlay.awaitSelection()   // suspends

What if stealFocus succeeds but the Compose window hasn't rendered yet? The overlay needs to be both
focused and showing content before the user can interact. There's a potential gap where the window has OS
focus but hasn't composed its first frame. Consider whether awaitSelection() should internally gate on
"first frame rendered" or whether stealFocus should wait for the window to be ready.

This is especially relevant since Phase 0 measured ~15ms steal latency — Compose first-frame render is
likely slower than that.

---
2. Focus return timing on confirmation countdown

Lines 86-88:

7. Coordinator tells Focus Manager: return focus to game
8. Macro runs

The coordinator returns focus then runs the macro. But the confirmation countdown (step 6) auto-confirms
after N seconds. If the user walks away during the countdown, focus returns to the game and the macro
starts — which is the intended behavior. Good.

However: what if the game has gone to background (alt-tabbed away) during the countdown?
returnFocusToGame() would need to remember which window was the game, not just "the previous foreground
window." The doc doesn't specify whether the Focus Manager snapshots the game HWND on steal or uses a
more fragile heuristic. The Phase 0 PoC code stores the previous HWND — worth calling out explicitly in
the doc that this is the design.

---
3. Open state might be too informal

Lines 50-51:

Open may not even need to be a shared state — it could just be "the overlay window is visible and
focused."

I'd push back slightly. Having an explicit Open state in the coordinator is cheap and useful for:
- Guard against re-entrancy: What if Alt+X is pressed while already open? The current pseudocode handles
this via if (macroRunning) return but doesn't guard against if (overlayOpen) return.
- Timeout ownership: Who manages the inactivity timeout (line 94)? If it's the overlay internally, fine.
But if the coordinator needs to enforce it, it needs to know the overlay is open.

Recommend: keep Open as an explicit coordinator state. It's one enum value.

---
4. Missing: what happens to the global keyboard hook while the overlay is focused?

The existing LeaderKeyDetector consumes raw keyboard input via a global hook. In v3, when the overlay is
focused, keyboard events go to both:
- The Compose window (normal Swing/AWT key events)
- The global hook (which feeds the leader key listener)

If the user presses Escape in the overlay, the global hook also sees it. If 1 is pressed to select a
macro, the global hook also sees 1. The doc should clarify: does the leader key listener pause/detach
while the overlay is open? Or does the coordinator simply ignore onLeaderKey() signals during Open state?
Either works, but it should be stated.

---
5. Open question #2 (confirmation UX) — recommendation

Line 273:

Alternative: clicking a button shows a tooltip/popover with the description, and a second click confirms.

I'd suggest the separate confirmation view (the current sketch) for Phase 2. Reasons:
- Tooltip/popover interaction is fiddly — hover timing, accidental dismissal, positioning near screen
edges.
- A full view swap is simpler to implement in Compose and easier to test.
- The countdown timer needs real estate that a tooltip struggles to provide.

The "double-click to confirm" pattern could be a future optimization once the basic flow is proven.

---
6. Open question #4 (game-specific filtering) — recommendation

Line 277:

Should the overlay auto-filter based on which game is currently running?

Yes, and the data is cheap to get. Before stealing focus, the coordinator already has the foreground
window HWND (to snapshot for returnFocusToGame). Checking the window title against known game titles
(Path of Exile, Path of Exile 2) is trivial. Pass the detected game to the overlay so it filters the
list. Show a small indicator ("POE2 detected") so the user knows filtering is active.

This is low-effort, high-UX-impact. Consider including it in Phase 1 rather than deferring.

---
7. Minor: the Coordinator pseudocode is blocking

Lines 169-185 show onLeaderKey() as a suspend function that blocks until the entire flow completes. This
means:
- The coordinator coroutine is occupied for the full duration of overlay interaction + macro execution.
- If macroEngine.run(macro) is long-running, the coordinator can't process new leader key events until it
finishes.

The if (macroRunning) return guard suggests awareness of this, but macroRunning would need to be set
before run(macro) returns. The pseudocode implies run(macro) is itself blocking. Consider clarifying:
does macroEngine.run(macro) suspend until the macro finishes, or does it launch-and-return? If it
suspends, the macroRunning flag is redundant (the coordinator is already occupied). If it launches, the
flag is needed and must be an AtomicBoolean or similar.

Either design works — just be explicit about which one.

---
8. Missing from the doc: overlay window properties

The current overlay (ComposeOverlayWindow.kt) is configured as:
- Non-focusable (isFocusableWindow = false)
- Always-on-top
- Transparent/undecorated

v3 requires the overlay to be focusable (that's the whole point). The doc should note that the overlay
window configuration flips from "passive, non-focusable, click-through" to "interactive, focusable,
captures input." This is a significant change to the Compose window setup and worth a sentence
acknowledging it, since the existing code explicitly sets isFocusableWindow = false.

---
9. Nit: "Communication" diagram arrows

Lines 194-207: the ASCII diagram shows Focus Manager appearing twice on the right side, which is a bit
confusing. Consider collapsing to one box or labeling the arrows more clearly. Minor readability thing.

---
Summary

Area: Core insight (CLI → GUI)
Verdict: Sound. Well-motivated by Phase 0 results.
────────────────────────────────────────
Area: Complexity reduction
Verdict: Real. Eliminating the state machine is correct.
────────────────────────────────────────
Area: Interaction flow
Verdict: Correct, with caveats on render-readiness timing.
────────────────────────────────────────
Area: Component design
Verdict: Clean. Coordinator pseudocode is easy to follow.
────────────────────────────────────────
Area: Phasing
Verdict: Reasonable. Phase 1 scope is achievable.
────────────────────────────────────────
Area: Gaps
Verdict: Focus return HWND snapshotting, global hook interaction during Open, overlay window focusability

change, macroRunning semantics.

The doc is in good shape. The gaps above are things to decide and document before starting Phase 1, not
blockers to the overall approach.