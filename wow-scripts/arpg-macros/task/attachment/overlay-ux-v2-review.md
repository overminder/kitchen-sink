Review of task/overlay-ux-v2.md

Overall impression

Well-structured design doc. The component boundaries are clear, the "what it knows / doesn't know"
framing keeps responsibilities sharp, and the communication diagram is easy to follow. The phased rollout
is sensible — each phase delivers user-visible value and the later phases (G7–G9) are cleanly deferred.

Strengths

1. Single StateFlow<LeaderState> replacing callbacks + per-command flows. This is the right call. The
   current isEnabled(command): Flow<Boolean> plus onLeaderActivated/onLeaderDeactivated callbacks in the
   existing LeaderKeyDetector is hard to extend and test. A single sealed-class state flow fixes both.
2. Overlay as a pure function of observed state. The current OverlayOutput interface
   (show(entries)/hide()) is imperative and tightly coupled to the 2-state (visible/hidden) model. Making it
   a renderer of LeaderState + execution status is a clean upgrade path.
3. acknowledgeExecution() as the sole imperative handshake. Good that you explicitly called out why this
   can't be reactive (focus must return before macro starts, and two independent observers can't coordinate
   ordering). The doc doesn't overuse this escape hatch.
4. Execution status as a separate observable (G8). Keeping detector state and macro runtime status on
   separate lifecycles is correct — they have different owners and different lifetimes.

Issues and questions

1. Executing state seems unnecessary — or its lifecycle is unclear

The detector goes Confirming → Executing, then the coordinator observes Executing, releases focus, calls
acknowledgeExecution() which transitions to Idle, then runs the macro.

Executing is a transient state that exists only so the coordinator can observe it and do the focus
handoff. But: if the coordinator is the only consumer of Executing, and it immediately acknowledges it,
this is really just a synchronous signal — not an observable state. Consider whether a simpler model
works:

- Confirmation timer expires (or user confirms) → detector emits a one-shot event (e.g.,
  Channel<MatchedCommand>) → coordinator receives it, releases focus, runs macro → detector goes back to
  Idle.

This avoids a state that's never meaningfully "observed" by the overlay (the doc says the overlay shows a
brief "starting..." indicator, but is that worth a whole state?).

Alternatively, if you want to keep Executing for the overlay's "starting..." indicator, clarify: how long
does Executing last? Is it until acknowledgeExecution() is called (milliseconds), or is there an
intentional delay?

2. Confirmation flow: who drives the confirm/cancel input?

The doc says during Confirming, the user can "confirm (or wait) to execute, or cancel." But:

- In Phase 2 (before G7/focus interception), keypresses still go to the game. How does the user confirm
  or cancel? Is confirmation just "wait for the countdown to finish" and cancel is "press any non-matching
  key" or "press Escape"?
- In Phase 3 (with G7), the overlay has focus so it can capture Enter/Escape. But Phase 2 doesn't have
  this.

The doc should clarify the Phase 2 confirmation UX — it's probably "auto-confirm after countdown, cancel
by pressing leader key or any key" but it's not stated.

3. Trigger key assignment (G6): where exactly?

G6 says "trigger keys are assigned in exactly one place." Currently they're in MainV2.kt's macroMapping
list. The doc proposes a MacroRegistry but doesn't say where the trigger-key-to-macro mapping is defined.
Is it:

- (a) Each macro declares its own trigger key in a registration DSL?
- (b) A central list (like today's macroMapping) that pairs trigger keys with macro factories?

Both are "one place" but they're architecturally different. (b) is what exists today and is simpler. If
(a), the doc should say so explicitly.

4. Detector knows "registered command strings" but not macros — how does the coordinator map back?

The detector only knows command strings (e.g., "11", "12"). When it emits Confirming(command = "11"), the
coordinator needs to look up which macro to run. This presumably goes through the MacroRegistry, but the
mapping from command string → macro entry isn't described. It's obvious, but worth a one-liner in the
Coordinator section.

5. Focus interception (G7) timing concern

"When the detector enters Picking, the overlay (or coordinator) asks the focus manager to bring the
overlay to the foreground."

SetForegroundWindow on Windows has restrictions — a background process can't just steal focus. The
typical workarounds (AttachThreadInput, alt-key simulation, AllowSetForegroundWindow) are non-trivial and
flaky. The doc hand-waves this as a "wiring detail." Given that this is the riskiest platform-specific
piece, it might be worth a sentence acknowledging the Win32 constraint and the planned workaround. Even a
"we'll use the AllowSetForegroundWindow / keyboard hook approach — details in implementation" would
help.

6. Phase 5 (G9) — screen capture exclusion

"Per-window capture (Windows Graphics Capture API)"

The current screen capture uses Robot.createScreenCapture() (or equivalent). Switching to Windows
Graphics Capture API is a significant change — it's a WinRT API, not a simple JNA binding. The doc
correctly flags this as "the most platform-heavy phase" but it might be worth noting whether the current
BitBlt/Robot-based capture can be kept as a fallback, or if G9 requires a full capture pipeline
replacement.

Minor nits

- The communication diagram shows Overlay reading from Macro Registry directly, but the text says the
  overlay knows the registry "for rendering labels, descriptions, categories." If the overlay observes
  LeaderState which carries the matched command string, the overlay still needs the registry to resolve
  that string to display metadata. Consider whether LeaderState.Picking / Confirming should carry the
  resolved MacroDescriptor directly instead of just the command string — this would keep the overlay from
  needing to know the registry at all.
- "Behavior" is used as a term for the observable state pattern (RxJava terminology). Since the codebase
  uses Kotlin coroutines, the actual type is StateFlow. The doc mentions StateFlow in the implementation
  phases but uses "Behavior" in the architecture sections — pick one for consistency.

Verdict

The design is sound. The main thing I'd want clarified before implementation is issue #2 (Phase 2
confirmation UX without focus interception) and issue #1 (whether Executing earns its keep as a full
state). The rest are "nice to clarify" but won't block implementation.