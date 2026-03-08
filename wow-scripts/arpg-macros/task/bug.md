# Issues that I found

Status: todo
Dependencies: none

## Description

### Issue 1

Not exactly a bug as in "not working as expected", but rather a UX feedback.

- What I see: BgMacroStatusTracker's overlay is in the top left corner of the screen, blocking some of the in-game status.
- What I expect: the bottom-left point of the statusline should be (315, 1212). This is an empty space in game.
 
### Bug 2

- What I see: PrintMousePosMacro doesn't actually print the mouse pos until I move the mouse a bit.
- What I expect: PrintMousePosMacro should immediately print the mouse pos
- My investigation:
  + PrintMousePosMacro.prepare calls stateIn which waits until the first value of the mouse pos to be available. The intention is that MacroDef.prepare is called exactly once during app startup time to initialize each macro's internal states, while MacroDef.Prepared.run is called for each "session" (e.g. each time user triggers the macro).
  + MacroDef.prepare however is actually called right before the macro runs in MacroRunnerImpl

### Bug 3

- What I see: In POE1, when AutoFlaskMacro was running recently, and I press the leader key to launch the full overlay (that lists all the available macros): If I press 6 (corresponds to the "Dump bag to stash" macro), nothing happens -- I don't enter the next step (confirmation countdown). OTOH, if AutoFlashMacro was not running recently, pressing 6 in the macro overlay works.
- What I expect: AutoFlashMacro should not affect the full macro list overlay.

### Bug 4

- What I see: In POE1, if I press leader key to launch the full macro list overlay, and alt-tab to a non-game screen (e.g. IDE), the overlay is still visible. If I then click on the dismiss button of the overlay, the game window will steal the focus.
- What I expect: the overlay should not stay visible if the foreground window changes to a non-game-or-overlay window.

### Bug 5

- What I see: In POE1, if I press leader key to launch the full macro list overlay, and press leader key again, and esc to dismiss the overlay: the overlay will be launched the second time.
- What I expect: pressing leader key again while the overlay is active should dismiss the overlay.
 
## My recommendation

1. Let's create a plan for fixing and testing these issues.
2. Taking a step back, I think the bugs were also partly caused by under specification: I only have a rough idea in my mind when I worked with claude to build the overlay. Now as we added more functionalities (e.g. bg macro), and I use the overlay more often, I have a more concrete idea of my use cases (and my concrete expectations for these use cases). Various features / use cases may interact with each other, and we need to describe our intention better in our spec, and use it to guide the creation of a detailed spec for implementation and testing.

Some example use cases:
- I may alt-tab between game and other windows, while a macro is still running
- A bg macro might have been running recently, and I'll start running a leader key macro

Some examples of "intention":
- overlays (bg macro status line, macro chooser) should only be visible in games (e.g. bug 4)
- macros should start running after confirmation (e.g. bug 2)
- macro systems should work independently, and not break each other (e.g. bug 3)
  + This one is harder to catch as we add more features to the app (quadratic growth of possible pairwise interactions)
  + It's hard to define "independently / break": auto attack macro may trigger flask macro, which is actually my expected behavior (so flask will also be automatically maintained during auto attacks), but without context such interaction can be seen as undesirable.

## Plans

- [Immediate bugfixes](bugfix-immediate.md) — direct fixes for each bug
- [UX guardrails](ux-guardrails.md) — intention-based invariants to prevent future bugs ([detailed spec](attachment/ux-guardrails-details.md))
