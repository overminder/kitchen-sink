# Issues that I found

Status: todo
Dependencies: none

## Description

### Bug 1

- What I see: BgMacroStatusTracker's overlay is in the top left corner of the screen, blocking some of the in-game status.
- What I expect: the bottom-left point of the statusline should be (315,1212)
 
### Bug 2

- What I see: PrintMousePosMacro doesn't actually print the mouse pos until I move the mouse a bit.
- What I expect: PrintMousePosMacro should immediately print the mouse pos
- My investigation:
  + PrintMousePosMacro.prepare calls stateIn which waits until the first value of the mouse pos to be available. The intention is that MacroDef.prepare is called exactly once during app startup time to initialize each macro's internal states, while MacroDef.Prepared.run is called for each "session" (e.g. each time user triggers the macro).
  + MacroDef.prepare however is actually called right before the macro runs in MacroRunnerImpl
