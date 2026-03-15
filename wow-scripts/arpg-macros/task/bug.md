# Issues that I found

Status: todo
Dependencies: none

## Description

What I see: When BG macro toggler is off, flask macro is still triggered.
What I expect: When BG macro toggler is off, flask macro (part of BG macros) can't be triggered.

Steps to replicate:
1. Enter POE1 game
2. press leader key, set flask menu to non-PF
3. play for a bit
4. press leader key, set BG macro to off
5. play for a bit. Pressing E will indeed not trigger flasks. However, at some point I pressed 5, which trigger flasks (I see both my in-game flaskes being active, AND the BG macro status line showing 2345 being pressed), and now pressing E will also trigger flasks.
