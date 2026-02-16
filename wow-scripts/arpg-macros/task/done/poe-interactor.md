# POE Interactor

Status: done
Dependencies: platform-abstraction.md

## Description

High-level game interaction primitives built on the platform abstraction. These are POE-specific operations composed from raw keyboard/mouse/clipboard actions:

- Copy item description (Ctrl+Alt+C + clipboard read)
- Apply currency to item (right-click currency, left-click item)
- Ctrl+click (quick-move item)
- Ctrl+Shift+click (quick-move to specific tab)

## Acceptance Criteria

- [x] `getItemDescriptionAt(point)`: move mouse, copy, return clipboard
- [x] `applyCurrencyTo(currency, item)`: right-click then left-click
- [x] `ctrlClick(point)`: hold ctrl, click, release
- [x] `ctrlShiftClick(point)`: hold ctrl+shift, click, release
- [x] Configurable delays between actions (with safe variance)
- [x] Uses injected platform interfaces (no direct JNA/AWT)
- [x] Unit tests with mock platform layer

## Notes

The "safe delay" concept (±10ms random variance) should be preserved to avoid detection patterns.

Screen coordinate constants (grid positions, stash slots) might belong here or in a separate constants file.
