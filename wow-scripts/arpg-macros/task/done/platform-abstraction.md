# Platform Abstraction Layer

Status: done
Dependencies: gradle-module-setup.md

## Description

Define interfaces that wrap all platform-dependent operations. The refactored code programs against these interfaces, allowing tests to inject mocks instead of hitting real OS APIs.

This is Windows-only, but the abstraction still matters for testability.

## Acceptance Criteria

- [x] `KeyboardInput` interface: key press/release events as Flow
- [x] `KeyboardOutput` interface: post key press/release
- [x] `MouseInput` interface: mouse move/click events as Flow
- [x] `MouseOutput` interface: post mouse move/click
- [x] `Clipboard` interface: read/write clipboard text
- [x] `Screen` interface: capture pixel color at coordinates
- [x] `Clock` interface: current time, delay (for testable timing)
- [ ] Windows implementations created (can be stubs initially)
- [x] Mock/fake implementations for testing

## Notes

The current codebase uses:
- `JNativeHook` for global keyboard/mouse hooks
- `JNA` / `Win32Api` for native calls
- `AwtRobot` for screen capture
- System clipboard via AWT

Group related operations logically. Consider whether input/output should be separate interfaces or combined per device.
