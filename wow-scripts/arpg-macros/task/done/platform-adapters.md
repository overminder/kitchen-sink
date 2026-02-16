# Platform Adapters

Status: done
Dependencies: macro-app-setup.md

## Description

Real implementations of macro-core's platform interfaces using JNativeHook, JNA, and AWT.

## Acceptance Criteria

- [x] `JNativeHookKeyboardInput` implements `KeyboardInput`
- [x] `JNativeHookKeyboardOutput` implements `KeyboardOutput`
- [x] `JNativeHookMouseOutput` implements `MouseOutput`
- [x] `AwtClipboard` implements `Clipboard`
- [x] `RealClock` implements `Clock`
- [x] `Win32Screen` implements `Screen`
- [x] Module compiles

## Notes

Key name mapping: macro-core uses String key names ("Ctrl", "Alt", "C") while JNativeHook uses int VC_* codes.
