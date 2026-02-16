# Leader Key Detector

Status: done
Dependencies: platform-abstraction.md

## Description

Reimplement the leader key detection mechanism with fixes for the known issues documented in `doc/leader-key.md`.

The leader key detector receives keyboard input via dependency injection and emits activation signals when a leader+command chord is completed.

## Acceptance Criteria

- [x] Detects leader key + command sequences (order-independent leader)
- [x] Activates immediately on match (no 1-second delay)
- [x] Stray key releases don't cancel pending activation
- [x] Partial sequences timeout after grace period
- [x] Multiple commands can be registered independently
- [x] Unit tests cover: happy path, mistyped recovery, timeout, stray keys
- [x] Uses injected `KeyboardInput` (no direct JNativeHook dependency)

## Notes

See `doc/leader-key.md` for the behavioral spec and known issues in the current implementation.

Key design change: separate match detection from the grace-period pulse. Emit `true` immediately on match, manage the pulse duration downstream or via a different mechanism.
