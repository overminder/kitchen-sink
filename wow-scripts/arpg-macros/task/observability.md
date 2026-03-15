# Production observability

Status: todo
Dependencies: none

## Description

### Motivation

The most common and hardest-to-debug bugs are real system integration bugs — at the boundary between macro logic and external systems (game pixel rendering, Win32 focus, JNativeHook delivery). Currently, the only runtime visibility is the overlay status line showing key press counts. When something goes wrong during gameplay, there's no way to determine what decisions the macro made, what pixel values it saw, or what state transitions occurred.

Every play session is implicitly a real integration test. The problem is we can't extract value from it — no recording, no automated analysis, no reproduction capability.

### Goal

Instrument the macro system so that every play session produces a structured event log that enables:
1. **Live monitoring** — real-time invariant checking during gameplay, surfaced through the overlay
2. **Post-session analysis** — automated detection of suspicious patterns and invariant violations
3. **Reproduction** — a session recording contains enough data to understand and reproduce any bug

### Relationship to [e2e-test.md](e2e-test.md)

Observability and testing are complementary but separate concerns:
- **Testing** verifies behavior under controlled conditions (fake platform, property-based, etc.)
- **Observability** captures behavior under real conditions (actual game, actual Win32)

Interlinks:
- Session recordings can feed into e2e test **regression extraction** (known-good session → test fixture)
- Session recordings can validate the **game simulator's** fidelity (compare real pixels vs simulator predictions)
- The **invariant catalog** (e.g., "no key output while game unfocused") is shared between live monitoring and property-based tests

## Plan

See `task/attachment/observability-details.md` for the full design.

### Layer 1: Session recording

Structured event log captured during every play session. Events:

| Event type | Data | Source |
|-----------|------|--------|
| `PIXEL_READ` | position, color, reader (e.g. `flask[2]`), result (active/inactive, distance) | BuffKeeper |
| `KEY_OUTPUT` | key, macro name | ReportingKeyboardOutput |
| `DECISION` | macro name, rationale (e.g. "buff inactive: distance=12.4 > 10") | BuffKeeper, BuffManager |
| `STATE_CHANGE` | component, old → new state | Coordinator, BackgroundMacroRunner |
| `FOCUS_CHANGE` | window title, is-game | ActiveWindowChecker |

Storage: append-only log file, one session per file. At ~20 events/sec → ~1KB/s → ~3.6MB/hour. Negligible.

### Layer 2: Live invariant checking

Run invariants against the live event stream during gameplay. When violated, surface through the existing overlay status line mechanism (or console).

Example invariants:
- Key output while game not in foreground
- Flask key pressed while buff detected as active (within last poll)
- State machine stuck in non-Idle state for >30s without activity
- Flask pressed N times within M ms (spam detection)

### Layer 3: Post-session analysis

After a session (or on demand), analyze the recording file:
- List all invariant violations with timestamps
- Identify suspicious patterns (rapid repeated presses, long gaps in expected activity)
- Summary: "Session 45min, 3 warnings: flask double-press at 23:45, focus race at 31:12"

### Layer 4: Regression extraction

Extract input sequences from a known-good recording as test fixtures for [e2e-test.md](e2e-test.md). If a code change causes different output for the same inputs, that's a regression.

## Acceptance Criteria

- [ ] Session recording captures pixel reads, key outputs, decisions, state changes, and focus changes
- [ ] Recording is always-on during normal gameplay with negligible performance impact
- [ ] Live invariant checking surfaces violations through overlay or console
- [ ] Post-session analysis tool produces a summary of a recorded session
- [ ] Invariant catalog is documented and shared with e2e-test invariant checking
- [ ] Session recordings are stored in a configurable directory, rotated by age/size

## Notes

- The `BgMacroStatusTracker` / `ReportingKeyboardOutput` infrastructure already captures key outputs — this task extends that pattern to pixel reads, decisions, and state transitions.
- Decision logging requires changes inside `BuffKeeper` / `BuffManager` — these currently make decisions silently. The logging should be non-invasive (decorator or callback pattern, not inline logging calls).
- Invariant catalog should be a shared definition (possibly in `macro-core`) so both this system and property-based tests reference the same invariants.
