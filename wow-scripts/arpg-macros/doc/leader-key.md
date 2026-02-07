# Leader Key Detector

## Purpose

Provides a vim-style leader key mechanism for triggering macros via keyboard chords. Instead of reserving many global hotkeys, all macros share a single leader key combination followed by a short command sequence. This keeps the keybinding space compact and avoids conflicts with in-game bindings.

## Desired Behavior

1. The user presses and releases a **leader key combination** (e.g., Alt+X — order doesn't matter).
2. Within a short grace window, the user types a **command sequence** (e.g., `1 1`).
3. The macro bound to that command activates **immediately** upon the final key release.
4. If the command sequence is mistyped, the state resets and the user can retry from the leader key.
5. If the user types the leader key but doesn't finish the command within the grace window, the partial state should reset (matching vim's leader timeout behavior).

## How It Works

The detector listens to a global stream of key-release events and maintains a rolling buffer of recently released keys. On each key release:

1. **Accumulate**: Append the key to the buffer.
2. **Leader check**: Once the buffer is long enough, check if the first N keys (as a set, so order-independent) match the leader combination. If not, discard the oldest key and return no match.
3. **Command check**: Once the buffer contains the leader keys plus enough subsequent keys, compare the post-leader portion against the registered command string. If it matches, clear the buffer and signal activation. If it doesn't match, clear the buffer (full reset — the user must re-type from the leader key).

The output is a Flow of booleans. After a successful match, the flow emits `true` for a grace period (1 second), then reverts to `false`. Consumers collect from this flow and act on `true` emissions.

## Registered Commands

Multiple macros each register a unique command string against the same leader key instance. Each registration creates an independent flow with its own buffer state — they don't interfere with each other. Duplicate command strings are rejected at registration time.

## Known Issues

### 1. Activation is delayed by the grace period

**Severity**: Minor (UX)

After the final key in a successful chord, the macro does not activate immediately. Instead, it activates after the full grace period (1 second) elapses with no further key releases. This is because the grace period delay sits between match detection and delivery to the consumer — the flow's internal structure causes the `true` value to only be emitted after the delay completes, not at the moment of detection.

In practice this means every chord has a 1-second lag before the macro starts.

### 2. Stray key releases during the grace period cancel activation

**Severity**: Minor (UX)

If any key is released within the 1-second window after a successful match (e.g., lifting a finger off Shift, or an unrelated keypress), the pending `true` emission is cancelled and replaced by the new key's result (almost certainly `false`). The match is silently lost and the user must re-type the entire chord.

Issues 1 and 2 share a root cause: the grace period mechanism is implemented as a delay *before* emitting the result. This makes it act as both a pulse duration and an accidental debounce/cancellation window.

### 3. No timeout on partial sequences

**Severity**: Minor (correctness)

If the user types the leader combination but never finishes the command sequence, the partial buffer persists indefinitely. Hours later, pressing the remaining command keys would complete the match and trigger the macro unexpectedly.

A true vim-style leader key resets pending state after a short timeout (typically the same as the grace period). The current implementation has no such timeout — partial state only clears on a successful match, a failed complete-length match, or a leader mismatch during the sliding window phase.

### 4. Leader prefix is re-validated on every key

**Severity**: Cosmetic

After the leader combination is recognized, each subsequent key release still re-checks that the first N buffer entries match the leader set. This always passes (those entries don't change) so it doesn't cause wrong behavior, but it represents a missing state transition — the detector never moves from "looking for leader" to "looking for command", it re-derives the phase from the buffer contents each time.
