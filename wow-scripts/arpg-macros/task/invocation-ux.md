# Macro Invocation UX Improvement

Status: todo
Dependencies: none

## Problem Statement

Two macro categories exist:
1. **Oneshot macros** — press a key combo, something happens immediately (town hotkeys, parse item, etc.)
2. **Long-running crafting macros** — roll items for minutes/hours with a specific strategy/preset

The current trigger system (`MainV2.kt`) maps leader key sequences (Alt+X → "11", "12", etc.) to macros. Pain points:

- **Preset explosion**: Many crafting presets exist (e.g. `TabletPresets.abyssCheap`, `abyssViaChaos`, `ritual`, and more to come). Each item type × crafting strategy = a new preset. The number grows faster than key mappings.
- **Memorization burden**: User must remember which key sequence maps to which macro. Currently mitigated by only mapping 2-3 at a time.
- **Rebuild-to-switch**: Changing which preset is active (e.g. `TabletPresets.ALL`) requires editing code and rebuilding. This interrupts game flow.
- **No in-context help**: The only way to see mappings is alt-tabbing to source code or console output.

## Current Architecture (relevant)

```
Leader key (Alt+X) → command sequence ("13") → LeaderKeyDetector emits true
    → MacroDef.prepare() → Prepared.run()

macroMapping = listOf(
    MacroMapping("13", WhichGame.POE2) { it.tabletRollingMacro },
    ...
)
```

- `MacroDefsComponent`: DI container with all macro instances
- `TabletRollingMacro.prepare()` hardcodes `TabletPresets.ALL` as the decision maker
- No GUI — output is console-only (`ConsoleOutput` → `KotlinConsole`)
- Dependencies: JNativeHook (input), JNA (Win32), coroutines. No Swing/JavaFX/Compose currently.

## Ideas

### Idea A: In-game overlay picker (recommended)

A transparent always-on-top window that shows a menu when the leader key is pressed. The user picks a macro/preset by pressing a number or letter key, no memorization needed.

**How it works:**
1. User presses leader key (Alt+X).
2. A small overlay appears at a fixed screen position (e.g. top-left corner) showing:
   ```
   [Crafting — Tablet]
     1. Abyss (chaos spam)
     2. Abyss (cheap/transmute)
     3. Ritual
   [Crafting — General]
     4. Alt-Aug-Regal
   [Utility]
     5. Map rolling
     6. Sort stash
   ```
3. User presses a key → overlay disappears, macro runs.
4. If user presses Escape or the timeout elapses, overlay disappears with no action.

**Feasibility:**
- Swing `JFrame` with `setUndecorated(true)` + `setAlwaysOnTop(true)` + transparent background. Available in JDK, zero new dependencies.
- On Windows, use JNA to set `WS_EX_NOACTIVATE | WS_EX_TOOLWINDOW` on the HWND so the overlay doesn't steal focus from the game. This is exactly what community tools like Awakened PoE Trade and POE Overlay do.
- POE typically runs windowed-fullscreen, which supports overlays natively.
- The overlay can also show the **currently active preset** and **macro status** (idle / running / stopped) as a persistent HUD element.

**Pros:**
- Solves both memorization and preset-explosion problems.
- In-game, no alt-tab needed.
- Extensible — can later show crafting progress, roll counts, etc.
- Proven pattern (many POE tools use this technique).

**Cons:**
- New subsystem (overlay rendering, focus management).
- Potential issues with fullscreen-exclusive mode (rare for POE).
- Need to handle DPI scaling on mixed-DPI setups.

**Rough implementation sketch:**
- New `macro-overlay` module (or add to `macro-app`).
- `OverlayWindow` class wrapping a transparent Swing JFrame.
- `MacroPicker` that listens to leader key activation, shows overlay, collects selection, returns chosen `MacroDef`.
- Registry of named presets: `data class PresetEntry(val name: String, val category: String, val factory: () -> MacroDef)`.
- `MainV2` wires picker into the coroutine event loop.

### Idea B: Two-level leader keys with overlay hint

Keep the leader key system but add hierarchy and a "cheat sheet" overlay.

**How it works:**
1. Alt+X → overlay shows top-level categories: `t`=tablet, `c`=craft, `m`=map, `u`=utility
2. Press `t` → overlay updates to show tablet presets: `1`=abyss chaos, `2`=abyss cheap, `3`=ritual
3. Press `2` → runs the preset, overlay disappears.

This is essentially Idea A but preserving the leader-key "tree navigation" metaphor (closer to vim/which-key). The overlay is what makes it usable — you see your options at each level.

**Pros:**
- Natural extension of existing leader key system.
- Muscle memory still works for frequent presets (Alt+X, t, 1 becomes fast).
- Easier to implement incrementally — overlay can start as just showing current level's options.

**Cons:**
- Still some memorization (but overlay mitigates it).
- More keypresses than Idea A for deep trees.

### Idea C: Hot-reload config file (no overlay)

Separate preset definitions from code. Load presets from a JSON/TOML file that can be edited without rebuilding.

```json
{
  "presets": {
    "13": {
      "name": "Tablet: Abyss (chaos)",
      "type": "tablet-chaos",
      "args": { "groups": [...] }
    }
  }
}
```

File watcher detects changes → reloads presets → next macro invocation uses updated config.

**Pros:**
- Solves the rebuild-to-switch problem completely.
- Can edit in any text editor without alt-tabbing to IDE.
- Simple implementation (just file I/O + JSON parsing).

**Cons:**
- Does NOT solve memorization — you still need to know key mappings.
- Config format needs to express the full `CraftDecisionMaker` tree (which can be complex).
- Loses type safety and IDE support for defining presets.

### Idea D: Cycle-through with mini status overlay

A single toggle key cycles through presets. A tiny persistent overlay shows the current selection.

1. Alt+X → shows current preset name in overlay corner: `[Tablet: Abyss chaos]`
2. Alt+X again (within timeout) → cycles to next: `[Tablet: Ritual]`
3. Trigger key (e.g. F9) → runs the currently selected preset.

**Pros:**
- Minimal UI — just a one-line status indicator.
- Very few keys to remember (cycle + run).

**Cons:**
- Slow to reach preset N if you have many (O(n) presses).
- Can't see all options at once.
- Awkward if you switch presets frequently.

## Recommendation

**Start with Idea B (two-level leader keys + overlay hint), evolve toward Idea A.**

Rationale:
1. The overlay is the key unlock regardless of which selection mechanism you pick. Build that first.
2. Two-level leader keys are a natural evolution of the existing system — less disruption.
3. The overlay starts simple (just show "which keys are available at this level") and can grow into a full picker later.
4. Idea C (config file) is orthogonal and can be added later to solve the rebuild problem independently.

### Suggested phasing

| Phase | What | Solves |
|-------|------|--------|
| 1 | Transparent overlay window infrastructure (show/hide, render text, no-focus) | Foundation |
| 2 | Leader key "which-key" — after Alt+X, overlay shows available next keys and their macro names | Memorization |
| 3 | Named preset registry — presets are registered with names/categories instead of anonymous lambdas | Discoverability |
| 4 | Dynamic preset switching — overlay allows selecting which preset a macro slot uses at runtime | Rebuild-to-switch |
| 5 | (Optional) Config file for preset definitions | Full no-rebuild workflow |

## Open Questions

- Should the overlay persist as a HUD (always showing macro status/active preset), or only appear on leader key?
  + A: only appear on leader key.
- Should the overlay use Swing, JavaFX, or Compose Desktop? Swing is zero-dependency but ugly. Compose is pretty but heavy. JavaFX is middle ground.
  + Compose since our macros use coroutines heavily. 
- POE2's anti-cheat: is there any risk of overlay detection? (Community consensus: transparent overlays via standard Win32 are fine, same as Discord overlay.)
  + Should be fine (awakened poe trade does this as well)
- Should preset definitions stay in Kotlin code (type-safe, IDE-friendly) or move to config files (no-rebuild)?
  + let's stay in kotlin for now.
