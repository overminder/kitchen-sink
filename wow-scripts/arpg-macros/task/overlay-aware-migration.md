# Migrate src/ to :macro-* and adapt overlay patterns

Status: in-progress
Dependencies: none

# Terminology

- "Old macro": src/
- "New macro": `:macro-*`
  + has an in-game overlay prototype

# High level requirements

- code: Most (but not all -- TODO list all missing macros with a checkbox to confirm the scope) old macros should be ported to new macro.
  * The porting should follow new macro's conventions: DI, platform abstraction
- ux: adapt ported macros to new macro's overlay. For example,
  * For leader key triggered macros: ensure discovery, and as a follow-up display macro running information
  * For non-leader key triggered macro that reads the initial mouse position: ensure discovery, and pass the mouse position via ActivationContext
  * For other triggered macros, the overlay should provide a single control to toggle enabled/disabled for all non-leader key triggered macros

# List of macros not yet ported

Source: `GameSpecific.ALL` in `src/main/kotlin/.../GameSpecific.kt`.

- [x] means don't migrate
- [h] means on hold (don't migrate for now, may change later)
- [ ] means will migrate
- [o] means migrated

## Leader-key triggered (overlay selection)

- [x] `PoeDivCard::turnInFromBag` — LEADER "03". Turn in div cards from inventory to NPC. POE1.
- [x] `PoeRerollKirac::main` — LEADER "05". Reroll Kirac missions using OCR. POE1.
- [o] `PoeDumpBag::bagToStash` — LEADER "06". Ctrl+click all bag items to stash. POE1.
- [o] `PoeDumpBag::bagToStashForced` — LEADER "08". Force-move all bag items to stash. POE1.
- [h] `PoeDumpBag::moveMapFromStashToBag` — LEADER "09". Move maps from map stash to bag. POE1.
- [h] `PoeHarvestReforge::main` — LEADER "10". Harvest bench reforge until target mod. POE1.
- [h] `PoeDumpBag::moveFromHeistLocker` — LEADER "12". Move heist contracts to inventory. POE1.
- [h] `PoeDumpBag::moveFromRegularStash` — LEADER "13". Move items from regular stash to bag. POE1.
- [h] `PoeAltAugRegal::multiRoll` — LEADER "15". Alt/aug/regal rolling on items in bag. POE1.
- [h] `PoeRollMap::kiracInvitation` — LEADER "17". Reroll Kirac invitations. POE1.
- [h] `PoeQualityApplier::main` — (LEADER, key TBD). Apply quality currency to items. POE1.
- [o] `ctrlClickManyTimesInPoe` — LEADER "01" toggle then runs continuously. Multi ctrl+click at mouse position. POE1. Note that even though in the old macro, this is not leader key triggered, it still needs an initial mouse position, so it makes sense to migrate it into a leader key triggered new macro.

## Non-leader-key triggered (background hotkey / toggle)

- [o] `triggerSkillInPoe` — Hardcoded key hold. Auto-insert skill presses while attacking. POE1.
- [o] `toggleAutoAttackInPoe` — Hardcoded key toggle (D). Toggle auto-attack in simulacrum. POE1.
- [o] `triggerSkillsInD4` — Hardcoded key hold (W/R). Trigger D4 skills on round-robin. D4.
- [ ] `autoFlaskInPoe`

## Out of scope (confirm by unchecking if wanted)

- [x] `PoeAutoAlt::play` — Hardcoded, no leader key. Superseded by CraftRollingMacro/V2.
- [x] `PoeAltAugRegal::craftInCurrencyTab` — LEADER "07". Superseded by CraftRollingMacro.
- [x] `PoeRollMap::main` — LEADER "11". Already ported as MapRollingMacro.
- [x] `PoeRollMap::sortInStash` — LEADER "14". Already ported as SortInStashMacro.
- [x] `MouseCap::printMousePos` — LEADER "02". Already ported as PrintMousePosMacro.
- [x] `townHotkeyInPoe` / `townHotkeyInPoe2` — Already ported as TownHotkeyMacro/V2.
- [x] Commented-out macros: `lodWolInD3`, `triggerSkillsInD3`, `tripleClickInPoe`, `novaOfFrostboltsInPoe`, `detonateMineInPoe`.

# Concise component responsibilities

## Existing (no changes needed)

| Component | Responsibility |
|-----------|---------------|
| **LeaderKeyListener** | Detects Alt+X chord, emits `Flow<Unit>`. No state machine. |
| **Coordinator** | Sequences: leader key → capture context → steal focus → show overlay → await selection → return focus → run macro. State guard prevents re-entrancy. |
| **FocusManager** | Steal/return OS window focus between game and overlay. Capture `ActivationContext`. Exclude overlay from screen capture. Platform-specific (Win32). |
| **OverlayController** | Interactive Compose window. `awaitSelection()` shows macro list, returns selection or cancel. `showExecutionStatus()`/`hideExecutionStatus()` for non-interactive status during macro run. |
| **MacroRegistry** | Source of truth for macro descriptors. `macrosFor(context)` filters by detected game. |
| **MacroRunner** | Resolves `MacroRegistration` → `MacroDef`, calls `prepare().run()`. |
| **ActivationContext** | Snapshot: game HWND, window title, cursor position. Captured before focus steal. |

## New or extended

| Component | Responsibility |
|-----------|---------------|
| **MacroRegistryImpl** | Extend `macroSpecs` list with newly ported macros. No structural changes. |
| **MacroDefsComponent** | Add DI provider methods for each new `MacroDef`. |
| **BackgroundMacroRunner** | New. Manages non-leader-key macros that run continuously (triggerSkill, autoAttack, ctrlClickMany). Provides a single enable/disable toggle exposed to the overlay. Replaces the ad-hoc `GameSpecific.ALL` wiring. |
| **MainV2** | Wire new background macros alongside existing town hotkey wiring. |

## Communication for background macros

```
Overlay ──toggle──▶ BackgroundMacroRunner ──enable/disable──▶ [triggerSkill, autoAttack, ...]
                         │
                    observes game window focus (isPoe, isD4)
                    observes key states (KeyHooks)
```

The overlay exposes a single toggle (visible when no leader-key macro is running) to enable/disable all background macros. Individual background macros still check their own game-specific conditions internally.

# Milestones

## M1: Port leader-key macros (bulk of work)

Port leader-key macros to `MacroDef` pattern and register in `MacroRegistryImpl`.

Each macro port involves:
1. Create `XyzMacro : MacroDef` in `macro-core/.../recipe/`
2. Wire in Dagger (`MacroDefsComponent`, `MacroModule`)
3. Add `MacroSpec` entry in `MacroRegistryImpl`
4. Delete old code from `src/` once verified

## M2: Port non-leader-key macros

These don't use the overlay for selection but need:
1. A `BackgroundMacroRunner` (or similar) to manage their lifecycle
2. A toggle in the overlay to enable/disable them as a group
3. Game-specific filtering (only run when the right game is focused)

## M3: Overlay toggle for background macros

Add a persistent UI element in the overlay (visible in Idle state or as an always-visible badge) that shows background macro status and allows toggling on/off.

## M3.1: refine

- Port autoFlaskInPoe, including the different configs in PoeFlasks (maybe as a dropdown in overlay, and ideally have the flask patterns better visualized than just a name. For example show 5 O-shapes (w:h=1:3 tall ellipsis) for 5 flask slots, outline-only for non-automated slot, filled for automated slot; same colors in an alt group, different colors in a par group)
- Change the "BG macros" toggle to only display when leader key is pressed.
- Pause any background macros when the main overlay is launched (excluding the small overlay that shows macro run confirmations)

## M4: Cleanup

- Remove `GameSpecific.ALL`, `GameSpecific.kt`, and the old `src/main.kt` entry point
- Remove dead imports and old `LEADER_KEY` detector from `src/`
- Verify `./gradlew build` and `./gradlew test` pass with only `:macro-*` modules
