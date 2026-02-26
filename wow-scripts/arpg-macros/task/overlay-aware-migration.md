# Migrate src/ to :macro-* and adapt overlay patterns

Status: todo
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

TODO

# Concise component design doc

TODO

# Milestones

TODO
