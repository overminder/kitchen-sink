# Screen Constants

Status: done
Dependencies: gradle-module-setup.md

## Description

Define the screen coordinate constants for POE UI elements at 2560x1440 resolution:
- Inventory grid positions
- Stash tab positions
- Currency tab slot positions
- Grid size and spacing calculations

## Acceptance Criteria

- [x] Bag grid slot calculator (row, column → screen point)
- [x] Stash grid slot calculator
- [ ] Currency tab known positions (chaos, scour, alch, etc.)
- [ ] Configurable base resolution (for future scaling support)
- [x] Grid iteration utilities (all slots in a region)

## Notes

The current code hardcodes 2560x1440. Consider whether to:
- Keep hardcoded (simplest, current user's setup)
- Add resolution scaling
- Make fully configurable

For now, hardcoded is fine — this is a personal tool.
