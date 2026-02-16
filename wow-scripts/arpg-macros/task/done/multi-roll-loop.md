# Multi-Roll Loop

Status: done
Dependencies: item-parser.md, map-scorer.md, reroll-provider.md, poe-interactor.md

## Description

The core loop that processes a batch of items (maps), evaluating each and rerolling until it meets criteria or resources are exhausted. This is the orchestration layer that ties together:
- Item reading (interactor + parser)
- Evaluation (scorer)
- Rerolling (provider)
- Progress tracking and reporting

## Acceptance Criteria

- [x] Processes items from a list of screen positions
- [x] Reads item description, parses, evaluates
- [x] Accepts good items, rerolls bad ones
- [x] Stops when: all done, currency exhausted, or cancelled
- [x] Reports summary (count, avg cost, scores)
- [x] `shouldContinue` callback for cancellation
- [x] Integration test with fully mocked platform layer

## Notes

The loop structure from `PoeMultiRoll.rollItems`:
1. Pop next item slot from work list
2. Read and parse item
3. If good: accept, remove from list
4. If bad: reroll if currency available, else stop
5. Repeat until list empty or stopped

The integration test should verify the full sequence of platform calls (mouse moves, clicks, clipboard reads) against expected behavior.
