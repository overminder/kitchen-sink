# Task Tracker

Lightweight, file-based task management for the incremental refactoring of this macro framework.

## Structure

Each task is a markdown file in this directory. File names are kebab-case and self-descriptive (e.g., `leader-key-detector.md`, `platform-abstraction.md`).

## Task File Format

See `_template.md` for the required fields. In brief:

```markdown
# Task Title

Status: todo | in-progress | done
Dependencies: task-a.md, task-b.md (or "none")

## Description
What this task accomplishes.

## Acceptance Criteria
- [ ] Criterion 1
- [ ] Criterion 2

## Notes
Any additional context, design decisions, or open questions.
```

## Workflow

1. **Find work**: Look for tasks with `Status: todo` whose dependencies are all `Status: done`.
2. **Start work**: Change status to `in-progress`.
3. **Complete work**: Check off acceptance criteria, change status to `done`.
4. **Discover new work**: Create new task files as subtasks emerge.

## Conventions

- Keep descriptions concise — detailed specs belong in `doc/`.
- Use relative links for dependencies: `[leader-key](leader-key-detector.md)`.
- One task = one focused deliverable. Split if scope creeps.
- The `refactor-map-rolling.md` task is the root goal — trace dependencies backward from there to find the critical path.

## Dependency Graph

```
refactor-map-rolling
├── leader-key-detector
│   └── platform-abstraction
│       └── gradle-module-setup
├── item-parser
│   └── gradle-module-setup
├── map-scorer
│   ├── item-parser
│   └── map-mod-database
│       └── gradle-module-setup
├── reroll-provider
│   ├── platform-abstraction
│   └── poe-interactor
│       └── platform-abstraction
└── multi-roll-loop
    ├── item-parser
    ├── map-scorer
    ├── reroll-provider
    └── poe-interactor

screen-constants
└── gradle-module-setup
```

**Critical path** (longest chain): `gradle-module-setup` → `platform-abstraction` → `poe-interactor` → `reroll-provider` → `multi-roll-loop` → `refactor-map-rolling`

**Parallelizable after gradle-module-setup**:
- `item-parser` (no platform deps)
- `map-mod-database` (no platform deps)
- `screen-constants` (no platform deps)
- `platform-abstraction` (blocks everything else)

```
refactor-craft-rolling
├── craft-decision-maker
│   └── (uses existing PoeRollableItem, CheckResult)
├── craft-methods
│   └── craft-decision-maker
└── craft-reroll-provider
    ├── craft-methods
    └── (uses existing poe-interactor, platform-abstraction)
```

```
macro-main
├── dagger-wiring
│   ├── macro-app-setup
│   └── platform-adapters
│       └── macro-app-setup
└── platform-adapters

macro-app-cleanup
└── macro-main
```
