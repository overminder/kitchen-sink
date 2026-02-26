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
  + When designing multiple components, describe their responsibility, communication patterns, and internal states.
- Use relative links for dependencies: `[leader-key](leader-key-detector.md)`.
- One task = one focused deliverable. Split if scope creeps.