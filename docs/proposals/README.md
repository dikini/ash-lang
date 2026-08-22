# Change proposals

Change proposals describe proposed changes to Ash language or runtime semantics. They are prospective and do not describe current Ash until implementation, tests, and the corresponding specification update merge together.

Status has two current-tree values:

- `proposed` — under consideration and cannot authorize implementation;
- `accepted` — semantically agreed and may authorize tasks, but is still not current Ash.

Remove the proposal after the complete change merges. Git preserves the transition and its evidence.

Use [the template](template.md) and allocate the next `CP-NNNN` ID.

## Accepted changes

- [CP-0003: Monomorphic Data and Patterns](CP-0003-monomorphic-data-and-patterns.md)
  authorizes the active data, tuple, pattern, and guarded-recursion increment.
