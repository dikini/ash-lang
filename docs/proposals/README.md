# Change proposals

Change proposals describe proposed changes to Ash language or runtime semantics. They are prospective and do not describe current Ash until implementation, tests, and the corresponding specification update merge together.

Status has two current-tree values:

- `proposed` — under consideration and cannot authorize implementation;
- `accepted` — semantically agreed and may authorize tasks, but is still not current Ash.

Remove the proposal after the complete change merges. Git preserves the transition and its evidence.

Use [the template](template.md) and allocate the next `CP-NNNN` ID.

## Proposed changes

No change proposal is currently under consideration.

## Accepted changes

- [CP-0005: Passive Static Modules](CP-0005-passive-static-modules.md) —
  declarations-only modules, deterministic imports, visibility, opacity,
  generated export summaries, and execution through entry `main`.
