# Change proposals

Change proposals describe proposed changes to Ash language or runtime semantics.
They are prospective and do not describe current Ash before the complete change
is integrated into `main`.

Status has two current-tree values:

- `proposed` — under consideration and cannot authorize implementation;
- `accepted` — semantically agreed and may authorize tasks, but is still not
  current Ash.

Remove the proposal from its product branch after one checkpoint retains the
implementation, tests, specification update, review, and verification. Git
preserves the transition and its evidence. This cleanup prepares the branch for
integration; it does not make the change current.

Use [the template](template.md) and allocate the next `CP-NNNN` ID.

## Proposed changes

- [CP-0012: Module `newtype`](CP-0012-module-newtype.md) proposes one
  allocation-free module-level nominal representation declaration with
  explicit wrapping and matching, existing visibility, independently validated
  Core conversion, and no representation-derived interface evidence.

## Accepted changes

No accepted change is currently awaiting implementation.
