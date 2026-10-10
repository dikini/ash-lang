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

No proposed semantic transition is under review.

## Accepted changes

- [CP-0022: Ash-authored foreign interfaces](CP-0022-ash-authored-foreign-interfaces.md)
  authorizes the bounded `ffi-ash` transition and its
  [implementation tasks](../tasks/README.md). It remains prospective until the
  complete product checkpoint is integrated into Main.
