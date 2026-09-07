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

- [CP-0018: Synchronous Typed Hooks](CP-0018-synchronous-typed-hooks.md) —
  transforming chains over exact effect APIs, scoped registration, explicit
  handler placement and checked normal-exit deregistration. Under review;
  implementation is not authorized.

## Accepted changes

No accepted change is currently awaiting implementation.
