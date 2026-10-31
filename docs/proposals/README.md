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

No proposed transitions are listed.

## Accepted changes

No accepted transitions are listed.

The [specification](../../spec/README.md) records the accepted, implemented
`ffi-ash` language, including generic cells, lexical regions, retained control
and pinned workers. Their transitions are integrated into Main. The bounded
[region model evidence](../design/lexical-regions/evidence.md) retains its
separate proof scope.

The [generic cell checkpoint evidence](../design/generic-cell/evidence.md)
retains the completed transition, verified local Main integration and
historical retrieval commands.
