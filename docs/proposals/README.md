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

- [CP-0034: Top-Level Declaration and Derive Macros](CP-0034-top-level-declaration-macros.md)
  — proposed module-level syntax rewriting and derives, with working grammar,
  service contracts and integration fixtures; slice 1 reconciliation remains.

## Accepted changes

- [CP-0032: Row-Indexed Handler Contexts](CP-0032-row-indexed-handler-contexts.md),
  accepted as one package with
  [Effects as Interfaces: Elaboration Proposal](../design/effects-resources/effect-interface-elaboration-proposal.md).
  Implementation is pending.

The [specification](../../spec/README.md) records the accepted, implemented
`ffi-ash` language, including generic cells, lexical regions, retained control
and pinned workers. Their transitions are integrated into Main. The bounded
[region model evidence](../design/lexical-regions/evidence.md) retains its
separate proof scope.

The [generic cell checkpoint evidence](../design/generic-cell/evidence.md)
retains the completed transition, verified local Main integration and
historical retrieval commands.
