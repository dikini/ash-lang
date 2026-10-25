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

No proposed changes are listed.

## Accepted changes

[CP-0025: Lexical region construction and paired allocators](CP-0025-lexical-region-construction.md)
is accepted for transition with a reviewed bounded preservation proof and an
independently audited frozen gate, retained through [PR #146](https://github.com/dikini/ash-lang/pull/146) at `aee02227b69fb6cbbd00c23904ffe2a0c7df6924`.
Retained verification and R1/R2 acceptance are complete. R3 implementation is
active and partial; no product criterion is complete. It is not current Ash.

The [generic cell checkpoint evidence](../design/generic-cell/evidence.md)
retains the completed transition, verified local Main integration and
historical retrieval commands.
