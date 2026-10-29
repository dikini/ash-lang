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

- [CP-0027: Pinned workers and copied channels](CP-0027-pinned-workers-and-copied-channels.md)
- [CP-0028: Checked functional network ledger](CP-0028-checked-functional-network-ledger.md)
- [CP-0029: Exact base-256 integer split](CP-0029-exact-base-256-integer-split.md)
- [CP-0030: Checked network codec](CP-0030-checked-network-codec.md)

The [region specification](../../spec/README.md)
records the lexical-region language rules; the bounded
[model evidence](../design/lexical-regions/evidence.md) retains its separate proof
scope. Proposal retirement prepares the product branch and does not replace
separately authorized Main integration.

The [generic cell checkpoint evidence](../design/generic-cell/evidence.md)
retains the completed transition, verified local Main integration and
historical retrieval commands.
