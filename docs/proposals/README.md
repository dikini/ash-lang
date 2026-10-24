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

The revised work uses [S1 #131](https://github.com/dikini/ash-lang/issues/131), [S2 #132](https://github.com/dikini/ash-lang/issues/132),
[S3 #133](https://github.com/dikini/ash-lang/issues/133) and [S4 #134](https://github.com/dikini/ash-lang/issues/134).

- [CP-0024: Smaller foreign-library boundary](CP-0024-checked-foreign-host-profile.md)
  records the agreed responsibilities; interface and memory mapping remain proposed.

## Accepted changes

No accepted technical transition currently authorizes new FFI implementation.
The [generic cell checkpoint evidence](../design/generic-cell/evidence.md)
retains the completed transition, verified local Main integration and
historical retrieval commands.
