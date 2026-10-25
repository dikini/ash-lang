# Borrowed effect-signature inputs

This checkpoint tests a local ownership change on retained producer base
`a2f1c938f35d5356544471dffac747cc52418519`, after the preserved dependency
work was rebased without changing its source projection. Fresh effect-instance
validation still checks the complete original owner, operation, arity, kinds and
depth before substitution. The local Type replacement map borrows validated
arguments instead of cloning them only to discard the map. Each retained
reference is paid; Row replacements and the resulting signature remain owned.
The existing substitution engine and error order are unchanged.

Actual session 97479 compiled successfully and completed all five commands:

| Selection | Result |
| --- | --- |
| New signature ownership, hostile and work controls | 2 passed |
| Existing effect identity discrimination | 1 passed |
| Existing effectful substitution controls | 3 passed |
| Required full-Row private image | 1 failed: Validation(Resource) |
| Required retained Access private image | 1 failed: Resource |

The image cases ran independently after the focused controls. The base image
completed its correspondence, hostile and exact/prefix/short/spent/fresh work
controls at 261150. Neither required canonical image restored, so its later
image controls receive no credit. No current failure stack, remaining deficit,
default fit or isolated saving is inferred. Startups, final regressions,
Clippy, delivered-subset specification and final PR review remain pending.

Every command's 5661 full-input and 613 runtime-inventory entries were equal
before and after, at aggregates `99c7f241` and `bbf75ae4`. The freshly built
library test artifact is 610882768 bytes, SHA-256
`3db3f53bd110aea78139d5f68060579a8c6a12747355214254c2dd474957dd95`.
It remains in the dedicated `parallel-f3` target, not this evidence directory.
Each Cargo child returned and was reaped by its runner; these receipts do not
include a separate contemporaneous process-group snapshot. No resource abort
or compiler warning was reported. No generated foreign output was executed.

[index.json](index.json) reconstructs 50 original files using bounded gzip
blobs and two deduplicated input maps. For `json-map-template`, recursively
replace each sole `$retained_map` object with the corresponding decoded map,
then serialize with two-space indentation and a final newline. Other records
are direct gzip bytes. Reconstructed sizes and SHA-256 values were compared
with every original. Tested task/plan snapshots preserve their exact inputs;
this README, later progress prose and the evidence paths are post-test changes,
not a new tested full-input fingerprint. Earlier failures and traces remain
separate in their original evidence checkpoints.
