# C1 bounded model gate record

This record belongs to [TASK-0057](../../../TASK-0057-local-retained-control.md).
It covers the candidate model and its selected ownership and completion
transitions, not source/Core/runtime correspondence or the C3 drain analysis.
The proposal remained proposed when this gate ran.

An independent reviewer passed the six-file candidate in [review.md](review.md)
and [review.json](review.json), pinned by [reviewed-manifest.json](reviewed-manifest.json)
at parent `33af1ed1e9adfaa2efa73443a6c0709131b00ff6`. The model modules in
the [proof root](../../../../design/retained-control/README.md) match that
manifest. The reviewed versions of the proposal, design note and correspondence
are in checkpoint `2ee000102be88ec77a6a6942102c915d37c5b019`; the reviewed
[model README](reviewed-model-readme.txt) is copied here. Later status and
evidence wording records acceptance and this gate without changing the model.

The frozen integration used the reviewed candidate, [config.json](config.json),
and the empty-registration [parent-seed.json](parent-seed.json). The complete
[evidence.json](evidence.json) has SHA-256
`fa3462c847fe90766c33ef6d069dceaf5a3febec0b1cb78d490efbf06d46ed0b`.
Both modules were freshly compiled by Lean 4.33.1 with one job and warnings
as errors. The [gate log](gate.log) records 18 model and 31 example reports;
their checked compiler outputs are [Ownership.log](Ownership.log) and
[OwnershipExamples.log](OwnershipExamples.log). The resulting sources and
registration were copied from the gate's source snapshot and match its
manifest. The receipt records the exact compiler/library pins, reports,
artifact hashes, scheduler settings and source paths at execution time.

These copied files preserve the original bytes, including their original
absolute paths; those paths identify the run and are not portable links.
Compiled artifacts remain in the shared module cache rather than in this
record. Independent retained-result verification and semantic acceptance are
separate from this successful candidate gate.
