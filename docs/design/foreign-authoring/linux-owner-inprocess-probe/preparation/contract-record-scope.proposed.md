# Proposed clarification of experiment text-record scope

Status: PROPOSED. No build, startup or limit change is authorized by this text.
Root and independent reviewer must resolve the interpretation before assigning
commands. The retained contract at compiler commit
1a8ecef0b03ddc75a45254543bd8f6f0bb10969c currently says:

> Each source/entry/generated text record: 1 MiB; report excess as unsupported.

Proposed replacement row:

| Record | Bound |
| --- | --- |
| Each adapted Ash experiment source/entry or generated experiment text record | 1 MiB; report excess as unsupported |

Add immediately after the bounds table:

The text-record bound applies to experiment inputs and generated text retained
for this comparison. The entire existing repository snapshot (compiler, configuration, documentation,
proof and historical evidence/archive files) is producer input, all pinned by the selected Git tree and a complete
per-file manifest, with equality checked before and after each build phase.
They must not be omitted, truncated or accepted merely from a smaller runtime
fingerprint census. For the selected 1a8ecef0 snapshot, all 2784 Git blobs are
pinned; its separate build.rs runtime-content census contains 177 files. Three
compiler producer inputs exceed 1 MiB: src/resolved.rs is 1,793,508 bytes,
src/elaborate.rs is 1,779,136 bytes, and src/core/validate.rs is 1,688,770 bytes.
This clarification does not create a compiler-source size acceptance claim;
these exact sizes and full hashes are explicit assigned producer inputs.

Tool executables and ordinary build intermediates are also distinct from the
final candidate image. Hash them by streaming against their frozen expected
sizes. The observed cached compiler was 589,362,808 bytes and remains unapproved
for reuse. The 128 MiB limit continues to apply to the selected final static
candidate only; it does not become a universal tool/intermediate cap. Generated
experiment text, output retention, link-map monitoring and receipt/manifest
bounds remain unchanged. Sampled storage monitoring is not a hard quota.

Rationale: silently dropping the three large implementation files would destroy
producer correspondence. Treating the existing compiler as a 1 MiB experiment
text artifact would refuse this selected snapshot before compilation. Explicit
review of the category boundary preserves complete input correspondence and
keeps the stated experiment/output bounds enforceable. If this interpretation
is rejected, the selected build remains unsupported; no alternate limit is
inferred. Retain an amendment with the next F2 evidence item if required by the
documentation owner. Do not claim the current retained wording already says it.

The complete snapshot has eight blobs above 1 MiB, not only the three compiler
implementation files. selected-source.json lists all eight exact paths, sizes
and hashes; the full archive manifest preserves all 2784 blobs/96,452,672 bytes.
The staged contract patch explicitly covers the entire pre-existing snapshot.
