# Arena source recovery checkpoint

Status: paused, unverified, incomplete. This capsule preserves work in progress;
it is not an executable delivery or current Ash semantics.

The source branch starts from verified preparation checkpoint
`dbe34ed2cbd96e6e50708034b9dddda4eb66a112`. That checkpoint's 313 passing checks
cover preparation, not typed Ash storage. No compiler, formatter, Cargo test,
architecture gate or final verification ran for the newly retained source.
`git diff --check` passed before recovery. No actual capture/type file changed.

The recovery retains scalar layout dictionaries, family evidence/source copying,
opaque native witnesses/references, actual native scalar storage/load code,
grouped evaluator source, and allocation fixtures/example. These changes remain
uncompiled. Expanded foreign admission and unsupported family paths retain
explicit refusal. The scalar allocation/load delivery gate has not passed.

Unfinished connections include:

- Grouped independent specialization admission is partially written. Its new
  helper calls are unresolved; new proof fields still need authentication,
  relocation and complete construction. The branch is not expected to compile.
- The [family helpers](family-specialization-helpers.rs) and
  [certificate getter](family-certificate-getter.rs) are insertion drafts, not
  active compiler source. Their [integration notes](family-integration.md)
  describe canonical dictionary and original-certificate obligations.
- Canonical family forwarding graphs still need independent authentication.
  The original family method contract/certificate readers are unfinished.
- Sealed original native storage relations exist in source. Their exact copied
  projection/owner/effect transfer and authenticated capture getter remain
  unfinished. Original template accessor visibility also needs review.
- [Private capture changes](capture-scalar-candidate.patch.gz) target the committed
  preparation baseline. [Composition notes](capture-composition.md) record
  caller migration and receipt APIs. They require sequential composition on a
  verified Fusion successor, review and connected compilation. Do not apply
  them blindly or treat the private patch as verified behavior.
- Actual Ash allocation/load, refusal, escape and override programs still need
  executable evidence. Useful payloads, ownership/sharing, explicit copies,
  scratch/control composition, results and final integration gates remain.

The [document patch](document-drafts.patch.gz) preserves the nine existing document
working copies without staging or changing those canonical draft files. It is
an unapplied recovery snapshot, not a documentation delivery. Active task/plan
and draft blueprint/results work remain unfinished; no lifecycle cleanup ran.
All existing stashes, unrelated work and both integration histories remain.
No merge into `codex/provider-experiments` occurred.

The [manifest](manifest.json) pins retained source and preserved drafts. The
unsigned recovery commit and normal branch push preserve this incomplete batch
for later resumption. All Arena agents stopped at this checkpoint.

Patch snapshots use lossless gzip archives so their meaningful diff context
whitespace remains byte-exact. The manifest records uncompressed hashes.
