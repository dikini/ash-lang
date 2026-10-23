# Generated canonical root and opaque leaf: compile/link WIP

This TASK0053 work item starts at retained PR119 `a3fc751d`. Runtime source
`1f1965c3` was tested before this README, task/plan notes and evidence assembly.
The generated binary compiles canonical Ash `src/lib.rs`, includes the private
shim and three actual payloads, and depends on the opaque dependency-free leaf.
Private typed function pointers retain the four native symbol references without
calling them. Startup remains a deterministic refusal; no evaluator or protected
startup positive is claimed.

Session28740 selected13 tests:12 ordinary Rust controls passed, and the actual
generated compile/link test failed `Association` after the canonical root/leaf
compiled and linked successfully. The retained Cargo log reports `Finished dev
profile` in2m45s; cleanup then removed22 files/19.6MiB. All eight before/after
maps contain the same8,095 inputs, all97 critical snapshots and physical tools
match, and every owned child was reaped with its group absent. Independent audit
`14a757a6` and own preservation `ab306ccd` retain those observations.

The capture record reports output pin `573a1d4e…`,1,569,672 bytes, and successful
BFD exit. Observation failure correctly deleted the staging ELF. It cannot be
physically rehashed and is not embedded here. No final producer receipt/request
succeeded; the missing-release linker negative was unreached. Raw outer logs
retain26 warning lines including summaries; the generated link log includes two
static glibc possible-loading warnings. No Clippy or warning-free claim.

Earlier44821 passed12 ordinary controls but failed lock settling because the
leaf redundantly declared its own workspace. Earlier65446 passed12 controls but
failed the generated dependency build script because HOME was required despite
explicit cache roots. Their narrow repairs and red evidence are preserved.

Source review after28740 found a guaranteed linked-root refusal: the request
decoder compares the final ASHNAT01/ASHLNK01-bound configuration pin directly
with raw serialized BuildData. The raw pin must instead match the original
configuration authenticated through the complete native/link chain. The actual
first failing predicate in28740 was not recorded; this source defect is not a
claim that execution reached that comparison. Repair and the same13-test gate
remain pending, including canonical receipt/request association and a coherent
missing-release unresolved-symbol negative. Full byte/original/runtime checks
remain mandatory.

The [index](index.json) retains content-addressed gzip originals from three
frozen gates, receipts/maps/raw logs, actual current fixture and independent
reviews. Binary input/tool omissions carry their external pins; no generated
ELF is retained. Paths describe historical observations, not authority.

Actual evaluator-to-leaf adapters, protected current-image/provider admission,
one-shot same-FD launch/report transport, genuine acquire/copy/Finish/Trace,
Clippy and full F-core remain open. Six closure fields stay Missing. No selected
native callback or generated application was executed, and no deployment was
provisioned. Root-owned formatting/check remains due before the F-core freeze,
fresh final native artifact and approval.
