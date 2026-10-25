# Final combined checked byte/window verification

This is TASK-0051/PR #101 candidate evidence on retained milestone `e9177c50`.
It records the final combined source after the owned-call State move, complete
canonical native fixture, and independently reviewed lint-only repairs. It does
not accept whole F3 or grant public checked execution/protected authority.

The final lint-first batch passed Clippy (`--lib --tests -- -D warnings`),
473 distinct unit tests in 477 occurrences, and one compile/link-only integration
test. The actual fresh test inventory verifies all 25 selector counts and the
473-name union; the proposal's old 442-name array is historical only. The first
native positive precedes the checked-declaration omission negative and module
controls. All 47 image controls, source/Core/transform/metadata/Host/codec controls,
retained passive ledger/admission/receipt/bridge tests, and capture controls pass.

Every final command preserves the same 4,483 full inputs (`16b237fe`) and 600
runtime inputs (`955457d1`). The dedicated `parallel-f3` target uses one job,
o incremental compilation, offline/locked Cargo and an empty RUSTC_WRAPPER.
Sampled resource bounds remained below 8 GiB target storage and above 3 GiB
available RAM. This configuration is distinct from earlier shared-target runs;
no exact cross-configuration savings claim follows.

At the unchanged 327680 allowance, both fresh exact two-owner repeats use
327365; nested cleanup uses 320457, and dependent cumulative reconstruction plus
independent-library correspondence uses 325006. The dependent control also
passes exact/one-short/prefix/fresh-retry checks. No fixture, tariff or allowance
was relaxed. The native fixture repair retains complete authentic declaration
IDs, kinds, signatures and origins; removing checked definitions while retaining
the same registry is rejected as Registry. Production validation is unchanged.

The final library artifact is `86755b89` (822,991,808 bytes); the integration
test artifact is `4bf74210` (561,948,704 bytes). The latter compiles/links a legacy
native fixture and observes its producer receipt without starting the generated
executable. All 16 external associations were streamed and verified: final ELF
`abec0e66` (461,336,008 bytes), receipt `a4928390` (750 bytes), equal ordinary/built
preparation work 76649. Generated-host naming warnings in the retained build log
are separate from the successful crate Clippy gate. Native loading behavior,
checked runtime activation and protected authority remain unestablished.

`index.json` preserves original paths, sizes and SHA-256 hashes. `raw-gzip`
records decompress directly; `json-map-template-gzip` records reconstruct JSON
by replacing sole `$retained_map` objects with the referenced decompressed JSON
map, then serializing with indent 2 and a final newline. All reconstructions were
verified against original bytes. Large maps are deduplicated; no ELF, object,
archive or cache is copied into this evidence. Actual artifacts remain in the
operator target for independent audit.

The preceding e917 batch's 473 units and integration passed but Clippy exposed
three library lints. A lint-first retry exposed five test-only lints before any
behavioral tests ran. Both failures and their exact inputs remain separate from
the final green map. The earlier real canonical fixture failure and its bounded
Registry-boundary diagnosis remain in
[combined-native-fixture](../combined-native-fixture/README.md). The standalone
State-move run remains in [owned-call-move](../owned-call-move/README.md).

The task prose and this evidence were added after testing. The retained tested
task snapshot reconstructs its exact tested hash; this is not a new uniform
full-input verification after documentation additions. Independent actual-head
review/retention remains the publication gate. The next full workspace gate is
the connected F-core checkpoint; whole F3/F4/F6 criteria remain unchecked.
