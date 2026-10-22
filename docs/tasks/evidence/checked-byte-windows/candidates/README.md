# Initial checked byte/window carrier candidates

These are focused static candidate results, not delivery acceptance. Each
command uses one shared-cache job and `cargo test --offline --locked --lib
checked_byte_window_ -- --nocapture`. All three complete before/after maps have
591 identical entries per command; raw log hashes and commands are in receipts.

| Candidate | Actual result | Aggregate prefix |
| --- | --- | --- |
| candidate-initial | Compile-only exit 101: new roles missing from private image Wire writer; unused import. No tests ran. | b647df5e |
| candidate-wire-tags | Library compiled; lib-test compile exit 101: existing hostile-image test match missing new roles. No tests ran. | af43fcde |
| candidate-role-dispatch | Compile passed, 4/5 tests passed; real source-template admission refuses Source Argument at resource span 3347..7619. | c041b45a |

The four passing controls in the third run are genuine initialized-State/view
preparation, default-profile refusal, isolated checked Bytes-owner binding and
all four new builtin names resolving. The connected all-four source/summary
positive remains unmet. The generic source-template error does not identify
which underlying registry, structure or flow predicate failed. A single pinned
GDB probe retained here did not reach `source_resource::invalid`; it supplies no
flow-site attribution, and its GDB process exit 0 is not a test pass.

Each subdirectory contains `source.patch` against unsigned checkpoint
`3cdde7d0d525f2d988ea338f305447f00b6d3bfb` plus the added
`src/foreign/scalar_preflight/checked_memory.rs` bytes and reconstruction JSON.
Apply the tracked overlay and install that new file to reproduce the complete
recorded input map. The final candidate test artifact is SHA256
`8a8ef81edf6de158e18a0b3dc7a581790a64aec312d29822eeb2d77a32a5f631`.
The selected F2 `target/debug/ash` remains SHA256
`5dca1b624bf206c44c6c4d3037675193800516eb936a0cf6420e67394e998d3e`.
No native/image startup ran. Compiler-only failures are not semantic refusals.

After the third run, the passive image decoder's exact quantifier-role list was
paired with the encoder's four new roles. That reviewed static correction is
unexecuted at this checkpoint; it preserves exact Type IDs/module/formal checks
and grants no checked runtime or image activation. Source/consumer/Core/
transform/static-image positives, hostile controls, bounds and regressions stay
pending. Existing checked execution refusal remains.
