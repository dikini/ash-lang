# TASK-0059: Nested Cell Validation

- ID: `TASK-0059`
- Status: active
- Related: [issue #195](https://github.com/dikini/ash-lang/issues/195), [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007](../decisions/AD-0007-typed-core-dialects.md), [DN-0053](../design/DN-0053-scoped-generic-cells-without-native-owners.md), [generic-cell specification](../../spec/static-semantics.md#generic-cell-foundation), [elaboration](../../spec/elaboration.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

The existing generic-cell rules allow helpers to access a live outer owner.
Independent linked Core validation reconstructs dependencies and control from
authenticated Core. The developer owns the connected path and Cargo slot; the
independent reviewer checks the frozen candidate. The PM owns publication and
integration coordination.

## Work

1. Reproduce the issue through the public pipeline and independent Core
   validation, then locate the invalid reconstruction.
2. Repair the existing analysis without changing semantics, admission,
   provenance, owner, capture, work, depth, or stack rules.
3. Verify the original example, positive controls, affected negative and forged
   Core cases, native execution and private-image restoration.
4. Freeze the candidate and evidence for independent review. Before PR
   publication, run a fresh full workspace gate on that exact head as the
   shared Core-validation readiness checkpoint. The PM coordinates it with the
   developer as Cargo operator. It can also serve the separately authorized
   pre-Main gate if the required inputs remain equal.

## Progress

Base: `9a8b73bb6495612cbd1521a3b1cc6e0c3e1b1c9b`. The minimal source is
`tests/fixtures/generic-cell/nested-helper-outer-read.ash`, SHA-256
`6e3dc5ba920c6edb478317282b8fd3e61b8241fd53e0b093110be4270c56ef2b`.
The original report and controls are retained at
`/tmp/ash-lab-verification-ebbw_y14/verification.txt`. The candidate passes the
focused checks below. Independent final review and the full gate remain pending.

The connected regression fails before repair: source checking and elaboration
complete, then independent Core validation reports `Handler` at 50,850 of
40,125,000 work units. The red command and output are in
`/tmp/ash-issue195-red.log` (2.28 seconds wall time including compilation).
An inner generic cell also fails; `/tmp/ash-issue195-diagnostic4.log` records
both variants with temporary diagnostic instrumentation.

## Verification

All Cargo commands used Rust 1.97.1, locked offline dependencies, one Cargo job
and an empty `RUSTC_WRAPPER`. Wall times include any compilation. Product and
fixture hashes before and after the focused checks match
`/tmp/ash-issue195-product.sha256`. The two changed capture files have SHA-256
`4ebd7663d3091fdbd76f11edf16fe77a650272fd504c4e2b8d23160b7e3e2f9e` and
`82c3552ca2da2c02715893c1b1fe841f32ccc3fc0d711818ed586bc8e5c2cb64`.

| Check | Result and receipt |
| --- | --- |
| `cargo test --locked --offline --lib symbolic_cell_ -- --nocapture` | 2 passed, including exact work refusal and retries; 143.30 s; `/tmp/ash-issue195-unit.log` |
| `cargo test --locked --offline --test resource_scope_runtime --test scoped_evidence_interactions -- --test-threads=1` | 37 and 54 passed, including local/imported nested helpers, local-cell callback, and both Core transforms; 30.91 s; `/tmp/ash-issue195-runtime-transforms.log` |
| `cargo test --locked --offline --test resource_scope_typing cell_ -- --test-threads=1` | 39 passed, including self and younger retention, recursive activation and resumed-stack enclosure; 13.27 s; `/tmp/ash-issue195-typing.log` |
| Nine exact Core and image tests | 9 passed, including forged owner/payload, possible targets, hidden retention, transformed Core and private-image reconstruction; commands and test-binary hash in `/tmp/ash-issue195-core-image.log` |
| `cargo clippy --locked --offline --all-features --lib --test resource_scope_runtime --test scoped_evidence_interactions --test resource_scope_typing -- -D warnings` | Passed; 40.79 s; `/tmp/ash-issue195-clippy.log` |
| `cargo fmt --all -- --check` and `cargo build --locked --offline --bin ash` | Passed; 7.03 s and 0.16 s; `/tmp/ash-issue195-fmt.log` and `/tmp/ash-issue195-build.log` |

The original Stream/Buffer source returned status 0, exact stdout
`Success(Success(0)) : Outcome<Outcome<Int>>` and empty stderr. Its source and
buffer SHA-256 values are `9ca168758b8e845047e42da849452d27848df91bdc690b6332df150ffc66e868`
and `e72e1274c3d81c33ea5b58d18f4f306b80ddb16ea9640f7646fa996fbbe905cf`;
the command and observation are in `/tmp/ash-issue195-handler-receipt.log`.
The imported helper with a generic inner cell was built with the matching
compiler and shared target cache, then executed twice after moving its source
directory. Both runs returned `42`, status 0 and empty stderr. Native build,
source, compiler, image and fingerprint pins are in
`/tmp/ash-issue195-native-build.receipt`; build time was 65.27 s.

The focused checks do not constitute a full workspace gate. The prior
generic-cell gate and its limits are recorded in [checkpoint evidence](../design/generic-cell/evidence.md).
The next gate runs fresh on the frozen candidate; its receipt belongs in the
handoff, not a subsequent edit to that candidate. Developer dispatch was
Terra 6.1/max and reviewer dispatch Sol 6.1/max; exact model runtimes are not
exposed by this environment.

## Discoveries

Capture-control discovery examines a generic-cell read under a symbolic helper
root. With an inner legacy cell, label matching already says the request cannot
match that frame, but operand reconstruction still rejects the symbolic
`Unknown` access. With an inner generic cell, an opaque call is conservatively
matched to the inner frame and passed to concrete operation decoding, which
rejects the call node. These failures precede focused owner proofs. The trace
in `/tmp/ash-issue195-diagnostic7.log` follows the read operand through
transparent forwarding to an existing input port recorded at acquisition.

The repair uses existing type metadata: the original standalone callable
captures the outer owner before acquiring the distinct inner owner. Focused
replay uses the same fact only for its exact designated resource and original
creation context, without traversing a restored cut. A dependency edge alone
cannot prove exclusive origin: another producer or a direct seed may coexist.
Actual calls, local-owner callbacks, recursive activations and restored frames
retain their own checks. The independent reviewer found no issue in the
candidate proof; final review awaits the frozen commit and gate receipt.

## Deviations

None. Work-limit reports #196 and #197 and the specified callback rejection are
outside this task.
