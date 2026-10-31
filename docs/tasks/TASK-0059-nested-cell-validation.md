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

Base: `9a8b73bb6495612cbd1521a3b1cc6e0c3e1b1c9b`. The original report and
controls are retained at `/tmp/ash-lab-verification-ebbw_y14/verification.txt`.
The minimal source `tests/fixtures/generic-cell/nested-helper-outer-read.ash`,
SHA-256 `6e3dc5ba920c6edb478317282b8fd3e61b8241fd53e0b093110be4270c56ef2b`,
passes source checking and elaboration before independent Core validation fails
with `Handler` at 50,850 of 40,125,000 work units. The red command and output
are in `/tmp/ash-issue195-red.log`. An inner generic cell also fails, as traced
in `/tmp/ash-issue195-diagnostic4.log`.

The first candidate `d2438c1953b84c5d39f19f51550afab0c1ec6cea` passes the
initial controls. Review then found that
`tests/fixtures/generic-cell/nested-helper-inner-handler.ash`, SHA-256
`01abd26d5d58b9a40e9a78c46d8362a68b120c89b9d91e6dbff396a6c4aabf58`, also
fails `core.validation.handler`: it explicitly reads an inner cell under its
exact source handler and then reads the live outer cell. The red public-pipeline
observation is in `/tmp/ash-issue195-handler-red.log`; the original source and
compiler pins are in `/tmp/ash-issue195-review-handler-default.log`. A wrapper
without the explicit inner read fails earlier under the exact effect-input rule
(`/tmp/ash-issue195-review-handler-probe.log`). The first candidate's full gate
was interrupted when this finding arose. Its partial output is in
`/tmp/ash-issue195-gate.log` and
`target/verification/logs/1793472455379099856-5-*.log`.

A second review check mutates a valid transformed Core program to retain the
inner owner in a closure written to the outer cell. Independent validation
initially returned `Handler` instead of the expected dependency escape
(`/tmp/ash-issue195-forgery-test.log`). The valid donor executes `42` before
and after each transform; the repaired validator rejects each mutated copy as
`ResourceEscape` (`/tmp/ash-issue195-r2-core-image.log`).

## Verification

All Cargo commands used Rust 1.97.1, locked offline dependencies, one Cargo job
and an empty `RUSTC_WRAPPER`. Wall times include compilation. Product, test,
fixture and build-configuration hashes are in
`/tmp/ash-issue195-current-product.sha256`.

| Check | Result and receipt |
| --- | --- |
| `cargo test --locked --offline --lib symbolic_cell_ -- --nocapture` | 3 passed, including root/focus, mixed-owner and exact-work refusal/retry cases; 0.17 s; `/tmp/ash-issue195-r2-unit.log` |
| `cargo test --locked --offline --lib cell_escape_call_uses_an_existing_dependent_input -- --nocapture` | Passed for later-argument and captured-callable witnesses, missing/no witness, and exact-work refusal/retry; 20.18 s; `/tmp/ash-issue195-call-witness-unit.log` |
| `cargo test --locked --offline --test resource_scope_runtime --test scoped_evidence_interactions -- --test-threads=1` | 41 and 54 passed, including local/imported and legacy helpers, exact local/outer handlers, local callback and Core transforms; 29.99 s; `/tmp/ash-issue195-r2-runtime.log` |
| `cargo test --locked --offline --test resource_scope_typing cell_ -- --test-threads=1` | 39 passed, including self and younger retention, recursive activation and resumed-stack enclosure; 9.93 s; `/tmp/ash-issue195-r2-typing.log` |
| Exact Core, image and control tests | 11 passed, including transformed hidden retention, possible targets, forged owner/payload, private-image reconstruction and removed-handler refusal; 12.85 s; commands and binary hash in `/tmp/ash-issue195-r2-core-image.log` |
| `cargo clippy --locked --offline --all-features --lib --test resource_scope_runtime --test scoped_evidence_interactions --test resource_scope_typing -- -D warnings` | Passed; 17.35 s; `/tmp/ash-issue195-r2-clippy.log` |
| `cargo clippy --locked --offline --all-features --lib --tests -- -D warnings` | Passed, including inline tests; 47.11 s; `/tmp/ash-issue195-r2-clippy-tests.log` |
| `cargo fmt --all -- --check` and `cargo build --locked --offline --bin ash` | Passed; 6.29 s and 0.14 s; `/tmp/ash-issue195-r2-fmt.log` and `/tmp/ash-issue195-r2-build.log` |

The matching compiler reproduced the original Stream/Buffer result: status 0,
exact stdout `Success(Success(0)) : Outcome<Outcome<Int>>` and empty stderr.
The same compiler returned `42` for the review source, an outer write/read
through an inner handler, intercepted outer write, resumed handler and outer
cleanup past a removed handler. Cleanup requiring the removed inner handler
still failed with `effect.cleanup-context`. Compiler and source hashes,
commands and results are in `/tmp/ash-issue195-r2-probes.log`.

The imported helper with the exact inner handler was built with the matching
compiler and shared target cache. Two executions after moving the source
directory returned `42`, status 0 and empty stderr. Native build, compiler,
input, image and runtime-fingerprint pins are in
`/tmp/ash-issue195-r2-native-build.receipt` and
`/tmp/ash-issue195-r2-native-run.log`; build time was 13.49 s.

Focused checks do not constitute a full workspace gate. The prior generic-cell
gate and its limits are recorded in [checkpoint evidence](../design/generic-cell/evidence.md).
The next gate runs fresh on the frozen candidate; its receipt belongs in the
handoff, not a subsequent edit to that candidate. Developer dispatch was
Terra 6.1/max and reviewer dispatch Sol 6.1/max; exact model runtimes are not
exposed by this environment.

## Discoveries

Capture-control discovery examines a generic-cell read under a symbolic helper
root. With an inner legacy cell, label matching already says the request cannot
match that frame, but operand reconstruction still rejects the symbolic
`Unknown` access. With an inner generic cell, an opaque call is conservatively
matched to the inner frame and passed to concrete operation decoding. The trace
in `/tmp/ash-issue195-diagnostic7.log` follows the read operand through
transparent forwarding to an existing input port recorded at acquisition.

The repair uses authenticated type metadata: the original standalone callable
captures the outer owner before acquiring the distinct inner owner. Focused
replay uses that fact only for its exact designated resource and original
creation context, without traversing a restored cut. The same proof excludes an
inner source handler only when every reconstructed handler-owner occurrence
has that proof. Empty, unknown, mixed, equal and unrelated occurrences retain
the existing strict path. Actual calls and local-owner callbacks still use
their own checks. A dependency edge alone cannot prove exclusive origin:
another producer or a direct seed may coexist.

The transformed-Core negative reached the focused payload check, which found a
younger-owner escape in a Call input. Diagnostic reconstruction then expected
only a Request and converted the escape to `Invalid` (`/tmp/ash-issue195-forgery-trace3.log`).
The corrected path searches existing Call inputs in the same order as payload
checking, requires an exact dependent owner, charges the work and reuses the
existing dependency and call-site provenance. A missing witness remains
invalid; no new input port is constructed.

## Deviations

None. Work-limit reports #196 and #197 and the specified callback rejection are
outside this task.
