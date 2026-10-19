# TASK-0046: Generic Cell Contents and Dependencies

- ID: `TASK-0046`
- Status: active
- Related: [CP-0023](../proposals/CP-0023-scoped-generic-cells.md),
  [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md),
  [TASK-0047](TASK-0047-generic-cell-execution-and-completion.md),
  [TASK-0048](TASK-0048-generic-cell-integrated-verification.md),
  [TASK-0049](TASK-0049-close-generic-cell-checkpoint.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

Start connected implementation from TASK-0045's reviewed foundation receipt,
not from completion of all its acceptance cases. Use CP-0023 and the pinned
ash-ffi base identified in TASK-0049. Coordinate shared elaboration, summary and
Core writers; TASK-0047 can develop runtime behavior against the same agreed
carrier. Public checked admission requires this task's dependency checks.

## Work

1. Track current cell contents separately from access and earlier read results.
   Propagate possible targets and value relationships through aliases, selected
   fields, closures, evidence, indexed operation metadata, imports, type/row
   instantiation, branches and recursive calls. Preserve each earlier snapshot
   rather than updating it with the slot's later contents.
2. Prove strict enclosing-owner dependencies for initialization and actual slot
   replacements. Reject self-retention, indirect resource cycles and younger or
   incomparable owners, including hidden captures. Do not reject permitted
   immutable cycles or mistake recursive activations of one site for one owner.
3. Follow exact handler selection and actual replies. An intercepted request
   contributes no builtin replacement, but clause, other-handler and resumed-
   computation mutations update contents facts in order. Preserve both
   CELL-P13's independent reply and CELL-N12's dependent later read.
4. Preserve the existing outward payload-crossing, scoped escape, native
   revocation and structural completion rules. Add source diagnostics at the
   causal retention/escape with the precedence required by CP-0023.
5. Carry the inferred relationships through public helper summaries and linked
   preparation. Independently reconstruct them from admitted linked Core;
   source summaries, cached assertions or runtime key checks supply no substitute
   authority. Copying, restoration and transforms must re-establish the proof.
6. Make joins and recursive analysis finite and charged before proportional
   work or retention. Refuse without partial module/summary/permission publication
   and permit a fresh sufficient-budget retry. Required positive cases cannot
   be dropped as a shortcut to termination.
7. Update static semantics and the dependency/summary/Core validation portions
   of elaboration with the delivered behavior. Record algorithm choices and
   measured limitations without adding source lifetime or capture annotations.

Start from baseline `src/core/capture.rs`, `src/core/capture/value.rs`,
`src/core/capture/control.rs`, `src/elaborate.rs`, `src/resolved.rs`,
`src/core/validate.rs` and `src/core/transform.rs`. Keep source admission and
independent linked validation distinct even if they reuse authenticated data
structures or analysis machinery.

## Progress

Implementation starts from reviewed foundation
`77032c7659278a49a80dc736497649e563ec2dd9` on `codex/generic-cells`.
The task-owned [execution plan](task-0046-execution-plan.md) records the sequence.
Dependency readiness and execution readiness remain separate; all original case
criteria stay open until their complete observations exist.

- [ ] CELL-P02: earlier scalar snapshots and snapshot-only closures escape with
  their original value after replacement.
- [ ] CELL-P03: inner cells retain and return outer access while its owner lives.
- [ ] CELL-P04: an earlier independent function snapshot escapes after a later
  outer-dependent replacement and still returns `7`.
- [ ] CELL-P05: same-site recursion stores an enclosing activation's capture,
  returns `9`, and retains distinct activations with one release each.
- [ ] CELL-P08: handler-provided closures retain their actual dependencies;
  local use and independent reply escape remain admitted.
- [ ] CELL-P09: independent outward payloads and outer-dependent values crossing
  unrelated inner scopes remain admitted at their permitted recipients.
- [ ] CELL-P10: admitted ordinary immutable cycles remain usable and preserve
  observable sharing without a resource-cycle diagnostic.
- [ ] CELL-P13: a handler writes an A-dependent closure into B but replies with
  an independent function; that reply snapshot escapes and returns `7`.
- [ ] CELL-N02: handles, wrappers and live-reader/evidence closures cannot escape
  their own resource scope, including through imports.
- [ ] CELL-N03: a fixed-type stored closure capturing its own cell rejects.
- [ ] CELL-N04: indirect cycles through younger cells, wrappers and helpers
  reject; a later clearing write does not repair retention.
- [ ] CELL-N05: younger/incomparable retention and unsafe branch alternatives
  reject even without a resource cycle.
- [ ] CELL-N06: later dependent reads and dependent handler replies cannot escape.
- [ ] CELL-N07: outward request payloads preserve hidden capture, evidence and
  indexed metadata dependencies despite an independent eventual body answer.
- [ ] CELL-N12: the builtin read after CELL-P13's handler retains A and rejects
  escape at A's close.
- [ ] Independent reconstruction and charged analysis cover all these cases;
  TASK-0048's adversarial and budget checks confirm the connected boundary.

Each ID includes every CP-0023 variant. Positive observations requiring runtime
remain open until TASK-0047 connects; a source-only pass is partial delivery.

## Verification

Add named cases to `tests/resource_scope_typing.rs`,
`tests/resource_scope_modules.rs` and `tests/resource_scope_core.rs`, plus
analysis and summary unit tests. Run:

```sh
CARGO_BUILD_JOBS=1 cargo test \
    --test resource_scope_typing --test resource_scope_modules \
    --test resource_scope_core
```

For every negative case assert the prescribed phase/reason and causal labels;
pair it with the relevant permitted case. Reconstruct dependency proofs after
transforms and imported-summary substitution. Coordinate runtime observations,
recursive activation counts and cyclic-value tests with TASK-0047. TASK-0048
checks tampering and exact/insufficient/retry budgets across all paths.
Retain frozen inputs, focused results, independent review and retained-commit
verification. TASK-0049 owns the full checkpoint gate.

### Resumed dependency delivery, 2026-10-19

The retained code candidate is
`3f72e9ce3a1822631eb94762dbe1f6c0bde1806c`, an unsigned descendant of the
reviewed foundation. The resumed developer and sole Cargo operator is
`/root/task0046_developer`; `/root/task0046_reviewer` supplies independent
review and `/root` owns acceptance. The developer dispatch retains requested
`gpt-6.1-sol`, `medium`; exact model runtime is unavailable. Historical
TASK-0045 assignments and results remain recorded in TASK-0049.

The pre-pause whole-library process was cancelled with exit 130. Its old
`/tmp` logs are absent after resume and supply no transferred result. Fresh
verification found and repaired a 64 KiB stack regression, exact-handler target
ambiguity and diagnostic/coverage gaps before this candidate was frozen.

Independent code and technical-evidence review by
`/root/task0046_reviewer` is clear at this pin. Root independently read the
retained file records and focused results. The coordinator accepted dependency
readiness at this code pin, preserving the original compound criteria and
TASK-0047/0048/0049 obligations. Complete task/checkpoint acceptance remains open.

The following is dependency evidence; it does not complete the original case
criteria above. Test names are in `tests/resource_scope_typing.rs` unless a
module is named. Each paired test retains its variants and causal assertions.

| Family | Named dependency evidence |
| --- | --- |
| P02, P03 | `cell_p02_snapshots_and_p03_enclosing_access_check_without_runtime_permission` |
| P04 | `cell_p04_snapshot_stays_independent_after_dependent_replacement`; `cell_p04_imported_read_helper_preserves_two_call_snapshots` |
| P05 | `cell_p05_recursive_activation_retains_enclosing_capture`; module test `cell_p05_imported_recursive_predecessor_relation_reconstructs_from_linked_code`; recursive self-replacement and resumed older-slot negative companions |
| P08, N06 | `cell_p08_actual_handler_reply_dependencies_pair_with_n06_escape` |
| P09, N07 | `cell_p09_independent_and_enclosing_payload_crossings_pair_with_n07`; imported evidence, indexed-metadata and outer/inner write-interceptor crossing companions |
| P10 | `cell_p10_independent_cyclic_immutable_payload_remains_admitted` |
| P13, N12 | `cell_p13_reply_snapshot_and_n12_later_builtin_read_keep_distinct_dependencies` |
| N02 | `cell_n02_hidden_access_closures_and_n05_unsafe_payload_joins_reject`; `cell_n02_access_wrappers_and_live_reader_results_cannot_leave_their_owner`; imported evidence companions |
| N03, N04 | `cell_n03_self_retention_and_n04_younger_cycle_reject_at_write`; `cell_n04_wrappers_and_selected_fields_keep_only_actual_payload_dependencies`, including genuine indirect cycles, opaque projections, imported capture factories and later-clear variants |
| N05 | `cell_n05_resumed_stack_does_not_extend_an_older_slots_birth_enclosure`; `cell_n05_every_possible_target_must_admit_the_replacement`; unsafe-join companions |

Additional paired source/Core tests distinguish actual handler owner arguments
through imported distinct/equal substitutions and a nonforwarding exact write
interceptor. The shared fixtures are independently rebuilt from actual Core
after identity/folding transforms. Available-code generic fixtures require
source/compiled admission parity; dependency-negative fixtures require the
typing phase, reason and causal labels. The dedicated missing-provider-code raw
API refusal remains separate from the authenticated public imported native-access
positive.
`generic_cell_dependency_admission_does_not_grant_execution_permission` confirms
that neither evaluator nor build publication receives generic execution
permission from this proof.

The candidate supplies implementation and focused evidence for all seven work
items at this boundary. Runtime observations, release counts and cyclic-value
sharing remain with
TASK-0047; the complete adversarial, capacity, native and budget matrix remains
with TASK-0048. The connected fresh full checkpoint gate remains with TASK-0049.
The unchecked original criteria are preserved.

The code tree is `0cae369bddc33a0355aaf08604f968824166bf76`. The frozen
manifest contains 1,759 tracked/non-ignored file records (path, mode and content
SHA-256), with canonical records digest
`37f7f6adaf44714775ab4d3a32fa5c50bbd1a98b4ff0f36f4a39f77d8c942986`.
Every run below preserved those exact records. Rust/Cargo 1.97.1,
rustfmt 1.9.0 and Clippy 0.1.97 were reconfirmed before handoff, as were the
manifest, lockfile, toolchain and Cargo configuration hashes. The inherited
Cargo configuration SHA-256 is
`13ed130670278614272c1fca1af627d4e427b8d306cd530a96f0d7555dbcd6a5`.
All commands ran sequentially in the product checkout with
`CARGO_BUILD_JOBS=1 RUSTC_WRAPPER=` and its stable target cache.

| Focused command | Result | Log SHA-256 |
| --- | --- | --- |
| `cargo test --lib --locked` | 1,916 passed | `74024bd79fe428d2d52ba73f57905a69c2876c9ff0a612fa3916838db69e115b` |
| `cargo test --test resource_scope_typing --test resource_scope_modules --test resource_scope_core --locked` | Core 2, modules 16, typing 101 passed | `cf90fddbb5b0996d5bc9e60d59ff4ee39093cbd9ec813315163866a9ce40ffdf` |
| `cargo test --test source_resource_execution --test source_resource_acquired_only --test native_buffer_source --test native_buffer_runtime --test native_buffer_interactions --test provider_retention_source --test resource_scope_runtime --locked` | 130 passed across seven targets | `c813b281deb66599e7d4c4db90f056518b00548002b3a070bd7ea9e56d3749d4` |
| `cargo clippy -p ash --all-targets --all-features --locked -- -D warnings` | Passed, warnings denied | `f7e2345b1c2044b852d65a036c2adf9daa9851ead6eefeb64a296a50f3f87028` |
| `RUSTDOCFLAGS="-D warnings" cargo doc -p ash --no-deps --all-features --locked` | Passed, warnings denied | `ce0c419bb2154defc5c9f90997f0d4de6f08ad27e8516f44432decd5701f90e3` |
| `cargo fmt --check` | Passed | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |

The three-suite command is the task-prescribed scope. The seven affected targets
cover source Scope/acquired-only phases, real native buffer interactions,
retention, blocked teardown and structural cleanup. Child-process reruns within
a test are not counted as additional test cases. The library run includes the
unchanged 64 KiB stack test, summary/import reconstruction, transformed Core,
State restrictions and exact/one-short/fresh-retry unit probes.

Library, resource and caller runs are fresh at the retained code commit.
Clippy ran before the administrative commit while the prior Git HEAD remained
`1c460f4eb07b156773521ff3b4d1e6a4dbe3d046`; its complete file records match the
retained candidate exactly. This transfers that focused result across Git
metadata only. These commands and custom working receipts are focused evidence,
not canonical verification-stage receipts or a complete workspace gate.
Working logs, file records and per-command receipts are in
`/tmp/task0046-resume/`; the durable pins, results and hashes are retained here.
Later receipt-only prose changes receive manual documentation checks and do not
claim a new code run. Root verifies their source/config equality before retaining
the handoff.

## Discoveries

The candidate uses ordered immutable value ports in control states, separately
from native monotone retained-data summaries. Focused reconstruction fixes each
target's acquisition enclosure and preserves it across continuation movement.
Recursive context folding merges ordinary formal inputs, so their owner atoms
alone cannot prove strict enclosure. The candidate instead retains a conditional
relation to existing original free-input ports frozen before fresh owner birth;
subtree inputs, missing/future ports and the fresh access cannot witness it.
Actual owner atoms remain available for later crossing and escape checks. The
same relation is rebuilt from linked Core rather than trusted from a summary.
Independent review of the retained dependency candidate is clear; the focused
verification record above pins its results and remaining obligations.

Stricter causal-diagnostic probes found an early builtin routing refusal when
conservative type matching considered an inner same-payload cell for an outer
access target. The repair intersects label matching with actual target
occurrences and preserves outward alternatives. It does not change ordinary
source-handler precedence. Review also identified full-State replay lookups
whose precharges omitted either the heap or newly nested cell vectors on hits;
a shared structural-key precharge and width/refusal/retry probes address those
sites in the candidate.

An enclosing declared-source access remains an ordinary eligible payload. The
public driver retains original provider code for its checked module pass and
independent linked validation. The raw `check_module` API receives only the
caller-supplied summaries and, by default, no imported provider code; its
missing-code refusal is a separate fail-closed control, not a language rejection
of that payload. The native-access probe records both API inputs explicitly.

Exact source handlers need the same actual-owner precision as builtin routing.
The candidate carries an authenticated owned-argument value port on the handler;
selection intersects known acquisition identities while retaining unmatched
outward paths. Free, unknown or uninstantiated alternatives preserve ordinary
conservative matching. Type-application metadata unions distinguish their
neutral seed from a genuine independent-value alternative. This distinction is
rebuilt from Core, copied through summaries and charged through the existing
equations; it supplies no source safety assertion or new runtime form. Imported
distinct/equal owner substitutions and intercepted self-dependent writes cover
both precision and refusal.

Diagnostic enrichment follows a generated Scope report's answer only when that
actual answer port retains the escaping owner; a completion-only dependency
keeps the report origin. Public native Scope probes pair a hidden body capture
with an independent function result. Unmaterialized original free-input ports
are omitted from predecessor witnesses rather than created as future evidence.
Private native phases retain their existing supported-control profile: a nested
generic scope receives the ordinary profile refusal, not new phase support.
Existing actual-State capture rejection and exact restricted-payload reasons
remain required.

The unchanged 64 KiB capture test exposed aggregate Rust frame pressure in the
finite graph-building call chain. Optional causal labels now use a fallible,
precharged fixed two-role carrier, with one-short/exact/fresh-retry probes and
no allocating failure clone. On this target, the actual foundation and compact
failure enums both measure 48 bytes. A bounded handler-builder extraction keeps
operation and charge order unchanged; independent inverse-extraction comparison
reproduced the previous file exactly. The fresh whole-library run includes the
original stack bound. No work allowance or test stack was increased.

An analysis that cannot admit a required positive remains unfinished work or a
semantic question for CP-0023, not an implicit reduction in scope.

## Deviations

None authorized. Cell scope lifetime and resource-cycle rejection are fixed;
temporary younger retention, new capture annotations and DN-0054 region
mechanisms are excluded.
