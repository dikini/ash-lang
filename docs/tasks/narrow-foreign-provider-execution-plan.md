# Narrow Foreign Provider Implementation Plan

**Goal:** Implement the accepted CP-0020 native-buffer contract and retain all
FOREIGN-01 through FOREIGN-10 evidence.

**Architecture:** Extend the closed builtin resource choices and existing
Effect Resource carrier. Keep raw pointers in a small safe-owning runtime
adapter; retain activation identity, capture and structural closing in the
current evaluator. Add no registry or general destructor/acquisition protocol.

**Tech stack:** Pinned Rust, Cargo, host C `calloc`/`free`.

**Owner:** [TASK-0030](TASK-0030-implement-narrow-checked-foreign-provider.md).
This plan organizes the accepted proposal; it defines no semantics.
Use subagent-driven development with test-first changes and separate contract
and quality review. The parent owns Cargo scheduling and final integration.

## 1. Isolated native owner

Files: new `native-buffer/Cargo.toml`, `native-buffer/src/lib.rs`,
`native-buffer/README.md`; workspace `Cargo.toml` and `Cargo.lock`.

1. Add focused tests for positive bounded length, zeroed allocation, checked
   read/write, rejected access leaving bytes unchanged and owner drop. Observe
   the missing implementation before implementing the safe owning API.
2. Implement the smallest owning wrapper over C `calloc`/`free`. Keep the pointer
   private and non-cloneable; validate lengths before calling C and bound every
   offset. Document each unsafe operation and the exactly-once Drop invariant.
3. Add deterministic allocation-failure and release evidence without replacing
   real native success tests. Keep fault injection private to tests.
4. Run `cargo test -p ash-native-buffer`, then strict package Clippy and ARM64
   compile checks. Record the first-party dependency and linking audit.
5. Review CP-0020 compliance, then Rust safety and code quality. Commit unsigned
   only after focused checks pass. This step contributes FOREIGN-02/03/08/10;
   evaluator-level publication and release evidence is still required.

## 2. Compiler admission and independent validation

Files: `src/parser/grammar.rs`, `src/parser/project.rs`, `src/surface.rs`,
`src/module.rs`, `src/resolve.rs`,
`src/resolved.rs`, `src/elaborate.rs`, `src/evidence.rs`, `src/interface.rs`,
`src/evidence_validation.rs`, `src/core/effect.rs`, `src/core/dialect.rs`,
`src/core/validate.rs` and their
existing traversal/transform helpers as required by compiler errors.
Tests: new `tests/native_buffer_syntax.rs`, `tests/native_buffer_typing.rs`,
`tests/native_buffer_modules.rs`, `tests/native_buffer_core.rs` and existing
internal builtin-summary tamper tests.

1. Add failing syntax/import/type tests for the exact CP API and nested Outcome.
2. Extend fixed resource selection and builtin identities; retain direct import
   provenance and sealed provider authority. Reuse dependency and row machinery.
   Authenticate the exact ordinary Outcome/Error constructors while keeping
   Handle's hidden constructor forbidden. Do not generalize the cell's blanket
   constructor rejection to the new builtin.
3. Generate length/read/write provider methods through existing evidence paths.
   Wrap only the acquisition result type; keep body type and scope obligations
   distinct. Preserve cell types, syntax and behavior.
4. Add and observe failing independent linked/Core tamper tests, then implement
   exact registry, acquisition, method, result wrapper and row authentication.
   Exercise both Core transforms and prove malformed input never reaches C.
5. Run new syntax, typing, module and Core targets plus predecessor resource
   targets. Review contract then quality; commit unsigned when green.
   Covers FOREIGN-01/04/06/07; runtime evidence remains open.

## 3. Evaluator acquisition, access and structural release

Files: `src/eval/machine.rs`, `src/eval/value.rs`, `src/eval/mod.rs`,
`src/eval/instantiation.rs` only where needed, root `Cargo.toml`;
new `tests/native_buffer_runtime.rs` and machine unit tests.

1. Add failing end-to-end tests for the exact proposal example, invalid lengths,
   nested body failure, zero bytes, index-before-byte precedence and length.
2. Extend the existing frame payload with a closed native owner choice. Keep
   handles non-owning and dispatch by authenticated API and lexical activation.
3. Charge proportional work and reserve fallible result/publication storage
   before allocation. Guard successful allocation until atomic publication;
   inject post-success failure and prove release with no body authority.
   Reserve an actual outcome heap slot, not merely spare Vec capacity that the
   body can consume. Keep the prepared slot unreachable until its result exists.
4. Reserve result wrapping and disposal work at acquisition. Normal completion
   releases then wraps; discard skips wrapping. Under the accepted fail-stop
   amendment, detect teardown resource failure and terminate without source
   cleanup, retries or recovery; report incomplete cleanup rather than claiming
   release succeeded. Do not add a second closing schedule.
   Mark each abandoned native owner to skip its wrapper when collecting the
   existing closing frames; action-local acquisitions still complete normally.
5. Test allocation failure, work exhaustion before native calls, write atomicity,
   fresh activations, captured owners and exact capacity reuse.
   Test negative host conversion inside the Rust integer boundary: current Ash
   source has no subtraction or negative literal syntax. Source cases cover zero
   and oversized positive lengths, indices and bytes without extending arithmetic.
6. Run `cargo test --test native_buffer_runtime` and focused machine tests;
   review contract then quality and commit unsigned when green.
   Covers FOREIGN-02/03/04/08/09 with real and injected native observations.

## 4. Composition and adversarial evidence

Files: new `tests/native_buffer_interactions.rs`; predecessor resource, cleanup,
hook and Core test files where shared fixtures already exist.

Before this gate, implement the accepted failure-boundary amendment test-first:
retain bounded failure records distinguishing capacity, allocator refusal and
work exhaustion with their phase; audit resource-bearing teardown and error
temporaries for detectable failures; preserve primary/secondary failures and
cleanup status; verify minimal diagnostic fallback without rich allocation.
Replace the superseded zero-growth assertion with explicit injected exhaustion
and fail-stop observations. Keep the atomic refused-allocation outcome and test
that initializer effects remain committed while no body authority is published.
Do not add retry, rollback, larger limits or a general ownership framework.

The amendment is split into two reviewable increments:

1. In `src/eval/machine.rs` and `src/eval/mod.rs`, introduce a fixed-size failure
   record retaining a primary cause, optional teardown cause and cleanup status.
   Preserve legacy failure constructors and codes. Distinguish native admission
   and access work exhaustion, capacity limits and allocator refusal, including
   the narrow acquisition path through `src/eval/instantiation.rs`. In
   `src/main.rs`, write resource-failure diagnostics directly to the existing
   output writer without building a rich String. Observe classification and CLI
   tests failing before implementation; check status 2, empty standard output,
   bounded output and writer-failure behavior. Add refused-allocation evidence
   that initializer effects remain committed and the body is never entered.
2. Audit and implement detectable teardown failures against that reporting
   boundary. Preserve primary failure and completion status; do not attempt
   recovery or silently continue evaluation. Replace the old zero-growth test
   only with explicit fail-stop tests. Review the affected destruction paths
   before changes; no quadratic traversal or general ownership framework.

Run focused library/native and binary diagnostic tests for each increment,
then strict workspace Clippy and formatting. Contract review precedes quality
review and any unsigned checkpoint commit. Full FOREIGN closure remains later.

1. Add failing cases for mixed owners, inner cleanup access, resume and recursive
   owned discard, skipped suffixes, running/outside-owner rejection and internal
   disposal. Implement only gaps exposed by these tests.
2. Cover source override precedence and closing-context rejection, imported and
   generic helpers, same-site reentrancy, independent owners and stale handles.
3. Retain exact/one-short/fresh work checks, deep disposal and provider-free
   no-state evidence; distinguish native calls from mock-only coverage.
4. Run focused new targets and all predecessor resource/cleanup/hook targets.
   Review effects/provenance and existential pressure, followed by Rust/resource
   quality. Close FOREIGN-04/05/06/07/08/09 only with inspected evidence.

## 5. Specification and integration closure

Files: `spec/syntax.md`, `spec/name-resolution.md`, `spec/static-semantics.md`,
`spec/elaboration.md`, `spec/dynamic-semantics.md`, `spec/README.md`,
`docs/tools/ash.md`; new
`docs/design/effect-ash/narrow-foreign-provider-evidence.md`; DN-0028 and indexes.

1. Update normative branch text only alongside implemented conformance tests.
   Test the exact source/CLI example and record actual rendering.
2. Map every FOREIGN row to concrete tests, commands and reviewed invariants.
   Record target gaps and dependency/linking evidence without claiming native
   ARM64 execution from a cross compile.
3. Run `cargo xtask verify`, strict lint through that command, ARM64 check,
   Markdown lint, relative-link and authority checks. Obtain independent final
   contract and code-quality approval and fix findings before closure.
4. Retain one product checkpoint with code, tests, spec and evidence. Remove
   CP-0020, TASK-0030 and this temporary plan from the completed product branch,
   updating their indexes; Git preserves the transition.
5. Merge unsigned into `integration/effect-ash-foundations`, verify the merged
   checkout, then remove only the clean merged feature worktree and branch.
   Preserve unrelated main changes and pinned worktrees. Do not push or tag.

## Execution record

- Setup: isolated worktree created; baseline workspace tests passed (2,545
  top-level plus 8 subprocess tests; `/tmp/ash-foreign-baseline-20260908.log`).
  Independent compiler mapping confirmed the existing Resource carrier can be
  reused; it identified selective Outcome/Error constructor authentication as
  distinct from the opaque Handle policy. Plan paths updated accordingly.
- Step 1: native owner implemented; 6 package tests, strict Clippy, rustdoc and
  ARM64 package compile checks pass. Independent contract and high-reasoning
  unsafe/code-quality reviews passed; evaluator
  integration remains open. Step 2 syntax test observed red
  at the missing `native_buffer` designator; contextual name and malformed input
  tests already pass (`/tmp/ash-native-syntax-red-20260908.log`).
  Parser/projection now retain the closed designator; 4 new and 4 predecessor
  syntax tests pass. Three runtime tests now fail at `module.unknown-builtin`
  (`/tmp/ash-native-runtime-loader-red-20260908.log`). Exercising the proposal
  example exposed unparenthesized payload patterns; corrected them to existing
  Ash constructor-pattern syntax without changing its contract.
  A red test also caught old resolution treating the new designator as a cell
  under a cell-only import. The guard now fails closed pending native builtin
  admission; that negative passes. Total focused frontend checks: 19 syntax/
  module tests plus this authority negative.
- Steps 3–5 were pending at the first checkpoint. No FOREIGN evidence row is
  complete yet.
- Step 2 compiler admission/typing/authentication now delegated at high reasoning;
  parent prepared runtime bounds and cleanup/capture/override fixtures. Runtime
  implementation remains pending compiler integration.
- Independent compiler contract review found and then cleared two control gaps:
  native allocation failure now reaches the continuation after initializer
  completion without entering the body or installing its owner; restored native
  results preserve Success projection around their frozen body value without
  reacquisition. Both source regressions were observed red, then green. Parent
  reran 23 native compiler integration tests and 9 internal authority/restoration
  tests successfully. Separate high-reasoning quality review passed; parent
  strict Clippy passed. Compiler checkpoint approved; runtime remains fail-closed.
- Step 3 is underway. Parent verified all eight interaction tests against the
  initial runtime implementation. A combined recursive native-owner/cleanup
  witness exhausted checker work before evaluation: in the retained recursive
  discard test, wrap the native body in `cleanup fn(ignored) { perform Record.digit
  depth } { ... }`. Using `Buffer.length b` instead of `depth` also exhausts work.
  Removing only that cleanup layer admits recursive native ownership and discard,
  with all body suffixes skipped. Separate tests retain native cleanup access,
  capture/resume/discard and mixed structural ordering. This resembles the
  previously recorded combined recursive cleanup/resource limit; admission of
  this combined stress case remains unproved. No limit or analyzer changed.
- Parent subsequently verified all 19 native runtime/interaction/import tests
  and 9 private runtime boundary tests. Runtime contract review remains blocked
  by teardown allocation: inherited capture flattening can grow storage before
  native release, and environment/type destruction can precede release on error
  paths. See the task's proposed prerequisite. The experimental allocation-free
  frame rotation was quadratic and is not retained. No runtime checkpoint,
  full verification, evidence closure or integration is claimed.
- While the teardown prerequisite awaits direction, parent independently verified
  the exact CLI fixture: successful exit, `Success(Success(42)) : Outcome<Outcome<Int>>`
  plus newline and empty stderr. `cargo check --workspace --all-targets --target
  aarch64-unknown-linux-gnu --locked` also passed. This is ARM64 compile evidence,
  not native ARM64 execution or release conformance. The teardown regression
  remains enabled and failing; no implementation expansion was made.
- The user subsequently accepted CP-0020's fail-stop resource-failure amendment
  and the atomic allocation-attempt boundary. The approval gate is resolved;
  implementation remains pending. Earlier zero-growth expectations and the
  proposed allocation-free teardown prerequisite are superseded, not silently
  satisfied. No test has yet been removed or relabeled as passing.
- Failure-reporting implementation is underway in a bounded high-reasoning
  subagent. Records retain resource/limit identity as well as cause and phase;
  unlabeled numeric amounts would not distinguish owner, activation and storage
  limits. Stable storage-reservation APIs may not expose whether refusal arose
  from allocation or representation capacity. Report that underlying cause as
  undetermined rather than inventing allocator or RAM-quota precision. No
  duplicated allocator model or unstable API is introduced.
- Amendment Markdown checks pass with only table line-length checks disabled;
  ordinary prose retains the standard line-length check.
- The reporting increment now retains fixed primary/secondary records and a
  bounded CLI writer. Focused reporting and native checks pass, but this is not
  a completed runtime checkpoint. Independent contract review found that
  refused allocation drops prepared environment and instantiation state before
  returning. Parent reproduced the new enabled regression: one environment
  worklist growth and one allocating type-disposal call, where neither is
  allowed. The earlier captured-frame zero-growth regression also remains red.
  Neither test is ignored. The next change must cover disposal before failure
  delivery as well as terminal teardown; ordinary native refusal must remain
  recoverable. A separate reachable-environment preflight scan is not retained.
- Shared fallible disposal now reuses the existing environment, captured-frame,
  type and kind traversals with eight inline work slots and fallible spill
  storage. Refusal delivery admits no spill allocation; insufficient retained
  capacity fails terminally. The former captured zero-growth test was replaced
  by injected exhaustion that first failed with a missing teardown report, then
  passed with primary/secondary failure and incomplete-cleanup evidence.
  Parent independently reran all 1,201 library tests, four refusal tests, the
  captured-exhaustion test, two scope/worklist tests and the handler-selection
  failure test successfully. Six imported-native tests also pass, covering
  generic capture/evidence escape, exact hook coincidence and row-lacks pairs.
  The implementer additionally passed 13 CLI and 17 runtime/interaction tests,
  strict Clippy and rustdoc. Independent contract re-review passed; separate
  high-reasoning Rust quality review is pending. Parent's fresh ARM64 workspace/
  all-targets compile check passed, without a native-execution claim. No runtime
  checkpoint or full FOREIGN closure is claimed.
- Changed Markdown relative paths resolve (47 links across ten files). Full
  changed-file Markdown lint found one new overlong prose line, now wrapped,
  and 24 overlong prose lines whose exact text already exists at `HEAD`.
  Table and formal-code line lengths were excluded from that check; no
  unrelated prose was rewritten. Amendment/task/plan lint passes separately.
- Parent's full `cargo xtask verify` passed on 2026-09-09 before the next reporting
  correction. The architecture target took 331 seconds (baseline: 341 seconds).
  Independent quality review found no further ownership/disposal issue, but
  found that shared capture-capacity failures and native request-selection work
  exhaustion still return legacy errors without resource details. Those paths
  bypass bounded diagnostic output when teardown succeeds. The implementer is
  correcting these existing paths test-first, retaining legacy reason codes
  alongside cause/phase/resource details. Quality approval and the runtime
  checkpoint remain pending; this successful verifier run does not waive the
  finding or close remaining FOREIGN evidence.
- The reporting audit also found legacy-only failures in cleanup entry,
  cleanup/registration/cell admission, environment and heap representation
  bounds, registration invocation counts and default generic instantiation.
  Each is reachable with an enclosing native owner, so none is an accepted
  exclusion. Complete their detectable-failure reporting in the same correction,
  preserving legacy primary codes and existing algorithms, charges and limits.
  Tests must cover native-outer failure contexts as well as direct bounds.
  Infallible host-allocation APIs do not expose a returned refusal to this
  mechanism; replacing them is not part of this implementation correction.
- Direct-path reporting corrections passed a fresh parent run of 1,210 library,
  14 CLI, nine native runtime, eight interaction and seven import tests.
  Contract re-review found two remaining generic row-helper defects: fallible
  clone reservations can panic, and row canonicalization converts storage
  refusal into a synthetic maximum work charge. Both are detectable failures
  within the accepted boundary. Correct them test-first through the existing
  helpers, preserving algorithms, work charges and limits; then repeat contract
  review before quality review. The earlier full verifier run predates these
  changes and is not final verification.
- The tool guide now describes tested bounded resource diagnostics, including
  unknown storage causes, primary/secondary failure retention and external
  termination limits. Its Markdown lint passes. All 63 relative file links in
  the eleven changed Markdown documents resolve; this does not check anchors.
  A read-only FOREIGN-07 audit confirms that linked mutations belong in the
  existing resolved-resource helper. Expression result and outward-row facts
  remain Core checks, while linked constructor checks authenticate result data.
  Extend these existing tests rather than add another validation layer.
- Row-helper regressions first reproduced six clone reservation panics and six
  reconstruction misclassifications, then passed after explicit storage-error
  propagation through the existing helpers. A native-owner-live regression also
  passes: it reports storage refusal, releases the owner once and runs neither
  callback nor suffix writes. The implementer is running broader checks;
  independent contract re-review is active. These are implementer results, not
  final parent verification or quality approval.
- Contract re-review cleared cloning but found the same storage/work confusion
  in the comparison worklist reached by canonicalization and tail membership.
  Distinct effect identities in the first tests bypassed that path. Extend the
  existing callback through comparison and test equal effect identities with
  differing arguments. No new comparison algorithm or work charge is needed.
- The same-effect comparison regression reproduced both canonicalization and
  tail-membership misclassification, then passed after callback propagation.
  All three row seam matrices pass. Independent contract re-review approved the
  complete runtime row chain with no remaining findings; Rust quality review
  is active. Broader implementer checks and fresh parent verification remain.
- The implementer passed 1,214 library tests, 14 CLI tests, nine native runtime,
  eight interaction and seven import tests, strict workspace Clippy, rustdoc,
  formatting and diff checks. Parent then independently reran the complete
  1,214/14/9/8/7 test set successfully. Rust quality review remains active; a
  fresh ARM64 workspace/all-targets compile check is running.
- Independent Rust quality review approved the reporting increment with no
  important or critical findings. Parent's ARM64 workspace/all-targets compile
  check passed. Record the reviewed runtime checkpoint unsigned; the remaining
  FOREIGN-07 test expansion, complete-provider review, final full verification,
  specification/artifact closure and local integration are still required.
- Runtime checkpoint `f9a02b6` is unsigned. The full contract audit found no
  semantic mismatch and accepted the separate FOREIGN-05 witnesses; the
  combined recursive cleanup checker limit remains documented. It requested
  native-specific targeted/renamed import, facade-only and copied-source-API
  tests for FOREIGN-01 alongside the planned FOREIGN-07 mutation/counter matrix.
  Those test-only additions are active. Final contract and quality review,
  full verification and integration remain pending.
- Final native import and linked/Core forgery QA passed, including transformed
  native positives and zero counters on all rejected cases. Independent final
  contract/effects/provenance/existential and Rust/resource reviews approved the
  complete provider with no remaining findings. Parent's `cargo xtask verify`
  and fresh ARM64 workspace/all-targets compile check passed after these
  changes. Markdown has no new findings against the compiler checkpoint;
  25 existing overlong lines remain. All 82 relative file links resolve and
  specification anchors were checked. Record the product checkpoint, remove
  completed transition artifacts and proceed to unsigned local integration.
