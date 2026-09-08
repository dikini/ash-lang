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
   releases then wraps; discard skips wrapping; internal teardown releases
   iteratively without source cleanup. Do not add a second closing schedule.
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
- Steps 3–5: implementation pending. No FOREIGN evidence row is complete yet.
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
