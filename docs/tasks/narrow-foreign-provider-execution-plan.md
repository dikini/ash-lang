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

Files: `src/syntax_resource.rs`, `src/module.rs`, `src/resolve.rs`,
`src/resolved.rs`, `src/elaborate.rs`, `src/evidence.rs`, `src/interface.rs`,
`src/core/effect.rs`, `src/core/dialect.rs`, `src/core/validate.rs` and their
existing traversal/transform helpers as required by compiler errors.
Tests: new `tests/native_buffer_syntax.rs`, `tests/native_buffer_typing.rs`,
`tests/native_buffer_modules.rs`, `tests/native_buffer_core.rs` and existing
internal builtin-summary tamper tests.

1. Add failing syntax/import/type tests for the exact CP API and nested Outcome.
2. Extend fixed resource selection and builtin identities; retain direct import
   provenance and sealed provider authority. Reuse dependency and row machinery.
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
4. Reserve result wrapping and disposal work at acquisition. Normal completion
   releases then wraps; discard skips wrapping; internal teardown releases
   iteratively without source cleanup. Do not add a second closing schedule.
5. Test allocation failure, work exhaustion before native calls, write atomicity,
   fresh activations, captured owners and exact capacity reuse.
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

- Setup: isolated worktree created; baseline workspace test process started.
- Steps 1–5: pending. No FOREIGN evidence row is complete yet.
