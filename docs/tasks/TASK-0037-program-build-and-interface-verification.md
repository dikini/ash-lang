# TASK-0037: Program build and interface verification

- ID: `TASK-0037`
- Status: active
- Related: [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [GitHub issue #3](https://github.com/dikini/ash-lang/issues/3)

> This task organizes authorized work. It does not define Ash semantics.

## Dependencies

Accepted CP-0022/AD-0013 and TASK-0036 checked contracts/Core. Build phases may
be developed against authenticated generic contracts; executable admission must
use the completed source/Core path.

## Work

1. Add additive compile/build/execute APIs and explicit `ash build` configuration,
   preserving existing non-foreign run_path/RunConfiguration callers.
2. Resolve the bounded target and explicit native link inputs; generate typed Rust
   call bridges and a host containing private checked Core and the existing evaluator.
3. Authenticate linked bindings against original library/operation contracts before
   acquisition. Revalidate reconstructed Core; no runtime compiler or name-only dispatch.
4. Support static archives and ordinary shared linkage, including the non-callable
   sentinel representation, without a library-specific runtime C shim.
5. Provide separate optional `ash check-ffi` C/header checks and mismatch diagnostics.
   Verification mappings supply no executable values or ownership authority.
6. Document reproducible source-only library authoring and native build/run inputs.

## Progress

Assignment, blockers, live progress and PR status belong to the linked GitHub
issue. This task retains scope, ordered work and durable implementation findings.

## Verification

Build and execute a checked Ash program with real scalar/native ownership calls,
then each library port. Verify static/shared linkage, unsupported targets/shapes,
missing symbols, stale or mismatched bridge registrations and Core. Run separate
header checks with a deliberate type/value mismatch. Inspect generated Rust for
exact origin/signature mapping and absence of library policy. Record source/config
pins, commands and native observations; one Cargo job and final integrated gate.

## Discoveries

The evaluator and private Core stay the execution engine. Bridge generation
replaces the experiment's handwritten executable adapters; header verification
is optional and cannot repair missing source contracts.

Standalone Core reconstruction needs original source provenance, registry and
method catalogs in addition to nodes. Capture those inputs while the canonical
compiler owns the admitted graph; reopening source paths after compilation can
read changed files. Reconstruction must preserve shared original contract
allocations and then invoke the existing independent modular validator. Recursive
serialization of Core alone would lose authority and safe traversal properties.

## Deviations

None authorized. Return concrete semantic gaps to CP-0022 instead of resolving
them locally. Keep excluded features outside this task.
