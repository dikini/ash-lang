# TASK-0036: Source contracts, Core and generic execution

- ID: `TASK-0036`
- Status: active
- Related: [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [GitHub issue #2](https://github.com/dikini/ash-lang/issues/2)

> This task organizes authorized work. It does not define Ash semantics.

## Dependencies

Accepted CP-0022 and AD-0013; the linked contract issue #1 supplies review and
acceptance evidence. Coordinate the executable boundary with TASK-0037. Library
ports depend on this generic mechanism, rather than granting native authority.

## Work

1. Admit the complete foreign/resource/access grammar and passive module exports,
   retaining exact defining origins, kinds and complete ordered Type/Row arguments.
2. Prepare one immutable checked foreign contract and checked template per defining
   occurrence. Use phase-specific types and authenticated native projections;
   specialize with fresh local identities without replaying source checking.
3. Implement generic native-effect interpretation, private resource data, finite
   copy windows, initialized output/extent evidence and guarded ownership phases.
4. Reconstruct and independently validate final Core through modules/transforms;
   preserve handler precedence, capture/resume/discard and quarantine dependencies.
5. Update affected specification sections alongside verified behavior. Preserve
   bounded work, fallible allocation, iterative traversal/disposal and depth limits.

## Progress

Assignment, blockers, live progress and PR status belong to the linked GitHub
issue. This task retains scope, ordered work and durable implementation findings.

## Verification

Use public-pipeline integration cases for source admission/publication, exact
identity and tagged argument checks, malformed/transformed Core, invalid access
and escape. Observe actual native acquisition, refusal, partial-owner cleanup,
window copies, completion order, resume/discard and retained-dependent blocking
through TASK-0037 bindings. Retain the open-Delta case and separate captured-control
witness. Run connected compiler/Core/evaluator regressions with one Cargo job;
run the full architecture/workspace gate at integrated delivery.

## Discoveries

DN-0036 supplies reusable guarded scopes, owner arguments and validation, but
Rust-authored manifests/adapters are experimental comparison evidence. They
cannot become the source authoring API. Private replaceable payloads and finite
window contracts are new obligations in CP-0022.

## Deviations

None authorized. Return concrete semantic gaps to CP-0022 instead of resolving
them locally. Keep excluded features outside this task.
