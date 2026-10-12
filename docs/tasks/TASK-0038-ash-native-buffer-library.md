# TASK-0038: Ash native-buffer library

- ID: `TASK-0038`
- Status: active
- Related: [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [GitHub issue #4](https://github.com/dikini/ash-lang/issues/4)

> This task organizes authorized work. It does not define Ash semantics.

## Dependencies

Verified TASK-0036/TASK-0037 generic source contracts, memory operations, guards,
report codecs and executable build. Cell behavior is outside this migration.

## Work

1. Author a passive Ash library declaring calloc/free, initialization, bounds and
   byte conversion policy, acquisition/completion and associated handlers.
2. Use the checked acquired_only codec to preserve Success/Failure and nested body
   results, positive-length refusal, accounting and pre-mutation checks.
3. Migrate callers explicitly to source imports/resource spellings. Remove builtin
   native-buffer authority and special compiler/evaluator dispatch after parity.
4. Update specification and publish mechanical migration/build/run instructions.

## Progress

Assignment, blockers, live progress and PR status belong to the linked GitHub
issue. This task retains scope, ordered work and durable implementation findings.

## Verification

Reuse native-buffer integration/deep-input cases through the generated executable:
positive and refused lengths, zeroed contents, bounds/byte refusal, pre-mutation
failure, nested/repeated scopes and normal/discard exactly-once release. Verify
unchanged cell behavior and required explicit source migration. Actual native
calls and connected regression evidence precede the retaining-branch merge.

## Discoveries

Multiple source provider methods now have the associated operations' exact
value types and effect row, with checked lexical forwarding and selected-handler
access authentication. This supplies a common provider prerequisite for the
buffer port. Byte read/write policy and primitives, outward owned discard,
accounting parity and removal of builtin buffer authority remain unimplemented
by this delivery.

Preserving result shape requires the accepted acquired_only codec; wrapping
builtin behavior in Scope would be an unintended semantic change.

## Deviations

None authorized. Return concrete semantic gaps to CP-0022 instead of resolving
them locally. Keep excluded features outside this task.
