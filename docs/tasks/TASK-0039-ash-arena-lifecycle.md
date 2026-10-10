# TASK-0039: Ash arena lifecycle

- ID: `TASK-0039`
- Status: active
- Related: [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [GitHub issue #5](https://github.com/dikini/ash-lang/issues/5)

> This task organizes authorized work. It does not define Ash semantics.

## Dependencies

Verified TASK-0036/TASK-0037 generic resource and generated native build support.
Typed Arena allocation and experimental storage families are not prerequisites.

## Work

1. Author source foreign calloc/free contracts and opaque ArenaState with source
   configuration, error, data, usage and scoped completion policy.
2. Acquire real backing, report initial usage (0,64,0,4) for configuration (64,4),
   and release exactly once through the common engine.
3. Reject invalid/out-of-profile configuration before acquisition. Zero logical
   capacity allocates one physical byte with an empty logical initialized region.
4. Cover repeated/nested scopes, refusal/no body, escape rejection and release;
   document excluded allocation/reference/storage features and build instructions.

## Progress

Assignment, blockers, live progress and PR status belong to the linked GitHub
issue. This task retains scope, ordered work and durable implementation findings.

## Verification

Execute complete Ash modules in generated hosts observing actual allocation and
release, exact usage, zero capacity, repeated/nested activations and configuration
refusal without body entry. Reject resource-dependent escape. Keep real native
behavior distinct from injected failure cases. Reuse shared lifecycle/control
evidence rather than duplicating corpora; verify on the retaining branch.

## Discoveries

The bounded source library uses the host allocator directly. The experiment's
Rust Arena backing and typed storage APIs are outside the product delivery.

## Deviations

None authorized. Return concrete semantic gaps to CP-0022 instead of resolving
them locally. Keep excluded features outside this task.
