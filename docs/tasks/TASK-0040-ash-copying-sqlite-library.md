# TASK-0040: Ash copying SQLite library

- ID: `TASK-0040`
- Status: active
- Related: [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [GitHub issue #6](https://github.com/dikini/ash-lang/issues/6)

> This task organizes authorized work. It does not define Ash semantics.

## Dependencies

Verified TASK-0036/TASK-0037 common source/Core/runtime/build and contrasting
TASK-0038 library evidence. The [retained minimal arena](https://github.com/dikini/ash-lang/issues/5)
supplies contrasting lifecycle evidence. Native SQLite binaries/headers are
explicit build/check inputs, not source authority.

## Work

1. Declare SQLite symbols, representations, constants, TRANSIENT sentinel, owners,
   diagnostic/column windows and consumption/retention assumptions entirely in Ash.
2. Implement source protocol state, diagnostics, partial acquisition, preparation
   tail offsets, bind/step/reset, scalar/text/blob copying and result conversions.
3. Complete source connection/statement resource lifecycle with finalization before
   close, distinct consumed/retained errors and blocked-dependent reports.
4. Migrate all retained realistic copying/persistence programs to the source library;
   remove handwritten manifests/adapters and runtime C shim from the product path.
5. Publish reproducible build/run/header-check guidance and tested limitations.

## Progress

Assignment, blockers, live progress and PR status belong to the linked GitHub
issue. This task retains scope, ordered work and durable implementation findings.

## Verification

Run existing copying/persistence programs through generated hosts. Observe
Completed(Completed(Ok(42),Closed),Closed), independent text/blob copies, NULL
versus empty, repeated/imported/simultaneous identities, reset/rebind, partial
acquisition cleanup, finalization-before-close and retained-owner quarantine.
Exercise exact view/index/extent correspondence and pre-call invalid-access
rejection. Distinguish real SQLite errors from injected failures, and record
source/native-input pins and commands on integrated delivery.

## Discoveries

SQLite requires source private protocol data, input-relative tail extraction
and separate diagnostic/column windows. Source contracts must express these
roles; Rust adapters cannot remain the library policy.

## Deviations

None authorized. Return concrete semantic gaps to CP-0022 instead of resolving
them locally. Keep excluded features outside this task.
