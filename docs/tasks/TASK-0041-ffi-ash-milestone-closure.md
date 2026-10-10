# TASK-0041: ffi-ash milestone closure

- ID: `TASK-0041`
- Status: active
- Related: [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [GitHub issue #7](https://github.com/dikini/ash-lang/issues/7)

> This task organizes authorized work. It does not define Ash semantics.

## Dependencies

Complete issue outcomes #2–#6 verified on integration/ffi-ash, with signed
explicit merges and receipts. The final Main integration gate remains separate.

## Work

1. Review complete implementation/specification correspondence, generic boundaries,
   library migrations and unsupported feature documentation against CP-0022.
2. Consolidate reproducible native build/run instructions and reusable exact-pinned
   positive/negative/lifecycle/control evidence without duplicate fixture corpora.
3. Run the full architecture/workspace gate on the integrated milestone branch;
   resolve regressions before opening the final Main delivery PR.
4. Link issues, tasks and delivering PRs. Close issues explicitly only after complete
   outcomes have retaining-branch verification receipts.
5. After complete checkpoint evidence closes, remove the accepted proposal and
   completed implementation tasks/plans from the product branch and repair their
   current-tree links before the final Main PR. Preserve delivering history links.
6. After the separate Main gate, preserve histories with a signed explicit merge,
   verify integrated Main and close the milestone and this task. Remove the clean
   checkpoint worktree/ref only after proving retaining ancestry under AD-0011.
   Protect paused Lean/Core workstreams.

## Progress

Assignment, blockers, live progress and PR status belong to the linked GitHub
issue. This task retains scope, ordered work and durable implementation findings.

## Verification

Run cargo xtask verify with one Cargo job on the integrated delivery and again
where merged changes warrant it. Check changed documentation metadata, authority,
relative links, Markdown and formal notation. Require generated-host static/shared
execution for all three libraries, separate C mismatch checks, independent Core
rejection, actual native lifecycle, copy/control/quarantine evidence and migration
commands. Final PR contains implementation, normative updates, libraries and
reproducible instructions; no Main integration before that gate.

## Discoveries

Prepared declarations and historical experiment passes do not establish product
completion. A receipt pins exact source/configuration and distinguishes executed
properties, foreign assumptions, calibration deficits and unproved properties.

## Deviations

None authorized. Return concrete semantic gaps to CP-0022 instead of resolving
them locally. Keep excluded features outside this task.
