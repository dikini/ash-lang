# TASK-0031: Close Effect Ash Milestone

- ID: `TASK-0031`
- Status: active
- Related: [execution plan](effect-ash-closure-execution-plan.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md)

> This task records the user's final milestone-closure request. It does not
> define semantics or authorize a new effect feature.

## Dependencies

All selected slices are retained on `integration/effect-ash-foundations` at
`035b456`. Main integration requires explicit approval under AD-0011; tagging
and pushing remain separate gates. Existing uncommitted main documentation and
the deferred TASK-0024 must be preserved.

## Work

Audit combined conformance, authority, Pure locality, downstream pressure and
simplification. Repair documentation against implemented behavior, retain the
milestone evidence, verify the approved main integration, and close transition
artifacts only when the complete milestone is current on main.

## Progress

- Independent high-reasoning semantic and downstream/simplification audits
  found no demonstrated defect or unjustified removable mechanism. The
  [closure evidence](../design/effect-ash/milestone-closure-evidence.md) records
  exact witnesses and residual risks.
- Fresh baseline: 1,214 library and 14 CLI tests pass. Full verification of the
  unchanged product code also passed at native-provider integration.
- Confirmed documentation omission: Effect Core's operation inventory omits
  implemented `Cleanup`; corrected from the existing validation contract.
  Stale completed-slice summaries were also corrected.
- Main approval and preservation of its uncommitted documentation are pending.
- The user subsequently requested a signed main merge. Preserve the existing
  documentation through temporary shelving/restoration; ordinary commits remain
  unsigned, and tag/push authorization is not included.
- Independent documentation review approved the pre-integration corrections
  and inventoried the post-main status updates. Changed-document lint has no
  new findings; all 96 relative file links resolve. Full `cargo xtask verify`
  passed after the closure corrections on 2026-09-09. Main integration and its
  verification remain pending explicit approval.

## Verification

Map DN-0028's completion obligations to concrete tests and inspected invariants.
Require independent semantic, Rust/resource, simplification and documentation
review; `cargo xtask verify`; documented ARM64 compilation evidence; Markdown,
link, authority and diff checks; verified main integration; clean closure-owned
state; preserved user changes and existing tags. Do not equate integration-branch
readiness with milestone completion on main.

## Discoveries

Main differs by one committed README addition and uncommitted documentation,
including overlapping task-index and trajectory changes. No compiler divergence
was found. TASK-0024 remains a separately deferred post-main repair task.

## Deviations

None. Pre-integration audits prepare the explicit integration gate; the final
completion claim still requires the integrated main state.
