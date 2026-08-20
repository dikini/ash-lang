# TASK-0002: Establish the Documentation System

- ID: `TASK-0002`
- Status: active
- Related: [AD-0002: Documentation System](../decisions/AD-0002-documentation-system.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- AD-0002 accepts the four documentation domains and their authority boundaries.
- Existing artifact, specification, and writing rules remain in force.

## Work

- Define the four domains, sources of truth, update triggers, lifecycle rules,
  and verification requirements in one project policy.
- Define execution plans as temporary task-owned project-management documents.
- Route contributors and agents to the policy through existing indexes and guides.
- Distinguish existing automated Rust documentation checks from manual checks.
- Do not move files, create empty documentation directories, or change Rust code.

The execution steps are in the
[implementation plan](../plans/2026-08-20-documentation-system.md).

## Progress

AD-0002 is accepted and this task is active. The policy is not yet implemented.

## Verification

- Every documented type maps to one of the four domains.
- Each domain names its source of truth, update trigger, lifecycle, and evidence.
- Language and tool claims retain different sources of truth.
- Current automated and manual checks remain distinct.
- Changed Markdown passes lint, link inspection, and `git diff --check`.
- `cargo xtask verify` continues to pass without runner changes.

## Discoveries

None.

## Deviations

None.
