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

AD-0002 is accepted. The documentation policy defines all four domains, their
sources of truth, update and lifecycle rules, and current verification boundary.
Repository indexes and contributor guidance route documentation work through the
policy.

## Verification

- Every documented type maps to one of the four domains.
- Each domain names its source of truth, update trigger, lifecycle, and evidence.
- Language and tool claims retain different sources of truth.
- Current automated and manual checks remain distinct.
- Changed Markdown passes lint, link inspection, and `git diff --check`.
- `cargo xtask verify` continues to pass without runner changes.

## Discoveries

- `cargo xtask verify` checks Rust documentation but does not check repository
  Markdown or relative links.
- The existing `docs/project/` index can hold the policy without a directory move
  or new documentation scaffold.

## Deviations

None.
