# TASK-0003: Correct the Documentation Policy

- ID: `TASK-0003`
- Status: active
- Related: [AD-0002: Documentation System](../decisions/AD-0002-documentation-system.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- AD-0002 requires lifecycle rules for every documentation domain.
- The post-implementation review identified three policy and routing gaps.

## Work

- State when obsolete Ash language, tool, and Rust crate documentation leaves the
  current tree.
- Link the documentation policy from the agent context route.
- Describe the full scope of the project-documentation index.
- Do not change AD-0002, Rust code, directory structure, or verification
  automation.

The execution steps are in the
[implementation plan](../plans/2026-08-20-documentation-policy-corrections.md).

## Progress

The correction design is approved and this task is active. No policy correction
has been applied yet.

## Verification

- The Ash language/tool and Rust crate domains have explicit removal rules.
- `AGENTS.md` links directly to the documentation policy.
- The project index describes its current policy scope.
- Changed Markdown passes lint and relative-link inspection.
- `cargo xtask verify` and `git diff --check` pass.

## Discoveries

None.

## Deviations

None.
