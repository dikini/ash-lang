# Documentation System Implementation Plan

<!-- markdownlint-disable MD001 MD036 -->

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Establish the accepted four-domain documentation policy without moving
existing files or changing verification automation.

**Architecture:** AD-0002 records the repository-workflow decision, while
`docs/project/documentation.md` holds the rules contributors apply. Existing
indexes route readers to the policy, and the artifact guide defines execution
plans as temporary task-owned records.

**Tech Stack:** Markdown, repository artifact templates, Markdownlint, Git, and
the existing Cargo verification runner.

---

Use `@superpowers:verification-before-completion` before every commit and before
finishing TASK-0002.

### Task 1: Record the accepted documentation decision

**Files:**

- Create: `docs/decisions/AD-0002-documentation-system.md`
- Modify: `docs/decisions/README.md`

**Step 1: Confirm that AD-0002 is unused**

Run:

```bash
! git log --all --name-only --pretty=format: | rg 'AD-0002'
```

Expected: exit 0 with no matches.

**Step 2: Add the accepted decision**

Create `docs/decisions/AD-0002-documentation-system.md`:

```markdown
# AD-0002: Documentation System

- ID: `AD-0002`
- Status: accepted

## Decision

Ash documentation belongs to four domains:

1. Project-management documentation records design, decisions, proposed changes,
   active work, dependencies, maturity, and task-owned execution plans.
2. Ash language and tool documentation describes the language and the observable
   behavior of the compiler, interpreter, REPL, and related tools.
3. Rust crate documentation describes implementation crates, APIs, examples,
   errors, invariants, and safety obligations.
4. Project documentation contains README files, contributor and agent guides,
   development policies, and material not owned by another domain.

Each domain has a named source of truth, update trigger, lifecycle, and
verification requirements. One document belongs to one domain even when it links
to material in another.

Language claims derive from the canonical specification. Tool claims derive from
tested tool behavior. Rust crate documentation is constrained by the implemented
Rust API and its tests. Project-management and project documentation remain
subordinate to the decisions, policies, implementations, or specification they
describe.

The operational rules live in `docs/project/documentation.md`. This decision does
not require directory moves, empty documentation scaffolds, or new verification
automation.

## Context

The artifact guide governs specification, design notes, architectural decisions,
change proposals, and tasks. The specification discipline governs language
changes. The writing guide applies to all project prose. These rules do not yet
classify tool documentation, Rust crate documentation, execution plans, or
general guides as one system.

A single policy keeps the common rules visible while allowing each domain to use
the source of truth appropriate to its subject. Separate policies or directory
trees would add structure before the repository has enough material to need it.

## Consequences

- Contributors can classify documentation before choosing its authority and
  verification evidence.
- Language and tool documentation share a product domain without sharing one
  source of truth.
- Rust crate documentation cannot define Ash semantics.
- General project documentation is a catchall, not an alternative authority.
- Execution plans become temporary records owned by active tasks.
- Documentation discrepancies return to the workflow that owns the disputed
  claim.
- Automation beyond existing Rust documentation checks requires a later task.

## Verification

- The documentation policy names all four domains and their sources of truth.
- Each domain has update, lifecycle, and verification rules.
- The artifact guide defines execution-plan ownership and removal.
- Repository indexes and contributor guidance route readers to the policy.
- Automated checks and manual review requirements remain distinguishable.
- No policy statement defines Ash language semantics.
```

**Step 3: Add AD-0002 to the decision index**

Append this item under `Current decisions` in `docs/decisions/README.md`:

```markdown
- [AD-0002: Documentation System](AD-0002-documentation-system.md)
```

**Step 4: Verify and commit the decision**

Run:

```bash
markdownlint --disable MD013 -- docs/decisions/AD-0002-documentation-system.md docs/decisions/README.md
test -f docs/decisions/AD-0002-documentation-system.md
git diff --check
```

Expected: all commands exit 0.

Commit:

```bash
git add docs/decisions
git commit -m "docs: accept documentation system"
```

### Task 2: Authorize the policy work

**Files:**

- Create: `docs/tasks/TASK-0002-establish-documentation-system.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/trajectory.md`

**Step 1: Confirm that TASK-0002 is unused**

Run:

```bash
! git log --all --name-only --pretty=format: | rg 'TASK-0002'
```

Expected: exit 0 with no matches.

**Step 2: Create the active task**

Create `docs/tasks/TASK-0002-establish-documentation-system.md`:

```markdown
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
```

**Step 3: Mark the task active in current-state views**

Replace `No implementation task is active.` in `docs/tasks/README.md` with:

```markdown
- [TASK-0002: Establish the Documentation System](TASK-0002-establish-documentation-system.md)
```

Replace the two-line inactive-task statement in `docs/trajectory.md` with:

```markdown
TASK-0002 is establishing the accepted documentation system. Other work still
needs enough evidence to authorize implementation.
```

Add this row to the trajectory table:

```markdown
| [Documentation system](decisions/AD-0002-documentation-system.md) | implementation | none | Complete [TASK-0002](tasks/TASK-0002-establish-documentation-system.md): define the policy and route current documentation through it. |
```

**Step 4: Verify and commit task activation**

Run:

```bash
markdownlint --disable MD013 -- docs/tasks/TASK-0002-establish-documentation-system.md docs/tasks/README.md docs/trajectory.md
test -f docs/decisions/AD-0002-documentation-system.md
test -f docs/plans/2026-08-20-documentation-system.md
git diff --check
```

Expected: all commands exit 0 and both task links resolve.

Commit:

```bash
git add docs/tasks docs/trajectory.md
git commit -m "docs: authorize documentation policy work"
```

### Task 3: Define the documentation policy

**Files:**

- Create: `docs/project/documentation.md`
- Modify: `docs/project/README.md`

**Step 1: Add the operational policy**

Create `docs/project/documentation.md`:

```markdown
# Documentation policy

Ash documentation belongs to one of four domains. Classify a document before
deciding what governs it, when it changes, and how to verify it.

When documentation disagrees with its source of truth, correct the documentation
unless the governing workflow changes both together. A document cannot create
language semantics, architecture, or tool behavior merely by describing it.

## Project-management documentation

This domain contains design notes, architectural decisions, change proposals,
tasks, the development trajectory, and task-owned execution plans.

The artifact type determines authority. The canonical specification remains the
only source of current Ash semantics. An accepted architectural decision governs
current non-language architecture. Proposals, tasks, plans, and design notes do
not define current Ash.

Update these documents with the work they describe. An execution plan belongs to
one active task, has no independent authority, and leaves the current tree when
the task finishes. Other artifact lifecycles follow the artifact guide.

Verify required sections, IDs, status, relationships, authority boundaries, and
the evidence named by the artifact.

## Ash language and tool documentation

This domain contains the normative specification, explanatory language material,
and documentation for the compiler, interpreter, REPL, and related Ash tools.

Language claims derive from `spec/`. Explanatory material must agree with the
current specification and must label proposed or future behavior. A language
change updates implementation, positive and negative tests, and the specification
together through the proposal workflow.

Tool claims derive from implemented and tested tool behavior. Documentation must
not present an implementation accident as a language rule. Update tool
documentation with changes to documented commands, inputs, outputs, diagnostics,
configuration, or platform behavior.

Verify semantic claims against `spec/`, language examples against required tests,
and documented tool behavior against the implementation. Test examples when
executable support exists.

## Rust crate documentation

This domain contains crate-level documentation, Rust API documentation, examples,
and descriptions of errors, invariants, and safety obligations.

The implemented Rust API and its tests constrain this documentation. Crate
documentation explains implementation interfaces; it does not define Ash
semantics. Update it with the API, invariant, error behavior, or safety obligation
it describes.

`cargo xtask verify` builds workspace documentation with warnings denied. The
workspace denies broken intra-doc links. Review API contracts, examples, errors,
invariants, and safety explanations with the relevant code change.

## Project documentation

This domain contains root and directory README files, contributor and agent
guides, development policies, and material not owned by another domain.

The decision, policy, implementation, or specification being described remains
authoritative. This domain is a catchall for subject matter, not authority.

Update project documentation with contributor setup, repository workflow, policy,
or project structure. Link new documents from the relevant index. Correct or
remove stale instructions.

Verify changed Markdown against the writing guide and Markdown lint. Check
relative links and documented commands. Confirm that normative, accepted,
proposed, and informative statements retain their actual status.

## Current verification boundary

`cargo xtask verify` enforces Rust formatting, build, lint, tests, and rustdoc
checks. Documentation classification, artifact structure, Markdown lint, relative
links, command accuracy, and authority review remain manual requirements.

Adding automated documentation checks requires an authorized task. A missing
automatic check does not remove the manual requirement.
```

**Step 2: Link the policy from the project index**

Add this item after the dependency policy in `docs/project/README.md`:

```markdown
- [Documentation policy](documentation.md)
```

**Step 3: Verify and commit the policy**

Run:

```bash
markdownlint --disable MD013 -- docs/project/documentation.md docs/project/README.md
test -f docs/project/documentation.md
git diff --check
```

Expected: all commands exit 0.

Commit:

```bash
git add docs/project
git commit -m "docs: define documentation policy"
```

### Task 4: Route contributors and define execution plans

**Files:**

- Modify: `docs/project/artifacts.md`
- Modify: `README.md`
- Modify: `CONTRIBUTING.md`
- Modify: `AGENTS.md`

**Step 1: Define execution plans in the artifact guide**

Add this subsection after `Tasks` in `docs/project/artifacts.md`:

```markdown
### Execution plans

An execution plan is a temporary project-management document owned by one active
task. It translates authorized work into ordered changes and verification steps.
It has no independent authority and cannot define semantics or architecture.
Link it from its task and remove it when the task finishes; Git retains the plan.
```

Add this sentence after the template rule in `Identity and references`:

```markdown
Execution plans do not receive artifact IDs.
```

**Step 2: Route readers from the root README**

Replace the project-documentation item in `README.md` with:

```markdown
- [project documentation](docs/project/README.md) defines documentation,
  dependencies, and the development discipline.
```

**Step 3: Route contributors to the policy**

Replace the opening of the final paragraph in `CONTRIBUTING.md` with:

```markdown
Follow the [documentation policy](docs/project/documentation.md) and
[writing guide](docs/project/writing.md).
```

Retain the existing submission-review requirements after those links.

**Step 4: Route documentation work in AGENTS.md**

Replace the specification/documentation context item with:

```markdown
- Specification/documentation: documentation policy, current specification, an
  implemented proposal's semantic delta, tests, and decisions that affect wording
  or structure.
```

Replace the verification sentence in the following paragraph with:

```markdown
Verify changes using the evidence required by the governing artifact and
documentation policy, then check links and authority boundaries in any
documentation you change.
```

**Step 5: Verify and commit routing**

Run:

```bash
markdownlint --disable MD013 -- docs/project/artifacts.md README.md CONTRIBUTING.md AGENTS.md
test -f docs/project/documentation.md
git diff --check
```

Expected: all commands exit 0 and every new relative link resolves.

Commit:

```bash
git add docs/project/artifacts.md README.md CONTRIBUTING.md AGENTS.md
git commit -m "docs: route documentation workflow"
```

### Task 5: Record final evidence

**Files:**

- Modify: `docs/tasks/TASK-0002-establish-documentation-system.md`

**Step 1: Run repository verification**

Run:

```bash
cargo xtask verify
markdownlint --disable MD013 -- \
  AGENTS.md \
  CONTRIBUTING.md \
  README.md \
  docs/decisions/AD-0002-documentation-system.md \
  docs/decisions/README.md \
  docs/plans/2026-08-20-documentation-system-design.md \
  docs/plans/2026-08-20-documentation-system.md \
  docs/project/README.md \
  docs/project/artifacts.md \
  docs/project/documentation.md \
  docs/tasks/README.md \
  docs/tasks/TASK-0002-establish-documentation-system.md \
  docs/trajectory.md
test -f docs/project/documentation.md
test -f docs/decisions/AD-0002-documentation-system.md
git diff --check
```

Expected: all commands exit 0.

**Step 2: Inspect authority and routing explicitly**

Run:

```bash
rg -n 'Project-management documentation|Ash language and tool documentation|Rust crate documentation|Project documentation' docs/project/documentation.md
rg -n 'documentation.md' README.md CONTRIBUTING.md AGENTS.md docs/project/README.md
rg -n 'execution plan' docs/project/artifacts.md docs/tasks/TASK-0002-establish-documentation-system.md
```

Expected: the policy contains all four domains; contributor routing reaches the
policy; the artifact guide and task agree on plan ownership.

**Step 3: Record the evidence and discoveries**

Replace `Progress` in TASK-0002 with:

```markdown
AD-0002 is accepted. The documentation policy defines all four domains, their
sources of truth, update and lifecycle rules, and current verification boundary.
Repository indexes and contributor guidance route documentation work through the
policy.
```

Replace `Discoveries` with:

```markdown
- `cargo xtask verify` checks Rust documentation but does not check repository
  Markdown or relative links.
- The existing `docs/project/` index can hold the policy without a directory move
  or new documentation scaffold.
```

Leave `Deviations` as `None.`

**Step 4: Verify and commit the evidence record**

Run:

```bash
markdownlint --disable MD013 -- docs/tasks/TASK-0002-establish-documentation-system.md
git diff --check
```

Expected: both commands exit 0.

Commit:

```bash
git add docs/tasks/TASK-0002-establish-documentation-system.md
git commit -m "docs: record documentation policy verification"
```

### Task 6: Complete TASK-0002

**Files:**

- Remove: `docs/tasks/TASK-0002-establish-documentation-system.md`
- Remove: `docs/plans/2026-08-20-documentation-system-design.md`
- Remove: `docs/plans/2026-08-20-documentation-system.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/trajectory.md`

**Step 1: Remove completed planning records**

Remove TASK-0002 and both documentation-system plan files. Git history retains
the authorization, design, implementation steps, and verification evidence.

**Step 2: Restore current-state indexes**

Replace the active task in `docs/tasks/README.md` with:

```markdown
No implementation task is active.
```

Replace the active-task statement in `docs/trajectory.md` with:

```markdown
No implementation task is active. Other work still needs enough evidence to
authorize implementation.
```

Remove the documentation-system row from the trajectory table.

**Step 3: Verify the final repository state**

Run:

```bash
cargo xtask verify
markdownlint --disable MD013 -- \
  AGENTS.md \
  CONTRIBUTING.md \
  README.md \
  docs/decisions/AD-0002-documentation-system.md \
  docs/decisions/README.md \
  docs/project/README.md \
  docs/project/artifacts.md \
  docs/project/documentation.md \
  docs/tasks/README.md \
  docs/trajectory.md
! rg -n 'TASK-0002|2026-08-20-documentation-system' docs README.md CONTRIBUTING.md AGENTS.md
test -f docs/project/documentation.md
test -f docs/decisions/AD-0002-documentation-system.md
git diff --check
git status --short
```

Expected: all checks before `git status` exit 0; no current-tree reference to the
completed task or plans remains; status lists only the intended cleanup changes.

**Step 4: Commit task completion**

```bash
git add docs/tasks docs/plans docs/trajectory.md
git commit -m "docs: complete documentation system task"
```
