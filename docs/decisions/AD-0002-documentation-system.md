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
