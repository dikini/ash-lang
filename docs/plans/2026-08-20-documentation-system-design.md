# Documentation System Design

## Purpose

Ash needs one documentation policy that distinguishes project-management records,
Ash language and tool documentation, Rust crate documentation, and general
project documentation. The policy must state what governs each domain, when its
documents change, how they are checked, and when they leave the current tree.

This design changes policy and routing only. It does not move existing files,
create placeholder documentation, or add verification automation.

## Decision structure

An architectural decision will accept the four-domain documentation system.
`docs/project/documentation.md` will contain the operational policy so routine
requirements can remain concise and easy to find.

| Domain | Contents | Authority |
| --- | --- | --- |
| Project management | Design notes, decisions, proposals, tasks, trajectory, and task-owned execution plans | Authority remains determined by artifact type; these documents do not override `spec/`. |
| Ash language and tools | The normative specification, explanatory language material, and compiler, interpreter, REPL, and related tool documentation | Language claims derive from `spec/`; tool claims derive from tested tool behavior. |
| Rust crates | Crate-level documentation, Rust API documentation, examples, and safety or invariant documentation | The implemented Rust API and its tests constrain the documentation; crate documentation does not define Ash semantics. |
| Project documentation | README files, contributor and agent guides, development policies, and material not owned by another domain | The governing decision, policy, or implementation remains authoritative; catchall documentation does not override it. |

When documentation disagrees with its source of truth, the documentation is
wrong unless the governing workflow changes both together.

## Update and lifecycle rules

Project-management documentation changes with the work it describes. An
execution plan belongs to one active task, has no independent authority, and
leaves the current tree when that task finishes. Decisions remain while they
govern current architecture. Other completed or superseded artifacts follow the
existing Git-history rule.

Ash language documentation changes with the implementation and tests that make
its claims true. Explanatory language material must agree with `spec/`. Tool
documentation changes with observable tool behavior.

Rust crate documentation changes with the API, invariant, error behavior, or
safety obligation it describes. It must not introduce language claims unsupported
by `spec/`.

General project documentation changes with contributor setup, repository
workflow, policy, or project structure. New documents must be reachable from the
relevant index. Stale instructions must be corrected or removed.

The policy will not require universal front matter, named owners, review dates,
or empty document types.

## Verification

Verification depends on the domain:

- Project-management documentation has the required artifact sections and
  correct IDs, status, relationships, authority, and evidence.
- Ash language claims agree with `spec/` and the required language tests. Tool
  commands and observable behavior are checked against the implementation.
- Rust crate documentation passes the existing rustdoc and intra-doc-link checks.
  API, error, invariant, and safety documentation is reviewed with its code.
- General project documentation passes Markdown, link, command, and writing-guide
  review.

The policy distinguishes checks enforced by `cargo xtask verify` from checks that
contributors perform manually. Additional automation requires a later task.

A discrepancy does not authorize a local change to governing semantics or
architecture. It returns to the specification, proposal, decision, or
implementation workflow that owns the disputed claim.

## Repository changes

Implementation will:

- add an accepted architectural decision;
- add `docs/project/documentation.md`;
- update the architectural-decision and project-documentation indexes;
- define task-owned execution plans in the artifact guide;
- update root and contributor routing where needed;
- create and later remove the task and execution plan required for the work.

It will not move directories, change Rust code, create empty documentation
scaffolds, or change the verification runner.

## Acceptance

The completed policy must ensure that:

- every documentation type maps to one of the four domains;
- every domain names its governing source of truth;
- update and removal triggers are explicit;
- automated and manual checks remain distinguishable;
- language and tool claims retain their different authorities;
- changed Markdown passes lint, link, and whitespace checks;
- no policy statement defines Ash semantics.
