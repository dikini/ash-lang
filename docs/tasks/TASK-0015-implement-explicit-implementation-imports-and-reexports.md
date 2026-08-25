# TASK-0015: Implement Explicit Implementation Imports and Re-exports

- ID: `TASK-0015`
- Status: active
- Related: [CP-0008: Explicit Implementation Imports and Re-exports](../proposals/CP-0008-explicit-implementation-imports-and-reexports.md), [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), and the [execution plan](../plans/2026-08-25-explicit-implementation-imports-and-reexports.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0008 is accepted transition authority. Current `spec/` remains normative
  until implementation, tests, and specification changes land together.
- The final `modular-ash` checkpoint supplies stable module, declaration,
  interface, implementation, method, evidence, and Core identities; generated
  body-free summaries; scoped coherence; linked evidence validation; one
  graph-wide type and constraint budget; and one linked pure Core program.
- The accepted semantic checkpoint is commit `0a9d334`. A fresh
  `cargo xtask verify` passes there with 935 tests and no failure.
- Implementation begins in a dedicated worktree created from the authorization
  checkpoint. It does not modify the retained `modular-ash` tag.
- Every behavioral change uses a witnessed red-green-refactor cycle. Production
  Rust follows `rust-skills`; unexpected failures use
  `superpowers:systematic-debugging`.

## Work

Execute the linked plan to:

- parse private implementation selectors and targeted public imports while
  preserving parser recovery and token-complete projection;
- replace automatic direct-import implementation availability with explicit
  per-interface selection;
- re-export selected global, nominal, constructor, interface, and method names
  under their selected spellings without changing defining identities;
- re-export selected implementation facts transitively, deduplicate identities,
  choose deterministic shortest authorization routes, and check overlap at the
  first combined effective closure;
- retain lightweight public-implementation authorization edges through linking
  and authenticate every selected route before Core synthesis;
- preserve privacy, opacity, hidden summary closure, orphan ownership,
  deterministic diagnostics, graph-wide budgets, and small-stack destruction;
- migrate every existing cross-module implementation use to an explicit
  selector and retain a negative witness for removed automatic availability;
- prove the three-module facade through the public driver and prove unchanged
  Core and runtime representation;
- update the specification, tool documentation, trajectory, and retained
  `lib-ash` evidence; and
- complete independent semantic, implementation, and authority-boundary review
  before the retained product checkpoint.

This task excludes later `lib-ash` kinds, method-local parameters,
multi-parameter interfaces, determination forms, associated outputs, and
defaults. It also excludes `pack-ash`, packages, caches, persistent artifacts,
separate linking, module signatures, wildcard or qualified-module re-exports,
named implementation selectors, specialization, runtime lookup, and new Core
or evaluator forms.

## Progress

- DN-0025 records the milestone dependency spine and the first increment's
  position before kind and determination work.
- CP-0008 records the accepted syntax, semantic delta, summary and route model,
  error ownership, non-goals, and required evidence.
- The dedicated `lib-ash-explicit-imports` worktree starts from authorization
  checkpoint `4f0541d`; its baseline `cargo xtask verify` passes.
- Task 2 parses targeted public imports and independent implementation
  selectors. Focused projection, malformed recovery, token-completeness,
  parser, formatting, and all-target compilation checks pass. Independent
  semantic-compliance and code-quality reviews have no open findings.
- Task 3 removes automatic implementation availability. Only explicit
  implementation selectors retain matching public facts; name and qualified
  imports retain no implementation facts. Selector diagnostics, identity
  deduplication, direct-route provenance, and exact index/summary budget probes
  pass focused and full-workspace verification. Independent semantic and code-
  quality reviews have no open findings.
- Task 4 re-exports selected global, nominal, constructor, interface, and method
  names under facade spellings without creating declarations or changing their
  defining identities. Summary closure preserves privacy, opacity, complete
  constructor families, constrained schemes, and method-only interfaces.
  Owner-indexed withheld facts keep same-spelling opaque constructors from
  distinct dependencies separate while preserving deterministic diagnostics.
  Candidate staging and summary closure use fallible, graph-budgeted, linear
  storage and iterative destruction. Focused resource, visibility, resolution,
  and diamond checks, the full workspace, and independent semantic and code-
  quality reviews have no open findings.
- The execution plan defines focused red-green increments, review checkpoints,
  migration, retained evidence, and lifecycle cleanup.

## Verification

Focused commands and witnessed RED/GREEN results are recorded in the execution
plan. Completion requires:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --workspace --all-targets --all-features
cargo clippy --locked --workspace --all-targets --all-features -- -D warnings
cargo xtask verify
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Manual review covers every CP-0008 evidence requirement, all changed relative
links, authority labels, exact grammar and notation fences, deterministic route
selection, privacy and opacity, implementation and binder ownership, summary
isolation, linked authentication before Core, resource charging, small-stack
destruction, and the absence of later `lib-ash` or `pack-ash` mechanisms.

## Discoveries

The current linked validator authenticates an imported implementation only when
its defining module is the immediate dependency. Transitive re-exports require
each checked module group to retain its lightweight public implementation
authorization entries so validation can follow summary edges to the defining
module without retaining dependency bodies in summaries.

Imported global, nominal, constructor, interface, and method facts already
retain defining identities independently from source aliases. Public name
re-exports can extend the generated summary boundary rather than introduce
facade declarations or Core forwarding functions.

The migration surface includes resolver and resolved-summary unit tests in
addition to integration fixtures. Final transition-artifact cleanup must remove
or replace intermediate CP-0008, TASK-0015, and execution-plan links from the
retained design, trajectory, and evidence documents.

Effective availability and public re-export authorization require independent
route winners. Equal-length suffixes use the graph-local hop-key sequence
defined by CP-0008; process-global source allocation and hash-map order do not
participate. Linked validation authenticates complete public authorization
inventories before using them to validate occurrence availability.

The retained orphan rule and acyclic module graph make valid overlapping
public implementations from distinct source modules unreachable. Task 5 uses
source programs for transitive availability and identity deduplication, and a
structurally assembled checked-closure fixture for first-combined-closure
overlap rejection. Task 6 owns the first full public-driver success because
checked groups do not yet retain the authorization tables needed by linked
validation.

## Deviations

Task 3 mechanically migrated three executable specification examples and their
exact paired source snippets so the full workspace stayed green. Task 8 still
owns the complete normative grammar, semantics, validation, and explanatory
reconciliation; no broader specification claim moved forward.

Task 4 required no elaboration, Core, or runtime change. Existing linked
identity validation already distinguishes the publishing summary from each
fact's defining owner. The new facade, closure, opacity, alias, and resource
evidence therefore lives in resolver and library-import tests; the existing
visibility, resolution, and diamond suites remain unchanged and pass as
regression witnesses.
