# TASK-0015: Implement Explicit Implementation Imports and Re-exports

- ID: `TASK-0015`
- Status: active
- Related: [CP-0008: Explicit Implementation Imports and Re-exports](../proposals/CP-0008-explicit-implementation-imports-and-reexports.md), [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), the [explicit-import evidence report](../design/lib-ash/imports-evidence.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), and the [execution plan](../plans/2026-08-25-explicit-implementation-imports-and-reexports.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0008 is accepted transition authority. Current `spec/` owns the
  implemented semantics; this task and the proposal remain non-normative.
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
- Task 5 publishes explicitly selected implementations through checked summaries
  with flat authorization routes. Transitive and diamond cases preserve the
  defining implementation, method, binder, prerequisite, and interface
  identities. Effective and public routes choose independent deterministic
  winners by hop count, transient source-order ranks, and graph-local hop keys.
  Overlap and selection diagnostics retain every chosen route hop. Summary,
  route-copy, route-comparison, effective-environment, and diagnostic retention
  have exact graph-budget boundaries and flat small-stack destruction. Focused
  tests, the full workspace, and independent semantic and code-quality reviews
  have no open findings.
- Task 6 moves each frozen summary's public implementation identities and flat
  authorization routes into a lightweight linked table without retaining
  imported facts, source bodies, method facts, or the complete summary. Linked
  validation authenticates every local inventory, then every dependency-ordered
  public table, then every effective inventory before inspecting occurrences.
  Each imported route must match its exact direct edge and an already
  authenticated dependency suffix; occurrence validation reuses the same
  predicate and never reselects. The three-module facade succeeds through the
  public driver, and independently validated Core still applies the original
  defining method binder. Exact retention preflight, forged-route, unused-table,
  failure-ownership, and 0/1/2-hop structural witnesses pass. The full workspace
  and independent semantic and resource-quality reviews have no open findings.
- Task 7 closes the explicit-import evidence matrix. Exact-limit witnesses cover
  wide selectors, atomic route prepends, multi-entry summary extraction and
  linked retention, a 20,000-hop authorization suffix, and the full 48-layer,
  four-way facade pipeline on a 256 KiB stack. Diagnostics now pin unavailable
  and conflicting selectors, name-only unsatisfied constraints, prerequisite
  routes, overlap routes, and CLI rendering while preserving relationships
  between distinct source files. The architecture guard excludes route and
  authorization state from Core and the evaluator. Every cross-module fixture
  that requires implementation evidence uses an explicit selector, with a
  retained negative witness for name-only imports. Focused suites, the full
  workspace, and three independent reviews have no open findings.
- Task 8 reconciles the specification and explanatory documentation with the
  implemented first `lib-ash` increment. The retained
  [evidence report](../design/lib-ash/imports-evidence.md) records selector and
  facade behavior, identity and summary isolation, coherence and information
  boundaries, diagnostics, exact resources and small-stack disposal, linked
  tamper rejection, unchanged Core and runtime representation, migration,
  maintenance sites, exclusions, and remaining milestone pressure. DN-0025,
  the trajectory, design index, and tool guide now point to that boundary. The
  executable specification target passes all 48 tests. Full-tree Markdown
  lint, relative-link inspection, whitespace checking, and `cargo xtask verify`
  pass. The all-target inventory is 330 library tests, 10 `ash` binary tests,
  648 integration tests, and one `xtask` test: 989 tests. Independent
  review and final verification are complete; lifecycle cleanup remains.
- Task 9's three independent reviews cover semantic and specification
  agreement; implementation, route, resource, and Core quality; and evidence,
  migration, links, authority boundaries, and exclusions. Review corrected one
  normative route-order distinction, stale current-dialect wording, and exact
  evidence attributions. Repeat review of the corrected state has no Critical,
  Important, or Minor findings. The exact final pre-cleanup gate passes all 989
  tests, formatting, all-target checking, clippy with warnings denied, test
  listing, `cargo xtask verify`, full-tree Markdown lint, and whitespace
  checking. The first increment is retained without closing or tagging the
  complete `lib-ash` milestone.
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

Before Task 6, the linked validator authenticated an imported implementation
only when its defining module was the immediate dependency. Transitive
re-exports required each checked module group to retain its lightweight public
implementation authorization entries so validation could follow summary edges
to the defining module without retaining dependency bodies in summaries.

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

Route comparison receives explicit transient dependency, import, and selector
ordinals from stable resolver traversal. It never substitutes `ModuleId` for a
rank and does not persist those ordinals in public authorization paths.

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

Task 5 proves the three-module facade through resolution, checking, summary
freeze, and entry-module availability. It does not run that fixture through the
public driver because checked module groups do not yet retain the public
authorization inventory required to authenticate a transitive route. The exact
driver failure remains `evidence.validation.unknown-identity`; Task 6 owns its
transition to success. The current orphan rule and acyclic module graph also
make a valid source-level sibling overlap witness unreachable, so Task 5 uses a
structurally assembled effective-closure test without changing orphan
ownership. Review added explicit charges for complete diagnostic routes,
summary storage and inspection, and equal-rank route comparison; it also
removed implicit cloning from allocation-owning authorization routes.

Task 6 drains frozen public authorization entries during the fallible
`CheckedModule::into_group` transition instead of storing a second copy on the
checked module. This preserves the required post-freeze boundary, moves route
storage without cloning, and assigns retention charges to linking. The complete
summary is still discarded before the linked program becomes observable.

Forged linked-state cases remain crate unit tests because `#[cfg(test)]`
mutation hooks are unavailable to integration crates. Public integration tests
cover source-level success and the body-free linked shape. The unchanged-Core
proof lives in `tests/interfaces.rs`, which owns the existing independent Core
inspection harness. `src/evidence_audit.rs` and `tests/interface_selection.rs`
required no change: the former authenticates occurrence slots before summary
freeze, and the latter remains a passing selection regression suite rather than
acquiring linked-table policy.

Task 7 keeps injected exact-limit cases in crate unit tests because integration
crates cannot set private graph budgets. `tests/interface_resources.rs` proves
the same deep facade shape through the public driver at the admitted limit. A
valid sibling-facade overlap remains unreachable under the retained orphan rule
and acyclic module graph, so the overlap-route diagnostic witness uses the
structurally assembled checked closure established in Task 5. Existing
production accounting, diagnostic reasons, rendering, and phase boundaries
were sufficient; Task 7 changes only evidence. CLI assertions canonicalize
numeric source identifiers by encounter order so output is allocation-
independent without erasing whether two labels refer to the same or different
source files.

Task 8 keeps the new `lib-ash` report informative and the specification
normative. The report records implemented evidence and future pressure without
promoting DN-0025's later kinds, interface forms, package model, or artifact
model into current Ash. The tool guide describes observed source reasons and
authorization-route labels but does not define their semantics. Retained
Modular Ash reports remain unchanged. Independent documentation and authority
review and final pre-cleanup verification pass. Task 9 cleanup remains.
