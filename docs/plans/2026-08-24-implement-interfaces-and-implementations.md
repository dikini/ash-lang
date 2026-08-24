# Interfaces and Implementations Execution Plan

> **For Codex:** Use `superpowers:executing-plans` to execute this plan task by
> task, preserving the review checkpoints.

**Goal:** Implement accepted CP-0006 as method-only Ash interfaces with scoped
implementations, separately checked constrained globals, one checked evidence
selection per occurrence, and lowering through the existing pure Core.

**Architecture:** Extend the lossless surface and resolved module forms with
stable interface identities and constrained schemes. Keep constraints outside
the ordinary `Type` algebra. A focused interface subsystem owns checked header
facts, implementation overlap, the persistent graph-wide work budget, evidence
selection, and pre-Core evidence validation. Checked definitions structurally
retain selections through `CheckedModule`, linking, and final synthesis. Impl
methods receive hidden module-qualified binders and join their module's existing
recursive Core group. Core and evaluation receive only existing type
abstractions, function binders, type applications, and term applications.

**Tech stack:** Rust 2024, existing event-producing concrete-tree parser,
module resolver, rank-1 elaborator, pure Core validator and evaluator, Cargo
integration tests, and Markdown specification.

---

Implementation follows `superpowers:test-driven-development`, `rust-skills`,
`superpowers:systematic-debugging` for unexpected failures,
`superpowers:requesting-code-review` at the named checkpoints, and
`superpowers:verification-before-completion`. Each behavior begins with the
named focused test and a witnessed expected failure. Prefer typed identity
newtypes, borrowed inputs, fixed boxed slices after construction, structured
errors, explicit worklists, and charged allocation over encoded names, cloning,
panics, or unbounded host recursion.

## Task 1: Authorize and baseline the implementation

### Task 1 — Files

- Create: `docs/tasks/TASK-0012-implement-interfaces-and-implementations.md`
- Create: `docs/plans/2026-08-24-implement-interfaces-and-implementations.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/proposals/CP-0006-interfaces-and-implementations.md`
- Modify: `docs/trajectory.md`

### Task 1 — Step 1: Record accepted authority and bounded work

Link CP-0006, DN-0023, AD-0005 through AD-0008, TASK-0012, and this plan. Keep
the current specification authoritative until the implementation, tests, and
specification land together.

### Task 1 — Step 2: Record the clean baseline

The accepted checkpoint is `ca79328` on `feature/modular-ash`. The witnessed
baseline command is:

```text
cargo xtask verify
```

Expected: PASS with 645 tests and no failure.

### Task 1 — Step 3: Validate and commit the task artifacts

Run:

```text
markdownlint --disable MD013 -- docs/tasks docs/plans docs/proposals docs/trajectory.md
git diff --check
```

Commit unsigned as:

```text
docs: authorize interface implementation
```

## Task 2: Parse interface, requirement, and impl forms

### Task 2 — Files

- Modify: `src/lexer/token.rs`
- Modify: `src/lexer/mod.rs`
- Modify: `src/parser/mod.rs`
- Modify: `src/parser/grammar.rs`
- Modify: `src/parser/project.rs`
- Modify: `src/surface.rs`
- Modify: the `SurfaceModule` test fixture literal in `src/module.rs`
- Modify: `tests/lexer.rs`
- Modify: `tests/parser.rs`
- Modify: `tests/modules_syntax.rs`
- Create: `tests/interfaces_syntax.rs`

### Task 2 — Step 1: Reserve the three words with a focused RED test

Add
`recognizes_interface_reserved_words_without_stealing_identifier_boundaries`
for `interface`, `impl`, and `where`, including prefixed/suffixed ordinary
identifiers and the closed token inventory.

Run:

```text
cargo test --locked --test lexer recognizes_interface_reserved_words_without_stealing_identifier_boundaries -- --exact
```

Expected RED: the words are ordinary identifiers or token variants are absent.
Add only the token family and rerun the complete lexer target GREEN.

### Task 2 — Step 2: Project interface declarations RED to GREEN

Add `projects_public_and_private_method_only_interfaces_exactly`. Assert the
single parameter, nonempty method list, visibility, exact CST/token coverage,
projected spans, and signature-only method shapes. Parsing does not enforce the
parameter-occurrence or arrow rules.

Run the exact test RED, add the grammar/CST projection/surface forms, then run:

```text
cargo test --locked --test interfaces_syntax projects_public_and_private_method_only_interfaces_exactly -- --exact
```

Expected GREEN.

### Task 2 — Step 3: Project ordered global requirements RED to GREEN

Add `projects_ordered_requirements_on_both_global_presentations`. Put `where`
after the complete equational value type and operational result type. Assert
qualified interface references, nested type arguments, multiple requirements,
and order.

Run the exact test RED. Extend `SurfaceExternalInterface` and
`SurfaceInlineOperationalHeader`, ensure type parsing stops at `where`, and rerun
GREEN:

```text
cargo test --locked --test interfaces_syntax projects_ordered_requirements_on_both_global_presentations -- --exact
```

### Task 2 — Step 4: Project impls and close recovery RED to GREEN

Add:

- `projects_generic_impl_prerequisites_and_flat_method_equations`;
- `projects_mixed_declarations_with_explicit_source_order` for interleaved
  types, interfaces, globals, and impls;
- `accepts_an_empty_impl_body_for_checker_owned_completeness`;
- `recovers_at_an_impl_method_line_and_closing_brace`; and
- malformed empty/trailing-comma requirements, malformed interface/impl heads,
  misplaced `where`, and malformed methods.

Retain flat impl equations and assert mixed declaration order explicitly;
later category-local identity ordinals do not derive from that cross-family
sequence. Surface projection remains flat; resolution partitions maximal
contiguous method groups, and checking owns interface membership. Synchronize at
logical method lines or the matching `}` without
mistaking a nested expression block for the impl close.

Witness each malformed-header, malformed-method, and delimiter-recovery family
with its exact test before running the complete target. Assert the parser-owned
expected form, retained diagnostic and synchronization span, and refusal to
project a recovery-bearing tree; `is_err()` alone is insufficient.

First run the positive impl projection witness RED, implement it, and rerun it
GREEN:

```text
cargo test --locked --test interfaces_syntax projects_generic_impl_prerequisites_and_flat_method_equations -- --exact
```

Then run:

```text
cargo test --locked --test interfaces_syntax
cargo test --locked --test modules_syntax
cargo test --locked --test parser
cargo fmt --check
```

Expected GREEN. Preserve an explicit unified declaration-order index or an
equivalent source-order structure; do not reconstruct cross-family diagnostic
order from separate surface vectors.

### Task 2 — Step 5: Review and commit

Review parser locality and recovery against AD-0005. Commit unsigned as:

```text
feat: parse Ash interfaces and implementations
```

## Task 3: Allocate stable identities and resolve local relationships

### Task 3 — Files

- Create: `src/interface.rs`
- Modify: `src/lib.rs`
- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/driver.rs`
- Modify: `src/resolve/module_tests.rs`
- Modify: `tests/resolution.rs`

### Task 3 — Step 1: Resolve local identities and namespaces RED to GREEN

Add RED cases:

- `resolves_local_interface_and_method_identities`;
- `rejects_interface_and_nominal_wrong_sorts`;
- `rejects_interface_conflicts_with_module_alias_and_targeted_nominal`;
- `rejects_method_conflicts_with_targeted_term`;
- `rejects_method_conflict_with_lowercase_renamed_constructor`; and
- `resolves_method_occurrences_in_the_tagged_term_namespace`.

Assert exact `resolve.unknown-interface`, `resolve.interface-kind`, existing
`resolve.type-kind`, `resolve.duplicate-type`, `resolve.duplicate-global`, and
`resolve.import-conflict` reasons in these first tests. Hidden method-binder
allocation reuses `resolve.binder-id-exhausted`; do not invent a separate
interface-identity exhaustion family.

Run:

```text
cargo test --locked --test resolution resolves_local_interface_and_method_identities -- --exact
cargo test --locked --lib resolve::module_tests
```

Expected RED because the identity and resolved forms are absent.

Define resolver-owned newtypes for `InterfaceId` and `MethodId`. Use tagged
resolved type-name entries for nominal versus interface sorts and a tagged term
representation such as `ResolvedTermName::{Global(BinderId), Method(MethodId)}`
so a method is never disguised as an ordinary global binder. Rerun the exact
tests GREEN before proceeding:

```text
cargo test --locked --test resolution resolves_local_interface_and_method_identities -- --exact
cargo test --locked --lib resolve::module_tests
```

### Task 3 — Step 2: Resolve ordered requirements RED to GREEN

Add `resolves_duplicate_requirements_as_distinct_ordered_occurrences` as the
first RED case. Cover unqualified local interfaces, wrong sorts, and parameters
that occur only in a requirement. Duplicate identity-equal requirements resolve
as two ordered occurrences with distinct `RequirementId` values; Task 4 owns
their rejection. Preserve source order and resolved type arguments.

Run:

```text
cargo test --locked --test resolution resolves_duplicate_requirements_as_distinct_ordered_occurrences -- --exact
```

Expected RED because the resolved requirement and owner-qualified identity are
absent.

Define `RequirementId` and `ResolvedRequirement`. Do not construct
`ConstrainedScheme` yet: it is a checked semantic object, and Task 4 owns
closure, visibility, duplicate, and undetermined-parameter checks. Rerun the
exact test GREEN.

### Task 3 — Step 3: Resolve impl identities and binders RED to GREEN

Add RED cases:

- `allocates_impl_and_hidden_method_binders_in_source_order`;
- `allocates_all_hidden_method_binders_before_resolving_bodies`; and
- `resolves_impl_prerequisites_and_method_occurrences_to_method_ids`;
- `derives_impl_method_identity_from_impl_and_interface_method`;
- `retains_duplicate_impl_method_groups_with_one_shared_semantic_identity`; and
- `leaves_extra_impl_method_group_without_semantic_identity`.

Run:

```text
cargo test --locked --test resolution allocates_all_hidden_method_binders_before_resolving_bodies -- --exact
```

Define `ImplId` and `ImplMethodId`. Partition the flat equations into maximal
contiguous method groups during resolution. Allocate all ordinary global and
one hidden impl-method `BinderId` per group before resolving any body. A group
that resolves to an interface `MethodId` receives the derived
`ImplId + MethodId`; duplicate groups therefore share that semantic identity
while retaining distinct invalid source groups, and an extra group receives no
semantic impl-method identity. Task 4 rejects duplicates and extras before
admitting the unique `ImplMethodId`-to-`BinderId` mapping or checking bodies.
Resolve requirement-only and prerequisite-only candidate variables far enough
for their checker-owned reasons. Rerun the exact test and the complete
resolution target GREEN.

The stable identity laws are explicit and category-local:

```text
InterfaceId  = defining ModuleId + interface declaration ordinal
MethodId     = InterfaceId + method declaration ordinal
ImplId       = defining ModuleId + impl declaration ordinal
ImplMethodId = ImplId + MethodId
RequirementOwner = Global(BinderId) | Impl(ImplId)
RequirementId = RequirementOwner + requirement ordinal
```

Task 4 validates the resolved identities against exact interface membership and
admits only one checked mapping for each required method.

### Task 3 — Step 4: Retain structural evidence slots and update consumers

Add `resolved_constraint_occurrences_start_with_owned_empty_evidence_slots` as
a RED case. It must inspect every resolved constrained-global and method
occurrence and find its structural evidence slot empty.

Run:

```text
cargo test --locked --test resolution resolved_constraint_occurrences_start_with_owned_empty_evidence_slots -- --exact
```

Add the empty structural slot directly to each resolved occurrence. Do not
allocate occurrence IDs merely to build a detached span/index table. Update
`src/elaborate.rs`, `src/driver.rs`, and every other exhaustive consumer
mechanically; this step adds no checking or selection behavior. Rerun the exact
test GREEN.

### Task 3 — Step 5: Run local resolution GREEN

Run:

```text
cargo test --locked --test resolution
cargo test --locked --lib resolve::module_tests
cargo check --locked --all-targets
cargo fmt --check
```

Expected GREEN for local identities and existing module behavior. Cross-module
interface and impl exports remain pending until checked summary publication in
Task 4.

### Task 3 — Step 6: Review and commit

Review identity ownership, allocation exhaustion, namespace separation, and
absence of string-encoded identities. Commit unsigned as:

```text
feat: resolve interface identities and constraints
```

## Task 4: Check headers, publish summaries, and enforce implementation overlap

### Task 4 — Files

- Modify: `src/interface.rs`
- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/driver.rs`
- Modify: `src/render.rs`
- Create: `tests/interfaces.rs`
- Create: `tests/interface_modules.rs`
- Create: `tests/interface_identity_diamond.rs`
- Create: `tests/interface_generic_summary.rs`
- Modify: `tests/implementations.rs`
- Modify: `tests/functions.rs`
- Modify: `tests/module_elaboration.rs`
- Modify: `tests/module_entry.rs`

### Task 4 — Step 1: Check interface declarations RED to GREEN

Add focused RED tests for method parameter occurrence, function shape,
method-local variables, public/private closure, duplicate requirements, and
undetermined requirement parameters. Construct `ConstrainedScheme` separately
from `Type` only after these checks succeed. Assert exact `interface.*` and
public/private `constraint.*` reasons.

Use `rejects_interface_method_without_parameter_occurrence` as the first
witness:

```text
cargo test --locked --test interfaces rejects_interface_method_without_parameter_occurrence -- --exact
```

Use `rejects_duplicate_global_requirement_before_scheme_construction` as the
separate constrained-global witness:

```text
cargo test --locked --test interfaces rejects_duplicate_global_requirement_before_scheme_construction -- --exact
```

Implement these judgments, rerun both exact tests, then the focused interface
declaration and constrained-global cases GREEN.

### Task 4 — Step 2: Admit impls and check membership and bodies RED to GREEN

Add focused RED tests for variable heads, primitive and nominal orphan
ownership, prerequisite variables, strict-subterm rejection,
missing/duplicate/extra methods, and existing type/pattern/coverage failures in
method bodies. Assert every corresponding `impl.*` reason before implementing
the behavior. Add precedence cases proving an invalid header never enters the
effective environment and therefore cannot produce a secondary overlap.

Name the complete ownership and opacity matrix directly:

- `accepts_impl_for_local_interface`;
- `accepts_impl_for_local_outer_nominal`;
- `rejects_foreign_interface_and_foreign_nominal_impl_as_orphan`;
- `rejects_primitive_impl_for_foreign_interface_as_orphan`; and
- `rejects_external_opaque_constructor_and_pattern_in_impl_body`.

Use `rejects_missing_impl_method` as the first membership witness:

```text
cargo test --locked --test implementations rejects_missing_impl_method -- --exact
```

Implement, in order, header admission, environment and overlap validation,
exact method membership, and impl method type/pattern/coverage checking. A
success produces a checked local registry; no public summary exists yet. Rerun
the exact test and the focused impl target GREEN.

### Task 4 — Step 3: Publish checked summaries RED to GREEN

Add RED cases for:

- public interface and impl facts crossing one checked direct import;
- `preserves_all_interface_identity_families_through_dependency_diamond` for
  `InterfaceId`, `MethodId`, `ImplId`, `ImplMethodId`, and `RequirementId`;
- alternate aliases and canonical routes preserving one interface identity;
- qualified and targeted interface/method imports;
- a targeted same-spelled interface and constructor;
- private interface and impl invisibility;
- generic head alpha-renaming and hidden nominal retention; and
- no summary publication after any header, completeness, or body failure.

Add exact admitted/limit-plus-one unit tests for imported facts and retained
headers before implementing their charges. The publication order is normative
for this implementation boundary: check interface signatures, admit impl
headers, construct and overlap-check the effective environment, check method
membership, check impl method types/patterns/coverage, build the checked local
registry, then call `ExportSummary::freeze`. Never synthesize summaries from
unchecked resolved declarations.

`ExportSummary` carries checked interface and method semantic facts. It does
not encode a public method as `ExportedGlobal` with a fabricated `BinderId`.
Import-side type maps retain distinct nominal and interface entries, and term
maps retain tagged global and method entries. Qualified requirement references
are first resolved here, after the dependency's checked interface summary is
available.

Use `public_impl_fact_is_available_on_a_targeted_direct_import_edge` as the
first publication witness:

```text
cargo test --locked --test interface_modules public_impl_fact_is_available_on_a_targeted_direct_import_edge -- --exact
```

Use `failed_public_impl_stages_never_produce_a_checked_summary` for header,
completeness, and body-failure atomicity:

```text
cargo test --locked --test implementations failed_public_impl_stages_never_produce_a_checked_summary -- --exact
```

Rerun the focused `interfaces`, `interface_modules`, `module_resolution`, and
`module_visibility` tests GREEN.

### Task 4 — Step 4: Enforce implementation overlap RED to GREEN

Add RED cases for:

- no impl re-export through an intermediary;
- route deduplication by `ImplId`;
- authenticated effective-environment overlap through an internal fact
  harness;
- `rejects_generic_local_overlap_after_pair_local_freshening`; and
- an injectable graph budget proving the same budget instance charges imported
  dependency facts and then local module checking without reset.

Add exact admitted/limit-plus-one unit tests for environment construction, route
deduplication, and overlap comparisons before implementing their charges.
Introduce one `InterfaceConstraintBudget` in the driver before the module loop;
pass it mutably through dependency fact admission and
`check_module_with_budget`. Task 6 must receive this same retained budget.

Use `alternate_direct_routes_to_one_impl_identity_do_not_self_overlap` as the
first module-boundary witness:

```text
cargo test --locked --test interface_modules alternate_direct_routes_to_one_impl_identity_do_not_self_overlap -- --exact
```

Run the exact RED case, implement route deduplication and fresh-head overlap,
cover synthetic-fact conflict order and provenance through the authenticated
internal harness, rerun the cases GREEN, then rerun:

```text
cargo test --locked --test interfaces
cargo test --locked --test module_resolution --test module_visibility
```

### Task 4 — Step 5: Run GREEN and regressions

Run:

```text
cargo test --locked --test interfaces
cargo test --locked --test implementations --test interface_modules
cargo test --locked --test module_resolution --test module_visibility
cargo test --locked --test resolution --test polymorphism
cargo fmt --check
```

Expected GREEN. Request an independent review of the namespace, summary,
orphan, termination, and implementation-overlap boundaries.

### Task 4 — Step 6: Commit

The header-admission checkpoint is unsigned commit `f3bbc3a`:

```text
feat: check interface implementation headers
```

Commit checked summaries, direct fact transport, identity deduplication,
overlap enforcement, and the completed Task 4 evidence unsigned as:

```text
feat: publish interface implementation summaries
```

## Task 5: Select and retain abstract and concrete evidence

### Task 5 — Files

- Created: `src/evidence.rs`
- Created: `src/evidence_audit.rs`
- Created: `tests/interface_selection.rs`
- Modified: `src/interface.rs`, `src/resolved.rs`, `src/elaborate.rs`,
  `src/driver.rs`, `src/lib.rs`, `src/resolve.rs`, and `src/types.rs`
- Modified compatibility regressions: `tests/bindings.rs`,
  `tests/data_and_adts.rs`, `tests/functions.rs`,
  `tests/module_elaboration.rs`, `tests/polymorphism.rs`,
  `tests/provenance.rs`, `tests/recursion.rs`, `tests/resolution.rs`, and
  `tests/semantics.rs`
- Unchanged regression: `tests/interfaces.rs`

### Task 5 — Step 1: Witness selection RED

The initial probe was:

```text
cargo test --locked --test interface_selection -- --ignored
```

It ran five ignored scaffolding cases and failed at unresolved method
`Internal(InvalidState)`, before selection and checked-body ownership existed.
The scaffolding was removed after the implementation supplied the retained
structural assertions below.

The completed integration tests prove:

- a constrained global method occurrence selects its exact abstract
  `RequirementId` before an otherwise matching impl;
- a constrained-global occurrence owns one selection per requirement in source
  order;
- a concrete local candidate records `ImplId`, substitution, prerequisites,
  and ordered `ImplMethodId` slots;
- Task 4's duplicate and requirement-only parameter cases remain GREEN
  regressions with their exact `constraint.duplicate-requirement` and
  `constraint.undetermined-parameter` reasons;
- absent candidates use `constraint.unsatisfied`;
- `rejects_public_global_obligation_instead_of_inferring_exported_requirement`
  proves requirements are never inferred into a public scheme;
- undetermined obligations never cause type guessing;
- an eligible local anonymous-function initializer closes obligations before
  `generalize_local` and reports `constraint.ambiguous`; and
- recursive constrained globals reuse their declared abstract evidence; and
- body errors across global and implementation declaration families follow the
  retained source declaration order.

They inspect the resulting `CheckedModule` to prove that each selection is
attached to its exact occurrence rather than joined from detached span-keyed
state. The linked-group probe confirms that successful checking produces
`CheckedDefinition` values and `CheckedModule::into_group` moves them into the
module group without exposing raw-definition synthesis. Unit tests also cover
independent empty slots, shared selected flat plans, exact selection and audit
work boundaries, and deep selection and destruction.

### Task 5 — Step 2: Complete checked selection and retention

Ordered obligation creation follows ordinary rank-1 instantiation. At closure,
checking selects exact abstract evidence, then exact-current-impl evidence,
then one coherent ordinary implementation; it does not solve an obligation
inference variable to fit a candidate. `CheckedModule` owns
`CheckedDefinition` values only after complete success, and its group transition
retains those values and their filled occurrence slots. The existing graph budget
charges obligations, candidates, substitutions, prerequisites, active goals,
retained selections, and the checked-body audit traversal.

The audit establishes only that every checked occurrence has the structurally
expected, filled slots before the type-state transition. It does not authenticate
linked identities, substitutions, availability, provenance, or method-slot
meaning, and it does not lower evidence. Those are Task 6 work.

The linker now derives the entry `main ()` expression from the checked entry
module and rejects an absent, polymorphic, constrained, or non-`Unit` entry
scheme. Standalone resolved-expression probes use a separate constructor and
cannot be presented as the final checked-module root.

### Task 5 — Step 3: Run GREEN and review

The following commands passed in the Task 5 worktree:

```text
cargo test --locked --test interface_selection
cargo test --locked --lib
```

At the recorded run, the integration target had 11 passing tests and the
library target had 252 passing tests. The complete all-target suite, Clippy,
and `cargo xtask verify` also passed. Independent logic and resource reviews
confirm that selection occurs in checking, body diagnostics preserve retained
cross-family source order, and checked definitions retain their filled slots
through the group transition without an unchecked final-synthesis bypass.
Task 6 still owns linked evidence validation and evidence lowering through Core.

### Task 5 — Step 4: Commit

Commit the completed checkpoint unsigned as:

```text
feat: select checked interface evidence
```

## Task 6: Validate evidence and lower through existing Core

### Task 6 — Files

- Modify: `src/interface.rs`
- Modify: `src/resolved.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/driver.rs`
- Modify: `src/diagnostic.rs`
- Modify: `src/core/validate.rs` only for ordinary resulting-Core witnesses if
  required
- Modify: `tests/interfaces.rs`
- Create: `tests/interface_validation.rs`
- Create: `tests/interface_corpus.rs`
- Modify: `tests/module_elaboration.rs`
- Modify: `tests/core_validation.rs`
- Modify: `tests/architecture.rs`

### Task 6 — Step 1: Write linked-evidence and validation RED tests

Add a cross-module constrained call with an exact result. Assert that Core:

- type-abstracts before evidence binders;
- type-applies a constrained occurrence before evidence application;
- applies evidence before the source value argument;
- maps `ImplMethodId` through its module-qualified hidden binder; and
- places impl methods in the defining module's ordinary recursive group.

Create the end-to-end corpus before implementing lowering and add these RED
cases with exact observations:

- `local_equal_int_observes_true` -> `true : Bool`;
- `cross_module_constrained_equal_observes_true` -> `true : Bool`;
- `complete_and_targeted_imports_observe_the_same_evidence` ->
  `(true, true) : (Bool, Bool)`;
- `hidden_carrier_composes_to_forty_two` -> `42 : Int`;
- `opaque_carrier_uses_public_operations` -> `true : Bool`;
- `higher_order_abstract_evidence_observes_true` -> `true : Bool`;
- `equational_and_operational_constraints_agree` ->
  `(true, true) : (Bool, Bool)`.

Run the corpus target RED before production changes in this task. Its failures
must be missing evidence validation/lowering behavior, not fixture setup.

In `tests/interface_validation.rs`, add pre-Core validator corruption tests for
wrong identities, unavailable selected impl, wrong substitutions, prerequisite
arity/order, missing or reordered same-typed slots, bad impl-method binder
mappings, abstract ownership, inference escape, scope, type, and provenance.
Keep `tests/core_validation.rs` limited to the resulting ordinary Core. Add
exact admitted/limit-plus-one unit tests for linked registry entries and every
interface-evidence validation visit before implementing those charges.
Add a driver injection witness proving an `evidence.validation.*` failure stops
before Core synthesis or evaluation.

### Task 6 — Step 2: Witness RED

Run:

```text
cargo test --locked --test interfaces cross_module_constraint_lowers_to_method_evidence -- --exact
cargo test --locked --test interface_validation
cargo test --locked --test interface_corpus
cargo test --locked --test core_validation --test module_elaboration
```

Expected RED before linked registry/evidence validation and lowering exist.

The recorded Task 6 RED run compiled all seven corpus fixtures and failed each
at final synthesis with `Internal(InvalidState)`. The focused
`cross_module_constraint_lowers_to_method_evidence` witness reached the same
boundary. Parsing, resolution, interface checking, selection, and linking had
therefore succeeded; the failures belonged to absent evidence lowering rather
than fixture setup.

The first bounded validation checkpoint now introduces the raw-linked to
validated-interface type state, location-only linked indexes, exact direct-edge
authentication, source-ordered occurrence worklists, and graph-budget
continuity through linking and validation. Fourteen validator unit tests, the
public validation integration test, and the twelve selection integration tests
pass. The corpus and Core-shape witnesses intentionally remain RED until the
validated wrapper becomes the only final-synthesis input and evidence lowers
through ordinary Core.

### Task 6 — Step 3: Link, validate once, and synthesize

Extend `ResolvedModuleProgram` with combined checked interface/impl registries
and structurally annotated checked-definition groups. Before Core synthesis,
validate each recorded
selection against identities, its owning module's direct effective environment,
substitution, prerequisite tree, method order, scheme, scope, type, and
provenance. This validator authenticates the recorded choice without searching
candidates.

Continue using the `InterfaceConstraintBudget` created by the driver in Task 4
before processing the module graph. Keep passing that same mutable value through
resolver import
admission, `check_module_with_budget`,
`link_modules(..., &mut budget) -> Result<...>`, and
`validate_interface_evidence(..., &mut budget)`. Each phase charges before
allocation; none resets or replaces the value. Introduce a distinct
`PipelineFailure::EvidenceValidation` or equivalent for pre-Core
`evidence.validation.*` failures. Do not route them through the existing Core
validation failure, because no Core program exists at this point.

Derive flattened evidence function types by requirement order then method order.
Lower abstract selections to evidence binders and concrete selections to hidden
impl-method binders with recorded type and prerequisite-evidence applications.
Leave `Type`, the Core dialect, and evaluator dispatch inventory unchanged.
Final lowering accepts the retained checked definitions and recorded selections
only; candidate search is neither called nor reachable from synthesis.

### Task 6 — Step 4: Run GREEN and architecture review

Run:

```text
cargo test --locked --test interfaces
cargo test --locked --test interface_validation
cargo test --locked --test interface_corpus
cargo test --locked --test module_elaboration --test core_validation --test architecture
cargo test --locked --test semantics
cargo fmt --check
```

Expected GREEN. Independently review the selection/validation erasure boundary
and every changed Core consumer.

The recorded final Task 6 run is GREEN. The seven required corpus observations
and the additional same-typed multi-method regression pass, as do the exact
Core-shape and validator-barrier witnesses. The focused matrix passes 84 tests,
the library passes 282 tests, and the complete test suite, format, all-target
checking, strict Clippy, and diff hygiene pass. Two independent review cycles
covered validation, lowering, Core consumers, budget accounting, and test
strength. Review fixes authenticate imported implementation publication,
revalidate generic-header termination through the checker's shared iterative
judgment, charge block scans before inspection, reject missing or reordered
same-typed slots, retain the closed Core/evaluator inventory, and avoid emitting
unused sibling methods for a single method occurrence. The repeated reviews are
clear.

### Task 6 — Step 5: Commit

Commit unsigned as:

```text
feat: lower validated interface evidence
```

## Task 7: Complete generic and recursive evidence

### Task 7 — Files

- Modify: `src/interface.rs`
- Modify: `src/resolved.rs`
- Modify: `src/elaborate.rs`
- Modify: `tests/interfaces.rs`
- Modify: `tests/interface_corpus.rs`
- Modify: `tests/recursion.rs`
- Modify: `tests/module_visibility.rs`

### Task 7 — Step 1: Write generic and recursion RED tests

Cover:

- `Equal<Option<A>> where Equal<A>` applied to `Option<Int>`;
- multiple prerequisite method slots and declaration order;
- exact-rigid self evidence without fresh current-impl instantiation;
- direct, mutual, global-to-method, and method-to-global recursion;
- expanding prerequisite rejection and ground cross-interface cycles;
- abstract prerequisite evidence inside current impl methods;
- deep valid prerequisite chains through an explicit worklist; and
- hidden-carrier and opaque-type generic impls.

Before implementing these behaviors, extend the end-to-end corpus with RED
cases and exact observations:

- `generic_option_evidence_observes_true` -> `true : Bool`;
- `recursive_impl_method_computes_forty_two` -> `42 : Int`; and
- `mutual_impl_methods_compute_forty_two` -> `42 : Int`.

Assert exact `impl.prerequisite-not-decreasing`, `constraint.cycle`, and rigid
self-selection failure behavior here. Add exact charge tests for generic
prerequisite traversal and evidence construction before implementing them.

### Task 7 — Step 2: Witness RED

Run:

```text
cargo test --locked --test interfaces generic_option_impl_constructs_prerequisite_evidence -- --exact
cargo test --locked --test interface_corpus
cargo test --locked --test recursion --test module_visibility
```

Expected RED at generic substitution, self evidence, cycle, or recursive group
construction.

### Task 7 — Step 3: Implement minimal generic evidence

Fresh-match only ordinary candidate head variables. Exclude the current
`ImplId` from general lookup while checking its methods. Exact self evidence
uses its rigid head and already abstract prerequisite slots. External generic
selection recursively selects prerequisites with an active-goal set and builds
method evidence by type application followed by ordered prerequisite
applications.

Keep prerequisite selection, validation, and destruction stack-safe.

### Task 7 — Step 4: Run GREEN and commit

Run:

```text
cargo test --locked --test interfaces
cargo test --locked --test interface_corpus
cargo test --locked --test recursion --test module_visibility --test module_entry
cargo test --locked --all-targets
cargo fmt --check
```

Expected GREEN. Commit unsigned as:

```text
feat: resolve generic interface evidence
```

## Task 8: Close structured diagnostics and resource boundaries

### Task 8 — Files

- Modify: `src/interface.rs`
- Modify: `src/diagnostic.rs`
- Modify: `src/render.rs`
- Modify: `src/driver.rs`
- Create: `tests/interface_diagnostics.rs`
- Create: `tests/interface_resources.rs`
- Modify: `tests/interface_validation.rs`
- Modify: `tests/module_entry.rs`
- Modify: `tests/module_cli.rs`
- Modify: `tests/diagnostics.rs`

### Task 8 — Step 1: Audit prior reason tests and add cross-stage RED cases

Inventory the exact reason assertions introduced in Tasks 3 through 7. Add only
the cross-stage witnesses that could not precede their production behavior:
primary and related spans spanning imports, private and transitive-only impl
non-leakage, existing entry precedence before `entry.main-constrained`, and one
CLI case proving rendering consumes structured data without owning policy.

### Task 8 — Step 2: Write exact budget and validator RED tests

Audit the exact charge tests introduced with each allocator and traversal. Add
only cross-stage resource RED cases proving:

- one budget persists from dependency admission through linking and evidence
  validation;
- cycle beats resource exhaustion for the same work;
- exhaustion is `internal.resource.constraint-work`;
- malformed plans remain `evidence.validation.*`; and
- deep valid selection, validation, and destruction fit a 256 KiB host stack.

### Task 8 — Step 3: Run RED then complete ownership and accounting

Run the focused targets and confirm each first failure is the missing behavior,
not fixture setup. Implement minimal typed reasons, causal labels, deterministic
ordering, pre-allocation charges, and explicit worklists.

### Task 8 — Step 4: Run GREEN and commit

Run:

```text
cargo test --locked --test interface_diagnostics --test module_entry --test module_cli
cargo test --locked --test interface_resources --test interface_validation
cargo test --locked --test diagnostics
cargo test --locked --all-targets
cargo clippy --locked --all-targets -- -D warnings
cargo fmt --check
```

Expected GREEN. Commit unsigned as two bounded checkpoints if useful:

```text
test: close interface diagnostic coverage
test: establish interface resource boundaries
```

## Task 9: Retain the end-to-end interface corpus

### Task 9 — Files

- Modify: `tests/interface_corpus.rs`
- Modify: `tests/architecture.rs`

### Task 9 — Step 1: Audit the already-green CP-0006 product corpus

Confirm that Tasks 6 and 7 introduced and turned GREEN independent named cases
with these exact observations:

- `local_equal_int_observes_true` -> `true : Bool`;
- `cross_module_constrained_equal_observes_true` -> `true : Bool`;
- `complete_and_targeted_imports_observe_the_same_evidence` ->
  `(true, true) : (Bool, Bool)`;
- `generic_option_evidence_observes_true` -> `true : Bool`;
- `hidden_carrier_composes_to_forty_two` -> `42 : Int`;
- `opaque_carrier_uses_public_operations` -> `true : Bool`, paired with the
  external impl-body constructor/pattern rejection in the negative corpus;
- `recursive_impl_method_computes_forty_two` -> `42 : Int`;
- `mutual_impl_methods_compute_forty_two` -> `42 : Int`;
- `higher_order_abstract_evidence_observes_true` -> `true : Bool`;
- `equational_and_operational_constraints_agree` ->
  `(true, true) : (Bool, Bool)`; and

Retain separate direct-only/no-reexport rejection, same-typed slot order, and
type-application/evidence-application/value-application trace cases.

Assert the closed Core/evaluator feature inventories contain no interface node,
dictionary, runtime registry, lookup, or dispatch rule.

### Task 9 — Step 2: Run the retained corpus and inventory

Run:

```text
cargo test --locked --test interface_corpus
cargo test --locked --test architecture
cargo test --locked --all-targets
cargo fmt --check
```

Expected GREEN. This task adds no production behavior. If the audit finds a
missing witness, add it to the owning earlier test target and confirm it fails
for the intended reason before changing production code; do not use this
consolidation checkpoint for late semantic implementation. Commit unsigned as:

```text
test: retain the interface integration corpus
```

## Task 10: Replace normative truth and record retained evidence

### Task 10 — Files

- Modify: `spec/README.md`
- Modify: `spec/lexical-structure.md`
- Modify: `spec/syntax.md`
- Modify: `spec/name-resolution.md`
- Modify: `spec/static-semantics.md`
- Modify: `spec/elaboration.md`
- Modify: `spec/dynamic-semantics.md`
- Modify: `docs/tools/ash.md`
- Modify: `tests/spec_examples.rs`
- Create: `docs/design/modular-ash/interfaces-evidence.md`
- Modify: `docs/design/DN-0023-interfaces-and-implementations.md`
- Modify: `docs/design/DN-0020-ash-dialect-milestones.md`
- Modify: `docs/design/README.md`
- Modify: `docs/trajectory.md`
- Modify: `docs/tasks/TASK-0012-implement-interfaces-and-implementations.md`

### Task 10 — Step 1: Add executable documentation examples first

Add local, cross-module, generic, hidden/opaque, and constrained-presentation
examples plus document-presence assertions. Run:

```text
cargo test --locked --test spec_examples
```

Expected RED until normative documents contain and agree with the examples.

### Task 10 — Step 2: Replace current specification truth

Apply CP-0006 to every affected specification area. Use `global signature` for
the pre-existing function annotation. State syntax, stable identities,
namespaces, checked schemes, impl admission, implementation overlap, selection,
summary lifecycle, structural evidence, validation, lowering, entry, failure
ownership, resources, and unchanged evaluation. Follow the formal-notation
guide for grammar and judgments.

Update tool docs only for observed source diagnostics; invocation and runtime
loading stay unchanged.

### Task 10 — Step 3: Draft retained implementation evidence

Record baseline `ca79328`, the required-evidence matrix and exact tests,
diagnostic/resource boundaries, summary and evidence lifecycle, Core/evaluator
inventory, unspecialized generic Core/evaluation trace, exclusions, and the
later audit pressure. Mark final review, locality inspection, and complete
verification as pending rather than claiming unrun results.

Mark interfaces implemented in the trajectory and make the core-versus-library
audit next. Do not start associated types or specialization.

### Task 10 — Step 4: Verify docs and commit checkpoints

Run:

```text
cargo test --locked --test spec_examples
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Review relative links, authority, formal notation, examples, and reason names.
Commit unsigned as:

```text
docs: specify Ash interfaces and implementations
docs: record interface implementation evidence
```

## Task 11: Review, verify, and remove transition artifacts

### Task 11 — Step 1: Review the completed product against CP-0006

Use concurrent independent reviews for syntax/namespaces, checking/evidence,
Core/validation/resources, and specification/evidence. Fix findings and repeat
until all tracks are clear. End each fix cycle with its own bounded unsigned
commit, and require `git status --short` to be empty before the final locality
inspection and verification.

Review the complete feature branch against `main` separately from the local
interface increment:

```text
git diff --stat main...HEAD
git diff --name-status main...HEAD
git log --oneline main..HEAD
```

This review owns complete-branch logic and regression pressure. Retain the
accepted-interface baseline view for interface-locality accounting:

Inspect implementation locality:

```text
rg -n '\b(Interface|Impl|Requirement|EvidenceSelection)\b' src/core src/eval
git diff --stat ca79328..HEAD
git status --short
```

Expected: ordinary generated Core facts may appear in tests or validation
inputs, but the closed Core/evaluator dialect contains no interface mechanism,
and the worktree is clean.

### Task 11 — Step 2: Run the complete verification boundary

Run:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --all-targets
cargo clippy --locked --all-targets -- -D warnings
cargo xtask verify
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Expected: every command passes. Manually account for every CP-0006 evidence
item, relative link, authority boundary, changed Core consumer, and excluded
feature.

### Task 11 — Step 3: Finalize witnessed retained evidence

After every review track is clear, update
`docs/design/modular-ash/interfaces-evidence.md` with the exact final commands,
results, test counts, implementation-locality inventory, resolved review
findings, and clean status. Retain the unspecialized evidence trace as the
baseline for any later specialization comparison.

Run:

```text
cargo test --locked --test spec_examples
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Expected: PASS. Commit the final evidence update unsigned before cleanup.

### Task 11 — Step 4: Remove completed transition artifacts

Only after the product review is clear:

- remove `docs/proposals/CP-0006-interfaces-and-implementations.md`;
- remove `docs/tasks/TASK-0012-implement-interfaces-and-implementations.md`;
- remove this execution plan;
- update proposal and task indexes; and
- remove live CP/task links from retained design/evidence documents.

Git retains the accepted proposal, task progress, and plan history. The current
tree retains the normative specification, DN-0023 result, and implementation
evidence.

Run:

```text
rg -n 'CP-0006|TASK-0012|2026-08-24-implement-interfaces-and-implementations' docs spec README.md
markdownlint --disable MD013 -- README.md spec docs
git diff --check
cargo xtask verify
```

Expected: the reference search is empty and all checks pass. Commit unsigned
as:

```text
docs: complete interface implementation
```

Do not merge. Retain the baseline for a later, separately authorized
core-versus-library audit; do not begin that audit from this task.
