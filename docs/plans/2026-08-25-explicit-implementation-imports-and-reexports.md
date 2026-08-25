# Explicit Implementation Imports and Re-exports Implementation Plan

> **For Codex:** REQUIRED SUB-SKILL: Use `superpowers:executing-plans` to
> implement this plan task by task, preserving the review checkpoints.

**Goal:** Implement accepted CP-0008 as explicit implementation selection and
targeted name and implementation re-exports, the first bounded `lib-ash`
increment.

**Architecture:** Extend targeted imports with an implementation-selector
channel and make `pub import` stage checked foreign identities into generated
summaries. Represent one implementation authorization as a flat, charged path
of module-to-dependency hops. Summaries publish body-free implementation facts
with their selected paths; checked module groups retain only lightweight public
authorization entries so linked validation can authenticate every hop before
unchanged Core lowering.

**Tech stack:** Rust 2024, the existing event-producing concrete-tree parser,
canonical acyclic module loader, identity-based resolver, bidirectional
elaborator, checked export summaries, interface evidence selector and validator,
pure typed Core, Cargo integration tests, and Markdown specification.

---

Implementation follows `superpowers:test-driven-development`, `rust-skills`,
`superpowers:systematic-debugging` for unexpected results,
`superpowers:requesting-code-review` at the named checkpoints, and
`superpowers:verification-before-completion`. Begin in a dedicated worktree
created with `superpowers:using-git-worktrees` from the authorization commit.
Keep current `spec/` authoritative until implementation, tests, and normative
updates land together. Use unsigned commits.

## Task 1: Authorize and baseline the increment

**Files:**

- Create: `docs/tasks/TASK-0015-implement-explicit-implementation-imports-and-reexports.md`
- Create: `docs/plans/2026-08-25-explicit-implementation-imports-and-reexports.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/proposals/CP-0008-explicit-implementation-imports-and-reexports.md`
- Modify: `docs/trajectory.md`

### Step 1: Confirm transition authority

Read CP-0008 and confirm its status is `accepted`, its `Related` list links
TASK-0015, and no requested behavior exceeds the proposal. Confirm the current
specification still describes Modular Ash's automatic direct-import behavior.

### Step 2: Record the clean baseline

Run:

```text
cargo xtask verify
```

Expected: PASS with 935 tests and no failure at accepted semantic checkpoint
`0a9d334`.

### Step 3: Validate the authorization artifacts

Run:

```text
markdownlint --disable MD013 -- docs/tasks docs/plans docs/proposals docs/trajectory.md
git diff --check
```

Expected: PASS with no output from `git diff --check`.

### Step 4: Commit

```text
git add docs/tasks/TASK-0015-implement-explicit-implementation-imports-and-reexports.md docs/plans/2026-08-25-explicit-implementation-imports-and-reexports.md docs/tasks/README.md docs/proposals/CP-0008-explicit-implementation-imports-and-reexports.md docs/trajectory.md
git commit --no-gpg-sign -m "docs: authorize explicit library imports"
```

Before Task 2, create the implementation worktree and branch from this commit.

## Task 2: Parse public imports and implementation selectors

**Files:**

- Modify: `src/parser/grammar.rs`
- Modify: `src/parser/project.rs`
- Modify: `src/surface.rs`
- Modify: `tests/modules_syntax.rs`
- Modify: `tests/parser.rs`

### Step 1: Write the positive projection test

Add `projects_public_imports_and_independent_selector_channels` to
`tests/modules_syntax.rs`. Parse:

```ash
pub import equality (Equal as Equality, equal, impl Equal)
```

Assert the import is public, the first two items are name selections with exact
aliases and spans, and the third is an implementation selection with interface
spelling `Equal` and no alias field.

Use explicit surface variants:

```rust
pub enum SurfaceImportItem {
    Name {
        name: SurfaceName,
        alias: Option<SurfaceName>,
        span: Span,
    },
    Implementation {
        interface: SurfaceName,
        span: Span,
    },
}
```

Run:

```text
cargo test --locked --test modules_syntax projects_public_imports_and_independent_selector_channels -- --exact
```

Expected RED: `pub import` does not enter the import prefix and the surface
representation has no visibility or implementation-item variant.

### Step 2: Implement the minimal positive grammar and projection

Add `public: bool` to `SurfaceImport`. Admit `pub import` only while the parser
is consuming the import prefix. In `import_declaration`, consume optional `pub`,
require a targeted list for a public import, and dispatch `impl` items before
ordinary import names. Update CST shape validation and projection without a new
lexer token or runtime form.

Rerun the exact test. Expected: GREEN.

### Step 3: Write malformed and recovery tests

Add focused cases for:

```ash
pub import equality as Equality
import equality (impl equal)
import equality (impl Equal as Renamed)
import equality (impl)
```

Assert the parser-owned reason, expected form, offending span, balanced events,
line-end recovery, and refusal to project a recovery-bearing tree. Also retain
the existing rejection of imports after declarations for both `import` and
`pub import`.

Run the new exact tests first. Expected RED, then GREEN after the minimal
grammar corrections.

### Step 4: Run the complete parser boundary

```text
cargo test --locked --test modules_syntax
cargo test --locked --test parser
cargo fmt --check
```

Expected: GREEN. Review token completeness, `pub` lookahead, logical-line
recovery, and the absence of parser-owned visibility semantics.

### Step 5: Commit

```text
git add src/parser/grammar.rs src/parser/project.rs src/surface.rs tests/modules_syntax.rs tests/parser.rs
git commit --no-gpg-sign -m "feat: parse explicit library import channels"
```

## Task 3: Make imported implementation availability explicit

**Files:**

- Modify: `src/resolve.rs`
- Modify: `src/resolved.rs`
- Modify: `src/elaborate.rs`
- Create: `tests/library_imports.rs`
- Modify: `tests/interface_modules.rs`
- Modify: `tests/interface_selection.rs`
- Modify: `tests/interface_corpus.rs`
- Modify: `tests/interface_generic_summary.rs`

### Step 1: Write the name-only RED witness

In `tests/library_imports.rs`, build a dependency exporting `Equal`, `equal`,
and `pub impl Equal<Int>`. The entry imports only `(Equal, equal)` and calls
`equal(1, 1)`. Assert `constraint.unsatisfied` at the method occurrence and
assert that `ResolvedModule::imported_facts()` contains the interface but not
the implementation.

Run:

```text
cargo test --locked --test library_imports name_only_import_does_not_select_implementation -- --exact
```

Expected RED: the current resolver imports every public implementation for the
dependency.

### Step 2: Split interface metadata retention from implementation selection

Keep public and hidden interface facts required by qualified names, selected
methods, constrained schemes, and implementation facts. Stop
`retain_dependency_interface_facts` from importing implementations
unconditionally. Add a resolver path for
`SurfaceImportItem::Implementation { interface, span }` that:

1. resolves the dependency's public interface spelling;
2. imports every public implementation in that summary whose
   `fact.interface` equals the selected `InterfaceId`;
3. creates no source binding; and
4. deduplicates one `ImplId` across repeated selected edges.

Charge every selector, inspected or indexed summary entry, cloned fact, type,
method, prerequisite, and retained route through the existing graph-wide
budgets. Do not add a second constraint limit.

Rerun the name-only test. Expected: GREEN.

### Step 3: Write and pass the implementation-only witness

Add `implementation_only_import_selects_evidence_without_binding_names`. Use:

```ash
import equality as Equality
import equality (impl Equal)

main : Unit -> Bool
main () = Equality.equal(1, 1)
```

Assert successful checking, one imported implementation, the qualified method
identity, and the original implementation and method identities. Also assert
that `Equal` and `equal` are unavailable as unqualified source names.

Run the exact test RED, implement the minimum remaining resolver behavior, and
rerun GREEN.

### Step 4: Own selector lookup failures

Add cases for a missing/private interface and a public nominal used by
`impl Nominal`. Preserve `resolve.unavailable-export` for unavailable public
spelling and `resolve.interface-kind` when the dependency publicly exports the
wrong declaration sort. Do not report constraint failure for a selector that
resolution could reject.

Run:

```text
cargo test --locked --test library_imports implementation_selector_rejects_an_unavailable_interface -- --exact
cargo test --locked --test library_imports implementation_selector_rejects_a_public_nominal -- --exact
```

Expected: GREEN after structured resolver diagnostics are complete.

### Step 5: Migrate direct cross-module selection fixtures

Add explicit `impl Interface` items to existing positive fixtures that rely on
cross-module evidence. Update assertions that currently say complete and
targeted imports receive identical ambient implementations. Preserve local
implementation cases unchanged.

At minimum audit and update:

```text
tests/implementations.rs
tests/interface_corpus.rs
tests/interface_diagnostics.rs
tests/interface_generic_summary.rs
tests/interface_identity_diamond.rs
tests/interface_modules.rs
tests/interface_selection.rs
tests/interface_validation.rs
tests/interfaces.rs
tests/modular_closure.rs
tests/module_visibility.rs
tests/spec_examples.rs
src/resolve/module_tests.rs
src/resolved.rs unit tests
```

Use this inventory check and inspect every match rather than applying a blind
rewrite:

```text
rg -n 'pub impl|import .* as|import .*\(' tests/*.rs
```

### Step 6: Run selection and migration GREEN

```text
cargo test --locked --test library_imports
cargo test --locked --test interface_modules
cargo test --locked --test interface_selection
cargo test --locked --test interface_corpus
cargo test --locked --test interface_generic_summary
cargo test --locked --workspace --all-targets --all-features
cargo fmt --check
```

Expected: GREEN. Review that qualified imports and name selectors alone never
add implementation facts, while all local private and public implementations
remain effective.

### Step 7: Commit

```text
git add src/resolve.rs src/resolved.rs src/elaborate.rs tests
git commit --no-gpg-sign -m "feat: select imported implementations explicitly"
```

## Task 4: Re-export selected names without forwarding declarations

**Files:**

- Modify: `src/resolve.rs`
- Modify: `src/resolved.rs`
- Modify: `src/elaborate.rs`
- Modify: `tests/library_imports.rs`
- Modify: `tests/module_resolution.rs`
- Modify: `tests/module_visibility.rs`
- Modify: `tests/interface_identity_diamond.rs`

### Step 1: Write the three-module name-facade RED test

Add `public_targeted_import_reexports_each_selected_name_namespace`. The base
module exports a global, transparent nominal and constructors, opaque nominal,
interface, and method. The facade uses aliases in one `pub import`. The entry
imports the facade's selected spellings and asserts the original `BinderId`,
`NominalTypeId`, `ConstructorId`, `InterfaceId`, and `MethodId` values.
Also assert that a parsed public implementation selector is only a staged
candidate at this boundary: Task 4 must not publish it without Task 5's checked
authorization-route representation.

Run:

```text
cargo test --locked --test library_imports public_targeted_import_reexports_each_selected_name_namespace -- --exact
```

Expected RED: `ResolvedExportCandidate` and `ExportSummary::freeze` publish
only local declarations.

### Step 2: Generalize checked export candidates

Extend `ResolvedExportCandidate` with explicit interface and method name maps
and allow term, nominal, and constructor candidates to refer to checked
imported facts. Keep selected spelling separate from defining spelling and
identity. Use one candidate representation per semantic namespace; do not
create facade globals, nominal declarations, interfaces, or Core binders.

During `ExportSummary::freeze`:

- obtain a local global scheme from `checked_globals` or an imported scheme
  from `ImportedFacts` by `BinderId`;
- clone imported nominal and constructor facts under the selected public
  spelling while retaining original access and family metadata;
- map public interface and method spellings to original identities; and
- retain an interface as hidden summary closure when only one of its methods is
  re-exported.

Charge every cloned type, scheme, constructor family, namespace entry, and
hidden fact. A failed module still publishes no summary.

Rerun the exact test. Expected: GREEN.

### Step 3: Preserve privacy, opacity, and aliases

Add RED/GREEN cases proving:

- a private dependency name cannot be publicly imported;
- an opaque constructor cannot be re-exported;
- an opaque nominal remains opaque after one and two facades;
- a hidden carrier in a public imported scheme remains unnameable;
- a selected alias becomes the facade's spelling without changing identity;
- selecting the same underlying identity along two aliases does not forge a
  second declaration; and
- ordinary private imports add no public summary entry.

Run:

```text
cargo test --locked --test library_imports name_reexports_preserve_privacy_opacity_and_identity -- --exact
cargo test --locked --test module_visibility
cargo test --locked --test module_resolution
```

Expected: GREEN.

### Step 4: Review name re-exports and commit

Review every `ExportSummary` owner assertion. Summary ownership names the
publishing module, while each exported fact retains its defining identity.
Remove only assertions that incorrectly equate those two concepts; keep binder,
nominal, constructor, interface, and method ownership validation exact.

```text
cargo check --locked --all-targets
cargo fmt --check
git add src/resolve.rs src/resolved.rs src/elaborate.rs tests/library_imports.rs tests/module_resolution.rs tests/module_visibility.rs tests/interface_identity_diamond.rs
git commit --no-gpg-sign -m "feat: re-export selected library names"
```

## Task 5: Build transitive implementation authorization routes

**Files:**

- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/evidence.rs`
- Modify: `tests/library_imports.rs`
- Modify: `tests/interface_modules.rs`
- Modify: `tests/interface_identity_diamond.rs`
- Modify: `tests/interface_diagnostics.rs`

### Step 1: Write the primary facade RED test

Add `public_implementation_selector_crosses_a_three_module_facade`. Use the
definition, facade, and application source from CP-0008. Run the complete
public driver and assert exact observation `true : Bool`. Inspect checked
summaries and assert one original `InterfaceId`, `MethodId`, `ImplId`, and
implementation-method binder through both edges.

Run:

```text
cargo test --locked --test library_imports public_implementation_selector_crosses_a_three_module_facade -- --exact
```

Expected RED: summaries publish local implementations only and imported
implementation ownership is restricted to the immediate dependency.

### Step 2: Introduce a flat authorization path

Represent a path as owned, non-recursive compiler data:

```rust
pub struct ImplementationRouteHop {
    pub from: ModuleId,
    pub to: ModuleId,
    pub import_span: Span,
}

pub struct ImplementationAuthorization {
    hops: Box<[ImplementationRouteHop]>,
}
```

An empty path belongs only to a public implementation declared by the
publishing module. Selecting a dependency summary prepends exactly one
`current -> dependency` hop to that summary entry's path. Every adjacent hop
must connect, and the final module must own the `ImplId` and hidden method
binders. Use checked addition, fallible reservation, charged cloning, iterative
inspection, and flat-slice destruction.

Wrap each summary implementation fact with its authorization path. Let
`ImportedImplementationFact` and `AvailableImplementation` retain the selected
path instead of assuming `ImplId.module() == direct_dependency`. Provide
borrowed accessors rather than restoring `Copy` through handles or globals.

Rerun the primary facade test. Expected: GREEN through checking; linked
validation remains pending in Task 6 if it rejects the new route.

### Step 3: Select deterministic shortest routes

Add a graph where one `ImplId` reaches the application through paths of
different lengths and another graph with equal lengths. Assert:

1. shortest hop count wins;
2. equal lengths preserve dependency order, then import source order; and
3. a stable path identity breaks any remaining equality without hash-map
   iteration affecting output.

Process summaries and selectors in stable source order. On duplicate `ImplId`,
compare the candidate route before discarding its charged fact and provenance.

Run:

```text
cargo test --locked --test library_imports implementation_routes_choose_the_deterministic_shortest_path -- --exact
```

Expected: GREEN.

### Step 4: Check closure overlap where facts first meet

Replace the old non-re-export witness with positive transitive availability.
Add sibling facade cases that publish overlapping `Equal<Int>`
implementations. Assert that unrelated branches check independently and the
first module selecting both reports the existing overlap reason with both
declarations and the chosen import/re-export paths.

Run:

```text
cargo test --locked --test library_imports distinct_reexported_implementations_conflict_at_the_first_combined_closure -- --exact
cargo test --locked --test interface_modules
cargo test --locked --test interface_diagnostics
```

Expected: GREEN with deterministic structured labels.

### Step 5: Review implementation authorization and commit

Review path ownership, identity deduplication, route tie-breaking, source label
order, fallible allocation, and small-stack drop. Do not add package identity,
artifact keys, implementation names, or head selectors.

```text
cargo check --locked --all-targets
cargo fmt --check
git add src/resolved.rs src/resolve.rs src/elaborate.rs src/evidence.rs tests/library_imports.rs tests/interface_modules.rs tests/interface_identity_diamond.rs tests/interface_diagnostics.rs
git commit --no-gpg-sign -m "feat: publish transitive implementation routes"
```

## Task 6: Authenticate re-export routes before Core

**Files:**

- Modify: `src/resolved.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/evidence_validation.rs`
- Modify: `src/evidence_audit.rs`
- Modify: `tests/interface_validation.rs`
- Modify: `tests/interface_selection.rs`
- Modify: `tests/library_imports.rs`

### Step 1: Write lightweight-publication and tampering RED tests

Add test-only mutation hooks that can independently change:

- one available implementation's first hop;
- one intermediate module's public implementation authorization suffix;
- one hop span;
- the final owner; and
- the selected `ImplId` while retaining a valid route.

For each mutation, assert `evidence.validation.*` before Core synthesis. Add a
structural test that linked groups retain public authorization entries but do
not retain another module's source body or duplicate implementation methods.

Run:

```text
cargo test --locked --test interface_validation rejects_a_forged_reexport_authorization_hop -- --exact
```

Expected RED: linked groups discard summaries and the validator understands
only local or defining-direct-dependency routes.

### Step 2: Retain lightweight public authorization entries

Add a compact checked record such as:

```rust
pub struct PublicImplementationAuthorization {
    id: ImplId,
    route: ImplementationAuthorization,
}
```

Build it only after `ExportSummary::freeze` succeeds. Move it through
`CheckedModule::into_group`; do not retain the complete cloned export summary in
the linked program. Include its exact storage and hop counts in the existing
link and validation budgets.

### Step 3: Validate every path iteratively

Before validating occurrence selections, validate every public authorization:

1. an empty path names a public local implementation and its defining binders;
2. each nonempty hop starts at the current group and matches one exact
   `DirectDependencyRoute`;
3. the dependency group publishes the same `ImplId` with the exact remaining
   suffix;
4. the final group owns the implementation fact and public source body; and
5. no malformed, disconnected, repeated, or over-budget path reaches Core.

Then validate each `AvailableImplementation` by matching its path to the first
dependency's public authorization and use the same predicate in
`implementation_is_available`. Validation authenticates; it never reselects.

Rerun every tampering test. Expected: GREEN.

### Step 4: Prove unchanged lowering

Extend the facade test to synthesize and independently validate Core. Locate
the implementation-method binder by original identity and assert both direct
and facade calls lower to ordinary binder, type-application, and term-
application structure. Assert the Core dialect and evaluator have no new
interface, route, dictionary, module, or registry node.

Run:

```text
cargo test --locked --test library_imports facade_selection_lowers_through_the_original_core_binder -- --exact
cargo test --locked --test interface_validation
cargo test --locked --test interfaces
```

Expected: GREEN.

### Step 5: Review linked validation and commit

Run `superpowers:requesting-code-review` for the summary-to-link authorization
boundary. Resolve every actionable finding before committing.

```text
cargo check --locked --all-targets
cargo fmt --check
git add src/resolved.rs src/elaborate.rs src/evidence_validation.rs src/evidence_audit.rs tests/interface_validation.rs tests/interface_selection.rs tests/library_imports.rs tests/interfaces.rs
git commit --no-gpg-sign -m "feat: validate re-exported implementation evidence"
```

## Task 7: Close resources, diagnostics, and migration evidence

**Files:**

- Modify: `src/diagnostic.rs` only if an existing structured reason needs new
  route labels; do not add a renderer-owned semantic reason
- Modify: `src/driver.rs` only for graph-wide accounting or test injection
- Modify: `tests/library_imports.rs`
- Modify: `tests/interface_resources.rs`
- Modify: `tests/interface_diagnostics.rs`
- Modify: `tests/module_cli.rs`
- Modify: `tests/architecture.rs`
- Modify: every migrated integration fixture identified in Task 3

### Step 1: Add exact resource RED tests

Cover separately and cumulatively:

- a wide implementation selector over a summary;
- many public name and implementation re-export entries;
- path prepending and duplicate-route disposal;
- link retention of lightweight public entries;
- validation of a deep re-export path; and
- destruction of admitted and rejected deep paths on a small host stack.

For each boundary, first run one exact-limit and one one-unit-short test. Assert
the existing `internal.resource.constraint-work` or type-work owner and exact
stage. Do not use exhaustion as a semantic cycle check.

Run:

```text
cargo test --locked --test interface_resources
```

Expected: RED before accounting is complete, then GREEN.

### Step 2: Complete deterministic diagnostic evidence

Assert exact structured labels for unavailable selector, name conflict,
unsatisfied name-only use, overlap through two facades, and a failing selected
implementation prerequisite. Labels identify the source occurrence, original
interface and implementation declarations, and every hop of the chosen route
in deterministic order. Private or unselected implementation metadata remains
absent.

Run:

```text
cargo test --locked --test interface_diagnostics
cargo test --locked --test module_cli
```

Expected: GREEN.

### Step 3: Audit migration completeness

Run:

```text
rg -n 'pub impl|public implementation|direct dependency|direct import|not re-export|transitive implementation' tests spec docs
```

Inspect every result. Add selectors to positive current-Ash programs. Preserve
old automatic and direct-only statements only in artifacts explicitly labeled
as retained `modular-ash` evidence or current-behavior text inside CP-0008.
Retain at least one executable negative test proving a qualified or targeted
name import alone does not admit evidence.

### Step 4: Run the whole implementation boundary

```text
cargo test --locked --workspace --all-targets --all-features
cargo clippy --locked --workspace --all-targets --all-features -- -D warnings
cargo fmt --check
```

Expected: GREEN. Record the new exact test inventory in TASK-0015 progress.

### Step 5: Review resource evidence and commit

Review graph-wide budget lifetime, stable label order, absence of unbounded
recursion, complete migration, and no Core/evaluator dispatch change.

```text
git add src tests
git commit --no-gpg-sign -m "test: close explicit library import evidence"
```

## Task 8: Update normative and explanatory documentation

**Files:**

- Modify: `spec/README.md`
- Modify: `spec/syntax.md`
- Modify: `spec/name-resolution.md`
- Modify: `spec/static-semantics.md`
- Modify: `spec/elaboration.md`
- Modify: `spec/dynamic-semantics.md` only if wording must clarify unchanged
  erasure; do not add a dynamic rule
- Modify: `docs/tools/ash.md`
- Modify: `docs/design/DN-0025-library-and-package-milestones.md`
- Modify: `docs/design/README.md`
- Create: `docs/design/lib-ash/imports-evidence.md`
- Modify: `docs/trajectory.md`
- Modify: `tests/spec_examples.rs`
- Modify: `docs/tasks/TASK-0015-implement-explicit-implementation-imports-and-reexports.md`

### Step 1: Make specification examples executable first

Update or add `tests/spec_examples.rs` witnesses for:

- name-only imports without implementation availability;
- implementation-only selection beside a qualified import;
- targeted public name re-export; and
- the complete three-module implementation facade.

Run each exact test against the pending prose/example change. Expected: GREEN
because Tasks 2 through 7 already implement the accepted semantics.

### Step 2: Update normative truth

Apply the documentation policy and writing guide. Update the complete grammar,
namespace and summary rules, effective implementation environment, selection,
module checking, failure ownership, linking, and evidence validation. State
that public imports are targeted, selector channels are independent, routes are
transitive and identity-preserving, and Core lowering is unchanged.

Use `ebnf` for grammar and `sequent` only for actual judgments. Do not present
later kinds, associated outputs, defaults, packages, or artifacts as current.

### Step 3: Record retained evidence

Create `docs/design/lib-ash/imports-evidence.md` as an informative report. It
must record:

- current and proposed authority boundaries;
- selector and facade corpus results;
- identity and summary facts;
- overlap, privacy, opacity, and deterministic diagnostics;
- exact resource and small-stack results;
- linked tampering rejection;
- Core and runtime observations;
- migration inventory;
- changed production and maintenance sites; and
- exclusions and remaining `lib-ash` pressure.

Link it from the design index, DN-0025, trajectory, and TASK-0015. Do not edit
the retained Modular Ash closure reports to pretend the new behavior existed at
that checkpoint.

### Step 4: Update tool and project state

Update `docs/tools/ash.md` for source failures and route labels without making
tool prose normative. Set trajectory maturity to an implementation checkpoint
only after the evidence passes. Record exact commands, inventory, and remaining
review in TASK-0015.

### Step 5: Verify documentation and commit

```text
cargo test --locked --test spec_examples
markdownlint --disable MD013 -- README.md spec docs
git diff --check
cargo xtask verify
```

Expected: PASS. Manually inspect every changed relative link, formal-notation
fence, authority label, source example, and retained historical statement.

```text
git add spec docs tests/spec_examples.rs
git commit --no-gpg-sign -m "docs: specify explicit library imports"
```

## Task 9: Review and retain the first `lib-ash` checkpoint

**Files:**

- Modify: any implementation, test, specification, or evidence file required
  by actionable review findings
- Modify: `docs/design/lib-ash/imports-evidence.md`
- Modify: `docs/design/DN-0025-library-and-package-milestones.md`
- Modify: `docs/design/README.md`
- Modify: `docs/trajectory.md`
- Remove after the retained checkpoint: `docs/proposals/CP-0008-explicit-implementation-imports-and-reexports.md`
- Remove after the retained checkpoint: `docs/tasks/TASK-0015-implement-explicit-implementation-imports-and-reexports.md`
- Remove after the retained checkpoint: `docs/plans/2026-08-25-explicit-implementation-imports-and-reexports.md`
- Modify after cleanup: `docs/proposals/README.md`
- Modify after cleanup: `docs/tasks/README.md`

### Step 1: Run independent reviews

Use `superpowers:requesting-code-review` for three separate passes:

1. CP-0008 semantic and specification agreement;
2. parser, resolver, summary, route, validation, resource, and Core quality;
3. evidence, migration, links, authority boundaries, and intentional
   exclusions.

Resolve every actionable finding with a focused failing test where behavior
changes. Repeat the affected review until it approves the exact state.

### Step 2: Run final verification

Use `superpowers:verification-before-completion`, then run:

```text
cargo fmt --check
cargo check --locked --workspace --all-targets --all-features
cargo test --locked --workspace --all-targets --all-features
cargo clippy --locked --workspace --all-targets --all-features -- -D warnings
cargo test --locked --workspace --all-targets --all-features -- --list
cargo xtask verify
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Expected: every command passes. Record the exact test inventory and review
outcomes in the retained evidence report.

### Step 3: Retain the product evidence

Update DN-0025 and the trajectory to mark only the explicit import/re-export
increment complete. Keep later `lib-ash` increments exploratory and preserve
decreasing planning detail. The milestone itself remains open and receives no
`lib-ash` tag at this checkpoint.

Commit review corrections and retained evidence unsigned:

```text
git add src tests spec docs
git commit --no-gpg-sign -m "docs: retain explicit library import evidence"
```

### Step 4: Remove transition artifacts

After the implementation, tests, specification, evidence, reviews, and final
verification are retained in one product checkpoint, remove CP-0008,
TASK-0015, and this temporary plan. Update proposal and task indexes so they
again report no active entries. Remove or replace every intermediate link to
those artifacts from DN-0025, the trajectory, and the retained evidence report;
historical unlinked IDs may remain. Git retains the transition history.

Run:

```text
markdownlint --disable MD013 -- README.md spec docs
git diff --check
cargo xtask verify
```

Expected: PASS with no stale link to a removed current-tree artifact.

Commit unsigned:

```text
git add -A docs
git commit --no-gpg-sign -m "docs: close explicit library import increment"
```

Do not tag `lib-ash`; the later kind, method-polymorphism, determination,
default, and final simplification increments remain unfinished.
