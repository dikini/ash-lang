# Method-Local Type Parameters Implementation Plan

> **For Codex:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to implement this plan task by task,
> preserving every RED witness and review checkpoint.

This temporary execution plan is owned by
[TASK-0017](../tasks/TASK-0017-implement-method-local-type-parameters.md) and
only organizes implementation. It does not define Ash semantics. The current
`spec/` remains current Ash while accepted
[CP-0010](../proposals/CP-0010-method-local-type-parameters.md) alone authorizes
the prospective transition.

**Goal:** Implement accepted CP-0010 as explicit fixed-kinded method-local type
parameters with authenticated compiler-generated polymorphic evidence while
ordinary source values remain rank 1.

**Architecture:** Extend the existing method path from parser through checked
linking rather than creating a second pipeline. Retain canonical method binder
records separately from the method monotype; instantiate those binders during
ordinary checking; publish inference-free occurrence arguments atomically with
the selected evidence; and carry one private validated relationship into Core.
Reuse existing `Forall`, type abstraction, type application, function, and
application nodes for abstract evidence and concrete adapters. Independent
validation owns the only nested-scheme exception, transformations preserve or
rebuild it, and every new fact erases before the unchanged evaluator.

**Tech stack:** Rust 2024, the existing event-producing concrete-tree parser,
resolved-surface and fixed-kind boundaries, bidirectional elaborator,
body-free summaries, interface evidence selector and linked validator, typed
pure Core, explicit evaluator machine, Cargo integration tests, and Markdown
specification.

---

Implementation follows `superpowers:test-driven-development`, `rust-skills`,
`superpowers:systematic-debugging` for unexpected results,
`superpowers:subagent-driven-development`,
`superpowers:requesting-code-review`, and
`superpowers:verification-before-completion`. Use one implementation agent at a
time because checkpoints share production state. Parallelize only independent
read-only audits. Report every agent's model and reasoning level.

For each production checkpoint:

1. assign a fresh implementer the complete checkpoint text;
2. observe and record every named RED before production edits;
3. implement the minimum coherent behavior and run the focused GREEN commands;
4. run an independent CP-0010/specification-compliance review and correct every
   actionable finding;
5. run an independent Rust/resource-quality review and correct every actionable
   finding;
6. repeat affected review and focused verification, mark every intended new
   path with `git add -N`, inspect `git status --short` for unexpected paths,
   then run `git diff --check`; and
7. create the named unsigned commit with
   `git -c commit.gpgsign=false commit`.

Keep `spec/` authoritative and unchanged through Checkpoint 6. Do not merge or
push the branch, tag a milestone, remove the branch, or remove the worktree.

## Budget and stop rules

The fixed allocation is `4 + 10 + 12 + 12 + 14 + 10 + 8 = 70` notional work
units. Record reserved and remaining units at each checkpoint boundary.
Starting any checkpoint, including a documentation checkpoint, reserves its
full allocation through corrections and review; that checkpoint may finish
inside the reserved units. Do not borrow, redistribute, or consume the final
closure allocation early. Never start unallocated work or work that would
require more than the seven reserved checkpoints.

Stop rather than improvise if a checkpoint cannot reach GREEN plus both reviews
inside its allocation, if any additional work would exceed 70, or if
implementation requires:

- semantics absent from or inconsistent with CP-0010;
- a persistent Core representation decision outside AD-0007's replaceable
  private-storage boundary;
- a production resource-limit increase;
- source higher-rank values, method determination or improvement, polymorphic
  recursion, source-visible implementation-method binders, dependency bodies,
  or method-local arguments that influence selection;
- a new Core interface node, runtime dictionary or interface state, or an
  evaluator change.

## Checkpoint 1: Authorize and baseline the increment — 4 units

**Files:**

- Create: `docs/tasks/TASK-0017-implement-method-local-type-parameters.md`
- Create: `docs/plans/2026-08-28-method-local-type-parameters.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/trajectory.md`
- Confirm: `docs/proposals/CP-0010-method-local-type-parameters.md`

### Step 1: Confirm transition authority

Confirm CP-0010 is `accepted`, the current specification still describes the
predecessor, and `main` contains no implementation of this transition.

### Step 2: Record the clean isolated baseline

Use:

```text
/home/dikini/Projects/ash-lang/.worktree/cp0010-method-local-type-parameters
```

Run:

```text
cargo build --all-targets --all-features
cargo test --all-targets --all-features
cargo xtask verify
```

Expected: PASS at `e4fbc54` before production changes.

### Step 3: Validate authorization artifacts

Run:

```text
git add -N docs/tasks/TASK-0017-implement-method-local-type-parameters.md docs/plans/2026-08-28-method-local-type-parameters.md
markdownlint --disable MD013 -- docs/tasks docs/plans docs/proposals docs/trajectory.md
git diff --check
```

Expected: PASS. Check every new relative link and confirm that no artifact
claims CP-0010 is current Ash.

### Step 4: Review and commit authorization

Run independent semantic/authority and artifact-quality reviews. Correct every
finding and repeat affected checks. Commit:

```text
git add docs/tasks/TASK-0017-implement-method-local-type-parameters.md docs/plans/2026-08-28-method-local-type-parameters.md docs/tasks/README.md docs/trajectory.md
git -c commit.gpgsign=false commit -m "docs: authorize method parameter implementation"
```

## Checkpoint 2: Syntax, resolution, identity, and kinds — 10 units

**Files:**

- Modify: `src/parser/grammar.rs`
- Modify: `src/parser/project.rs`
- Modify: `src/surface.rs`
- Modify: `src/resolve.rs`
- Modify: `src/resolved.rs`
- Modify: `src/kind.rs`
- Modify: `tests/interfaces_syntax.rs`
- Modify: `tests/resolution.rs`
- Modify: `tests/kinds.rs`
- Modify: `tests/diagnostics.rs`

### Step 1: Write and witness the syntax RED

Add `projects_method_local_type_parameters_and_kinds` for:

```ash
interface Functor<F : Type -> Type> {
    map<A, B : Type> : (A -> B, F<A>) -> F<B>
}
```

Assert token completeness, binder-list span, binder and kind spans, written
order, and the absent-versus-present distinction. Run:

```text
cargo test --locked --test interfaces_syntax projects_method_local_type_parameters_and_kinds -- --exact
```

Expected RED: `<` after the method name is rejected as a missing colon and
`SurfaceInterfaceMethod` has no binder list.

### Step 2: Own malformed syntax and recovery

Add empty-list, duplicate-separator, missing-kind, missing-`>`, and following
valid-method cases. Assert parser ownership, exact causal spans, balanced
events, token-complete next-line recovery, and refusal to project a
recovery-bearing tree. Reuse the existing type-parameter production and its
owner-sensitive recovery.

### Step 3: Write and witness binder-policy RED tests

Extend the predecessor resolution and kind seams and add
`method_type_binders_are_complete_ordered_and_declaration_ordered`. Cover a
binder that duplicates the interface parameter, a duplicate local binder, an
unused listed binder, an unlisted free name under a present list, written
order, fixed omitted `Type`, higher-kinded binders, and module-wide declaration
identity order.

Run:

```text
cargo test --locked --test resolution method_type_binders_are_complete_ordered_and_declaration_ordered -- --exact
```

Expected RED: resolution treats every method-local name as a rejection
candidate and cannot distinguish a present complete list.

### Step 4: Implement the minimum front-end behavior

Retain an optional ordered method list on the surface method. Allocate
canonical `ResolvedTypeVariable` records in the existing cross-family
declaration preparation order. Scope the interface parameter plus listed
binders over that signature only. Reuse the existing duplicate, unused, and
unknown-type reasons and fixed-kind engine.

Keep absent-list candidates distinct. An absent list with another free name
must retain `interface.method-parameter`, including its precedence over the
candidate's invalid kind application. A present list proceeds through fixed
kind checking, then the interface-parameter and outer-`Function` rules.

### Step 5: Verify, review, and commit front-end behavior

Run:

```text
cargo test --locked --test interfaces_syntax
cargo test --locked --test resolution
cargo test --locked --test kinds
cargo test --locked --test diagnostics
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

After both reviews and corrections, commit:

```text
git add src/parser/grammar.rs src/parser/project.rs src/surface.rs src/resolve.rs src/resolved.rs src/kind.rs tests/interfaces_syntax.rs tests/resolution.rs tests/kinds.rs tests/diagnostics.rs
git -c commit.gpgsign=false commit -m "feat: retain method-local type parameters"
```

Record cumulative use as 14/70.

## Checkpoint 3: Checked schemes and occurrence inference — 12 units

**Files:**

- Modify: `src/interface.rs`
- Modify: `src/evidence.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/resolved.rs`
- Modify: `src/types.rs`
- Modify: `tests/interfaces.rs`
- Modify: `tests/implementations.rs`
- Modify: `tests/interface_selection.rs`
- Modify: `tests/polymorphism.rs`
- Modify: `tests/architecture.rs`

### Step 1: Write and witness method-scheme RED tests

Turn the current rejected candidate case into an absent-list compatibility test
and add `polymorphic_method_occurrence_instantiates_all_binders_once`. Assert
one interface obligation, ordered fresh method arguments, and two distinct
instantiations of one method scheme.

Run:

```text
cargo test --locked --test interfaces polymorphic_method_occurrence_instantiates_all_binders_once -- --exact
```

Expected RED: interface checking rejects nonempty method parameters and method
occurrence synthesis quantifies only the interface parameter.

Add separate ambiguity cases: an unresolved interface argument remains
`constraint.ambiguous`; an otherwise unresolved method argument is
`type.ambiguous`; a case requiring higher-order matching remains rejected.

### Step 2: Retain schemes and publish occurrence evidence atomically

Retain checked method binder records separately from the monotype body. Extend
the selector's method entry with that scheme. Instantiate the interface and
method binders at their fixed kinds, but create exactly one evidence obligation.

Selection may close before whole-module inference. Keep the choice and ordered
method arguments in private pending state. Only after the complete inference
substitution closes may checking zonk them and fill the occurrence's one-shot
slot with interface argument, method arguments, and selection. Publish nothing
on ambiguity or an earlier module failure.

### Step 3: Write and witness implementation-rigidity RED tests

Extend the checked implementation scheme seam with
`implementation_method_scheme_orders_head_then_method_parameters`. Assert
explicit head-then-method order and preserve the distinction between both
sequences. Add direct-recursion evidence: the current implementation method
reuses its rigid method arguments; another occurrence instantiates normally;
polymorphic recursive self-use is rejected.

Add focused implementation-membership and exact-current evidence cases with a
polymorphic method. Authenticate the exact method scheme, rigid local arguments,
current implementation identity, and resulting checked type without letting
method-local arguments enter candidate selection.

### Step 4: Implement rigid method checking

Check each implementation body once under rigid implementation-head and method
binders. Append method binders after head binders in the checked scheme, retain
their boundary explicitly, and leave prerequisite ordering unchanged. Do not
put the interface method's source spellings in the implementation body scope.
Do not change membership, overlap, orphan ownership, termination, prerequisite,
exact-current, concrete selection, or candidate choice.

### Step 5: Verify, review, and commit checked schemes

Run:

```text
cargo test --locked --test interfaces
cargo test --locked --test implementations
cargo test --locked --test interface_selection
cargo test --locked --test polymorphism
cargo test --locked --test architecture
cargo test --locked --lib -- interface
cargo test --locked --lib -- elaborate
cargo check --locked --all-targets
git diff --check
```

After both reviews and corrections, commit:

```text
git add src/interface.rs src/evidence.rs src/elaborate.rs src/resolved.rs src/types.rs tests/interfaces.rs tests/implementations.rs tests/interface_selection.rs tests/polymorphism.rs tests/architecture.rs
git -c commit.gpgsign=false commit -m "feat: check polymorphic interface methods"
```

Record cumulative use as 26/70.

## Checkpoint 4: Summary, import, and linked authentication — 12 units

**Files:**

- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify: `src/resolve/module_tests.rs`
- Modify: `src/evidence.rs`
- Modify: `src/evidence_audit.rs`
- Modify: `src/evidence_validation.rs`
- Modify: `src/driver.rs`
- Modify: `tests/interface_generic_summary.rs`
- Modify: `tests/interface_modules.rs`
- Modify: `tests/interface_identity_diamond.rs`
- Modify: `tests/library_imports.rs`
- Modify: `tests/interface_validation.rs`
- Modify: `tests/module_elaboration.rs`
- Modify: `tests/architecture.rs`

### Step 1: Write and witness detached-summary RED tests

Add `detached_summary_preserves_complete_method_scheme`: check a public
polymorphic interface, retain only its `ExportSummary`, discard bodies, and
check a consumer solely from the summary.

Run:

```text
cargo test --locked --test interface_generic_summary detached_summary_preserves_complete_method_scheme -- --exact
```

Expected RED: checked interface methods retain no canonical method-binder
records for the detached summary.

Add qualified and targeted method imports, explicit implementation imports,
facades, diamonds, private and public interfaces, and hidden or opaque kind
closure.

### Step 2: Write summary and linked tampering RED matrices

Extend private summary mutations for missing, extra, duplicate, reordered,
wrong-kind, wrong-owner, wrong-origin, and wrong-spelling binders; a free or
escaped method binder; and a nested scheme forged into each non-method fact.

Extend linked mutations for occurrence argument count, order, kind, and checked
type; wrong `MethodId` or `ImplMethodId`; wrong combined implementation
parameter order; selected type mismatch; wrong adapter head, method,
prerequisite, or argument order; and a selection whose checked type differs
from its exact method-scheme instantiation.

### Step 3: Implement body-free and linked authentication

Carry canonical binder records and the monotype body through every public and
hidden body-free mirror. Authenticate the complete binder set, order, kinds,
spelling, owner, origin, body scope, and method identity before dependent
checking.

After inference closure, retain exact occurrence method arguments. Linked
validation rederives their relationship to the defining method scheme and the
selected evidence, authenticates the implementation method's combined binder
relationship, and produces the only capability that may authorize polymorphic
Core evidence. It does not reselect evidence or lower Core.

Charge graph facts to the constraint ledger and retained binder, kind, and type
copies to type work before publication.

### Step 4: Verify, review, and commit linked authentication

Run:

```text
cargo test --locked --test interface_generic_summary
cargo test --locked --test interface_modules
cargo test --locked --test interface_identity_diamond
cargo test --locked --test library_imports
cargo test --locked --test interface_validation
cargo test --locked --test module_elaboration
cargo test --locked --test architecture
cargo test --locked --lib -- resolved
cargo test --locked --lib -- evidence_validation
git diff --check
```

After both reviews and corrections, commit:

```text
git add src/resolved.rs src/resolve.rs src/resolve/module_tests.rs src/evidence.rs src/evidence_audit.rs src/evidence_validation.rs src/driver.rs tests/interface_generic_summary.rs tests/interface_modules.rs tests/interface_identity_diamond.rs tests/library_imports.rs tests/interface_validation.rs tests/module_elaboration.rs tests/architecture.rs
git -c commit.gpgsign=false commit -m "feat: authenticate method schemes across modules"
```

Record cumulative use as 38/70.

## Checkpoint 5: Authenticated polymorphic Core evidence — 14 units

**Files:**

- Modify: `src/resolved.rs`
- Modify: `src/evidence_validation.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/type_ops.rs`
- Modify: `src/core/transform.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/driver.rs`
- Modify: `tests/core_validation.rs`
- Modify: `tests/interfaces.rs`
- Modify: `tests/polymorphism.rs`
- Modify: `tests/architecture.rs`

Do not modify `src/eval/machine.rs`. Runtime tests must prove it remains
unchanged.

### Step 1: Write and witness abstract and concrete lowering RED tests

Add `abstract_polymorphic_method_evidence_instantiates_at_retained_arguments`.
It must find one nested scheme only in the generated evidence domain and
type-apply the evidence binder before term application.

Add `concrete_method_evidence_uses_one_generated_adapter` for a generic
implementation with prerequisites. Assert exact head-then-method type arguments
and prerequisite application order without body copying or specialization.

Run:

```text
cargo test --locked --test core_validation concrete_method_evidence_uses_one_generated_adapter -- --exact
```

Expected RED: evidence domains remain monomorphic and concrete selection
exposes the implementation method directly.

### Step 2: Establish private Core authentication

Carry one minimal immutable method-evidence relation beside the validated
linked/Core inputs. Relate the constrained definition, requirement and method
position, `MethodId`, interface argument, canonical method scheme, and, for an
adapter, `ImplMethodId` and complete instantiation relationship. Do not extend
AD-0009's global owner rows and do not place authority in unchecked Core nodes.

### Step 3: Lower polymorphic evidence using existing Core forms

Derive a nested method scheme only for a generated polymorphic evidence domain.
Type-apply abstract evidence with the occurrence's retained method arguments.
For concrete or exact-current evidence, generate one type abstraction over
fresh method binders whose body completely type-applies the existing
implementation method with head arguments followed by method arguments, then
applies prerequisite evidence in declaration order.

### Step 4: Validate and transform independently

Independent validation derives the expected scheme from canonical records,
requires each nested scheme at one exact evidence position, validates adapter
scope and complete application, and consumes every relation once. Canonical
method facts remain identity-exact. Only an authenticated generated adapter may
use one capture-free, order- and kind-preserving alpha-renaming.

Add one positive authenticated forwarding case in which an evidence variable
flows to the matching generated evidence domain of another constrained
definition, then reject forwarding to every wrong method, owner, requirement,
position, or scheme.

Identity and literal-folding transforms preserve or rebuild the relationship,
type abstractions, type applications, binder scope, and provenance, then pass
fresh validation.

### Step 5: Complete the Core tampering matrix

Reject a nested scheme in every ordinary slot; missing, duplicate, unconsumed,
wrong-owner, wrong-position, wrong-order, wrong-kind, or wrong-method authority;
wrong forwarding; capture, escape, shadowing, mismatched adapter schemes, wrong
implementation binders, partial or reordered type applications, and wrong
prerequisite application. Repeat malformed cases after both transforms. Accept
one complete capture-free generated adapter renaming and reject a renamed
canonical method fact.

Update the architecture inventory so the bounded private validation authority
is permitted in Core while interface nodes, dictionaries, dispatch, and every
runtime evidence state remain forbidden.

### Step 6: Verify, review, and commit Core authentication

Run:

```text
cargo test --locked --test core_validation
cargo test --locked --test interfaces
cargo test --locked --test polymorphism
cargo test --locked --test architecture
cargo test --locked --lib -- core
cargo check --locked --all-targets
git diff --check
```

After both reviews and corrections, commit:

```text
git add src/resolved.rs src/evidence_validation.rs src/elaborate.rs src/core/dialect.rs src/core/type_ops.rs src/core/transform.rs src/core/validate.rs src/driver.rs tests/core_validation.rs tests/interfaces.rs tests/polymorphism.rs tests/architecture.rs
git -c commit.gpgsign=false commit -m "feat: lower authenticated polymorphic method evidence"
```

Record cumulative use as 52/70.

## Checkpoint 6: Product evidence, diagnostics, migration, and resources — 10 units

**Files:**

- Create: `tests/method_parameter_resources.rs`
- Create: `tests/fixtures/method-parameters/linked-product/interface.ash`
- Create: `tests/fixtures/method-parameters/linked-product/implementation.ash`
- Create: `tests/fixtures/method-parameters/linked-product/entry.ash`
- Modify: `tests/interfaces.rs`
- Modify: `tests/polymorphism.rs`
- Modify: `tests/interface_resources.rs`
- Modify: `tests/diagnostics.rs`
- Modify: `tests/source_diagnostics.rs`
- Modify: `tests/module_cli.rs`
- Modify: `tests/corpus.rs`
- Modify: `tests/architecture.rs`
- Modify owning production files only when a witnessed resource or teardown RED
  exposes a gap.

### Step 1: Write the complete linked product RED

The fixture uses one higher-kinded interface with `map<A, B>`, calls it at
unrelated `Int` and `Bool` instantiations inside one separately checked
constrained global, supplies a concrete generic implementation, and selects it
explicitly from the entry module.

Run:

```text
cargo test --locked --test interfaces linked_polymorphic_method_evidence_evaluates -- --exact
cargo test --locked --test method_parameter_resources
```

Expected RED: the complete product fixture, carrier inventory, and exact
accounting evidence are absent. A behavioral failure from an earlier checkpoint
returns to that checkpoint before this work continues.

### Step 2: Close behavior, exclusion, and diagnostic evidence

Retain complete library and CLI observations; both transformed programs with
fresh validation and equal evaluation; the exact erased evaluator trace; every
CP-listed unavailable higher-rank source route; absent-list predecessor
behavior; deliberate rejected-to-accepted migration; and exact typed reasons,
primary and related spans, causal labels, and failure precedence.

The runtime inventory must separately prove that polymorphic method evidence
adds no evaluator value, environment-entry class, frame, lookup, transition,
failure reason, or runtime interface state. The retained trace may contain only
the existing type-erasure, recursive-binding, variable, and strict-application
transitions.

### Step 3: Close carrier, resource, and disposal evidence

Inventory every new syntax, binder, scheme, occurrence, summary, linked,
adapter, Core-authentication, transformation, and teardown carrier. Derive
additive formulas from implemented fields. Prove exact success, one-short
atomic failure, retry, deep and wide accepted and rejected teardown on a
256 KiB stack. Do not change a production limit.

### Step 4: Verify, review, and commit product evidence

Mark the intended new product-evidence paths before the diff gate:

```text
git add -N tests/method_parameter_resources.rs tests/fixtures/method-parameters/linked-product/interface.ash tests/fixtures/method-parameters/linked-product/implementation.ash tests/fixtures/method-parameters/linked-product/entry.ash
```

Run:

```text
cargo test --locked --test method_parameter_resources
cargo test --locked --test interface_resources
cargo test --locked --test diagnostics
cargo test --locked --test source_diagnostics
cargo test --locked --test module_cli
cargo test --locked --test corpus
cargo test --locked --test interfaces
cargo test --locked --test polymorphism
cargo test --locked --test core_validation
cargo test --locked --workspace --all-targets --all-features
git diff --check
```

After both reviews and corrections, commit:

```text
git add src tests
git -c commit.gpgsign=false commit -m "test: close method parameter evidence"
```

Record cumulative use as 62/70.

## Checkpoint 7: Specification, retained evidence, reviews, and closure — 8 units

**Files:**

- Modify: `spec/syntax.md`
- Modify: `spec/name-resolution.md`
- Modify: `spec/static-semantics.md`
- Modify: `spec/elaboration.md`
- Modify: `spec/dynamic-semantics.md`
- Modify: `spec/README.md`
- Modify: `docs/tools/ash.md`
- Modify: `docs/design/DN-0025-library-and-package-milestones.md`
- Modify: `docs/design/README.md`
- Modify: `docs/trajectory.md`
- Create: `docs/design/lib-ash/method-parameters-evidence.md`
- Modify: `docs/tasks/TASK-0017-implement-method-local-type-parameters.md`
- Modify: `tests/spec_examples.rs`

### Step 1: Write executable specification RED tests

Add manifest entries and executable examples before normative edits. Run:

```text
cargo test --locked --test spec_examples
```

Expected RED: current normative documents do not yet contain the implemented
grammar, judgments, complete linked example, or exclusion boundary.

### Step 2: Reconcile implemented truth

Update normative wording only from retained Checkpoints 2 through 6. Use the
required formal fences and keep authority labels exact. Update the tool guide,
DN-0025, trajectory, and executable overview together.

Create `docs/design/lib-ash/method-parameters-evidence.md`. Record exact
checkpoints, production and maintenance sites, authentication relationships,
tampering matrix, resource formulas, stack results, migration, observations,
reviews, verification, and intentional exclusions.

Run focused documentation and executable tests, then commit:

```text
git add spec docs tests/spec_examples.rs
git -c commit.gpgsign=false commit -m "docs: specify method-local type parameters"
```

### Step 3: Run final independent reviews

Run three fresh reviews sequentially:

1. semantic and specification;
2. implementation, Core, and resources;
3. evidence, migration, lifecycle, and authority.

Correct every actionable finding and repeat every affected review.

### Step 4: Run and inspect the complete gate

Mark the new retained evidence report before the diff gate:

```text
git add -N docs/design/lib-ash/method-parameters-evidence.md
```

Read complete output from:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --workspace --all-targets --all-features
cargo clippy --locked --workspace --all-targets --all-features -- -D warnings
cargo test --locked --workspace --all-targets --all-features -- --list
cargo xtask verify
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Check every changed relative link, authority label, formal fence, documented
command, and current-versus-proposed claim. Record counts and review verdicts,
then commit the retained evidence:

```text
git add docs tests
git -c commit.gpgsign=false commit -m "docs: retain method parameter evidence"
```

### Step 5: Close transition artifacts

Only after the retention commit exists and the worktree is clean, remove
CP-0010, TASK-0017, this execution plan, their index entries, and stale links.
Retain implementation, tests, specification, and
`docs/design/lib-ash/method-parameters-evidence.md`. Re-run Markdown lint,
relative-link checks, `cargo xtask verify`, and `git diff --check`.

Commit:

```text
git add -A docs
git -c commit.gpgsign=false commit -m "docs: close method parameter increment"
```

Record cumulative use as 70/70. Do not merge, push, tag, delete the branch, or
remove the worktree without explicit user approval.
