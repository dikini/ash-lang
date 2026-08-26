# Explicit Kinds and Higher-Kinded Parameters Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use `superpowers:executing-plans` to
> implement this plan task by task, preserving every RED witness and review
> checkpoint.

**Goal:** Implement accepted CP-0009 as explicit monomorphic kinds,
higher-kinded declaration parameters, canonical unary semantic type
application, and independently validated kinded Core, the second bounded
`lib-ash` increment.

**Architecture:** Preserve n-ary named applications in the CST and surface tree,
then fold them into one unary resolved `Type::Application` tree. Assign each
resolved declaration binder and transient inference variable one fixed kind;
derive local nominal kinds before checking declaration types; check interface
arguments against their selected parameter kinds; retain kinded body-free facts
through linking; and independently rederive kind relationships in Core. Keep
schemes outer rank-1, Core expression instantiation simultaneous and n-ary, and
all kind and type operations erased before the unchanged evaluator machine.

**Tech stack:** Rust 2024, the existing event-producing concrete-tree parser,
resolved-surface boundary, bidirectional elaborator, checked body-free export
summaries, interface evidence selector and linked validator, typed pure Core,
explicit evaluator machine, Cargo integration tests, and Markdown
specification.

---

Implementation follows `superpowers:test-driven-development`, `rust-skills`,
`superpowers:systematic-debugging` for unexpected results,
`superpowers:subagent-driven-development`,
`superpowers:requesting-code-review`, and
`superpowers:verification-before-completion`. Use one implementation agent at a
time because tasks share production state; parallelize only independent
read-only audits. Report every agent's assigned model and reasoning level.

For each production task:

1. assign a fresh implementer the complete task text;
2. observe and record the named RED failure before production edits;
3. implement the minimum coherent behavior and run the focused GREEN commands;
4. run an independent CP-0009/specification-compliance review and correct all
   findings;
5. run an independent Rust and resource-quality review and correct all
   findings;
6. rerun focused verification and `git diff --check`; and
7. create the named unsigned commit with
   `git -c commit.gpgsign=false commit`.

Keep the current `spec/` authoritative until Task 12 lands the implemented,
tested normative delta. Do not merge this branch into `main` and do not create
a milestone tag.

## Task 1: Authorize and baseline the increment

**Files:**

- Create: `docs/tasks/TASK-0016-implement-explicit-kinds-and-higher-kinded-parameters.md`
- Create: `docs/plans/2026-08-26-explicit-kinds-and-higher-kinded-parameters.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/proposals/CP-0009-explicit-kinds-and-higher-kinded-parameters.md`
- Modify: `docs/trajectory.md`

### Step 1: Confirm transition authority

Confirm CP-0009 is `accepted`, names `a1647ff` as its semantic base,
and records the predecessor integration state. At authorization,
`main@4f0541d` did not contain the predecessor; `main` now equals the
predecessor checkpoint `a1647ff`. Confirm the current specification does not
yet contain the explicit-kinds transition.

### Step 2: Record the clean baseline

The dedicated worktree is:

```text
/home/dikini/Projects/ash-lang/.worktrees/lib-ash-kinds
```

Record the already observed clean baseline:

```text
cargo build --locked
cargo xtask verify
```

Expected: PASS at the `a1647ff` product base before production changes.

### Step 3: Validate authorization artifacts

Run:

```text
markdownlint --disable MD013 -- docs/tasks docs/plans docs/proposals docs/trajectory.md
git diff --check
```

Expected: PASS. Check every new relative link and confirm no artifact claims
the proposal is current Ash.

### Step 4: Commit

```text
git add docs/tasks/TASK-0016-implement-explicit-kinds-and-higher-kinded-parameters.md docs/plans/2026-08-26-explicit-kinds-and-higher-kinded-parameters.md docs/tasks/README.md docs/proposals/CP-0009-explicit-kinds-and-higher-kinded-parameters.md docs/trajectory.md
git -c commit.gpgsign=false commit -m "docs: authorize explicit kinds implementation"
```

## Task 2: Retain kind and explicit-binder syntax

**Files:**

- Modify: `src/parser/mod.rs`
- Modify: `src/parser/grammar.rs`
- Modify: `src/parser/project.rs`
- Modify: `src/surface.rs`
- Modify: `src/resolve.rs`
- Create: `tests/kinds_syntax.rs`
- Modify: `tests/interfaces_syntax.rs`
- Modify: `tests/parser.rs`
- Modify: `tests/resolution.rs`

### Step 1: Write the contextual-kind RED tests

Add projection tests for:

```ash
type Wrapped<F : Type -> Type, A> = Wrapped(F<A>)

interface Functor<F : Type -> Type> {
    map : (Int -> Int, F<Int>) -> F<Int>
}

keep<F : Type -> Type, A> : F<A> -> F<A>
keep value = value

impl<F : Type -> Type> Functor<Wrapped<F>> {
    map (function, Wrapped(value)) = Wrapped(function(value))
}
```

Assert a `SurfaceKind` tree with right-associative arrows, a shared
`SurfaceTypeParameter { name, kind, span }`, exact binder order and spans, and
the exact single interface parameter. Also parse `type Type = Type` to prove
`Type` remains an ordinary uppercase identifier outside a kind annotation.

Run:

```text
cargo test --locked --test kinds_syntax projects_contextual_kinds_and_explicit_binders -- --exact
```

Expected RED: the parser rejects polymorphic global headers and surface binders
have no kind field.

### Step 2: Implement the minimum grammar and projection

Add contextual kind parsing without a lexer keyword. Reuse the existing arrow
token. Preserve one named application and its argument vector in `SurfaceType`.
Replace nominal and interface parameter names with the shared parameter record;
add optional binder lists to both global presentations and implementations.
Keep omitted lists distinguishable from present lists, and keep the interface
production exactly one parameter.

Mechanically adapt the resolver to read each parameter record's name while
preserving all predecessor kind-`Type`, implicit-binding, saturation, and
failure policy. Semantic binder and kind behavior remains Task 4 work.

Rerun the exact test. Expected: GREEN.

### Step 3: Own malformed syntax and recovery

Add RED cases for a missing kind after `:`, a missing arrow codomain, unclosed
kind grouping, duplicate separators, empty binder lists, an implementation list
in the wrong position, and a two-parameter interface. Assert parser-owned
reasons, expected forms, offending spans, balanced events, independent next-line
recovery, token completeness, and refusal to project a recovery-bearing tree.

Implement only parser policy. Projection remains ledger-free and bounded by the
admitted CST and structural-depth check.

### Step 4: Prove legacy syntax and complete parser behavior

Retain omitted nominal/interface kind annotations, globals and implementations
without explicit lists, both global presentations, all predecessor fixtures,
and contextual nominal `Type`.

Run:

```text
cargo test --locked --test kinds_syntax
cargo test --locked --test interfaces_syntax
cargo test --locked --test parser
cargo test --locked --test resolution
cargo fmt --check
cargo check --locked --all-targets
```

### Step 5: Review and commit syntax

Run the standard semantic and quality reviews, then commit:

```text
git add src/parser/mod.rs src/parser/grammar.rs src/parser/project.rs src/surface.rs src/resolve.rs tests/kinds_syntax.rs tests/interfaces_syntax.rs tests/parser.rs tests/resolution.rs
git -c commit.gpgsign=false commit -m "feat: retain explicit kind syntax"
```

## Task 3: Close the type-site inventory and canonicalize application

**Files:**

- Modify: `src/types.rs`
- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify: `src/interface.rs`
- Modify: `src/evidence.rs`
- Modify: `src/evidence_audit.rs`
- Modify: `src/evidence_validation.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/pattern.rs`
- Modify: `src/driver.rs`
- Modify: `src/core/data.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/transform.rs`
- Modify: `src/core/type_ops.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/eval/machine.rs`
- Modify: `tests/architecture.rs`
- Modify: `tests/polymorphism.rs`
- Modify: `tests/core_validation.rs`

### Step 1: Write the closed-inventory and unary-application RED tests

In `src/types.rs`, add a test that builds:

```text
Application(Application(Nominal(Result), Int), Bool)
```

and proves structural injectivity, left-spine `outer_nominal`, conventional
rendering, charged clone/equality/hash work, and iterative disposal. In
`tests/architecture.rs`, add an exhaustive `Type`-variant match and a manifest
of every type-bearing source, resolved, checked, summary, evidence, registry,
Core binder, Core pattern, and Core node site. The guard must require an owning
kind rule, required result or scheme rule, failure owner, budget, and disposal
owner for every entry.

Run:

```text
cargo test --locked --lib -- types::tests::canonical_application_is_unary_and_injective --exact
cargo test --locked --test architecture kind_inventory_is_closed -- --exact
```

Expected RED: `Type::Application` and the kind-site manifest do not exist.

### Step 2: Replace the saturated semantic representation mechanically

Replace `Type::AppliedNominal(NominalTypeId, Box<[Type]>)` with
`Type::Application(Box<Type>, Box<Type>)`. Fold every currently saturated
nominal application left while temporarily retaining predecessor saturation
and failure behavior. Add iterative `outer_nominal` and migrate every consumer,
including orphan and evaluator nominal-shape inspection.

Update clone, equality, hashing, display, substitution, unification, matching,
charging, provenance rebuilding, Core admission and transformations, and
disposal without recursion. `ResolvedTypeProvenanceNode::Application` retains
one function child, one argument child, the complete application span, and the
causal argument span per unary fold.

Do not change Core `TypeApplicationNode`: it remains simultaneous n-ary scheme
instantiation.

### Step 3: Prove representation uniqueness and preserved behavior

Add architecture assertions that production source contains no
`AppliedNominal` variant or second saturated semantic form. Prove bare,
partially assembled, and saturated left spines have stable outer ownership;
both application children participate in occurs, substitution, matching, and
strict-subterm traversal; both retained Core transforms preserve the tree; and
evaluation observations remain unchanged.

Publish exact application-node work formulas in unit tests and prove exact and
one-short clone, equality, hash, render, and retention boundaries plus deep
iterative disposal on a 256 KiB thread.

Run:

```text
cargo test --locked --lib -- types
cargo test --locked --test architecture
cargo test --locked --test polymorphism
cargo test --locked --test core_validation
cargo test --locked --workspace --all-targets --all-features
```

### Step 4: Review and commit canonical application

After the standard reviews:

```text
git add src tests/architecture.rs tests/polymorphism.rs tests/core_validation.rs
git -c commit.gpgsign=false commit -m "refactor: canonicalize semantic type application"
```

## Task 4: Assign declaration kinds and check resolved facts

**Files:**

- Create: `src/kind.rs`
- Modify: `src/lib.rs`
- Modify: `src/types.rs`
- Modify: `src/surface.rs`
- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify: `src/resolve/module_tests.rs`
- Modify: `src/interface.rs`
- Modify: `src/evidence.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/driver.rs`
- Modify: `src/core/validate.rs`
- Create: `tests/kinds.rs`
- Modify: `tests/resolution.rs`
- Modify: `tests/polymorphism.rs`
- Modify: `tests/implementations.rs`
- Modify: `tests/diagnostics.rs`
- Modify: `tests/cli.rs`
- Modify: `tests/core_validation.rs`
- Create: `tests/kind_modules.rs`
- Modify: `tests/interface_generic_summary.rs`
- Modify: `tests/module_elaboration_nominals.rs`

### Step 1: Write exact binder-policy RED tests

Cover global explicit lists as ordered bijections with free variables from the
value type and requirements, implementation lists as ordered bijections with
free head variables, prerequisite variables as a subset, nominal phantom
parameters, and unchanged method-local rejection. Assert list order becomes
scheme/head order. Add exact failures for duplicate, unused, unlisted,
prerequisite-only, and undetermined variables.

Requirement-only global variables count toward the explicit global bijection
and remain available for the existing determination check. An implementation
prerequisite-only variable is allocated as a candidate so the existing
`impl.prerequisite-variable` rule, not `resolve.unknown-type`, continues to own
that failure.

Run:

```text
cargo test --locked --test resolution explicit_kind_binders_are_complete_and_ordered -- --exact
```

Expected RED: surface binder lists are retained but resolution still allocates
implicit kind-`Type` candidates and has no unused explicit-binder reason.

### Step 2: Define canonical kinded binders and environments

Make `ResolvedTypeVariable` the defining source binder record by adding its
fixed `Kind`. Add ordered `(TypeVariableId, Kind)` records wherever checked
schemes and facts must cross a boundary. Derive each nominal constructor kind
from its ordered parameter records. If a cache is retained, validate equality
with that derivation.

Mechanically add `Kind::Type` to every predecessor `ResolvedTypeVariable`
fixture and constructor, including Core-validation fixtures. Inventory every
struct literal rather than leave a mixed representation.

Implement iterative, budgeted `Kind` clone, equality, hash, display, arrow
folding, and disposal in `src/types.rs`. Do not rely on recursive derives for
unbounded source depth.

### Step 3: Write total resolved-kinding RED tests

In `tests/kinds.rs`, cover primitives, declared variables, bare nominals,
applications, tuples, term functions, and every resolved value-type site. Add
positive partial constructors and higher-kinded interface arguments. Add exact
negative cases:

```ash
type Option<A> = None | Some(A)
bad : Option
bad = None
```

and a kind-domain mismatch. Assert `kind.expected-type`, `kind.not-applicable`,
or `kind.argument` with structured expected/found kinds and causal spans.

Expected RED: resolution still owns saturation/application rejection and no
total kind judgment exists.

### Step 4: Implement `DELTA`, `XI`, and `IOTA`

Allocate all local nominal and parameter identities first. Derive and freeze
all local nominal kinds in deterministic declaration order before checking any
payload, global, interface method, implementation head, or prerequisite.
Authenticate imported nominal and interface parameter kinds from body-free
facts. Fold surface named applications left with one provenance node per
argument and allow residual kinds when the owning rule admits them.

Before any consumer can use those imported environments, add the minimal
canonical kinded summary shape for nominal parameters, interface parameters,
and scheme binders and authenticate it without dependency bodies. Prove the
direct body-free import path here. Task 8 later closes hidden/evidence fields,
all route forms, exhaustive tampering, and linked authentication.

Implement the total `DELTA`/`OMEGA`/`XI` synthesis engine and the value-type and
`IOTA` interface-argument judgments from CP-0009. It includes `K-Inference`, but
resolved declaration checking always supplies empty `OMEGA`; Task 6 connects
the same engine to elaboration's transient registry. An omitted kind annotation
on any explicit binder means `Type`; every binder introduced by an implicit
global or implementation header is fixed at `Type`. No use infers an arrow kind
in this increment. This is a phase-dependent constraint that keeps explicit
kinds independently implementable and testable, not a permanent language
principle.

Expose kind failures as a distinct typed pipeline case with structured
expected/found kinds and causal spans. A successfully returned resolved module
must already have passed resolved kind checking; no public path may bypass it.

### Step 5: Prove ownership, order, and exact resources

Test mutual nominal visibility, summary-only imported kinds, deterministic
first failure, every value and constraint boundary, exact kind-node and
binder-record formulas, one-short atomic failure, and deep/wide iterative
checking and disposal.

In this task, replace the predecessor
`nominal_type_applications_must_be_saturated` and
`type_parameters_of_kind_type_cannot_be_applied` expectations with their exact
`kind.expected-type` and `kind.not-applicable` stage/reason results. Record the
deliberate migration in TASK-0016 progress. No full-suite command may straddle
old resolution ownership and new kind ownership.

Run:

```text
cargo test --locked --test kinds
cargo test --locked --test resolution
cargo test --locked --test polymorphism
cargo test --locked --test implementations
cargo test --locked --test diagnostics
cargo test --locked --test cli
cargo test --locked --test core_validation
cargo test --locked --test kind_modules body_free_summary_supplies_direct_kinds -- --exact
cargo test --locked --test interface_generic_summary
cargo test --locked --test module_elaboration_nominals
cargo test --locked --lib -- kind
cargo check --locked --all-targets
```

### Step 6: Review and commit resolved kinds

```text
git add src/kind.rs src/lib.rs src/types.rs src/surface.rs src/resolved.rs src/resolve.rs src/resolve/module_tests.rs src/interface.rs src/evidence.rs src/elaborate.rs src/driver.rs src/core/validate.rs tests/kinds.rs tests/resolution.rs tests/polymorphism.rs tests/implementations.rs tests/diagnostics.rs tests/cli.rs tests/core_validation.rs tests/kind_modules.rs tests/interface_generic_summary.rs tests/module_elaboration_nominals.rs
git -c commit.gpgsign=false commit -m "feat: check explicit declaration kinds"
```

## Task 5: Establish the kinded Core boundary

**Files:**

- Modify: `src/core/type_ops.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/transform.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/resolved.rs`
- Modify: `src/eval/machine.rs`
- Modify: `tests/core_validation.rs`
- Modify: `tests/polymorphism.rs`
- Modify: `tests/architecture.rs`

### Step 1: Write the structural Core binder-kind RED witness

Construct Core directly with a `TypeAbstractionNode` that has an ordered
function-kinded binder and a matching outer scheme. Apply it once with the
existing n-ary `TypeApplicationNode` to a partial nominal constructor, then ask
the independent validator to admit it.

Run:

```text
cargo test --locked --test core_validation structurally_validates_higher_kinded_outer_instantiation -- --exact
```

Expected RED: checked schemes are kinded after Task 4, but Core abstractions
retain only identities and independent validation still assumes kind-`Type`
arguments.

### Step 2: Retain kinded Core binders without changing expression arity

Make outer schemes and `TypeAbstractionNode` retain the same ordered kinded
binder list. A `TypeApplicationNode` still supplies one monotype per binder and
performs simultaneous substitution. Checked monotypes use unary structural
`Type::Application`; do not curry Core expression operations.

Resolved Core binders must agree with canonical registry records. Generated
binders are owned by their local abstraction and matching outer scheme. Every
ordinary value binder, pattern, expression annotation, and result satisfies
kind `Type`; the abstraction annotation is a scheme and has no ordinary kind.

### Step 3: Independently validate local Core kinds

Extend Core admission and validation to rederive nominal constructor kinds and
monotype application results from immutable registries. Validate binder order,
kind, scope, ownership, abstraction/scheme agreement, type-argument count and
kind, simultaneous substitution, inference exclusion, and kind-`Type` value
annotations without consuming a checker success capability.

Add focused wrong-kind and wrong-count mutations to prove the validator, not
the builder, owns independent rejection. Task 9 later closes the full linked
tampering matrix after body-free and linked facts exist.

### Step 4: Preserve kinds through both transforms

Prove both retained transforms preserve canonical applications and binder kinds
and return Core that passes fresh validation. Add exact and one-short builder,
admission, transform-rebuild, validation, and iterative teardown probes. No
evaluator value, frame, lookup, or transition changes.

Run:

```text
cargo test --locked --test core_validation
cargo test --locked --test polymorphism source_instantiation_is_explicit_in_validated_core -- --exact
cargo test --locked --lib -- core
cargo check --locked --all-targets
```

### Step 5: Review and commit the Core boundary

```text
git add src/core/type_ops.rs src/core/dialect.rs src/core/transform.rs src/core/validate.rs src/elaborate.rs src/resolved.rs src/eval/machine.rs tests/core_validation.rs tests/polymorphism.rs tests/architecture.rs
git -c commit.gpgsign=false commit -m "feat: establish kinded Core validation"
```

## Task 6: Make inference and outer generalization kind-aware

**Files:**

- Modify: `src/types.rs`
- Modify: `src/kind.rs`
- Modify: `src/interface.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/driver.rs`
- Modify: `tests/kinds.rs`
- Modify: `tests/polymorphism.rs`
- Modify: `tests/bindings.rs`

### Step 1: Write the fixed-`OMEGA` RED witness

Add a program that instantiates:

```ash
keep<F : Type -> Type, A> : F<A> -> F<A>
keep value = value
```

with a local nominal constructor. Assert the instantiation allocates `F` at
`Type -> Type`, may solve it with a nominal constructor or partial application,
and evaluates unchanged. Add unit probes for registration before use and a
missing or conflicting `OMEGA` entry.

Run:

```text
cargo test --locked --test polymorphism higher_kinded_instantiation_preserves_fixed_kinds -- --exact
```

Expected RED: scheme binders already retain fixed kinds, but instantiation does
not copy them into a registered `OMEGA` entry and missing/conflicting transient
entries have no owned rejection path.

### Step 2: Implement kinded instantiation and first-order solving

Register every fresh inference variable in transient `OMEGA` before it enters a
type. Scheme instantiation copies each declared binder kind. Make unification,
occurs checking, substitution, zonking, and reconstruction traverse canonical
applications and consult fixed kinds before solving. Reject missing or
conflicting entries and same-shape mismatches; never synthesize a type lambda or
change a variable kind.

### Step 3: Write and implement higher-kinded local generalization

Add RED/GREEN cases showing an eligible anonymous-function local generalizes
eligible inference variables of fixed function kind into the outer scheme.
Assert no `forall` appears below a term-function arrow, recursive or ineligible
locals remain monomorphic, and method-local source parameters remain rejected.

### Step 4: Prove complete zonking and resource behavior

Test structural injectivity, both application children in occurs checking,
same-kind partial solutions, a case that would require a type lambda, exact and
one-short substitution/unification/generalization budgets, and no inference
variable in a checked summary candidate or Core input.

Run:

```text
cargo test --locked --test kinds
cargo test --locked --test polymorphism
cargo test --locked --test bindings
cargo test --locked --lib -- elaborate
cargo check --locked --all-targets
```

### Step 5: Review and commit inference

```text
git add src/types.rs src/kind.rs src/interface.rs src/elaborate.rs src/driver.rs tests/kinds.rs tests/polymorphism.rs tests/bindings.rs
git -c commit.gpgsign=false commit -m "feat: preserve kinds through type inference"
```

## Task 7: Extend interface and implementation evidence to higher kinds

**Files:**

- Modify: `src/interface.rs`
- Modify: `src/evidence.rs`
- Modify: `src/evidence_audit.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/pattern.rs`
- Modify: `tests/interfaces.rs`
- Modify: `tests/implementations.rs`
- Modify: `tests/interface_selection.rs`
- Modify: `tests/interface_diagnostics.rs`
- Modify: `tests/interface_resources.rs`

### Step 1: Write the higher-kinded interface RED program

Use `IntFunctor<F : Type -> Type>`, a higher-kinded `Wrapped<F, A>` nominal,
and a generic implementation whose prerequisite is `IntFunctor<F>`. Exercise
method checking, generic head matching, selected evidence, Core lowering, and
evaluation in one source program.

Run:

```text
cargo test --locked --test interfaces higher_kinded_interface_evidence_evaluates -- --exact
```

Expected RED: defining binders are kinded, but candidate freshening, head
matching, substitutions, and selected method evidence do not yet authenticate
or preserve those kinds.

### Step 2: Make matching and selection kind-preserving

Freshen candidate implementation binders with their declared kinds. Match only
the candidate's independently freshened head variables. Require the complete
goal to contain no inference variable before selection and never refine goal
variables. Preserve full-head overlap, deterministic selection, prerequisite
cycles, and exact method membership.

### Step 3: Prove termination, overlap, and orphan ownership

Add cases where both function and argument children determine strict-subterm
success or failure; generic partial heads overlap structurally; and bare,
partial, and saturated local nominal spines yield the same orphan owner.
Primitive, tuple, function, and variable heads have none. Include abstract and
concrete evidence and cases that would require higher-order matching.

### Step 4: Prove failure and resource boundaries

Assert higher-kinded head and prerequisite `kind.argument` failures occur before
ordinary matching or selection. Charge every comparison through the graph-wide
constraint budget and every retained type/kind clone through the appropriate
type-work budget. Add exact, one-short, atomic, and small-stack probes.

Run:

```text
cargo test --locked --test interfaces
cargo test --locked --test implementations
cargo test --locked --test interface_selection
cargo test --locked --test interface_diagnostics
cargo test --locked --test interface_resources
```

### Step 5: Review and commit interface evidence

```text
git add src/interface.rs src/evidence.rs src/evidence_audit.rs src/elaborate.rs src/pattern.rs tests/interfaces.rs tests/implementations.rs tests/interface_selection.rs tests/interface_diagnostics.rs tests/interface_resources.rs
git -c commit.gpgsign=false commit -m "feat: select higher-kinded interface evidence"
```

## Task 8: Close kinded body-free and linked module facts

**Files:**

- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify: `src/resolve/module_tests.rs`
- Modify: `src/evidence.rs`
- Modify: `src/evidence_validation.rs`
- Modify: `src/driver.rs`
- Modify: `tests/kind_modules.rs`
- Modify: `tests/interface_generic_summary.rs`
- Modify: `tests/interface_modules.rs`
- Modify: `tests/library_imports.rs`
- Modify: `tests/interface_validation.rs`
- Modify: `tests/module_elaboration_nominals.rs`

### Step 1: Write the body-free import RED witness

Compile a dependency that exports a higher-kinded nominal, interface, global,
implementation, and hidden kind closure; retain only its immutable summary;
discard dependency bodies; then compile a consumer using those facts.

Run:

```text
cargo test --locked --test kind_modules body_free_summary_preserves_defining_kinds -- --exact
```

Expected RED: Task 4's direct nominal, interface, and scheme kind records exist,
but complete hidden/evidence closure, non-direct route retention, exhaustive
import authentication, and linked kind validation do not.

### Step 2: Complete the canonical kind closure

Extend the direct kind records by carrying ordered kinded binders through public schemes, data constructors,
interfaces, implementation heads and prerequisites, selected evidence, and the
hidden identity closure they require. Preserve defining identities through
complete, qualified, targeted, implementation-only, facade, transitive, and
diamond routes. Opacity hides constructors and spellings, not a nominal
identity's derived kind.

### Step 3: Exhaustively authenticate summaries before local checking

Import admission rederives nominal kinds and rejects duplicate or mismatched
binder kinds, invalid parameter order or derivation, unbound variables,
kind-invalid public or hidden types, and invalid implementation facts as
dependency-summary internal failures. It cannot use dependency bodies or
recompute a defining kind from an alias.

Add private mutation tests for every new public and hidden kind field in
`src/resolve/module_tests.rs` or `src/resolved.rs` unit tests.

### Step 4: Authenticate linked evidence before Core

Validate kinded schemes, implementation heads, substitutions, prerequisites,
selected method types, and authorization relationships before Core synthesis.
Mutate each independently checkable field and prove the owning linked boundary
rejects it without reselection or evaluation.

### Step 5: Prove routes, resources, and body disposal

Cover direct, qualified, targeted, implementation-only, facade, transitive,
diamond, opaque, and hidden carriers after bodies are unavailable. Prove exact
retention formulas, one-short atomic failure, deterministic dependency order,
and iterative accepted/rejected teardown.

Run:

```text
cargo test --locked --test kind_modules
cargo test --locked --test interface_generic_summary
cargo test --locked --test interface_modules
cargo test --locked --test library_imports
cargo test --locked --test interface_validation
cargo test --locked --test module_elaboration_nominals
cargo test --locked --lib -- kind
```

### Step 6: Review and commit module facts

```text
git add src/resolved.rs src/resolve.rs src/resolve/module_tests.rs src/evidence.rs src/evidence_validation.rs src/driver.rs tests/kind_modules.rs tests/interface_generic_summary.rs tests/interface_modules.rs tests/library_imports.rs tests/interface_validation.rs tests/module_elaboration_nominals.rs
git -c commit.gpgsign=false commit -m "feat: authenticate kinded module facts"
```

## Task 9: Close linked Core tampering and erasure

**Files:**

- Modify: `src/core/type_ops.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/transform.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/resolved.rs`
- Modify: `src/evidence_validation.rs`
- Modify: `src/driver.rs`
- Modify: `tests/core_validation.rs`
- Modify: `tests/polymorphism.rs`
- Modify: `tests/interfaces.rs`

### Step 1: Write the linked Core and tampering RED witnesses

Compile the higher-kinded interface program through body-free summary admission
and linked evidence validation, synthesize Core, run both transforms, and ask
for independent revalidation. Add private mutations for every independently
checkable kind relationship before evaluation.

Run:

```text
cargo test --locked --test core_validation linked_higher_kinded_core_revalidates_after_both_transforms -- --exact
```

Expected RED: Task 5 validates locally assembled kinded Core, but the complete
linked registry and authenticated evidence relationships are not yet supplied
to every Core admission and revalidation path.

### Step 2: Connect linked registries without changing Core shape

Feed only authenticated linked nominal, constructor, declared-binder, and
generated-binder facts into the Task 5 validator. Preserve unary structural
monotype application and simultaneous n-ary `TypeApplicationNode`
instantiation. Do not trust selection-time or transform-time success.

### Step 3: Rebuild and independently validate all kind relationships

Independently mutate and reject every listed relationship: nominal parameter
order and kind, nominal-kind derivation, resolved and generated binder identity,
kind, ownership, and provenance, variable scope and shadowing, unary application
domain and result, abstraction/scheme agreement, type-argument count and kind,
simultaneous substitution result, inference escape, and each ordinary kind-
`Type` value annotation. Each mutation must stop at Core validation before
evaluation.

### Step 4: Prove transform and runtime boundaries

Run the higher-kinded linked program through Core construction, both retained
transforms, independent revalidation, erasure, and evaluation. Assert kinds
introduce no runtime value, lookup, interface object, frame, or transition.
Only `outer_nominal` shape inspection may change mechanically.

Add exact and one-short Core construction, transform rebuilding, validation,
and teardown probes using Core's independent type-work ledgers.

Run:

```text
cargo test --locked --test core_validation
cargo test --locked --test polymorphism
cargo test --locked --test interfaces
cargo test --locked --lib -- core
cargo check --locked --all-targets
```

### Step 5: Review and commit Core kinds

```text
git add src/core/type_ops.rs src/core/dialect.rs src/core/transform.rs src/core/validate.rs src/elaborate.rs src/resolved.rs src/evidence_validation.rs src/driver.rs tests/core_validation.rs tests/polymorphism.rs tests/interfaces.rs
git -c commit.gpgsign=false commit -m "feat: authenticate linked kinds in Core"
```

## Task 10: Close diagnostics and resource evidence

**Files:**

- Modify: `src/types.rs`
- Modify: `src/kind.rs`
- Modify: `src/resolve.rs`
- Modify: `src/resolved.rs`
- Modify: `src/interface.rs`
- Modify: `src/evidence.rs`
- Modify: `src/evidence_validation.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/driver.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/transform.rs`
- Modify: `src/core/validate.rs`
- Modify: `tests/diagnostics.rs`
- Modify: `tests/source_diagnostics.rs`
- Modify: `tests/module_cli.rs`
- Create: `tests/kind_resources.rs`
- Modify: `tests/interface_resources.rs`

### Step 1: Write the complete diagnostic matrix

Add exact API and CLI cases for `kind.not-applicable`, `kind.argument`, and
`kind.expected-type`. Cover ordinary application, interface arguments,
implementation heads, prerequisites, and each value-type owner. Assert causal,
argument, declaration, primary, and related spans plus structured expected and
found kinds. Test deterministic precedence independently from rendered text.

Expected RED: individual stages have kind failures, but the complete public and
CLI relationship matrix is absent.

### Step 2: Publish additive resource formulas

In `tests/kind_resources.rs` and owning unit modules, name the exact additive
formula for construction, clone, equality, hashing, rendering, kind checking,
substitution, occurs checking, unification, implementation matching,
summary/import/link admission, Core construction, both transforms, and
independent validation and disposal. Include every kind node, unary application node,
binder-kind record, compared pair, retained clone, work-stack cell, and index
cell charged by that boundary.

### Step 3: Prove exact, one-short, atomic, and teardown behavior

For each operation, including disposal, prove its exact boundary and one-short
failure where allocation or retained work can fail, with stable owner, reason,
and precedence. A failed operation retains no partial fact and leaves immutable
inputs unchanged. Exercise deep and wide accepted and rejected teardown.

### Step 4: Prove deep and wide 256 KiB behavior

On a 256 KiB thread stack, run deep and wide success and rejection for every
operation in Step 2, including accepted and rejected disposal. Include a wide
source argument vector folded into a deep unary application tree and body-free
summary/link/Core boundaries. No host recursion may scale with admitted type or
kind depth.

Run:

```text
cargo test --locked --test diagnostics
cargo test --locked --test source_diagnostics
cargo test --locked --test module_cli
cargo test --locked --test kind_resources
cargo test --locked --test interface_resources
cargo test --locked --lib -- kind
cargo test --locked --lib -- resource
```

### Step 5: Review and commit diagnostic resources

Use an additional independent resource reviewer after the standard semantic
and quality reviews.

```text
git add src tests/diagnostics.rs tests/source_diagnostics.rs tests/module_cli.rs tests/kind_resources.rs tests/interface_resources.rs
git -c commit.gpgsign=false commit -m "test: close kind diagnostics and resources"
```

## Task 11: Prove migration and the complete product path

**Files:**

- Modify: `tests/polymorphism.rs`
- Modify: `tests/resolution.rs`
- Modify: `tests/corpus.rs`
- Modify: `tests/spec_examples.rs`
- Modify: `tests/interfaces.rs`
- Modify: `tests/kind_modules.rs`
- Modify: `tests/core_validation.rs`
- Modify: other predecessor fixtures identified by the migration inventory

### Step 1: Audit deliberate stage and reason shifts

Confirm Task 4 already replaced the predecessor witnesses
`nominal_type_applications_must_be_saturated` and
`type_parameters_of_kind_type_cannot_be_applied` with exact kind-stage
diagnostics for unsaturated `Option` and `A<Int>`. Keep `Type` legal as a
nominal spelling outside kind annotations. Audit the complete predecessor
corpus for any additional intentional shift, record each in the retained
migration matrix, and leave no stale resolution-owned expectation.

### Step 2: Prove compatibility forms

Inventory every predecessor-valid omitted nominal/interface kind and implicit
global or implementation binder. Assert unchanged source compiles without edits,
retains first-occurrence order, and assigns kind `Type`; no legacy header gains
a function kind from use.

### Step 3: Run the complete positive path

Use one linked higher-kinded program through parsing, projection, resolution,
kind checking, inference, evidence selection, summary freeze, body disposal,
import admission, linked validation, Core synthesis, both transforms,
independent Core validation, erasure, and evaluation. Assert exact public
library and CLI observations.

### Step 4: Run all predecessor and current tests

```text
cargo test --locked --test polymorphism
cargo test --locked --test resolution
cargo test --locked --test corpus
cargo test --locked --test spec_examples
cargo test --locked --test interfaces
cargo test --locked --test kind_modules
cargo test --locked --test core_validation
cargo test --locked --workspace --all-targets --all-features
```

### Step 5: Review and commit migration

```text
git add tests
git -c commit.gpgsign=false commit -m "test: prove explicit kind migration"
```

## Task 12: Reconcile the specification and retain kind evidence

**Files:**

- Modify: `spec/syntax.md`
- Modify: `spec/name-resolution.md`
- Modify: `spec/static-semantics.md`
- Modify: `spec/elaboration.md`
- Modify: `spec/README.md`
- Modify: `docs/tools/ash.md`
- Modify: `docs/design/DN-0025-library-and-package-milestones.md`
- Modify: `docs/design/README.md`
- Modify: `docs/trajectory.md`
- Create: `docs/design/lib-ash/kinds-evidence.md`
- Modify: `docs/tasks/TASK-0016-implement-explicit-kinds-and-higher-kinded-parameters.md`
- Modify: `tests/spec_examples.rs`

### Step 1: Write failing executable specification examples

Add the accepted grammar, kind rules, interface-argument rule, exact binder
rules, Core distinction, and representative failures to the normative examples
manifest in `tests/spec_examples.rs` before changing prose.

Run:

```text
cargo test --locked --test spec_examples
```

Expected RED: current specification snippets and manifest do not yet contain
the implemented kind transition.

### Step 2: Update normative truth from implementation

Reconcile syntax, resolution ownership and summary authentication, static kind
and inference rules, interface/implementation rules, failure/resource
ownership, Core abstraction and simultaneous application, linking, and
independent validation. Use the documentation policy and formal-notation
fences. Do not promote later `lib-ash` features.

### Step 3: Retain evidence and maintenance ownership

Create `docs/design/lib-ash/kinds-evidence.md`. Record the final semantic
boundary, complete type-bearing site map, production and maintenance sites,
named positive/negative/tamper tests, exact resource formulas and measured
results, 256 KiB outcomes, diagnostic and migration matrices, final test counts,
review outcomes, integrated predecessor dependency, no-tag decision, and
exclusions. Update
the tool guide, DN-0025, design index, trajectory, and task progress without
claiming the complete `lib-ash` milestone is closed.

### Step 4: Verify documentation and executable truth

```text
cargo test --locked --test spec_examples
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Manually check every changed relative link, authority label, formal notation
fence, documented command, and current-versus-prospective claim.

### Step 5: Review and commit specification

Run independent specification/authority and evidence/resource reviews after the
standard semantic review.

```text
git add spec docs tests/spec_examples.rs
git -c commit.gpgsign=false commit -m "docs: specify explicit kinds"
```

## Task 13: Complete independent review, gates, and lifecycle cleanup

**Files:**

- Modify: every file required by review corrections
- Modify: `docs/design/lib-ash/kinds-evidence.md`
- Modify: `docs/design/DN-0025-library-and-package-milestones.md`
- Modify: `docs/design/README.md`
- Modify: `docs/trajectory.md`
- Modify: `docs/proposals/README.md`
- Modify: `docs/tasks/README.md`
- Remove: `docs/proposals/CP-0009-explicit-kinds-and-higher-kinded-parameters.md`
- Remove: `docs/tasks/TASK-0016-implement-explicit-kinds-and-higher-kinded-parameters.md`
- Remove: `docs/plans/2026-08-26-explicit-kinds-and-higher-kinded-parameters.md`
- Remove: `docs/plans/2026-08-26-explicit-kinds-design.md`

### Step 1: Run final independent reviews

Run read-only semantic/specification, implementation/Core/resource, and
evidence/migration/authority reviews in parallel. Correct every finding, rerun
the affected focused tests, and repeat affected reviews. No Critical,
Important, or Minor correctness issue may remain.

### Step 2: Run the exact pre-cleanup gate

Read the complete output of:

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

Record exact test counts, command results, review verdicts, and final resource
measurements in the evidence report and TASK-0016. Create a mandatory unsigned
pre-cleanup retention commit containing the finalized evidence report,
TASK-0016 record, and every review correction:

```text
git add -A
git -c commit.gpgsign=false commit -m "docs: retain explicit kind evidence"
git status --short
```

Expected: the commit succeeds and `git status --short` has no output.

### Step 3: Prove cleanup is authorized

Before removing anything, confirm:

```text
test -f docs/design/lib-ash/kinds-evidence.md
git log -1 --format=%s
git status --short
```

Expected: the retained evidence exists, the latest commit is the mandatory
pre-cleanup retention checkpoint, and the worktree is clean.

Manually confirm the retained evidence contains every result formerly owned by
the proposal, task, design record, and plan; all review findings are resolved;
the task records every gate complete; and no retained document still requires a
transition artifact link.

### Step 4: Remove transition artifacts and repair indexes

Remove CP-0009, TASK-0016, both temporary plans, their proposal/task index
entries, and stale links. Retain the normative specification, implementation,
tests, `kinds-evidence.md`, predecessor evidence, and the explicit statement
that the complete `lib-ash` milestone remains open. Do not create a tag.

Use `apply_patch` for removals and link repairs, then run:

```text
markdownlint --disable MD013 -- README.md spec docs
git diff --check
cargo xtask verify
```

### Step 5: Commit the cleanup unsigned

```text
git add -A docs
git -c commit.gpgsign=false commit -m "docs: close explicit kinds increment"
```

Leave branch `lib-ash-kinds` in its dedicated worktree, based on `a1647ff`,
clean, untagged, and unmerged into `main`. The predecessor-order restriction is
already satisfied because `main` contains `a1647ff`.
