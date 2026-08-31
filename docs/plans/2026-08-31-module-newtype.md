# Module `newtype` Implementation Plan

> **For Codex:** Use `superpowers:subagent-driven-development` to execute this
> plan checkpoint by checkpoint. Preserve each RED witness and review boundary.

This temporary execution plan is owned by
[TASK-0019](../tasks/TASK-0019-implement-module-newtype.md). It organizes work
and does not define Ash semantics. The current `spec/` remains authoritative;
accepted [CP-0012](../proposals/CP-0012-module-newtype.md) alone authorizes the
prospective transition.

**Goal:** Implement one allocation-free module-level nominal `newtype` with
explicit wrapping and irrefutable matching, existing visibility, no inherited
interface evidence, authenticated pure Core conversion, and unchanged runtime
representation.

**Architecture:** Enrich the existing nominal declaration pipeline with an
explicit data-or-newtype kind and one canonical representation template.
Resolution and summaries own identity and source access. Module checking owns
kind-correct representation admission and the newtype-only cycle graph. Typed
Core owns an erased one-child conversion authenticated against linked canonical
facts. The explicit evaluator enters that child directly.

**Tech stack:** Rust 2024, the event-producing lexer/parser, projected surface
tree, module resolver and body-free summaries, fixed-kind and bidirectional
checker, typed pure Core, explicit evaluator machine, Cargo integration tests,
and Markdown specification.

---

Implementation follows `superpowers:test-driven-development`, `rust-skills`,
`superpowers:systematic-debugging` for unexpected results,
`superpowers:subagent-driven-development`,
`superpowers:requesting-code-review`, and
`superpowers:verification-before-completion`.

Use one implementation agent at a time because checkpoints share product
state. Parallelize only independent read-only reviews. For every product
checkpoint:

1. assign the complete checkpoint to one implementer;
2. add the named behavioral test and observe its expected RED before production
   edits;
3. implement only the coherent behavior needed for that checkpoint;
4. run focused GREEN commands;
5. obtain independent semantic/Core and Rust/resource reviews and correct every
   Critical or Important finding;
6. repeat affected checks, inspect `git status --short`, and run
   `git diff --check`; and
7. create the named unsigned commit with
   `git -c commit.gpgsign=false commit`.

Keep `spec/` unchanged through Checkpoint 5. Do not merge, push, tag, remove the
branch, or remove the worktree. Stop and return to CP-0012 rather than inventing
semantics or raising a production resource limit.

## Checkpoint 1: Authorize and isolate the increment

**Files:**

- Create: `docs/tasks/TASK-0019-implement-module-newtype.md`
- Create: `docs/plans/2026-08-31-module-newtype.md`
- Modify: `docs/tasks/README.md`

### Step 1: Confirm authority and baseline

Confirm CP-0012 is accepted, TASK-0019 is active, and `spec/` still describes
the pure predecessor. The `d1e323d` `main` baseline must pass:

```text
cargo xtask verify
```

### Step 2: Create the isolated product branch

Confirm `.worktree/` is ignored. Create
`.worktree/cp0012-module-newtype` on `feature/cp0012-module-newtype` from
`d1e323d`. Cherry-pick `f79ce51`, `65b339c`, `328c4a5`, and `209bfe5` in that
order, followed by the authorization commit at the then-current
`planning/effect-ash-program` tip. Do not merge either branch.

The product branch must begin with no Rust or normative specification delta.
Require five commits after `d1e323d`, verify `git diff --quiet d1e323d -- src
spec`, and record the resolved authorization and product commit hashes in
TASK-0019.

### Step 3: Validate and commit authorization

Run:

```text
markdownlint --disable MD013 -- docs/proposals docs/tasks docs/plans
git diff --check
git status --short
```

Check every changed relative link and artifact status. Commit on the planning
branch, then carry the commit onto the product branch:

```text
git -c commit.gpgsign=false commit -m "docs: authorize module newtype implementation"
```

## Checkpoint 2: Syntax and projected declaration kind

**Files:**

- Modify: `src/lexer/token.rs`
- Modify: `src/lexer/mod.rs`
- Modify: `src/parser/mod.rs`
- Modify: `src/parser/grammar.rs`
- Modify: `src/parser/project.rs`
- Modify: `src/surface.rs`
- Modify: `tests/lexer.rs`
- Modify: `tests/parser.rs`
- Modify: `tests/modules_syntax.rs`

### Step 1: Write and witness the syntax RED

Add:

```rust
#[test]
fn module_newtype_projects_same_spelled_one_field_representation() {
    // pub opaque newtype UserId = UserId(Int)
}
```

Assert `TokenKind::Newtype`, `NodeKind::NewtypeDeclaration`, retained
`SurfaceDeclarationIndex::Type(0)`, `Newtype` declaration kind, public opaque
visibility, both `UserId` spellings and spans, and the sole `Int` field. Run:

```text
cargo test --locked --test modules_syntax \
  module_newtype_projects_same_spelled_one_field_representation -- --exact
```

Expected RED: `newtype` is an ordinary identifier and no declaration starts.

### Step 2: Implement lexical and grammar ownership

Reserve `newtype` in `src/lexer/mod.rs` and add the token display. Add a
dedicated CST node and parser route for private, public transparent, and public
opaque forms. Enforce one constructor and one field in parsing and recovery.
Retain a distinct constructor spelling for resolution; it is not malformed
syntax.

Keep `SurfaceDeclarationIndex::Type`. Add a nominal declaration-kind enum to
`SurfaceTypeDeclaration` so a one-field ordinary `type` is never inferred to be
a `newtype`.

### Step 3: Complete syntax evidence

Cover keyword boundaries, all visibility forms, kinded parameters, missing and
nullary constructors, extra fields and constructors, missing delimiters, a
distinct constructor spelling that projects successfully, following valid
declarations, token-complete recovery, causal spans, and exact syntax-ledger
success/one-short/retry behavior. Preserve every ordinary `type` case.

### Step 4: Verify, review, and commit syntax

Run:

```text
cargo test --locked --test lexer --test parser --test modules_syntax
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

After both reviews and corrections, commit:

```text
git -c commit.gpgsign=false commit -m "feat: parse module newtype declarations"
```

## Checkpoint 3: Identity, kind admission, and authenticated summaries

**Files:**

- Modify: `src/surface.rs`
- Modify: `src/resolve.rs`
- Modify: `src/resolved.rs`
- Modify: `src/kind.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/types.rs` only for shared type-work helpers
- Create: `tests/module_newtypes.rs`
- Modify: `tests/resolution.rs`
- Modify: `tests/kinds.rs`
- Modify: `tests/module_resolution.rs`
- Modify: `tests/module_visibility.rs`
- Modify: `tests/library_imports.rs`
- Modify: `tests/module_elaboration_nominals.rs`

### Step 1: Write and witness the identity RED

Add a base module with `pub newtype UserId = UserId(Int)`, a public facade
re-export, and an entry import that names only `UserId`. Assert the imported
fact keeps the defining `NominalTypeId`, declaration kind, parameter order,
transparent access, constructor identity, and canonical representation. Run:

```text
cargo test --locked --test module_newtypes \
  module_newtype_identity_survives_facade_reexport -- --exact
```

Expected RED: the projected declaration kind has no resolved or summary
carrier.

### Step 2: Extend the existing nominal pipeline

Reuse `NominalTypeId`, `ConstructorId`, `SurfaceDeclarationIndex::Type`, and
`ResolvedDeclarationIndex::Type`. Extend identity installation and registry
construction with explicit declaration kind. After identity allocation and
before publication, reject a different constructor spelling as
`resolve.newtype-constructor-name` at that spelling.

Carry one canonical fact through `ResolvedNominalType`, `ImportedNominalFact`,
public `ExportedType`, hidden `ExportedHiddenType`, the hidden constructor and
family closure, `ExportSummary::freeze`, import and re-export merge comparison,
authentication, `ResolvedRegistry::checker_view`, and `combine_checked`. It
contains owner and identity, ordered parameter records, sole same-spelled
constructor identity, representation template, visibility, access, and origin.
Each carrier embeds or derives this one fact. Transparent constructor
projections and schemes derive from it; no carrier retains a second independent
representation payload.

Transparent routes install source constructor access. Opaque routes expose only
nominal identity, parameters, and kind. Private and opaque hidden facts remain
available to authenticated linking but never install source bindings.

### Step 3: Admit representation kinds and cycles

Resolution authenticates imports and installs identities. The existing kind
stage in `resolve_module_with_budget` then validates all ordinary constructor
payloads and all newtype representations in combined declaration/type order;
its exhaustion remains `kind.resource-exhausted`. Only after that stage
succeeds does `check_module_with_budget` build and traverse the newtype-only
representation graph with `checking_type_work`, before interface checking.

Use the module type-work ledger. Charge every discovered representation
occurrence, retained edge/index, pending entry, and visited or active entry
before retain or visit. Traverse and dispose iteratively. On exhaustion report
`internal.resource.type-work`, publish no checked module or summary, and allow
the same logical input to succeed with a replenished budget. Report the first
cycle as `newtype.recursive-representation`; never follow through ordinary data.
Add a mixed-error witness proving kind failure precedes graph/cycle analysis
and graph exhaustion maps to `internal.resource.type-work`.

### Step 4: Complete identity and summary evidence

Cover distinct same-representation identities; declaration order; parameters
and substitution; kind-before-cycle and mixed-failure precedence; direct,
mutual and deep cycles; an ordinary-data break in a would-be cycle; private,
opaque and transparent access; aliases, targeted imports, direct re-exports,
facade diamonds, hidden carriers, and malformed summary facts.

Tamper independently with declaration kind, owner, identity, parameter
identity/order/kind, representation substitution, constructor cardinality,
identity/spelling/owner/provenance, representation, access, and origin. Add
exact-success, one-short atomic failure, fresh retry, and deep accepted and
rejected teardown beside each private carrier owner.

### Step 5: Verify, review, and commit identity

Run:

```text
cargo test --locked --test module_newtypes --test resolution --test kinds
cargo test --locked --test module_resolution --test module_visibility
cargo test --locked --test library_imports --test module_elaboration_nominals
cargo test --locked --lib -- resolve
cargo test --locked --lib -- resolved
cargo test --locked --lib -- kind
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

After both reviews and corrections, commit:

```text
git -c commit.gpgsign=false commit -m "feat: retain module newtype identities"
```

## Checkpoint 4: Static typing, patterns, and explicit evidence

**Files:**

- Modify: `src/types.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/pattern.rs`
- Modify: `src/core/dialect.rs`
- Modify as justified: `src/core/type_ops.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/core/transform.rs`
- Modify: `src/eval/machine.rs`
- Modify as required: `src/interface.rs`
- Modify as required: `src/evidence.rs`
- Modify: `tests/module_newtypes.rs`
- Modify: `tests/data_and_adts.rs`
- Modify: `tests/polymorphism.rs`
- Modify: `tests/implementations.rs`
- Modify: `tests/interface_selection.rs`
- Modify: `tests/diagnostics.rs`

### Step 1: Write and witness the evidence-isolation RED

Add a `Render<Int>` implementation, wrap an `Int` as `UserId`, and request
`Render<UserId>` without declaring it. Run:

```text
cargo test --locked --test implementations \
  representation_does_not_supply_nominal_interface_evidence -- --exact
```

Expected RED after Checkpoint 3: the checker has no newtype-specific wrap path.
The completed case must report `constraint.unsatisfied`, never select the
representation implementation.

### Step 2: Type explicit conversion sites

Give an accessible constructor the rank-1 scheme
`forall parameters. representation -> owner<parameters>`. Preserve nominal
inequality in unification. Permit an explicit constructor pattern with one
subpattern and type it as an irrefutable unwrap. Coverage treats it as the sole
constructor without introducing a runtime tag test.

Keep explicit implementation ownership on the nominal outer type. Do not add
evidence lift, local implementation search, implicit coercion, or a general
representational equality relation.

### Step 3: Complete static evidence

Cover scalar, tuple, ordinary nominal, nested and parameterized
representations; constructors passed and returned as first-class values;
irrefutable function and binding patterns; explicit matches; ordinary nominal
mismatches; inaccessible constructors; explicit nominal implementations; no
representation evidence lift; coverage; stable spans; failure precedence; and
poisoned-state refusal to publish. Preserve ordinary data and interface tests.

### Step 4: Introduce the conversion carrier and lowering

Add the typed one-child newtype-conversion computation and builder admission so
the type checker never calls the allocating ordinary-constructor route. Lower
newtype constructor values to an ordinary unary function with a wrap body and
lower newtype patterns through explicit unwrap structure without a constructor
tag test. Update the exhaustive Core traversal and iterative disposal required
for the code to compile, but keep the conversion unavailable to a completed
linked program until Checkpoint 5 adds canonical-relation validation.

At this preparatory boundary, independent Core validation rejects every
conversion before it can produce a `ValidatedProgram`, because canonical
relation authentication is not implemented yet. Add exhaustive transform and
evaluator dispatch arms that cannot receive the conversion through validated
production input; they must preserve structured refusal rather than evaluate,
rebuild, or panic. Checkpoint 5 replaces those temporary refusal paths with
canonical validation, reconstruction, and direct-child evaluation.

Parameterized constructor lowering must call
`Elaborator::fresh_type_variable` before building each `TypeAbstraction`; that
path registers kind and origin and supports rollback. Add a one-short failure
and retry witness for generated-binder registration. Never construct a raw
generated `TypeVariableId` at this boundary.

### Step 5: Verify, review, and commit static semantics

Run:

```text
cargo test --locked --test module_newtypes --test data_and_adts
cargo test --locked --test polymorphism --test implementations
cargo test --locked --test interface_selection --test diagnostics
cargo test --locked --lib -- elaborate
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

After both reviews and corrections, commit:

```text
git -c commit.gpgsign=false commit -m "feat: check module newtype conversions"
```

## Checkpoint 5: Core authentication and zero-cost execution

**Files:**

- Modify: `src/core/validate.rs`
- Modify: `src/core/transform.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/eval/machine.rs`
- Modify `src/eval/value.rs` only for existing test-scoped observation
- Modify: `tests/core_validation.rs`
- Modify: `tests/semantics.rs`
- Modify: `tests/architecture.rs`
- Modify: `tests/module_newtypes.rs`

### Step 1: Write and witness the Core RED

Add a linked program wrapping `42` as `UserId`. Inspect reachable Core for
exactly one wrap conversion with `Int` child and `UserId` result and no
allocating constructor node for `UserId`. Require the previously unavailable
conversion to authenticate, run both transforms, and independently revalidate:

```text
cargo test --locked --test core_validation \
  module_newtype_conversion_authenticates_representation -- --exact
```

Expected RED: Checkpoint 4 can construct the conversion, but independent
validation cannot yet authenticate its canonical representation relation.

### Step 2: Authenticate, transform, and erase

Core validation derives the relation from the linked canonical fact and child
and enclosing type annotations. Check owner, complete nominal application,
parameter position and kind, substitution, direction, child/result types,
declaration and source provenance. Do not recheck source access or routes.

Reject ordinary constructors used as conversions and newtypes reaching
ordinary constructor or constructor-pattern Core. Both transforms must rebuild
the conversion and return to independent validation. The evaluator dispatches
the conversion by entering its child without inspecting registry metadata,
allocating a cell, tagging, copying, or adding runtime state.

### Step 3: Complete Core and runtime evidence

Tamper with direction, owner, ordinary/newtype kind, child/result relation,
fresh-binder application, and provenance. Add exact construction and validation
resource boundaries, retry, and 256-KiB accepted/rejected teardown. Cover
scalar, tuple, ordinary nominal, parameterized, nested and deep execution;
source type rendering versus representation value rendering; deterministic
traces; and closed Core/evaluator inventory guards.

Add and run the internal allocation witness with an ordinarily allocating
representation so zero wrapper allocation cannot be confused with zero total
allocation:

```text
cargo test --locked \
  eval::machine::tests::module_newtype_wrapper_allocates_no_constructor_cell \
  -- --exact
```

### Step 4: Verify, review, and commit Core

Run:

```text
cargo test --locked --test core_validation --test semantics
cargo test --locked --test architecture --test module_newtypes
cargo test --locked --lib -- core
cargo test --locked --lib -- eval
cargo fmt --check
cargo check --locked --all-targets
cargo clippy --locked --workspace --all-targets --all-features -- -D warnings
git diff --check
```

After both reviews and corrections, commit:

```text
git -c commit.gpgsign=false commit -m "feat: erase module newtype conversions"
```

## Checkpoint 6: Resources, specification, evidence, and closure

**Files:**

- Create: `tests/newtype_resources.rs`
- Modify: `tests/corpus.rs`
- Modify: `tests/spec_examples.rs`
- Modify affected owner-local unit tests in `src/`
- Modify: `spec/README.md`
- Modify: `spec/lexical-structure.md`
- Modify: `spec/syntax.md`
- Modify: `spec/name-resolution.md`
- Modify: `spec/static-semantics.md`
- Modify: `spec/elaboration.md`
- Modify: `spec/dynamic-semantics.md`
- Create: `docs/design/effect-ash/module-newtype-evidence.md`
- Modify: `docs/design/README.md`
- Modify: `docs/trajectory.md`
- Update, then remove after the retained checkpoint:
  `docs/proposals/CP-0012-module-newtype.md`
- Update, then remove after the retained checkpoint:
  `docs/tasks/TASK-0019-implement-module-newtype.md`
- Remove after the retained checkpoint:
  `docs/plans/2026-08-31-module-newtype.md`
- Modify: `docs/proposals/README.md`
- Modify: `docs/tasks/README.md`

### Step 1: Close the resource matrix RED-first

Create the first retained-carrier matrix test and run:

```text
cargo test --locked --test newtype_resources \
  module_newtype_resource_matrix_accounts_all_new_carriers -- --exact
```

Expected RED: the resource suite and its carrier inventory do not exist. Before
any specification or evidence-report change, make the test enumerate every new
retained carrier and prove at least one measured exact-success and
one-unit-short boundary.

Inventory and measure every new syntax event, declaration record, identity and
canonical fact, representation type and substitution, graph entry, summary and
link fact, conversion node, generated binder/function, transform copy, and Core
validation fact. For each retained owner, add exact success, one-unit-short
failure before publication, retry with the same logical input, and deep or wide
accepted and rejected teardown.

Use `tests/newtype_resources.rs` for public pipeline boundaries and owner-local
unit tests for private budget hooks. Keep syntax, module type work, Core
construction, Core validation, and interface constraint ledgers distinct.
Confirm a program without `newtype` retains its prior Core inventory, evaluator
trace, heap behavior, observation, and resource boundary.

### Step 2: Reconcile normative truth

Before changing `spec/`, compare every retained test to CP-0012. If product
evidence contradicts the accepted semantics, stop and return to the proposal.

Update lexical tokens; grammar; declaration, identity, namespace, visibility,
import and re-export rules; kinds, cycles, typing, patterns, coverage,
interfaces, failure order and resources; summary, linking, conversion and Core
validation; evaluator erasure and observation. Add executable examples and keep
local/runtime identity, local implementations and changed overlap/orphan rules,
effects, resources, providers, hooks, proof evidence, existential packages,
dynamic loading, implicit coercions, heap inspection, special `newtype`
rendering, and general ABI or foreign-representation guarantees excluded.

### Step 3: Retain evidence and migration

Record exact implementation commits, semantic corpus, diagnostic matrix,
summary/Core tampering, resource formulas, transforms, runtime allocation
observation, predecessor migration, reviews, downstream-pressure audit, and
verification in `docs/design/effect-ash/module-newtype-evidence.md` and link it
from `docs/design/README.md`. Update the product-branch trajectory to record the
checkpoint as complete and pending integration and to identify local `newtype`
as the next programme input. A later separately authorized integration action,
not this product branch, may record module `newtype` as current on `main`.

### Step 4: Run independent final reviews and the full gate

Obtain independent reviews for semantic/specification compliance, Core and
runtime authentication, Rust ownership and resources, documentation authority
and links, downstream Effects pressure, and simplification. Correct every
actionable finding and repeat affected checks. Run:

```text
cargo test --locked --test newtype_resources
cargo test --locked --test corpus --test spec_examples
cargo test --locked --test module_newtypes --test module_visibility
cargo test --locked --test module_resolution --test module_elaboration_nominals
cargo test --locked --test core_validation --test architecture
cargo xtask verify
markdownlint --disable MD013 -- docs spec README.md AGENTS.md
git diff --check
git status --short
```

Manually check every changed relative link and formal-notation fence.

### Step 5: Retain, then clean the transition artifacts

Commit resources and product evidence, then normative specification and the
retained evidence report. While CP-0012 and TASK-0019 still exist, record their
final evidence. In a separate cleanup commit, remove the accepted proposal,
completed task, and task-owned plan and restore their indexes. Run the full gate
again after cleanup.

Suggested unsigned commits are:

```text
git -c commit.gpgsign=false commit -m "test: retain module newtype evidence"
git -c commit.gpgsign=false commit -m "docs: specify module newtypes"
git -c commit.gpgsign=false commit -m "docs: close module newtype transition"
```

Do not merge the product branch or the Effects Ash milestone, push, tag, delete
the branch, or remove the worktree. Report the verified branch and independent
review record, then continue the next separately authorized Effects programme
checkpoint on its own branch.
