# Resume-Required Effect Kernel Implementation Plan

> **For Codex:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to execute this plan checkpoint by
> checkpoint. Preserve each RED witness and review boundary.

This temporary execution plan is owned by
[TASK-0020](../tasks/TASK-0020-implement-resume-required-effect-kernel.md). It
organizes work and does not define Ash semantics. Current `spec/` remains
authoritative; accepted
[CP-0013](../proposals/CP-0013-resume-required-effect-kernel.md) alone
authorizes the prospective transition.

**Goal:** Implement identity-bearing open and closed effect rows, typed
operation requests, exhaustive ordered lexical handlers, and immediate
non-escaping control whose operation clause resumes exactly once.

**Architecture:** Add a distinct shared `EffectRow` and computation-type layer
before syntax consumers. Source checking retains the least effect row and
lowers accepted requests and handlers into a separate validated effect Core
dialect. The explicit evaluator owns ordered handler boundaries and moves the
selected typed control segment into first-order one-shot continuation data;
the pure dialect remains uninhabited by effect operations.

**Tech stack:** Rust 2024, event-producing lexer/parser, projected surface
tree, module resolver and body-free summaries, fixed-kind bidirectional
checker, typed Core dialects and transforms, explicit evaluator machine, Cargo
integration tests, and Markdown specification.

---

Implementation follows `superpowers:test-driven-development`, `rust-skills`,
`superpowers:systematic-debugging` for unexpected results,
`superpowers:subagent-driven-development`,
`superpowers:requesting-code-review`, and
`superpowers:verification-before-completion`.

Use one implementation agent at a time because all checkpoints share semantic
state. Parallelize only independent read-only reviews. Do not run a disposable
experiment. Use focused tests during RED/GREEN work and the complete verifier
only at the fresh baseline and final closure.

The 17-unit budget is a scope ceiling:

| Boundary | Units |
| --- | ---: |
| Authorization and isolation | 1 |
| Shared rows and computation types | 4 |
| Syntax, identity, and summaries | 3 |
| Source typing and resume usage | 4 |
| Effect Core and evaluator | 3 |
| Specification and closure | 2 |

If a checkpoint needs semantics absent from CP-0013 or consumes the remaining
budget needed by later rows in the table, stop and return to the proposal. Do
not investigate checked discard, resources, hooks, cleanup, async control, or
multi-shot behavior.

For every retained product boundary:

1. assign the complete boundary to one implementation agent;
2. write the named behavioral or tamper test and retain its expected RED;
3. make the smallest coherent production change;
4. run focused GREEN tests and all-target checking;
5. obtain the named independent review and correct each Critical or Important
   finding;
6. run `git diff --check` and inspect `git status --short`; and
7. create the named unsigned commit with
   `git -c commit.gpgsign=false commit`.

## Checkpoint 1: Authorize and isolate the product transition

**Files:**

- Create: `docs/tasks/TASK-0020-implement-resume-required-effect-kernel.md`
- Create: `docs/plans/2026-09-01-resume-required-effect-kernel.md`
- Modify: `docs/tasks/README.md`

### Step 1: Record acceptance and authorization

Confirm CP-0013 is `accepted`, TASK-0020 is `active`, and the task links this
plan. Confirm no CP or task identity was reused across Git history. Run:

```text
markdownlint-cli2 docs/proposals docs/tasks docs/plans
git diff --check
```

Commit the planning branch unsigned:

```text
git -c commit.gpgsign=false commit \
  -m "docs: authorize resume-required effect kernel"
```

### Step 2: Create the fresh product worktree

Confirm `.worktree/` is ignored and both the path and branch are unused. Create
`.worktree/cp0013-effect-kernel` on `feature/cp0013-effect-kernel` from
then-current verified `main`. Cherry-pick, without merging, these planning
commits in order:

1. `f79ce51` — effect-ash program design;
2. `65b339c` — effect-ash milestone plan;
3. `392f976` — proposed CP-0013;
4. `41be641` — accepted CP-0013; and
5. the authorization commit containing TASK-0020 and this plan.

Record the resolved main base, authorization commit, and product tip in
TASK-0020. Confirm the carried tree has no `src/`, `tests/`, or `spec/` delta
from the product base. Run `cargo xtask verify` once in the product worktree.
Do not proceed if it fails.

## Checkpoint 2: Establish shared rows and source static semantics

This checkpoint has three small product commits followed by one semantic and
implementation review. Keep `spec/` unchanged until final closure.

### Step 1: Add the row and computation algebra

**Files:**

- Modify: `src/types.rs`
- Modify: `src/kind.rs`
- Modify: `src/elaborate.rs`
- Modify as required: `src/resolved.rs`
- Modify as required: `src/core/type_ops.rs`
- Create: `tests/effect_rows.rs`
- Modify: `tests/kinds.rs`
- Modify: `tests/polymorphism.rs`
- Modify: `tests/architecture.rs`

Write `open_row_union_requires_an_existing_lacks_fact` first. Construct one
open row variable, union it with an exact effect instance, and require the
typed ambiguity until the row variable already lacks that instance. Add
closed equality/order/idempotence, exact-instance arguments, substitution,
exact removal, one-tail union, unrelated-tail ambiguity, occurs, fixed-kind,
generalization, instantiation, rendering, exact-resource, retry, and deep-drop
cases.

Run the focused RED, expecting missing `EffectRow` and computation carriers:

```text
cargo test --locked --test effect_rows \
  open_row_union_requires_an_existing_lacks_fact -- --exact
```

Implement:

- stable effect and operation identity carriers needed by row members;
- `EffectInstance`, canonical known members, optional tail, and retained lacks
  facts;
- a computation type containing one value `Type` and one `EffectRow`;
- a function type whose codomain is a computation type;
- `Kind::EffectRow` with the CP-0013 binder-owner restrictions;
- iterative equality, rendering, cloning, substitution, free-variable,
  occurs, union, exact removal, and disposal operations;
- row inference variables and fixed-kind unification in the existing
  elaborator substitution transaction; and
- charge-before-retention, atomic failure, and retry at each proportional
  owner.

Preserve one-tail ambiguity rather than adding qualified union constraints.
Existing function constructors and tests must create an empty computation row
through one compatibility helper, not copy empty-row construction throughout
the compiler.

Run:

```text
cargo test --locked --test effect_rows --test kinds --test polymorphism
cargo test --locked --lib -- types
cargo test --locked --lib -- kind
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

Commit unsigned:

```text
git -c commit.gpgsign=false commit -m "feat: add effect row algebra"
```

### Step 2: Resolve effect declarations and row syntax

**Files:**

- Modify: `src/lexer/token.rs`
- Modify: `src/lexer/mod.rs`
- Modify: `src/parser/mod.rs`
- Modify: `src/parser/grammar.rs`
- Modify: `src/parser/project.rs`
- Modify: `src/surface.rs`
- Modify: `src/resolve.rs`
- Modify: `src/resolved.rs`
- Create: `tests/effects_syntax.rs`
- Create: `tests/effect_modules.rs`
- Modify: `tests/lexer.rs`
- Modify: `tests/parser.rs`
- Modify: `tests/module_resolution.rs`
- Modify: `tests/module_visibility.rs`
- Modify: `tests/library_imports.rs`

Write `public_effect_identity_survives_facade_reexport` first with a generic
public effect, two operations, a targeted re-export, and an entry import.
Assert defining `EffectId`, operation order and identities, parameter kinds,
operation types, visibility, and origins. Expected RED: `effect` is an
ordinary identifier and no effect declaration projects.

Reserve all five CP-0013 keywords and add the exact grammar for effect
declarations, `EffectRow`, computation codomains, `perform`, `handle`, clauses,
and `resume`. Preserve token-complete recovery, syntax budgets, the stated
precedence, and the keyword migration. Project explicit surface forms rather
than inferring effects from ordinary function syntax.

Allocate all effect and operation identities before bodies resolve. Extend the
shared uppercase namespace, import/re-export projections, body-free public and
hidden summaries, diamond authentication, and checked registry with one
canonical effect fact. Operations remain effect-local and create no term
binding. Enforce effect parameter and operation-shape restrictions in their
earliest owning stage.

Run:

```text
cargo test --locked --test effects_syntax --test effect_modules
cargo test --locked --test lexer --test parser
cargo test --locked --test module_resolution --test module_visibility
cargo test --locked --test library_imports
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

Commit unsigned:

```text
git -c commit.gpgsign=false commit -m "feat: resolve effect declarations"
```

### Step 3: Type requests, handlers, and resume usage

**Files:**

- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/pattern.rs`
- Modify as required: `src/interface.rs`
- Modify as required: `src/evidence.rs`
- Create: `tests/effect_typing.rs`
- Create: `tests/effect_diagnostics.rs`
- Modify: `tests/functions.rs`
- Modify: `tests/bindings.rs`
- Modify: `tests/data_and_adts.rs`
- Modify: `tests/polymorphism.rs`
- Modify: `tests/diagnostics.rs`

Write `closed_handler_discharges_exact_effect_and_keeps_main_pure` first using
the accepted `Cell` example. Expected RED: the resolved forms have no effectful
expression typing.

Extend every expression synthesis/checking result with a least effect row.
Function creation stays pure and moves its body row into the latent codomain.
Application, strict primitives, tuples, constructors, matches, blocks, and
bindings union child rows in current evaluation order. Extend global and
eligible-local generalization and instantiation only for permitted row
variables.

Type `perform` from the exact substituted operation signature. Type a handler
against one exact input member and one shared least output row. Require one
irrefutable clause per operation, forward unknown identities, re-add direct
same-instance clause requests, and reject a nonempty entry row.

Implement resume as a resolved clause-scope fact, not a value. The usage pass
threads available/consumed state through strict children and match branches,
rejects unconsumed completion or a consumed-state use, and forbids capture by
nested functions, recursive members, or nested handler clauses. Retain stable
diagnostics and poisoning; no rejected module may publish a checked summary.

Cover closed and open relays, higher-order latent rows, branch unions,
distinct same-shaped APIs, distinct parameterized instances, ambiguous open
union, exhaustive coverage, exact removal, forwarding, same-instance
reintroduction, zero/double/branch resume, capture rejection, resume outside a
clause, failure precedence, and predecessor pure inference.

Run:

```text
cargo test --locked --test effect_typing --test effect_diagnostics
cargo test --locked --test functions --test bindings --test data_and_adts
cargo test --locked --test polymorphism --test diagnostics
cargo test --locked --lib -- elaborate
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

Obtain one independent semantic/Core review and one Rust/resource review of
the complete static checkpoint. Correct every Critical or Important finding,
repeat affected focused tests, then commit unsigned:

```text
git -c commit.gpgsign=false commit -m "feat: check effect handlers"
```

## Checkpoint 3: Add independently validated effect Core

**Files:**

- Modify: `src/core/data.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/mod.rs`
- Modify: `src/core/type_ops.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/core/transform.rs`
- Modify: `src/elaborate.rs`
- Modify: `tests/architecture.rs`
- Modify: `tests/core_validation.rs`
- Create: `tests/effect_core.rs`

Write `effect_core_rejects_forged_handler_row_and_resume_owner` first by
constructing valid request/handler/resume Core and independently corrupting the
effect identity, operation identity, input row, output row, resume owner, use
state, and handler nesting. Expected RED: the pure dialect has no production
effect family or validator.

Add a named production effect dialect with typed request, handler, clause, and
resume families. Reuse pure value families and the accepted computation
operation-family seam. Do not add effect variants to each pure feature or
inhabit the pure operation family.

Lower checked source facts into explicit effect Core. Independently validate
canonical effect facts, substituted operation types, node computation types,
row equations, exhaustive coverage, pattern scope, exact discharge, resume
ownership/use/non-escape, provenance, reachability, and empty linked entry.
Extend identity and folding transforms, iterative disposal, and resource
accounting, then revalidate each transform result.

Run:

```text
cargo test --locked --test effect_core --test core_validation
cargo test --locked --test architecture
cargo test --locked --lib -- core
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

Obtain one independent architecture/Core review, correct every Critical or
Important finding, and commit unsigned:

```text
git -c commit.gpgsign=false commit -m "feat: validate effect core"
```

## Checkpoint 4: Execute ordered deep handlers

**Files:**

- Modify: `src/eval/machine.rs`
- Modify as required: `src/driver.rs`
- Create: `tests/effect_runtime.rs`
- Modify: `tests/semantics.rs`
- Modify: `tests/cli.rs`

Write `nested_forwarding_restores_intervening_handlers_in_original_order`
first. Trace an inner nonmatching handler, an outer matching handler, a request
from the outer clause, resume, the restored selected and intervening scopes,
and return to the outer clause. Expected RED: validated effect Core has no
machine entry or transitions.

Extend the explicit machine with an ordered active-handler stack and a distinct
first-order captured-continuation owner. On request, move the ordinary control
segment and intervening handler boundaries above the nearest exact match into
that owner. Run the selected clause outside those boundaries. On resume,
atomically consume the capability, reinstall the selected and intervening
boundaries in their original order, run the captured remainder, unwind it, and
return its result to clause control.

Do not use Rust closures, clone captured control, make ordinary frames
implicitly capturable, or add an unhandled-operation source outcome. A request
or second resume reaching the machine after validation is an internal
invariant failure.

Cover nearest same-instance selection, different-instance forwarding,
same-instance delegation to an outer handler, clause requests bypassing
captured intervening handlers, post-resume clause control, multiple sequential
requests, distinct parameterized instances, exact trace order, deep stacks,
one-short captured-control allocation, atomic failure, retry, and iterative
teardown.

Run:

```text
cargo test --locked --test effect_runtime --test semantics --test cli
cargo test --locked --lib -- eval
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

Obtain one independent evaluator/Rust-resource review, correct every Critical
or Important finding, and commit unsigned:

```text
git -c commit.gpgsign=false commit -m "feat: evaluate effect handlers"
```

## Checkpoint 5: Retain specification and closure evidence

**Files:**

- Modify: `spec/README.md`
- Modify: `spec/lexical-structure.md`
- Modify: `spec/syntax.md`
- Modify: `spec/name-resolution.md`
- Modify: `spec/static-semantics.md`
- Modify: `spec/elaboration.md`
- Modify: `spec/dynamic-semantics.md`
- Modify: `docs/tools/ash.md`
- Create: `docs/design/effect-ash/resume-required-effect-kernel-evidence.md`
- Modify: `tests/spec_examples.rs`
- Modify: `tests/corpus.rs`
- Modify: `tests/architecture.rs`
- Modify: `docs/trajectory.md`

### Step 1: Retain the combined evidence

Add one evidence report mapping each CP-0013 requirement to source, Core,
runtime, diagnostic, resource, and predecessor observations. Add a combined
corpus case which uses open-row relay, two exact effect instances, nested
forwarding handlers, and exactly-once resume. Preserve the pure locality guard
and all predecessor corpus cases.

Commit unsigned after focused tests and diff hygiene:

```text
git -c commit.gpgsign=false commit -m "test: retain effect kernel evidence"
```

### Step 2: Update normative truth

Write the complete grammar, identity, kind, row, inference, handler, resume,
Core, failure, and small-step rules into the affected specification sections.
Every `ebnf` and `sequent` fence receives matching prose. Add executable
positive examples and exact negative reasons. Update tool documentation only
for implemented behavior.

Run:

```text
cargo test --locked --test spec_examples --test corpus --test architecture
markdownlint-cli2 docs spec README.md AGENTS.md
git diff --check
```

Obtain independent semantic/specification, architecture, Rust/resource,
documentation, and simplification reviews. Correct every Critical or Important
finding and repeat affected focused tests. Commit unsigned:

```text
git -c commit.gpgsign=false commit -m \
  "docs: specify resume-required effects"
```

### Step 3: Run the final product gate and clean transition artifacts

Run:

```text
cargo xtask verify
markdownlint-cli2 docs spec README.md AGENTS.md
git diff --check
git status --short
```

Manually check every changed link, artifact authority, formal rule, diagnostic
precedence, exact row/resource formula, Core forgery case, transform
revalidation, runtime trace, pure locality guard, and the absence of excluded
features.

After the complete checkpoint is retained, remove CP-0013, TASK-0020, and this
temporary plan from the product branch and update their indexes. Keep DN-0027,
DN-0028, the normative specification, and the retained evidence report. Commit
the clean transition boundary unsigned:

```text
git -c commit.gpgsign=false commit -m \
  "docs: close resume-required effect transition"
```

Run Markdown lint, link inspection, `git diff --check`, and `git status
--short` once more. Do not merge, push, tag, delete a branch, or remove a
worktree. Report the final product tip and independent review result for a
separate integration decision.
