# Local `newtype` Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use
> superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Add sequential local `newtype` declarations with rigid lexical
identity, identity-free closure escape, authenticated Core scope, and unchanged
allocation-free representation execution.

**Architecture:** Extend the existing module-newtype path rather than creating
a second nominal system. Resolution adds narrow lexical name stacks and retains
local instances of the existing canonical fact shapes under a lexical owner.
Elaboration reuses wrap and unwrap conversions and folds one erased scope node
around the block remainder. Existing iterative type traversal checks outward
escape, and independent Core validation authenticates the scope relation.

**Tech Stack:** Rust 2024, Ash event parser and projected surface tree,
resolver and fixed-kind checker, bidirectional elaborator, typed Pure and Effect
Core, explicit evaluator machine, Cargo integration tests, and Markdown
specification.

---

This temporary plan belongs to
[TASK-0022](../tasks/TASK-0022-implement-local-newtype.md). Accepted
[CP-0014](../proposals/CP-0014-local-newtype.md) alone authorizes semantics.
Current `spec/` remains authoritative until the complete checkpoint lands on
`main`.

Execute in this session with `superpowers:subagent-driven-development`. Use
`superpowers:test-driven-development` and `rust-skills` for implementation,
`superpowers:systematic-debugging` for unexpected failures,
`superpowers:requesting-code-review` at the named gates, and
`superpowers:verification-before-completion` before closure. Use one writer at
a time because all steps share the product worktree. Read-only semantic/Core
and Rust/resource reviews may run in parallel.

Every commit uses `git commit --no-gpg-sign`. Do not merge, push, tag, delete
the branch, remove the worktree, raise a production limit, or add semantics
outside CP-0014.

## Task 1: Authorize and isolate the checkpoint

**Files:**

- Create: `docs/proposals/CP-0014-local-newtype.md`
- Create: `docs/tasks/TASK-0022-implement-local-newtype.md`
- Create: `docs/plans/2026-09-02-local-newtype.md`
- Modify: `docs/proposals/README.md`
- Modify: `docs/tasks/README.md`

### Step 1: Confirm authority and identity

Verify CP-0014 is accepted, TASK-0022 is active, and neither `CP-0014` nor
`TASK-0022` appears earlier in Git history. Confirm the branch root is
`fa26025` and `main` remains at its existing head.

### Step 2: Confirm the isolated baseline

Verify `.worktree/` is ignored and the product worktree is on
`feature/cp0014-local-newtype`. The baseline command is:

```text
CARGO_INCREMENTAL=0 cargo test --locked --workspace
```

Expected: all library, binary, integration, xtask, and doc tests pass.

### Step 3: Validate and commit authorization

Run:

```text
markdownlint --disable MD013 -- docs/proposals docs/tasks docs/plans
git diff --check
git status --short
```

Commit:

```text
git commit --no-gpg-sign -m "docs: authorize local newtype implementation"
```

## Task 2: Project the sequential declaration

**Files:**

- Modify: `src/parser/grammar.rs`
- Modify: `src/parser/project.rs`
- Modify: `src/surface.rs`
- Create: `tests/local_newtypes_syntax.rs`
- Modify: `tests/parser.rs`

### Step 1: Add the syntax RED

Add `local_newtype_projects_as_a_private_sequential_declaration`. Parse:

```ash
main : Unit -> Int
main () = {
    newtype Offset = Offset(Int)
    let value = Offset(42)
    match value { Offset(inner) => inner }
}
```

Assert one local newtype declaration retains its name, constructor, sole
representation field, parameters, declaration span, and position before the
binding. Run:

```text
cargo test --locked --test local_newtypes_syntax \
  local_newtype_projects_as_a_private_sequential_declaration -- --exact
```

Expected RED: block grammar accepts only `let` declarations.

### Step 2: Reuse module-newtype projection

Add `SurfaceLocalDeclaration::Newtype(SurfaceTypeDeclaration)` and admit the
existing `NewtypeDeclaration` node in a block. Project through the existing
one-constructor/one-field helper. Reject `pub` and `opaque` in block position by
the existing parser boundary; do not add a local declaration structure or new
keyword.

### Step 3: Complete syntax evidence

Cover parameters, malformed shape and recovery, a following declaration,
token completeness, visibility-modifier rejection, structural-depth limits,
exact syntax charging, one-short failure, and retry. Preserve module-newtype
and binding projections.

### Step 4: Verify and commit

Run:

```text
cargo test --locked --test local_newtypes_syntax --test parser
cargo test --locked --test newtypes_syntax
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

Commit:

```text
git commit --no-gpg-sign -m "feat: parse local newtype declarations"
```

## Task 3: Resolve lexical identity and canonical facts

**Files:**

- Modify: `src/types.rs`
- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify: `src/kind.rs`
- Modify: `tests/resolution.rs`
- Modify: `tests/kinds.rs`
- Create: `tests/local_newtypes.rs`
- Modify: `tests/architecture.rs`

### Step 1: Add the identity RED

Add `nested_shadowed_local_newtypes_keep_distinct_lexical_identities`. Use an
outer module nominal plus two sequential same-spelled local declarations over
`Int`. Assert that representation resolution sees the preceding identity,
each declaration receives a distinct lexical owner, and leaving each block
restores both type and constructor bindings.

Run:

```text
cargo test --locked --test local_newtypes \
  nested_shadowed_local_newtypes_keep_distinct_lexical_identities -- --exact
```

Expected RED: the surface local declaration has no resolved carrier.

### Step 2: Generalize only nominal ownership

Give `NominalTypeId` an explicit module-or-lexical owner. A lexical owner is
module-qualified and allocated once per source declaration. Preserve the
existing public construction and accessors where module identities are
required, and add narrow checked accessors rather than changing unrelated ID
families. `ConstructorId` continues to contain its nominal owner and ordinal.

Update exhaustive comparisons, rendering, and resource-free scalar carriers
mechanically. Keep equality and ordering injective across owner classes.

### Step 3: Add lexical stacks and reuse fact construction

Extend block resolution checkpoints with lexical nominal and constructor name
stacks consulted before module maps. Resolve declarations left to right. Resolve
the representation under the preceding stack plus its parameter scope, then
install the name/constructor pair for the remainder. Roll back both stacks on
success and every error path.

Extract the reusable part of module-newtype fact construction. Retain local
`ResolvedNominalType`, `ResolvedConstructor`, parameters, representation, and
provenance in a lexical partition. Shared lookup dispatches by owner. Do not
append locals to module declaration arrays or publish them in summaries,
imports, exports, or implementation inventories.

Delay immutable checker-registry publication until body resolution has
finished. Replace any early whole-registry dependency with the narrow fact view
it actually needs; do not clone the registry per declaration.

### Step 4: Reuse kind admission

Register local parameters and nominal kind through the existing kind engine.
Check the representation once after resolution. Sequential scope eliminates a
local cycle pass. Reject self and forward references at resolution, not through
module cycle machinery.

### Step 5: Complete identity and resource evidence

Cover sibling and nested identities, shadowing and restoration, constructor
pairing, parameters and kinds, preceding local/module representations,
self/forward/after-scope failures, use from a following `let rec`, exclusion
from a recursive group, absence from summaries, exact name/fact retention,
one-short atomic failure, retry, and deep stack-safe teardown.

### Step 6: Review and commit lexical identity

Obtain independent compiler/Core and Rust/resource review. Correct every
Critical or Important finding. Run:

```text
cargo test --locked --test local_newtypes --test resolution --test kinds
cargo test --locked --lib -- resolve
cargo test --locked --lib -- resolved
cargo test --locked --lib -- kind
cargo test --locked --test architecture
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

Commit:

```text
git commit --no-gpg-sign -m "feat: retain local newtype identities"
```

## Task 4: Enforce escape and lower lexical scope

**Files:**

- Modify: `src/resolved.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/pattern.rs` only if shared constructor lookup requires it
- Modify: `src/core/dialect.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/core/transform.rs`
- Modify: `src/eval/machine.rs`
- Modify: `src/diagnostic.rs` or the existing typed reason owner
- Modify: `tests/local_newtypes.rs`
- Modify: `tests/core_validation.rs`
- Modify: `tests/semantics.rs`
- Modify: `tests/diagnostics.rs`
- Modify: `tests/architecture.rs`

### Step 1: Add the escape-boundary RED

Add `identity_free_closure_may_capture_a_local_newtype`. Compile and execute
the accepted CP-0014 example. Assert result type `Unit -> Int`, ordinary closure
capture of the erased value, exactly one local scope carrier around the lexical
remainder, wrap/unwrap conversions beneath it, and no ordinary constructor node
or wrapper allocation.

Run:

```text
cargo test --locked --test local_newtypes \
  identity_free_closure_may_capture_a_local_newtype -- --exact
```

Expected RED: local constructor typing and lexical Core scope do not exist.

### Step 2: Reuse typing and conversion lowering

Route local owners through existing canonical nominal and constructor lookup.
Reuse module-newtype constructor scheme synthesis, irrefutable pattern typing,
representation substitution, `NewtypeConversionNode`, and interface-evidence
isolation. The local identity is a rigid nominal constant; do not add it to
generalization candidates.

### Step 3: Check the complete outward boundary

At each local-newtype scope close, zonk the outward computation and use the
existing iterative nominal-identity traversal to inspect its value type, row,
effect arguments, scheme, and requirements. Emit
`type.local-nominal-escape` at the escaping expression or binding and relate it
to the declaration. Accept capture when the exposed computation is
identity-free; do not inspect closure environments as public types.

Add exact positive and negative cases for direct value, constructor, tuple,
nominal application, function domain/codomain, effect argument, generalized
scheme, implicit package, unwrapped representation result, polymorphic
consumption, identity-free closure, and identity-exposing closure.

### Step 4: Add the one Core scope carrier

Add a unary pure local-nominal scope node containing owner and body. Build it at
the elaborator's existing reverse block fold. Include it in typed construction,
origins, reachability, iterative disposal, and both transforms. It contributes
the child's type and effect row unchanged.

Independent validation indexes retained local facts and scope introductions.
Require a one-to-one fact/scope relation, require every local identity use to
occur beneath its owner, and reject the identity in the scope node's own result
type or row. Validate constructor, pattern, conversion, effect metadata, and
all nested type occurrences. Add tamper cases for missing, duplicate,
unmatched, wrong-owner, out-of-scope, and escaping relations.

Evaluation enters the child directly. Add no heap variant, environment entry,
continuation frame, registry lookup, or runtime failure.

### Step 5: Complete Core and runtime evidence

Prove both Core transforms preserve and revalidate nested scopes. Prove pure and
effect dialects both admit the shared static scope node, while local identity
does not change effect-row algebra. Measure no wrapper allocation and run deep
nested accepted and rejected cases on a small host stack. Add exact Core
builder/validator success, one-short failure, retry, and teardown evidence.

### Step 6: Review and commit escape enforcement

Obtain independent semantic/Core and Rust/resource review. Correct every
Critical or Important finding. Run:

```text
cargo test --locked --test local_newtypes --test core_validation
cargo test --locked --test semantics --test diagnostics
cargo test --locked --test architecture
cargo test --locked --lib -- elaborate
cargo test --locked --lib -- core
cargo test --locked --lib -- eval
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

Commit:

```text
git commit --no-gpg-sign -m "feat: enforce local newtype scope"
```

## Task 5: Specify and close the checkpoint

**Files:**

- Modify: `spec/README.md`
- Modify: `spec/syntax.md`
- Modify: `spec/name-resolution.md`
- Modify: `spec/static-semantics.md`
- Modify: `spec/elaboration.md`
- Modify: `spec/dynamic-semantics.md`
- Modify: `tests/spec_examples.rs`
- Modify: `docs/design/DN-0026-effect-ash-resource-first-milestones.md`
- Modify: `docs/design/DN-0027-effect-ash-program-design.md`
- Modify: `docs/design/DN-0028-effect-ash-milestone-plan.md`
- Modify, then remove: `docs/proposals/CP-0014-local-newtype.md`
- Modify, then remove: `docs/tasks/TASK-0022-implement-local-newtype.md`
- Remove: `docs/plans/2026-09-02-local-newtype.md`
- Modify: `docs/proposals/README.md`
- Modify: `docs/tasks/README.md`

### Step 1: Write normative truth with executable examples

Update the linked CP-0014 specification sections. Add one complete executable
identity-free closure example and one stable escape diagnostic example. Keep
module-newtype, effect-kernel, and predecessor examples current. Add manifest
tests for every new normative rule or example.

### Step 2: Reconcile failure and resource formulas

Record actual phase ownership, precedence, exact additive formulas, atomic
publication, retry, and iterative teardown. Remove any planned carrier that the
implementation did not need. If implementation contradicts CP-0014, return to
the proposal instead of changing semantics locally.

### Step 3: Run independent closure reviews

Run independent semantic/specification, compiler/Core, and Rust/resource
reviews. Each reviewer checks CP-0014 and the complete diff from `fa26025`.
Correct every Critical or Important finding and repeat affected tests. This is
a product-checkpoint review, not authorization to merge the Effects Ash
milestone.

### Step 4: Run the full verification gate

Run:

```text
CARGO_INCREMENTAL=0 cargo xtask verify
markdownlint --disable MD013 -- docs spec README.md AGENTS.md
git diff --check
git status --short
```

Check every changed relative link, formal rule, example, diagnostic, Core
carrier inventory, resource formula, and runtime observation manually.

### Step 5: Close transition artifacts

Record verified hashes and review outcomes in TASK-0022. Update the Effects Ash
trajectory to name local `newtype` as implemented on the product branch and
scoped exact evidence as the next checkpoint. Remove CP-0014, TASK-0022, and
this plan; update their indexes. Git preserves the accepted transition.

Commit specification and closure separately:

```text
git commit --no-gpg-sign -m "docs: specify local newtypes"
git commit --no-gpg-sign -m "docs: close local newtype transition"
```

Leave `feature/cp0014-local-newtype` unmerged for checkpoint integration and
keep the Effects Ash milestone unmerged pending its independent final review.
