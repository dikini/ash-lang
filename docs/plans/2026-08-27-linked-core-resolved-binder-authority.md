# Linked Core Resolved Binder Authority Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Authenticate the stable owner and source order of every resolved global type binder that crosses linked Core validation while preserving generated-binder alpha-renaming and runtime erasure.

**Architecture:** Retain ordered `BinderId -> [TypeVariableId]` rows in the already shared combined `ResolvedRegistry`, authenticate them before publishing `ValidatedInterfaceProgram`, and require module-aware Core validation to match each resolved abstraction to its immediate term-binder owner and exact row. Generated type binders remain local to their abstraction and matching `Forall`; both Core transforms share the immutable registry without copying authority.

**Tech Stack:** Rust, Cargo, Ash's fallible type-work and constraint-work ledgers, immutable `Arc<ResolvedRegistry>`, unit and integration tests.

---

## Governing context

Read before editing:

- `docs/proposals/CP-0009-explicit-kinds-and-higher-kinded-parameters.md`, especially **Core boundary**, **Resources and failure behavior**, and **Required evidence**;
- `docs/tasks/TASK-0016-implement-explicit-kinds-and-higher-kinded-parameters.md`;
- `docs/plans/2026-08-27-linked-core-resolved-binder-authority-design.md`;
- Task 9 in `docs/plans/2026-08-26-explicit-kinds-and-higher-kinded-parameters.md`;
- `docs/decisions/AD-0007-typed-core-dialects.md`; and
- `spec/elaboration.md` only as current normative context, not as authority for
  CP-0009's unimplemented delta.

Use @superpowers:test-driven-development for every behavior change,
@rust-skills for Rust implementation, @superpowers:systematic-debugging for an
unexpected failure, and @superpowers:verification-before-completion before each
commit or completion claim. Do not edit `spec/` before Task 12. Do not change a
production resource limit.

### Task 1: Establish the real linked authority REDs

**Files:**

- Modify: `src/core/validate.rs:3020` (private test module and linked fixture)
- Modify: `tests/core_validation.rs:1-210` (positive linked witness only)

#### Step 1: Tighten the existing positive witness

Change `linked_higher_kinded_core_revalidates_after_both_transforms` so it:

- identifies the exact arrow-kinded abstraction and its matching outer
  `Forall`;
- identifies the exact `TypeApplicationNode` whose function has that scheme;
- asserts the bare `Option` argument and simultaneous substituted result;
- rebuilds identity traversal and literal folding independently from the same
  original `ValidatedProgram`; and
- independently validates and evaluates both outputs.

Keep the existing exact test name:

```rust
#[test]
fn linked_higher_kinded_core_revalidates_after_both_transforms() { /* ... */ }
```

#### Step 2: Add a private linked mutation fixture

Inside `src/core/validate.rs` tests, compile real temporary modules through:

```text
load_module_graph
  -> resolve_module
  -> check_module
  -> link_modules
  -> validate_interface_evidence
  -> Elaborator::for_module_program
  -> synthesize_module_program
  -> finish
```

Return an owning fixture that retains its `ModuleGraph` beside the linked
`UnvalidatedProgram`, module/source relation, and stable global/type-variable
identities needed by each mutation. Derive `&[&SourceFile]` only while that
fixture is alive. Keep mutation access private to the crate test module; do not
add a public testing API.

#### Step 3: Write the cross-owner RED

Use two same-Kind polymorphic globals. Coherently swap their resolved type-
variable identities across each abstraction, matching outer `Forall`, binder
scheme, body annotation, and occurrence. Ask `validate_modules` to reject with
`ValidationReason::Registry` at the owning abstraction.

```rust
#[test]
fn linked_core_rejects_coherent_resolved_binder_owner_swap() {
    let (program, sources, relation, owners) = linked_owner_fixture();
    let tampered = mutate_linked_core(program, Mutation::SwapResolvedOwners(owners));
    let error = validate_modules(tampered, &sources, &relation)
        .expect_err("linked owner authority must reject a coherent swap");
    assert_eq!(error.reason(), ValidationReason::Registry);
}
```

#### Step 4: Run the cross-owner test and confirm RED

Run:

```text
cargo test --locked --lib -- core::validate::tests::linked_core_rejects_coherent_resolved_binder_owner_swap --exact
```

Expected: FAIL because current module-aware validation accepts the coherently
swapped Core.

#### Step 5: Write and run the within-owner order RED

Use one global with two same-Kind parameters. Coherently reorder the identities
through the abstraction, outer `Forall`, scheme body, and occurrences.

Run:

```text
cargo test --locked --lib -- core::validate::tests::linked_core_rejects_coherent_resolved_binder_reorder --exact
```

Expected: FAIL because the flattened canonical map does not retain source
order.

Do not commit while these tests are red.

### Task 2: Retain ordered rows in the combined registry

**Files:**

- Modify: `src/resolved.rs:10520-10775`
- Modify: `src/resolved.rs:10790-11340`
- Modify: `src/resolved.rs:11620-12010`
- Modify: `src/resolved.rs:13980-14035` (exact registry inventory guard)
- Review: `tests/architecture.rs` for a new retained-authority inventory entry

#### Step 1: Add the private retained row

Add a scalar-only record and registry storage:

```rust
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ResolvedGlobalParameterRow {
    owner: BinderId,
    parameters: Box<[TypeVariableId]>,
}

pub struct ResolvedRegistry {
    // existing fields
    global_parameter_rows: Box<[ResolvedGlobalParameterRow]>,
    global_parameter_positions: HashMap<BinderId, usize>,
}
```

Expose crate-private borrowed accessors for deterministic iteration and exact
owner lookup. Do not expose mutation and do not clone Kind, spelling, or
`Origin` into a row.

#### Step 2: Add checked counts and exact precharge

Extend `CombinedRegistryCounts` with the number of non-empty global rows. Reuse
the existing `global_parameters` count for parameter identity slots. Extend the
combined-registry retention formula by:

```text
2 * global_rows + global_parameters
```

Charge row slots, position-index slots, and parameter identity slots before
reserving or retaining any row. Use checked arithmetic and preserve the owning
`ResolvedBuildFailure::TypeResource` reason.

Before aggregate retention precharge, extend `validate_checked_registries` with
a pre-reserved `HashSet<BinderId>` for non-empty scheme owners. Charge its
storage to the constraint ledger, reject duplicate owners there, and update the
exact constraint-work formulas. Retention must not become the first semantic
duplicate check.

#### Step 3: Retain rows without a simultaneous staging copy

In dependency and checked-scheme order:

```rust
if !scheme.scheme.type_parameters.is_empty() {
    let mut parameters = Vec::new();
    parameters
        .try_reserve_exact(scheme.scheme.type_parameters.len())
        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
    parameters.extend(
        scheme
            .scheme
            .type_parameters
            .iter()
            .map(|(identity, _)| *identity),
    );
    builder.retain_global_parameter_row(
        scheme.binder,
        parameters.into_boxed_slice(),
    )?;
}
```

Reject a duplicate owner or parameter, a generated identity, a missing
canonical record, or a nominal parameter. Publish the complete row and its
index atomically. Reuse `validate_checked_registries`' existing global
type-variable uniqueness set; do not allocate a second duplicate-parameter set
during retention or omit it from the formula.

Update the exact no-`..` `ResolvedRegistry` inventory destructure and audit
`tests/architecture.rs` so the new fields cannot bypass future carrier review.

#### Step 4: Add borrowed row tests

Extend the existing wide and malformed combined-registry fixtures to assert:

- deterministic owner and parameter order;
- exact lookup by `BinderId`;
- no row for an empty scheme, interface parameter, nominal parameter, or
  implementation head parameter;
- duplicate owner and duplicate identity rejection; and
- accepted and rejected iterative teardown on a 256 KiB thread.

#### Step 5: Prove exact and one-short retention

Update the existing exact combined-registry formulas and one-short assertions
in `src/resolved.rs:14106-14725`. Assert that the measured delta is exactly
`2S + R`, not a Kind or Origin clone.

Run:

```text
cargo test --locked --lib -- resolved::tests::combine_checked
```

Expected: all matching combined-registry tests pass.

### Task 3: Authenticate rows before Core synthesis

**Files:**

- Modify: `src/evidence_validation.rs:1810-1885`
- Modify: `src/evidence_validation.rs:1974-2105`
- Modify: `src/evidence_validation.rs:4500-4810`
- Modify: `src/resolved.rs` for a private `#[cfg(test)]` registry-row mutation
  helper used by evidence-validation tests
- Modify: `src/driver.rs:680-730` only if phase-ledger evidence requires wiring

#### Step 1: Add a linked row mutation test

Before `ValidatedInterfaceProgram` is published, privately mutate each retained
field independently:

```text
owner
parameter identity
parameter order
row order
row position index
missing row
extra row
duplicate owner
```

Each mutation must fail in linked evidence validation, before Core synthesis,
with the existing internal evidence-validation failure family.

#### Step 2: Compare rows with checked schemes

Extend `authenticate_linked_registry_facts` to walk module groups and non-empty
checked schemes in dependency/declaration order. Require exact row owner and
parameter sequence, exact position index, canonical identity existence, and no
unconsumed row.

Do not reconstruct rows from Core and do not retain group/scheme payloads past
`ValidatedInterfaceProgram` consumption.

#### Step 3: Charge the owning constraint ledger

Charge one deterministic row visit and one identity visit per retained fact.
Do not charge type work because this pass borrows IDs and canonical Kinds and
does not retain or clone a Type or Kind.

#### Step 4: Prove exact, one-short, precedence, and retry

Extend the existing `authenticate_linked_registry_facts` measured tests. A
one-short failure must publish no validated capability; retry with exact work
must succeed; an earlier malformed canonical registry fact must retain
precedence over a later row mismatch.

Run:

```text
cargo test --locked --lib -- evidence_validation::tests::linked_registry
cargo test --locked --test interface_validation
```

Expected: all matching unit tests and the integration test pass.

### Task 4: Enforce resolved owner rows in module-aware Core validation

**Files:**

- Modify: `src/core/validate.rs:390-415`
- Modify: `src/core/validate.rs:1620-1760`
- Modify: `src/core/validate.rs:2015-2075`
- Modify: `src/core/validate.rs:3020-end`

#### Step 1: Independently validate retained row structure

Extend module-aware registry validation to require:

- row and position-index cardinality equality;
- every position to point back to the exact row owner;
- a non-empty parameter list;
- a resolved owner whose module exists in the module/source relation;
- resolved parameter identities with canonical records;
- no parameter owned by an ordered nominal row; and
- uniqueness of row owners and parameter identities.

Traverse the row order already authenticated by linked evidence validation so
failure order remains deterministic. This pass checks the retained registry's
internal structure without reconstructing authority from unchecked Core.

#### Step 2: Derive immediate abstraction owners

During the existing binder scan, retain a charged map from a
`TypeAbstractionNode` initializer `NodeId` to its owning `RecursiveBind` member
`BinderId`. Final linked resolved globals use recursive module groups; a local
sequential `Bind` must never claim registry-row authority. Reject a shared
initializer or duplicate owner association.
Let `O` be the number of retained owner entries. Charge one unit before each
map insertion; the map is validator-local and is discarded on every result.

#### Step 3: Match resolved abstractions to exact rows

Change `collect_type_binders` to accept the derived owner map. For an
abstraction with resolved parameters:

```rust
let owner = abstraction_owners
    .get(&node)
    .ok_or_else(|| ValidationError::new(ValidationReason::Registry, Some(node)))?;
let expected = program
    .registry
    .global_parameters(*owner)
    .ok_or_else(|| ValidationError::new(ValidationReason::Registry, Some(node)))?;
if !abstraction
    .parameters()
    .iter()
    .map(|(identity, _)| *identity)
    .eq(expected.iter().copied())
{
    return Err(ValidationError::new(ValidationReason::Registry, Some(node)));
}
```

Require all parameters in that abstraction to be resolved, compare each Kind
with the canonical record, reject nominal ownership, and consume the row once.
Owner uniqueness already proves that one owner cannot consume two rows, so use
a charged scalar consumed count rather than an additional `S`-cell set. After
the scan, require the consumed count to equal the row count. Remove the module-
aware fallback that accepts canonical map membership without row authority.

Keep single-source `validate` compatible with direct locally assembled Core;
the linked row requirement belongs to `validate_modules`.

#### Step 4: Preserve deterministic failure ownership

Registry/row validation precedes node type and scope validation. For a row
mismatch plus a later ordinary node-type or scope mutation, assert
`ValidationReason::Registry` at the first deterministic owner. Preserve the
existing earlier precedence of registry, envelope, graph, and term-binder
metadata validation. For two row mismatches, assert retained row and arena
traversal order.

#### Step 5: Run the original REDs and confirm GREEN

Run:

```text
cargo test --locked --lib -- core::validate::tests::linked_core_rejects_coherent_resolved_binder_owner_swap --exact
cargo test --locked --lib -- core::validate::tests::linked_core_rejects_coherent_resolved_binder_reorder --exact
```

Expected: both pass with `ValidationReason::Registry`.

#### Step 6: Run the focused validator suite

Run:

```text
cargo test --locked --lib -- core::validate
cargo test --locked --test core_validation
```

Expected: all tests pass without increasing
`CORE_VALIDATION_TYPE_WORK_LIMIT`.

### Task 5: Close generated-binder and linked Core mutation evidence

**Files:**

- Modify: `src/core/validate.rs:3020-end`
- Modify: `src/core/type_ops.rs` only for private mutation support or ownership
  cleanup required by a witnessed test
- Modify: `src/core/dialect.rs` only for private mutation support or exact Core
  construction evidence required by a witnessed test
- Modify: `src/elaborate.rs` only when a linked mutation proves a missing
  generated fact at construction
- Modify: `tests/polymorphism.rs`
- Modify: `tests/interfaces.rs`

#### Step 1: Add generated negative mutations

From real linked Core, independently mutate and reject:

- one generated identity in the abstraction but not its `Forall`;
- generated Kind disagreement;
- duplicate/reused generated identity;
- capture or shadowing;
- escape outside the owning abstraction; and
- malformed abstraction provenance or a source/module relation mismatch.

Assert the existing `TypeOperation`, `TypeScope`, `Provenance`, or `Registry`
owner specified by the first failing relationship. Provenance mutations target
the abstraction `Origin` or its source/module relation; they must not treat the
elaborator's generated identity, allocation ordinal, or original span as
external authority or invent a new exact abstraction-to-declaration span rule.

#### Step 2: Add the alpha-renaming positive

Coherently replace one generated identity with a fresh generated identity in
the abstraction, outer `Forall`, body types, binder types, and only the
occurrences lexically owned by that abstraction. The mutator must track scope
and avoid capture. Fresh module-aware validation must accept it.

```rust
#[test]
fn linked_core_accepts_capture_free_generated_alpha_renaming() { /* ... */ }
```

#### Step 3: Complete the Task 9 relationship matrix

Cover each independently retained relationship named by Task 9:

```text
nominal parameter order and Kind
nominal Kind derivation
resolved identity, Kind, owner, order, and provenance
generated identity, Kind, local ownership, provenance, scope, and shadowing
unary application domain and residual result
abstraction and outer-scheme agreement
type-argument count, order, Kind, and simultaneous result
inference escape
every architecture-listed ordinary kind-Type annotation
```

Reuse a table-driven private mutation enum. Each case must stop at Core
validation before evaluation.

#### Step 4: Verify evaluator observations

In `tests/polymorphism.rs` and `tests/interfaces.rs`, assert higher-kinded
abstraction/application erasure adds no runtime value, interface object,
lookup, frame, or transition. Do not edit `src/eval/machine.rs` unless a test
shows a mechanical `outer_nominal` regression.

Run:

```text
cargo test --locked --test polymorphism
cargo test --locked --test interfaces
```

Expected: all tests pass with unchanged evaluator observations.

### Task 6: Prove transforms and independent revalidation

**Files:**

- Modify: `src/core/transform.rs:138-250` only if a witnessed failure exists
- Modify: `src/core/transform.rs:620-920` (resource and teardown tests)
- Modify: `tests/core_validation.rs:1-210`

#### Step 1: Run the tightened linked positive test

Run:

```text
cargo test --locked --test core_validation linked_higher_kinded_core_revalidates_after_both_transforms -- --exact
```

Expected: PASS. Each transform is rebuilt from the original validated program,
then independently revalidated and evaluated.

#### Step 2: Add authority-preservation assertions

Privately assert both unchecked transform outputs share the exact registry
`Arc` and therefore the exact resolved-global rows. No transform may rebuild,
filter, or clone a row.

#### Step 3: Add folding exact and one-short evidence

The existing exact higher-kinded transform probe covers identity traversal.
Add the corresponding `fold_literal_primitives` exact and one-short probe using
the transform's independent type-work ledger. Assert one-short failure
publishes no program and both accepted and rejected deep payloads dismantle on
a 256 KiB thread.

Run:

```text
cargo test --locked --lib -- core::transform
```

Expected: all transform tests pass and no row work is charged because the
registry is shared.

### Task 7: Publish integrated resource and teardown evidence

**Files:**

- Modify: `src/resolved.rs` tests
- Modify: `src/evidence_validation.rs` tests
- Modify: `src/core/dialect.rs` tests
- Modify: `src/core/transform.rs` tests
- Modify: `src/core/validate.rs` tests
- Modify: `tests/core_validation.rs`

#### Step 1: Measure complete additive formulas

Record exact formulas in test constants and comments for:

- combined-registry row retention (`2S + R` delta);
- combined-registry constraint work for the pre-retention `S`-entry owner-
  uniqueness index;
- linked row authentication;
- Core construction of the carrier-rich linked fixture, with zero resolved-row
  retention work because construction shares the registry `Arc`;
- identity rebuilding, with zero resolved-row retention work;
- folding rebuilding, with zero resolved-row retention work; and
- one cumulative module-aware Core validation pass, including the initializer-
  owner index and row consumption.

Do not infer formulas from limits. Measure the exact fixture and prove each
term through a focused probe. The Core-validation formula must name the row-
structure visits and uniqueness storage, `O` charged initializer-owner map
entries, canonical Kind comparisons, and the scalar consumption count. Do not
hide an `S`-cell bitmap or set behind the scalar term.

#### Step 2: Add one-short atomic failures

For each fallible phase, provide exactly one less unit than measured. Assert the
owning resource reason, no partial publication, and successful retry with the
exact allowance.

#### Step 3: Preserve predecessor witnesses

Re-run the depth-96 pipeline and width-32,767 Core witness. Keep the accepted
validator capacity at 983,040 and the existing width formula unless the new
row-bearing fixture intentionally adds separately published terms.

#### Step 4: Prove small-stack teardown

On 256 KiB worker threads, drop accepted and each rejected state containing
deep Types, Kinds, Origins, transform temporaries, and registry rows. Rows add
only scalar slices and must not create recursive teardown.

Run:

```text
cargo test --locked --lib -- resolved::tests::combine_checked
cargo test --locked --lib -- evidence_validation::tests::linked_registry
cargo test --locked --lib -- core
cargo test --locked --test core_validation
```

Expected: all focused resource and teardown tests pass.

### Task 8: Review, verify, and commit Task 9

**Files:**

- Review: `src/core/type_ops.rs`
- Review: `src/core/dialect.rs`
- Review: `src/core/transform.rs`
- Review: `src/core/validate.rs`
- Review: `src/elaborate.rs`
- Review: `src/resolved.rs`
- Review: `src/evidence_validation.rs`
- Review: `src/driver.rs`
- Review: `tests/core_validation.rs`
- Review: `tests/polymorphism.rs`
- Review: `tests/interfaces.rs`
- Review: `tests/architecture.rs`
- Review: `docs/plans/2026-08-27-linked-core-resolved-binder-authority-design.md`
- Review: `docs/plans/2026-08-27-linked-core-resolved-binder-authority.md`

#### Step 1: Run focused Task 9 gates

Run and read complete output:

```text
cargo test --locked --test core_validation
cargo test --locked --test polymorphism
cargo test --locked --test interfaces
cargo test --locked --lib -- core
cargo check --locked --all-targets
```

Expected: zero failures and zero build errors.

#### Step 2: Run broad regression gates

Run and read complete output:

```text
cargo fmt --check
cargo test --locked --workspace --all-targets --all-features
cargo clippy --locked --workspace --all-targets --all-features -- -D warnings
cargo test --locked --workspace --all-targets --all-features -- --list
cargo xtask verify
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Expected: zero failures, warnings, lint findings, broken documentation, or
whitespace errors.

#### Step 3: Run independent parallel reviews

Dispatch three fresh `gpt-5.6-sol/xhigh` reviewers:

- semantic and CP-0009 conformance;
- adversarial mutation completeness and failure precedence; and
- Rust ownership, exact resources, atomic failure, and small-stack teardown.

Resolve every correctness finding and repeat affected gates. Report each
reviewer's model and reasoning level.

#### Step 4: Audit scope and authority

Confirm:

- no `spec/` file changed;
- no production limit changed;
- generated alpha-renaming remains valid;
- no evaluator value/frame/transition changed;
- the working branch remains `lib-ash-kinds` in the dedicated worktree;
- `main` remains an ancestor and is not checked out or merged; and
- only Task 9 and its approved planning artifacts are included.

#### Step 5: Commit without signing

```text
git add src/core/type_ops.rs src/core/dialect.rs src/core/transform.rs src/core/validate.rs src/elaborate.rs src/resolved.rs src/evidence_validation.rs src/driver.rs tests/core_validation.rs tests/polymorphism.rs tests/interfaces.rs tests/architecture.rs docs/plans/2026-08-27-linked-core-resolved-binder-authority-design.md docs/plans/2026-08-27-linked-core-resolved-binder-authority.md docs/tasks/TASK-0016-implement-explicit-kinds-and-higher-kinded-parameters.md
git -c commit.gpgsign=false commit -m "feat: authenticate linked kinds in Core"
```

Omit unchanged files from `git add`. Inspect the staged diff before committing
and verify the commit is unsigned. Do not merge to `main`.
