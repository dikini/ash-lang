# Monomorphic Data and Patterns Shared-Pipeline Implementation Plan

> **For Codex:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to
> implement this plan task-by-task.

**Goal:** Implement CP-0003 through the retained CST, resolution, typed Core,
independent validation, and explicit evaluator machine, then remove the
parallel extended pipeline.

**Architecture:** Feature-owned forms join the existing closed parser and Core
dialect assemblies. Resolution emits stable term, type, and constructor
identities plus immutable registries; typed elaboration emits structured
patterns and matches; validation rechecks Core without surface syntax; the
existing machine gains explicit heap, matching, and initialization work.

**Tech Stack:** Rust 2024, arena-backed typed Core, event-producing recursive
descent parser, explicit evaluator machine, `cargo test`, and `cargo xtask`.

---

### Task 1: Make the shared parser own CP-0003 syntax

**Files:**

- Modify: `src/parser/cst.rs`
- Modify: `src/parser/grammar.rs`
- Modify: `src/parser/expression.rs`
- Modify: `src/parser/project.rs`
- Modify: `src/parser/mod.rs`
- Test: `tests/parser.rs`

**Step 1: Write failing parser tests**

Add direct `parse(lex(source))` tests for a nominal declaration, multiline
constructor list, tuple expression and type, match arms, nested constructor
patterns, tuple-domain header, and contiguous multi-clause equation. Assert
exact node kinds and full source spans without calling `driver::run_source`.

**Step 2: Confirm the retained parser fails**

Run `cargo test --locked --test parser data_and_pattern` and expect failure
because the retained grammar rejects or recovers through the new forms.

**Step 3: Add feature-local concrete forms**

Add concrete node kinds for type declarations, constructors, tuple forms,
patterns, matches, arms, and clauses. Add grammar functions owned by those
forms and list them in the existing closed definition, prefix, pattern, and
type assemblies. Keep application and infix grouping in the existing
expression layer.

**Step 4: Add recovery tests and implementation**

Cover missing constructor payload delimiters, malformed tuple commas, missing
`=>`, missing arm bodies, and a valid construct following each error. Assert
token completeness, exact missing-token positions, balanced recovery, and
projection refusal while a recovery node remains.

**Step 5: Run the parser boundary**

Run `cargo test --locked --test lexer --test parser`; expect all tests to pass.

**Step 6: Commit**

```text
git add src/parser tests/lexer.rs tests/parser.rs
git commit --no-gpg-sign -m "feat: parse data and pattern syntax in retained CST"
```

### Task 2: Project complete Surface forms

**Files:**

- Modify: `src/surface.rs`
- Modify: `src/parser/project.rs`
- Test: `tests/parser.rs`

**Step 1: Write failing projection tests**

Project the positive parser corpus and assert ordered type declarations,
constructor payload types, tuple arity, pattern structure, arm boundaries,
clause grouping, delimiter spans, and whole-node spans.

**Step 2: Confirm projection fails**

Run the focused projection tests and expect unsupported-node or shape failures.

**Step 3: Add Surface representations and iterative projection**

Represent type declarations, constructor declarations, patterns, match arms,
tuple expressions and types, and multi-pattern headers. Preserve spellings and
all causal spans. Extend the existing projection work stacks rather than adding
host recursion at the admitted structural depth.

**Step 4: Add malformed-tree probes**

Construct concrete trees with duplicate children, foreign token indices,
hidden recovery nodes, wrong tuple arity, and out-of-order delimiters. Assert
projection rejects each before Surface escapes.

**Step 5: Verify and commit**

```text
cargo test --locked --test parser
git add src/surface.rs src/parser/project.rs tests/parser.rs
git commit --no-gpg-sign -m "feat: project data syntax into shared Surface"
```

### Task 3: Resolve nominal, constructor, and pattern identities

**Files:**

- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify: `src/types.rs`
- Test: `tests/resolution.rs`

**Step 1: Write failing resolution tests**

Cover self, mutual, and forward payload types; distinct nominal declarations;
file-wide constructors; duplicate type and constructor spellings; unknown type
and constructor names; separate namespaces; nested pattern binders; duplicate
binders across one equation domain; shadowing; and scope restoration after a
failed pattern.

**Step 2: Confirm failure at resolution**

Run `cargo test --locked --test resolution data_and_pattern`; expect Surface to
project while retained resolution lacks the new identities.

**Step 3: Add resolved registries and types**

Add immutable nominal and constructor metadata to `ResolvedProgram`. Allocate
all nominal identities in source order, allocate constructor identities, then
resolve every payload type. Replace resolved-stage `SurfaceType` use with a
resolved type carrying identities.

**Step 4: Resolve patterns with stable binders**

Allocate one `BinderId` per binder definition, attach identities to occurrences,
reject duplicate names across the complete pattern vector, and restore every
scope after success or failure.

**Step 5: Verify and commit**

```text
cargo test --locked --test resolution
git add src/resolved.rs src/resolve.rs src/types.rs tests/resolution.rs
git commit --no-gpg-sign -m "feat: resolve nominal data and pattern identities"
```

### Task 4: Add registry-bearing typed Core families

**Files:**

- Create: `src/core/data.rs`
- Create: `src/core/pattern.rs`
- Modify: `src/core/mod.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/validate.rs`
- Test: `tests/core_validation.rs`

**Step 1: Write malformed-Core tests first**

Add builder-level and validator-level cases for empty declarations, duplicate
or foreign identities, unknown payload types, wrong constructor owner, wrong
payload type, empty or unary tuple types, pattern binder reuse, wrong pattern
type, branch disagreement, foreign child handles, unreachable nodes, and
missing provenance.

**Step 2: Confirm the current Core cannot express or reject them**

Run the new focused `core_validation` tests and expect construction failures or
missing APIs.

**Step 3: Add immutable Core registries**

Make the selected program own validated nominal and constructor registries.
Route all type admission through registry-aware validation. Nominals compare by
identity; tuples and functions compare structurally through `same_type`.

**Step 4: Add feature-local node families**

Represent tuple construction, nullary data, constructor functions, typed
patterns, pattern bindings, structured matches, and guarded recursive data.
Every node and pattern exposes its type and origin. Add them to the one closed
pure-dialect assembly and builder API.

**Step 5: Verify and commit**

```text
cargo test --locked --test core_validation --test architecture
git add src/core tests/core_validation.rs tests/architecture.rs
git commit --no-gpg-sign -m "feat: add typed data and pattern Core families"
```

### Task 5: Elaborate finite tuples and constructors through shared Core

**Files:**

- Modify: `src/elaborate.rs`
- Test: `tests/data_and_adts.rs`
- Test: `tests/diagnostics.rs`
- Test: `tests/provenance.rs`

**Step 1: Add direct shared-elaborator tests**

Bypass `run_source` and call lex, parse, project, resolve, and elaboration
directly for tuple values, nominal inequality, payload constructors as unary
functions, nullary constructors, tuple-domain functions, and constructor
owner/payload mismatches.

**Step 2: Confirm the shared elaborator fails**

Run the focused cases and expect missing-form or typing failures.

**Step 3: Add registry-aware elaboration**

Seed the type context with resolved constructor types. Synthesize tuple and
constructor occurrences and check tuple-domain functions. Emit only the new
typed Core families with complete causal origins.

**Step 4: Verify finite Core without evaluation**

Validate every elaborated program, corrupt one registry and one constructor
node, and assert the independent validator rejects both.

**Step 5: Verify and commit**

```text
cargo test --locked --test data_and_adts --test diagnostics --test provenance
git add src/elaborate.rs tests/data_and_adts.rs tests/diagnostics.rs tests/provenance.rs
git commit --no-gpg-sign -m "feat: elaborate finite data through shared Core"
```

### Task 6: Implement typed patterns and total coverage

**Files:**

- Create: `src/pattern.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/core/validate.rs`
- Test: `tests/data_and_adts.rs`
- Test: `tests/core_validation.rs`

**Step 1: Write failing shared-stage pattern tests**

Cover binders, `_`, Boolean, unit, tuple, nested constructors, duplicate
binders, constructor ownership and payload mismatches, match branch typing,
equation arity, local irrefutability, concrete missing witnesses, and redundant
arms. Pair match and equation cases.

**Step 2: Confirm expected failures**

Run the focused data and Core suites and record that the retained elaborator
does not yet produce structured pattern Core.

**Step 3: Add expected-type pattern checking**

Return a typed pattern plus stable binder facts. Make matches, equations,
operational domains, anonymous domains, and local bindings call the same rule.

**Step 4: Replace fixed-fuel coverage**

Implement usefulness as an explicit worklist with memoized typed matrix states.
Keep useful, not useful, and structured resource failure distinct. Reuse it for
exhaustiveness, redundancy, and irrefutability in elaboration and Core
validation.

**Step 5: Verify boundary depth**

Run nested recursive nominal, tuple, Boolean, and Unit matrices at the admitted
pattern and type depth on a 256 KiB thread stack.

**Step 6: Verify and commit**

```text
cargo test --locked --test data_and_adts --test core_validation
git add src/pattern.rs src/elaborate.rs src/core/validate.rs tests/data_and_adts.rs tests/core_validation.rs
git commit --no-gpg-sign -m "feat: type and validate shared Core patterns"
```

### Task 7: Evaluate finite data and matches in the retained machine

**Files:**

- Modify: `src/eval/value.rs`
- Modify: `src/eval/machine.rs`
- Modify: `src/eval/mod.rs`
- Modify: `src/driver.rs`
- Test: `tests/data_and_adts.rs`
- Test: `tests/semantics.rs`

**Step 1: Write failing machine and trace tests**

Construct validated shared Core directly. Assert strict tuple order, function
before argument, constructor application, one scrutinee evaluation, first-arm
selection, selected-body-only evaluation, lexical capture, and structured
impossible-match failure.

**Step 2: Confirm the retained machine lacks transitions**

Run focused runtime tests and expect unsupported-node failures.

**Step 3: Add heap-backed locations and frames**

Extend `Evaluation` with its per-run heap. Add explicit frames for tuple
elements, constructor calls, match selection, and pattern work. Keep closures
inspectable and keep every continuation as first-order Rust data.

**Step 4: Add iterative matching and rendering**

Match with an explicit work stack. Render with enter and leave frames plus an
active location set so shared acyclic values repeat and active cycles terminate.

**Step 5: Verify and commit**

```text
cargo test --locked --test data_and_adts --test semantics
git add src/eval src/driver.rs tests/data_and_adts.rs tests/semantics.rs
git commit --no-gpg-sign -m "feat: evaluate data and matches in retained machine"
```

### Task 8: Integrate constructor-guarded recursive data

**Files:**

- Modify: `src/elaborate.rs`
- Modify: `src/core/recursion.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/eval/machine.rs`
- Test: `tests/recursion.rs`
- Test: `tests/data_and_adts.rs`

**Step 1: Write failing guardedness and initialization tests**

Cover nullary and payload roots, constructor and tuple paths, delayed function
occurrences, recursive-free leaves, rejected calls, primitives, matches, and
blocks, mixed function/data groups, self cycles, mutual cycles, uninitialized
access, alias loops, and invalid locations.

**Step 2: Confirm retained recursion only admits functions**

Run the focused tests and expect guarded data rejection.

**Step 3: Add the shared guarded-root judgment**

Elaboration and validation independently enforce declared nominal owner, full
constructor application, and permitted recursive-occurrence paths.

**Step 4: Add explicit group initialization states**

Preallocate every member location, install function templates, evaluate guarded
data initializers in source order, store aliases, and then enter the body. Data
lookup returns its location without dereferencing it.

**Step 5: Run deep ownership tests**

Evaluate, render, and destroy the 10,000-member cyclic group and a long heap
graph on a 256 KiB thread stack.

**Step 6: Verify and commit**

```text
cargo test --locked --test recursion --test data_and_adts
git add src/elaborate.rs src/core src/eval/machine.rs tests/recursion.rs tests/data_and_adts.rs
git commit --no-gpg-sign -m "feat: initialize guarded cyclic data in shared machine"
```

### Task 9: Complete transforms, diagnostics, and evidence

**Files:**

- Modify: `src/core/transform.rs`
- Modify: `src/diagnostic.rs`
- Modify: `src/render.rs`
- Modify: `tests/core_validation.rs`
- Modify: `tests/diagnostics.rs`
- Modify: `tests/provenance.rs`
- Modify: `tests/semantics.rs`
- Modify: `docs/design/mini-ash/data-and-patterns/evidence.md`

**Step 1: Write failing transform and provenance tests**

Require identity traversal and literal folding to preserve registries, types,
patterns, matches, binders, origins, and evaluation. Add structural diagnostic
assertions for every CP-0003 reason with primary and related spans.

**Step 2: Extend exhaustive consumers**

Rebuild every new Core family iteratively, validate transformed output, and
evaluate it differentially. Render diagnostics only from structured data.

**Step 3: Repeat maintenance probes**

Mutate one registry accessor, type consumer, Core node family, and machine
transition assembly. Record compiler-discoverable changed sites and revert each
probe.

**Step 4: Update evidence and commit**

```text
cargo test --locked --test core_validation --test diagnostics --test provenance --test semantics
git add src/core/transform.rs src/diagnostic.rs src/render.rs tests docs/design/mini-ash/data-and-patterns/evidence.md
git commit --no-gpg-sign -m "test: complete data pipeline validation evidence"
```

### Task 10: Remove the parallel pipeline and complete the review gate

**Files:**

- Delete: `src/extended.rs`
- Modify: `src/lib.rs`
- Modify: `src/driver.rs`
- Modify: `tests/data_and_adts.rs`
- Modify: `tests/spec_examples.rs`
- Modify: `docs/tasks/TASK-0009-implement-monomorphic-data-and-patterns.md`
- Modify: `docs/design/mini-ash/data-and-patterns/evidence.md`

**Step 1: Make all end-to-end tests use the shared pipeline**

Remove test-only dependencies on `extended` APIs. Assert every CP-0003 example
passes through the ordinary driver and every stage-specific rejection retains
its owning pipeline category.

**Step 2: Delete routing and private representations**

Delete `uses_extended_syntax`, `PipelineFailure::Extended`,
`ExtendedCoreProgram`, and the complete `extended` module. Search for all
remaining references and require no matches.

**Step 3: Run the requirement audit**

Check every CP-0003 evidence bullet against a named test. Check Markdown,
relative links, anchors, authority boundaries, formal notation, exclusions,
and changed composition points. Record review remediation in TASK-0009 and the
retained evidence.

**Step 4: Run complete verification**

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --all-targets
cargo xtask verify
git diff --check
git status --short
```

Expected: all commands pass and the worktree contains only intended final
changes.

**Step 5: Commit the review candidate**

```text
git add -A
git commit --no-gpg-sign -m "refactor: converge data and patterns on shared pipeline"
```

**Step 6: Stop and request review**

Do not merge, sign, remove transition artifacts, or clean up the worktree.
Report the commit sequence, complete verification evidence, requirement audit,
and any remaining deviations. Request review and explicit integration
confirmation.
