# Recursive Function Definitions Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Implement file-wide recursive global functions and explicit local `let rec ... and ...` function groups as the second retained Mini-Ash semantic increment.

**Architecture:** Resolution creates simultaneous binder scope before resolving recursive bodies, while elaboration checks those bodies against already declared monotypes. One typed `RecursiveBind` Core computation holds ordinary function initializers and lowers to a template-only recursive environment frame; recursive references remain binder edges, so Core ownership stays acyclic and runtime frames do not own closures back to themselves.

**Tech Stack:** Rust 2024 edition, event-producing recursive-descent parser, bidirectional typed elaborator, arena-owned typed Core, explicit evaluator machine, Cargo integration tests, Markdown EBNF and sequent specifications.

---

### Task 1: Generalize ordered local declarations without changing behavior

This mechanical preparation separates “a declaration in source order” from
“a nonrecursive binding.” It must preserve every current program before the
recursive variant is added.

**Files:**

- Modify: `src/surface.rs`
- Modify: `src/resolved.rs`
- Modify: `src/parser/project.rs`
- Modify: `src/resolve.rs`
- Modify: `src/elaborate.rs`
- Modify: `tests/parser.rs`
- Modify: `tests/resolution.rs`
- Modify: `tests/bindings.rs`
- Modify: `tests/functions.rs`
- Modify: `tests/provenance.rs`

**Step 1: Record the green characterization boundary**

Run:

```text
cargo test --locked --test parser --test resolution --test bindings --test functions --test provenance
```

Expected: all existing tests pass.

**Step 2: Introduce the ordered declaration containers**

Use these closed containers, initially with only the existing binding variant:

```rust
pub enum SurfaceLocalDeclaration {
    Binding(SurfaceBinding),
}

pub struct SurfaceBlock {
    pub declarations: Vec<SurfaceLocalDeclaration>,
    pub result: Box<SurfaceExpr>,
    pub span: Span,
}
```

Mirror the boundary after resolution:

```rust
pub enum ResolvedLocalDeclaration {
    Binding(ResolvedBinding),
}

pub struct ResolvedBlock {
    pub declarations: Vec<ResolvedLocalDeclaration>,
    pub result: Box<ResolvedExpr>,
    pub span: Span,
}
```

Rename projector work records from bindings to declarations. Update resolver
and elaborator work stacks to match the variant explicitly while retaining
initializer-before-binder scope and right-to-left Core folding.

**Step 3: Use compiler and one-search discovery**

Run:

```text
cargo check --locked --all-targets
rg -n '\.bindings|bindings:' src tests
```

Expected: compiler errors and the search locate every old block-field consumer;
remaining `bindings` names refer only to internal stacks or semantic binding
payloads, not `SurfaceBlock` or `ResolvedBlock` fields.

**Step 4: Verify behavior preservation**

Run:

```text
cargo test --locked --all-targets
```

Expected: all baseline tests pass with no language-behavior change.

**Step 5: Commit the refactor unsigned**

```text
git add src tests
git -c commit.gpgsign=false commit -m "refactor: represent ordered local declarations"
```

### Task 2: Add recursive groups to typed Core and the explicit machine

This slice creates the semantic target independently from surface syntax. Its
tests construct Core directly so malformed states remain testable.

**Files:**

- Create: `src/core/recursion.rs`
- Modify: `src/core/mod.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/core/transform.rs`
- Modify: `src/eval/machine.rs`
- Modify: `src/eval/value.rs`
- Modify: `src/resolved.rs`
- Modify: `tests/core_validation.rs`
- Modify: `tests/semantics.rs`
- Modify: `tests/architecture.rs`

**Step 1: Write failing Core-construction and validation tests**

Add tests that require an API shaped like:

```rust
let root = builder.recursive_binding(
    vec![(function_binder, function_node)],
    body,
    Type::Int,
    origin,
)?;
```

Cover a valid one-member group and rejection of:

- an empty group;
- a repeated binder capability;
- an integer initializer;
- a function whose type differs from its binder;
- a recursive occurrence outside its group;
- a foreign child or binder;
- an ownership cycle made by test-only Core corruption.

Run:

```text
cargo test --locked --test core_validation recursive -- --nocapture
```

Expected: compilation fails because recursive Core APIs do not exist.

**Step 2: Implement the feature-owned Core payload**

Add a local family with inspectable members:

```rust
pub struct RecursiveBindingMember {
    binder: TypedBinder,
    initializer: NodeId,
}

pub struct RecursiveBindingNode {
    members: Box<[RecursiveBindingMember]>,
    body: NodeId,
}
```

Add `PureComputation::RecursiveBind`. Keep member order stable and expose
read-only accessors. The builder checks arena capabilities but deliberately
allows malformed empty, duplicate, and non-function groups so the independent
validator owns those invariants.

Replace the fixed `[Option<NodeId>; 2]` child contract with an allocation-free
indexed contract:

```rust
impl PureExprKind {
    pub(super) fn child_count(&self) -> usize;
    pub(super) fn child_at(&self, index: usize) -> Option<NodeId>;
}
```

Update graph validation, free-binder analysis, postorder transformation, and
all exhaustive closed-dialect matches. A recursive group contributes every
initializer followed by its body. Scope analysis unions all child requirements
and removes every member binder from the group result.

**Step 3: Verify Core rejection and transforms**

Run:

```text
cargo test --locked --test core_validation recursive -- --nocapture
cargo test --locked --test semantics identity_traversal_preserves_recursive_groups -- --exact
```

Expected: the valid group validates, every malformed case has the intended
`ValidationReason`, and identity traversal preserves member order, binder
identity, types, origins, and shared edges.

**Step 4: Write failing direct-machine tests**

Construct validated Core for two members where `first` calls `second` and
`second` retains an unused reference to `first` before returning `42`. Add a
lexical-scope test in which caller bindings use the same spelling but different
binder identities. Assert that recursive lookup captures the definition frame,
not the caller environment.

Run:

```text
cargo test --locked --test semantics recursive_machine -- --nocapture
```

Expected: failure because the evaluator has no recursive-binding transition.

**Step 5: Implement template-only recursive environment frames**

Refactor environment entries into ordinary value entries and recursive group
entries. A recursive template contains only:

```rust
struct RecursiveFunctionTemplate {
    binder: BinderId,
    parameter: BinderId,
    body: NodeId,
    origin: Origin,
}
```

Sort templates by `BinderId::value()` and use binary search at lookup. Store the
visible environment length on each frame so lookup can materialize:

```rust
Closure {
    parameter,
    body,
    program: Arc::clone(program),
    environment: Environment::rooted_at(group_frame),
    origin,
}
```

The group frame owns its lexical parent and templates, never closures. Update
iterative environment destruction to detach the parent and closure captures of
ordinary entries while treating recursive templates as leaf payloads. Entering
`RecursiveBind` extends the environment once and evaluates its body directly.

**Step 6: Verify runtime ownership and transition locality**

Run:

```text
cargo test --locked --test semantics recursive_machine -- --nocapture
cargo test --locked eval::machine -- --nocapture
cargo test --locked --test architecture
```

Expected: recursive calls return `42`, lexical capture uses the definition
frame, environment destruction passes on a 256 KiB test stack, and the
transition-ownership table names the recursive feature's entry owner.

**Step 7: Commit the Core/runtime slice unsigned**

```text
git add src/core src/eval src/resolved.rs tests/core_validation.rs tests/semantics.rs tests/architecture.rs
git -c commit.gpgsign=false commit -m "feat: represent and evaluate recursive Core groups"
```

### Task 3: Parse and project explicit local recursive groups

**Files:**

- Modify: `src/lexer/token.rs`
- Modify: `src/lexer/mod.rs`
- Modify: `src/parser/mod.rs`
- Modify: `src/parser/grammar.rs`
- Modify: `src/parser/project.rs`
- Modify: `src/surface.rs`
- Modify: `tests/lexer.rs`
- Modify: `tests/parser.rs`

**Step 1: Write failing token and positive parser tests**

Test `rec` and `and` as exact reserved-word tokens while `record` and
`android` remain identifiers. Parse and project:

```ash
{
    let rec first : Unit -> Int = fn(ignored) {
        second ()
    }
    and second : Unit -> Int = fn(ignored) {
        42
    }
    first ()
}
```

Assert one `SurfaceLocalDeclaration::Recursive` with two ordered members and
exact group, member, binder, annotation, initializer, and delimiter spans.

Run:

```text
cargo test --locked --test lexer recognizes_recursion_reserved_words -- --exact
cargo test --locked --test parser projects_recursive_group -- --exact
```

Expected: failures because `rec`, `and`, and recursive CST nodes are absent.

**Step 2: Implement the grammar-owned syntax**

Add `TokenKind::Rec` and `TokenKind::And`, and add:

```rust
pub enum SurfaceLocalDeclaration {
    Binding(SurfaceBinding),
    Recursive(SurfaceRecursiveGroup),
}

pub struct SurfaceRecursiveGroup {
    pub members: Vec<SurfaceRecursiveMember>,
    pub span: Span,
}
```

The member stores a required `SurfaceType`, an arbitrary `SurfaceExpr`
initializer, and exact spans. Add `NodeKind::RecursiveBindingGroup` and
`NodeKind::RecursiveBindingMember`. Parse another member only when a consumed
logical line end is followed by `and`; otherwise leave the group's final line
end for the owning block. Update exact concrete-tree shape validation and
iterative projection.

**Step 3: Add failing recovery tests**

Cover:

- `let rec name = ...` with a missing annotation;
- `let rec name : T =` with a missing initializer;
- `and` followed by a line end or block close;
- stray `and` outside a recursive group;
- one malformed member followed by a valid later declaration and result;
- projection refusal while any missing or error node remains.

Require dedicated `ParseReason::ExpectedRecursiveMember` and
`ParseReason::UnexpectedAnd` where the source fact is specific. Verify primary
and synchronization spans.

Run:

```text
cargo test --locked --test parser recursive_group_recovery -- --nocapture
```

Expected: the new recovery assertions fail before implementation.

**Step 4: Implement bounded group recovery**

Synchronize a failed member at its logical line end, the enclosing `}`, or EOF.
Do not consume a valid later block result as the missing initializer. Preserve
balanced parser events and let the existing projection boundary reject every
recovery-bearing tree.

**Step 5: Verify the parser slice**

Run:

```text
cargo test --locked --test lexer --test parser
```

Expected: all lexer and parser tests pass, including existing precedence and
structural-depth cases.

**Step 6: Commit the syntax slice unsigned**

```text
git add src/lexer src/parser src/surface.rs tests/lexer.rs tests/parser.rs
git -c commit.gpgsign=false commit -m "feat: parse local recursive groups"
```

### Task 4: Resolve and elaborate simultaneous recursive scope

This is the first end-to-end source slice. It also changes globals from
sequential bindings to one file-wide recursive group.

**Files:**

- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/source.rs`
- Create: `tests/recursion.rs`
- Modify: `tests/resolution.rs`
- Modify: `tests/functions.rs`
- Modify: `tests/provenance.rs`
- Modify: `tests/diagnostics.rs`
- Modify: `tests/bindings.rs`

**Step 1: Write failing resolution tests**

Add isolated tests for:

- global self use;
- a global forward reference;
- mutual global references across equational and operational presentations;
- local self and mutual references;
- local forward reference within one group;
- capture of an outer binder;
- shadowing an outer binder by a group member;
- duplicate names within one group with a related first-definition label;
- ordinary `let value = value` still failing with `resolve.unknown-name`;
- a name outside its recursive group remaining unavailable;
- scope-stack restoration after a member-body failure.

Run:

```text
cargo test --locked --test resolution recursive -- --nocapture
```

Expected: current global recursion fails as unknown and resolved recursive-group
types are missing.

**Step 2: Implement two-pass global resolution**

In the first pass, validate equation-name agreement and global-name freshness,
allocate every global binder, record duplicate provenance, and install the
complete file scope. In the second pass, allocate parameters and resolve every
body against that file scope plus its parameter scope. Do not let a body
failure leak a parameter scope.

**Step 3: Implement local group resolution**

Add:

```rust
pub enum ResolvedLocalDeclaration {
    Binding(ResolvedBinding),
    Recursive(ResolvedRecursiveGroup),
}
```

When the work stack reaches a recursive group, allocate all members, reject a
duplicate spelling, insert every member into the current block scope, then
resolve every initializer. Retain the simultaneous scope for later declarations
and the block result. Keep each occurrence's source origin and stable binder
identity.

**Step 4: Verify resolution before typing**

Run:

```text
cargo test --locked --test resolution
```

Expected: all old sequential-local tests and new recursive/global scope tests
pass.

**Step 5: Write failing monomorphic elaboration tests**

In `tests/recursion.rs`, require exact successful observations for:

```ash
first : Unit -> Int
first ignored = second ()

fn second(ignored : Unit) -> Int {
    let retain : Unit -> Int = fn(value) {
        first value
    }
    42
}

first ()
```

and the analogous local `let rec ... and ...` program. Add failures for a body
result mismatch, an argument mismatch, `let rec value : Int = 1`, and a block
that computes a function rather than using `fn` directly.

Run:

```text
cargo test --locked --test recursion -- --nocapture
```

Expected: failures because recursive groups do not enter the type context or
lower to Core.

**Step 6: Add initialization safety and monomorphic group checking**

Add `TypeReason::UnsafeRecursiveInitializer` with stable display text
`recursion.unsafe-initializer`. Before mutating the group type context, inspect
every initializer and reject any kind other than `ResolvedExprKind::Function`.
The diagnostic uses the initializer as primary, relates the group and
annotation, and offers direct `fn` initialization as help.

For globals, lower every explicit interface, materialize every global typed
binder, and insert all global `TypeFact`s before checking any body. For a local
group, lower all required annotations, materialize and insert all member typed
binders, then check every function against its declared monotype. Remove the
whole group from the context only when leaving the block.

Do not modify `src/types.rs` or introduce inference variables, generalization,
recursive types, or polymorphic recursion.

**Step 7: Lower both scope forms through one recursive Core node**

Accumulate each typed binder and checked function initializer in source order,
then call `CoreBuilder::recursive_binding`. Use
`GeneratedReason::RecursiveBindingLowering` for the group node while retaining
existing `FunctionLowering` and `TypeChecking` causes on members and bodies.
When a file has no globals, retain the result as the root without manufacturing
an empty group.

Update old tests that intentionally asserted global `Bind` roots: they must now
inspect one `RecursiveBind` while local ordinary bindings remain `Bind`.

**Step 8: Verify end-to-end recursive behavior**

Run:

```text
cargo test --locked --test recursion --test resolution --test functions --test bindings --test provenance --test diagnostics
```

Expected: both presentations and local groups return `42`, rejected programs
stop at their owning source stage, and existing nonrecursive local behavior is
unchanged.

**Step 9: Commit the front-end integration unsigned**

```text
git add src/resolved.rs src/resolve.rs src/elaborate.rs src/source.rs tests
git -c commit.gpgsign=false commit -m "feat: resolve and elaborate recursive functions"
```

### Task 5: Complete validation, provenance, diagnostic, and depth evidence

**Files:**

- Modify: `tests/core_validation.rs`
- Modify: `tests/recursion.rs`
- Modify: `tests/semantics.rs`
- Modify: `tests/provenance.rs`
- Modify: `tests/diagnostics.rs`
- Modify: `tests/cli.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/core/transform.rs`
- Modify: `src/eval/machine.rs`
- Modify: `src/main.rs` only if an exact CLI test exposes a rendering defect

**Step 1: Add the full malformed-Core matrix**

Write focused tests for all CP-0002 validator obligations, including empty and
duplicate groups, non-function initializer, member/type disagreement, missing
scope, foreign handles, invalid binder and group provenance, ownership cycles,
and unreachable children. Assert the exact `ValidationReason` and associated
node.

Run:

```text
cargo test --locked --test core_validation recursive -- --nocapture
```

Expected: any uncovered invariant fails before the validator is completed.

**Step 2: Add transform and provenance preservation tests**

Assert that identity traversal retains group/member order, binder identities,
types, member origins, group origin, and recursive variable occurrences. Put a
foldable primitive inside one recursive function body and verify that constant
folding rebuilds the group, validates independently, and preserves evaluation.

Assert exact spans for the local group, member name, annotation, initializer,
parameter, body, recursive occurrence, generated group, and both global
presentations.

Run:

```text
cargo test --locked --test semantics recursive -- --nocapture
cargo test --locked --test provenance recursive -- --nocapture
```

Expected: failures identify any missing traversal or cause relationship.

**Step 3: Add exact source and CLI diagnostics**

Cover missing member, stray `and`, missing annotation, unsafe integer
initializer, unsafe computed-function initializer, duplicate group member,
recursive body mismatch, and recursive argument mismatch. Assert reason,
primary and related spans, expected/found values, help, exit status `1`, empty
stdout, and stable stderr reason.

Run:

```text
cargo test --locked --test diagnostics recursive -- --nocapture
cargo test --locked --test cli recursive -- --nocapture
```

Expected: exact diagnostics pass without renderer string parsing in semantic
tests.

**Step 4: Add deep group, call, and drop tests**

Generate 10,000 annotated functions. Each function except the last computes
`1 + next ()`; the last retains an unused reference to the first and returns
`1`. Run resolution, elaboration, validation, and evaluation on a thread with a
small Rust stack. Assert result `10000`, substantial explicit machine-frame
growth, and successful destruction.

Add a direct-Core 50,000-member environment destruction test on a 256 KiB
stack. Inspect strong counts around one materialized recursive closure to prove
that the group frame has no owning edge back from its templates.

Run:

```text
cargo test --locked --test recursion deep -- --nocapture
cargo test --locked eval::machine::tests::recursive -- --nocapture
```

Expected: completion without Rust stack overflow, leaks, or dynamic-scope
capture.

**Step 5: Run the broad implementation suite**

Run:

```text
cargo test --locked --all-targets
```

Expected: all existing and recursive implementation tests pass.

**Step 6: Commit hardening unsigned**

```text
git add src tests
git -c commit.gpgsign=false commit -m "test: harden recursive function semantics"
```

### Task 6: Update the corpus, normative specification, and executable docs

Specification edits happen only after implementation evidence exists, and land
in the same branch as that evidence.

**Files:**

- Create: `tests/fixtures/recursion/valid/global-mutual.ash`
- Create: `tests/fixtures/recursion/valid/local-mutual.ash`
- Create: `tests/fixtures/recursion/type/unsafe-initializer.ash`
- Delete: `tests/fixtures/first-stratum/resolve/excluded-recursion.ash`
- Delete: `tests/fixtures/first-stratum/resolve/excluded-forward-reference.ash`
- Modify: `tests/corpus.rs`
- Modify: `tests/spec_examples.rs`
- Modify: `spec/README.md`
- Modify: `spec/lexical-structure.md`
- Modify: `spec/syntax.md`
- Modify: `spec/name-resolution.md`
- Modify: `spec/static-semantics.md`
- Modify: `spec/elaboration.md`
- Modify: `spec/dynamic-semantics.md`
- Modify: `docs/tools/ash.md`

**Step 1: Add failing retained-corpus and documentation tests**

Move the former recursion and forward-reference exclusions into positive
coverage and add the mutual global, mutual local, and unsafe-initializer cases.
Extend `tests/spec_examples.rs` with constants for every new source block that
the specification and tool guide will publish.

Run:

```text
cargo test --locked --test corpus --test spec_examples
```

Expected: documentation assertions fail until normative pages contain the
implemented examples.

**Step 2: Update lexical and syntax truth**

Add `rec` and `and` to the normative token/reserved-word lists. Replace the
block grammar with the accepted `local_declaration`,
`recursive_binding_group`, and `recursive_member` productions. Explain the
logical-line grouping and show one executable local group. Every production
uses `::=` and ends in `;`; prose accompanies the `ebnf` fence.

**Step 3: Update resolution and static semantics truth**

Replace sequential global scope with file-wide simultaneous scope. Describe
local group allocation, visibility, duplicates, shadowing, and the continued
nonrecursion of ordinary `let`.

Add the initialization-safety judgment and the accepted typing rules from
CP-0002. State explicitly that recursive checking uses declared monotypes and
adds no type form, inference variable, generalization, or recursive-type rule.
Every `sequent` family receives a consistent verbal explanation.

**Step 4: Update elaboration and small-step truth**

Describe one recursive Core group, acyclic binder references, function
presentation convergence, and provenance. Add `E-Let-Rec`,
`E-Rec-Apply-Argument`, and `E-Rec-Beta` to the sole normative small-step
relation. Explain `rec_closure`, simultaneous capture-avoiding substitution,
and strict evaluation.

**Step 5: Update current-Ash and executable documentation**

Describe recursive functions in `spec/README.md`. Add a complete recursive
`42 : Int` example to `docs/tools/ash.md` without changing invocation syntax or
exit policy.

**Step 6: Verify executable documentation**

Run:

```text
cargo test --locked --test corpus --test spec_examples --test cli
```

Expected: all published source examples execute or reject with their documented
structured reason and exact CLI observation.

**Step 7: Commit specification and docs unsigned**

```text
git add spec docs/tools tests/corpus.rs tests/spec_examples.rs tests/fixtures
git -c commit.gpgsign=false commit -m "docs: specify recursive function definitions"
```

### Task 7: Distill cross-stage maintenance evidence

**Files:**

- Create: `docs/design/mini-ash/recursive-definitions/evidence.md`
- Modify: `docs/design/DN-0019-primitive-feature-composition.md`
- Modify: `docs/tasks/TASK-0008-implement-recursive-function-definitions.md`

**Step 1: Measure the production diff**

Run and retain the observations needed for the evidence report:

```text
git diff --numstat main...HEAD -- src
git diff --name-only main...HEAD -- src | sort
git diff main...HEAD -- src | rg '^\+.*(Recursive|recursive|Rec|rec_)' -n
```

Classify changes as feature-owned behavior, central closed-dialect joins,
cross-stage representation changes, or unrelated test/document updates. Record
the number of production files and explicit dispatch sites without claiming
that line count measures semantic difficulty.

**Step 2: Probe maintenance discovery**

In an uncommitted patch, rename one recursive member accessor, change the child
iteration contract, and add one field to `RecursiveFunctionTemplate`. Run
`cargo check --all-targets` after each mutation and record whether compiler
errors find all updates. Revert only those deliberate probe edits with
`apply_patch`; do not discard other worktree changes.

Also record one stable `rg` query that finds all recursive Core dispatch joins.

**Step 3: Write and link the evidence**

The evidence report must distinguish:

- what localized in `src/core/recursion.rs` or recursive evaluator helpers;
- what necessarily changed because ordered declarations and closed staged
  representations crossed the pipeline;
- which joins were compiler-discoverable or required semantic inspection;
- how reuse of functions and one recursive binding form avoided thunks,
  recursive types, and continuation machinery;
- which findings transfer to ADTs and which remain specific to recursion.

Add a concise “recursive-definition transfer” subsection to DN-0019 linking the
report. Update TASK-0008 discoveries and progress with factual evidence.

**Step 4: Verify documentation boundaries**

Run:

```text
git diff --check
rg -n 'current Ash|normative|accepted|proposed|informative' docs/design/mini-ash/recursive-definitions/evidence.md docs/design/DN-0019-primitive-feature-composition.md docs/tasks/TASK-0008-implement-recursive-function-definitions.md
```

Expected: the report treats implementation as evidence, DN-0019 as
informative, CP-0002 as the transition authority, and `spec/` as current
language truth after the implementation branch is complete.

**Step 5: Commit evidence unsigned**

```text
git add docs/design docs/tasks/TASK-0008-implement-recursive-function-definitions.md
git -c commit.gpgsign=false commit -m "docs: distill recursive feature integration evidence"
```

### Task 8: Verify, audit, and prepare review

**Files:**

- Modify: `docs/tasks/TASK-0008-implement-recursive-function-definitions.md`
- Modify: `docs/proposals/CP-0002-recursive-function-definitions.md` only if an
  implementation discovery requires an explicitly reviewed proposal correction
- Delete later, only after verified completion: `docs/plans/2026-08-22-recursive-function-definitions.md`
- Delete later, only after verified completion: `docs/tasks/TASK-0008-implement-recursive-function-definitions.md`
- Delete later, only after verified completion: `docs/proposals/CP-0002-recursive-function-definitions.md`

**Step 1: Run formatting and focused structural searches**

Run:

```text
cargo fmt --check
git diff --check
rg -n 'PureComputation::' src tests
rg -n 'SurfaceLocalDeclaration|ResolvedLocalDeclaration' src tests
rg -n 'RecursiveBind|recursive_binding' src tests
rg -n 'unsafe-initializer|ExpectedRecursiveMember|UnexpectedAnd' src tests spec docs/tools
```

Expected: every closed consumer is reviewed, every stage boundary is covered,
and no stale sequential-global claim remains in normative or tool docs.

**Step 2: Run the complete repository verifier**

Run:

```text
cargo xtask verify
```

Expected: formatting, build, clippy, all tests, and rustdoc pass.

**Step 3: Perform the CP-0002 completion audit**

For every proposed behavior, semantic delta, resulting truth, non-goal, and
required-evidence bullet, cite a current file, exact test, command result, or
inspection. Treat missing or indirect evidence as incomplete and add the
necessary test or implementation before proceeding.

Explicitly audit:

- ordinary `let` initializer scope;
- direct-function-only initialization;
- all-global and one-group simultaneous scope;
- unchanged `Type` algebra;
- acyclic Core ownership;
- no template-to-closure environment cycle;
- lexical rather than caller capture;
- explicit machine depth rather than Rust call depth;
- executable documentation and exact CLI output;
- intentional exclusion of cyclic data and effects.

**Step 4: Review the complete branch diff**

Run:

```text
git status --short --branch
git log --oneline --decorate main..HEAD
git diff --stat main...HEAD
git diff --check main...HEAD
```

Inspect every production and normative-document change. Resolve findings and
rerun `cargo xtask verify` after any correction.

**Step 5: Record final task evidence and commit unsigned**

Update TASK-0008 progress, verification, discoveries, and deviations with the
actual commands and outcomes. Commit the reviewable state unsigned:

```text
git add docs/tasks/TASK-0008-implement-recursive-function-definitions.md
git -c commit.gpgsign=false commit -m "docs: record recursive implementation verification"
```

**Step 6: Stop for user review and merge confirmation**

Report the branch, worktree, commits, verifier result, requirement audit, and
material design findings. Do not merge. After the user reviews and explicitly
confirms integration, remove the completed CP, task, and execution plan as
required by the artifact lifecycle, commit that cleanup unsigned on the
feature branch, rerun verification, and create only the final merge commit with
GPG signing enabled.
