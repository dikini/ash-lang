# First Mini-Ash Nucleus Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to implement this plan task by
> task, with specification and code-quality review after each task.

**Goal:** Implement accepted CP-0001 as the first retained `ash
<source-file>` interpreter, with tests and normative specification.

**Architecture:** One Rust crate owns a staged pipeline from UTF-8 source through
lexer, event parser, recovery-free surface projection, resolution,
bidirectional typed elaboration, independently validated pure Core, and an
explicit evaluator machine. Feature-local modules feed closed parser and Core
dialect assembly points. Structured failures and causal source origins cross
stage boundaries without becoming strings.

**Tech Stack:** Rust 1.97.1, Cargo, the Rust standard library, and exactly
`num-bigint` 0.5.1 with default features disabled and only `std` enabled.

---

## Authority and execution rules

- [CP-0001](../proposals/CP-0001-first-mini-ash-nucleus.md) exclusively owns
  language behavior.
- [TASK-0006](../tasks/TASK-0006-implement-first-mini-ash-nucleus.md) owns this
  temporary plan.
- AD-0004 through AD-0008 constrain the implementation boundaries.
- Before editing product code, use `superpowers:using-git-worktrees` to
  create an isolated worktree on branch `task/0006-first-mini-ash`.
- Before every Rust implementation task, use
  `superpowers:test-driven-development` and `rust-skills`.
- Implement each task through `superpowers:subagent-driven-development` with a
  fresh implementer, specification-compliance review, and code-quality review.
  Resolve and re-review every finding before proceeding.
- Treat each listed group of failing tests as an ordered series of the smallest
  useful red-green cycles: add one behavior, run its focused test and observe
  the expected failure, add only enough production code to pass, and rerun it.
  The grouped steps are coverage checklists, not permission to write all tests
  or production code in one batch.
- After every task, run its focused tests and `cargo xtask verify`, then commit
  with `git commit --no-gpg-sign` after both reviews approve it.
- Before every commit, run `git status --short`, review the unstaged diff only
  for the task-owned paths, stage only those explicit paths, run
  `git diff --cached --check`, and review `git diff --cached`. Stop if any
  unrelated user or agent change overlaps a task-owned path.
- Do not decide a semantic gap in code. Record it in TASK-0006 and return to
  CP-0001.
- Do not merge. Final integration requires independent whole-change review,
  fresh verification, explicit user confirmation, and a GPG-signed merge.

## Target source layout

```text
src/
  lib.rs
  main.rs
  source.rs
  integer.rs
  diagnostic.rs
  lexer/
    mod.rs
    token.rs
  parser/
    mod.rs
    cst.rs
    event.rs
    expression.rs
    grammar.rs
    project.rs
  surface.rs
  resolved.rs
  resolve.rs
  types.rs
  elaborate.rs
  core/
    mod.rs
    binding.rs
    dialect.rs
    function.rs
    literal.rs
    primitive.rs
    transform.rs
    validate.rs
    variable.rs
  eval/
    mod.rs
    machine.rs
    value.rs
  driver.rs
  render.rs
tests/
  architecture.rs
  cli.rs
  corpus.rs
  diagnostics.rs
  semantics.rs
  fixtures/first-stratum/
    valid/
    parse/
    resolve/
    type/
docs/tools/
  README.md
  ash.md
spec/
  README.md
  lexical-structure.md
  syntax.md
  name-resolution.md
  static-semantics.md
  elaboration.md
  dynamic-semantics.md
```

Keep private helpers beside the feature that owns them. `parser::grammar`
and `core::dialect` are the only closed assembly modules. Do not replace
these modules with one parser function, one semantic-expression enum containing
all feature data directly, or one evaluator transition function containing all
feature behavior.

### Task 1: Establish the worktree, dependency evidence, and integer type

**Files:**

- Modify: `Cargo.toml`
- Modify: `Cargo.lock`
- Modify: `src/lib.rs`
- Create: `src/integer.rs`
- Create: `tests/integer.rs`
- Modify:
  `docs/tasks/TASK-0006-implement-first-mini-ash-nucleus.md`

#### Task 1, step 1: Create and verify the isolated worktree

Use `superpowers:using-git-worktrees`. Create branch
`task/0006-first-mini-ash`, then run:

```bash
git status --short --branch
cargo xtask verify
```

Expected: the task branch is clean and every baseline verification step passes.

#### Task 1, step 2: Add the exact dependency candidate

Add the candidate without a floating compatible-version range or mutable
default-feature set:

```toml
[dependencies]
num-bigint = { version = "=0.5.1", default-features = false, features = ["std"] }
```

Resolve `Cargo.lock`, but do not write the integer wrapper yet.

#### Task 1, step 3: Admit the resolved dependency graph

Run:

```bash
cargo tree --edges normal
cargo tree -e features -i num-bigint
cargo audit
cargo deny check advisories sources bans
cargo metadata --locked --format-version 1 | jq -r '.packages[] | [.name, .version, (.license // "MISSING"), (.source // "workspace")] | @tsv'
```

Inspect the exact resolved versions, every non-workspace package's SPDX
expression or reviewed license files, enabled features, target metadata, and
upstream unsafe sites. Do not add a provisional license allowlist while Ash's
license is unselected. Record the expected `RUSTSEC-2021-0090` warning as a
name collision with the unrelated crates.io `ash` package, and confirm that
`cargo audit` still exits successfully and reports no dependency advisory.
Update TASK-0006's dependency record. Stop and remove the candidate if
advisories, ambiguous licensing, native target restrictions, unexpected
features, or unsafe-code findings contradict the preflight.

#### Task 1, step 4: Write the failing arbitrary-precision tests

Create `tests/integer.rs`:

```rust
use ash::integer::Integer;

#[test]
fn parses_and_calculates_beyond_machine_width() {
    let left = Integer::parse_decimal("184467440737095516160").unwrap();
    let right = Integer::parse_decimal("100000000000000000000").unwrap();

    assert_eq!((&left + &right).to_string(), "284467440737095516160");
    assert_eq!((&left * &right).to_string(), "18446744073709551616000000000000000000000");
}

#[test]
fn rejects_non_decimal_and_negative_source_literals() {
    assert!(Integer::parse_decimal("-1").is_err());
    assert!(Integer::parse_decimal("01").is_err());
    assert!(Integer::parse_decimal("1_000").is_err());
}
```

#### Task 1, step 5: Run the test and observe the expected failure

Run:

```bash
cargo test --test integer
```

Expected: compilation fails because `ash::integer` does not exist.

#### Task 1, step 6: Implement the minimal integer wrapper

Export `pub mod integer;` from `src/lib.rs`. Implement a private
`num_bigint::BigInt` wrapper with:

```rust
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Integer(num_bigint::BigInt);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InvalidInteger;

impl Integer {
    pub fn parse_decimal(text: &str) -> Result<Self, InvalidInteger>;
}
```

`parse_decimal` must accept exactly `0|[1-9][0-9]*`. Implement
`Display`, `Add` for `&Integer`, and `Mul` for
`&Integer`. Do not expose `BigInt` from Ash-owned APIs.

#### Task 1, step 7: Verify the integer boundary

Run:

```bash
cargo test --test integer
cargo xtask verify
```

#### Task 1, step 8: Commit

```bash
git add Cargo.toml Cargo.lock src/lib.rs src/integer.rs tests/integer.rs docs/tasks/TASK-0006-implement-first-mini-ash-nucleus.md
git commit --no-gpg-sign -m "feat: establish Mini-Ash integer foundation"
```

### Task 2: Add source identities, byte spans, origins, and structured diagnostics

**Files:**

- Create: `src/source.rs`
- Create: `src/diagnostic.rs`
- Modify: `src/lib.rs`
- Create: `tests/source_diagnostics.rs`

#### Task 2, step 1: Write failing source and diagnostic tests

Test:

- LF has a one-byte range and CRLF has a two-byte range;
- a span rejects `start > end` and an end beyond its source;
- line/column rendering derives from bytes without changing stored ranges;
- a generated origin retains its causal primary and related source spans;
- a diagnostic retains its typed reason independently from rendered text.

Use these public contracts:

```rust
pub struct SourceId(u32);
pub struct ByteRange { start: u32, end: u32 }
pub struct Span { source: SourceId, range: ByteRange }
pub struct SourceFile { /* id, display path, UTF-8 text, line starts */ }

pub enum Origin {
    Source(Span),
    Generated { cause: Box<Origin>, reason: GeneratedReason },
    Related { primary: Box<Origin>, related: Vec<Span> },
}

pub struct Diagnostic<R> {
    pub reason: R,
    pub primary: SourceLabel,
    pub related: Vec<SourceLabel>,
    pub expected: Option<String>,
    pub found: Option<String>,
    pub help: Option<String>,
}
```

Expose checked constructors plus read-only `start`, `end`, `source`, and
`range` accessors. Do not expose fields or unchecked public constructors that
can create invalid ranges or cross-source spans.

#### Task 2, step 2: Run the focused test

Run `cargo test --test source_diagnostics`.

Expected: compilation fails because the modules do not exist.

#### Task 2, step 3: Implement the smallest checked source model

Use checked `u32` conversions at file admission. Keep byte ranges
half-open. Make invalid construction return typed errors rather than panic.
Diagnostic rendering may be a simple plain-text method for now; later tasks add
stage-specific reasons and source excerpts.

#### Task 2, step 4: Verify

Run:

```bash
cargo test --test source_diagnostics
cargo xtask verify
```

Expected: all tests and workspace checks pass.

#### Task 2, step 5: Commit

```bash
git add src/lib.rs src/source.rs src/diagnostic.rs tests/source_diagnostics.rs
git commit --no-gpg-sign -m "feat: add source and diagnostic foundations"
```

### Task 3: Implement delimiter-aware lexing

**Files:**

- Create: `src/lexer/mod.rs`
- Create: `src/lexer/token.rs`
- Modify: `src/lib.rs`
- Create: `tests/lexer.rs`

#### Task 3, step 1: Write failing token and newline-context tests

Define tests for:

- every keyword, punctuation token, identifier, and integer;
- exact LF and CRLF spans;
- bare CR, BOM, Unicode identifiers, comments, negative literals, and unknown
  characters;
- blank line tokens;
- newline suppression inside parentheses;
- block newlines re-enabled inside an outer parenthesis;
- restoration of the parenthesized context after the inner block closes.

The token contract is:

```rust
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

pub enum TokenKind {
    Identifier(String),
    Integer(Integer),
    True,
    False,
    Fn,
    Let,
    IntType,
    BoolType,
    UnitType,
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Colon,
    Equal,
    EqualEqual,
    Plus,
    Star,
    Arrow,
    Comma,
    Semicolon,
    LineEnd,
    EndOfFile,
}
```

Comma and semicolon are tokenized so the parser can report that they are
excluded at the correct span; they are never accepted grammar entries.

#### Task 3, step 2: Run the focused test

Run `cargo test --test lexer`.

Expected: compilation fails because `ash::lexer` does not exist.

#### Task 3, step 3: Implement the lexer

Track a delimiter-context stack whose top entry decides newline behavior:
`File` and `Brace` emit `LineEnd`;
`Paren` suppresses it. Push `Brace` even inside
`Paren`. Retain exact token and delimiter spans. Return all lexical
failures as structured `LexReason` values.

Do not diagnose mismatched closing delimiters in the lexer. Emit their tokens
and let the parser own grammar recovery.

#### Task 3, step 4: Verify

Run:

```bash
cargo test --test lexer
cargo xtask verify
```

#### Task 3, step 5: Commit

```bash
git add src/lib.rs src/lexer tests/lexer.rs
git commit --no-gpg-sign -m "feat: add Mini-Ash lexer"
```

### Task 4: Build the event parser, concrete tree, and surface projection

**Files:**

- Create: `src/parser/mod.rs`
- Create: `src/parser/event.rs`
- Create: `src/parser/cst.rs`
- Create: `src/parser/expression.rs`
- Create: `src/parser/grammar.rs`
- Create: `src/parser/project.rs`
- Create: `src/surface.rs`
- Modify: `src/lib.rs`
- Create: `tests/parser.rs`

#### Task 4, step 1: Write failing expression and type parser tests

Cover:

- `1 + 2 * 3`;
- left-associated repeated application, multiplication, and addition;
- non-associative equality rejection;
- right-associated function arrows;
- parenthesized expression and type grouping;
- integer, Boolean, unit, identifiers, and an empty-global program result.

Assert both CST token coverage and projected surface structure.

#### Task 4, step 2: Run the focused test

Run `cargo test --test parser`.

Expected: compilation fails because parser and surface APIs do not exist.

#### Task 4, step 3: Implement the event and tree contracts

```rust
pub enum Event {
    Start(NodeKind),
    Token(usize),
    Missing { expected: ExpectedForm, at: Span },
    Error(ParseReason),
    Finish,
}

pub struct ConcreteTree {
    pub root: ConcreteNode,
    pub tokens: Vec<Token>,
    pub diagnostics: Vec<Diagnostic<ParseReason>>,
}

pub enum ProjectionError {
    RecoveryNodesPresent,
    MalformedTree(InternalReason),
}
```

The surface types must be feature-local payload structs wrapped by a closed
`SurfaceExprKind`. Every surface node and definition carries a full span.

#### Task 4, step 4: Implement expression parsing

Use one Pratt or precedence-climbing function driven by a closed operator table.
Application is detected by a primary-expression start and has the highest
binding power. Keep block, function, definition, binding, pattern, and type
entry points outside the operator function.

#### Task 4, step 5: Add failing grammar-form tests

Add both V-002 presentations, V-003 through V-005, and V-008. Add rejection
tests for tuples, match, multi-parameter functions, multi-binder equations,
polymorphic headers, semicolons, and missing final results.

#### Task 4, step 6: Implement the complete CP-0001 grammar

`parser::grammar` is the closed assembly point. It lists the two global
forms, block and function prefixes, primary forms, types, and operator entries.
It emits missing/error events but never fabricates a valid semantic node.

#### Task 4, step 7: Implement projection and its hard boundary

Projection must fail when any missing or error node exists. Add a direct test
that constructs or parses a recovery-bearing CST and proves no
`SurfaceProgram` can be obtained.

#### Task 4, step 8: Verify

Run:

```bash
cargo test --test parser
cargo xtask verify
```

#### Task 4, step 9: Commit

```bash
git add src/lib.rs src/parser src/surface.rs tests/parser.rs
git commit --no-gpg-sign -m "feat: parse the Mini-Ash surface"
```

### Task 5: Resolve stable lexical binder identities

**Files:**

- Create: `src/resolved.rs`
- Create: `src/resolve.rs`
- Modify: `src/lib.rs`
- Create: `tests/resolution.rs`

#### Task 5, step 1: Write failing resolution tests

Cover:

- sequential globals and rejection of self-reference and forward reference;
- local initializer scope and V-003 shadowing;
- parameter scope and parameter shadowing;
- unknown names;
- duplicate globals;
- equation/interface name agreement;
- distinct `BinderId` values for shadowed spellings;
- definition-to-occurrence provenance.

Assert structured `ResolveReason` values and primary/related spans.

#### Task 5, step 2: Define the resolved contracts

```rust
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BinderId(u32);

pub struct Binder {
    pub id: BinderId,
    pub spelling: String,
    pub origin: Origin,
}

pub struct ResolvedOccurrence {
    pub binder: BinderId,
    pub spelling: String,
    pub origin: Origin,
}
```

Resolved feature payloads mirror surface structure but replace binding and
occurrence strings with these identities. Do not combine resolution with
typechecking.

#### Task 5, step 3: Run the focused test

Run `cargo test --test resolution`.

Expected: compilation fails because the resolver does not exist.

#### Task 5, step 4: Implement sequential resolution

Use explicit scope stack operations:

```rust
fn resolve_initializer(&mut self, expression: &SurfaceExpr) -> Result<ResolvedExpr, ResolveError>;
fn introduce_local(&mut self, binder: &SurfaceBinder) -> Binder;
fn introduce_global(&mut self, binder: &SurfaceBinder) -> Result<Binder, ResolveError>;
```

Resolve an initializer before calling `introduce_local`. Resolve a global
body before publishing its binder to the following program. Preserve both names
and spans for diagnostics.

#### Task 5, step 5: Verify

Run:

```bash
cargo test --test resolution
cargo xtask verify
```

#### Task 5, step 6: Commit

```bash
git add src/lib.rs src/resolved.rs src/resolve.rs tests/resolution.rs
git commit --no-gpg-sign -m "feat: resolve Mini-Ash binders"
```

### Task 6: Establish types, pure Core families, and independent validation

**Files:**

- Create: `src/types.rs`
- Create: `src/core/mod.rs`
- Create: `src/core/dialect.rs`
- Create: `src/core/literal.rs`
- Create: `src/core/variable.rs`
- Create: `src/core/function.rs`
- Create: `src/core/binding.rs`
- Create: `src/core/primitive.rs`
- Create: `src/core/validate.rs`
- Modify: `src/lib.rs`
- Create: `tests/core_validation.rs`
- Create: `tests/architecture.rs`

#### Task 6, step 1: Write failing structural type tests

Test `Int`, `Bool`, `Unit`, structural
`Function(domain, codomain)`, right-associated rendering, and
parenthesized function domains.

The type contract is:

```rust
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Type {
    Int,
    Bool,
    Unit,
    Function(Box<Type>, Box<Type>),
}
```

#### Task 6, step 2: Write failing Core construction and rejection tests

Build the four `I-001` through `I-004` invalid cases plus a node
from outside the pure dialect. Require independent validation rejection after
unchecked construction.

Each Core feature module owns typed payload structs. The dialect module owns
only the closed wrappers:

```rust
pub struct TypedExpr {
    pub ty: Type,
    pub origin: Origin,
    pub kind: PureExprKind,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct NodeId(u32);

pub struct PureProgram {
    nodes: Vec<TypedExpr>,
    root: NodeId,
}

pub struct ValidatedProgram(std::sync::Arc<PureProgram>);

pub enum PureExprKind {
    Value(PureValue),
    Variable(VariableNode),
    Computation(PureComputation),
}

pub enum PureValue {
    Integer(IntegerNode),
    Boolean(BooleanNode),
    Unit(UnitNode),
    Function(FunctionNode),
}

pub enum PureComputation {
    Bind(BindingNode),
    Apply(ApplicationNode),
    Primitive(PrimitiveNode),
}
```

Payload fields stay in their feature modules. Do not add effect, handler,
continuation, tuple, match, or placeholder `Impure` variants.
Child payloads refer to arena-owned nodes through `NodeId`; they do not
own recursive `Box<TypedExpr>` or `Arc<TypedExpr>` trees. Node IDs are
private implementation handles, not stable language identities.

`CoreBuilder` first produces an `UnvalidatedProgram`. Its private storage
envelope records dialect identity separately from `PureExprKind`, so a test
corruption constructor can represent a node from another dialect without
adding that node, an effect variant, or placeholder machinery to the pure
dialect. Validation consumes this unchecked value, checks membership and all
other invariants, projects only pure nodes into `PureProgram`, and returns the
`ValidatedProgram` owning the sole shared `Arc<PureProgram>`. Transforms return
unchecked programs and must cross the same consuming validation boundary.

#### Task 6, step 3: Run the tests and observe failure

Run:

```bash
cargo test --test core_validation
cargo test --test architecture
```

Expected: compilation fails because types and Core do not exist.

#### Task 6, step 4: Implement the closed pure dialect and validator

The validator receives an `UnvalidatedProgram`, explicit binder-scope stack,
and source map. It checks every reachable typed node through an explicit work
stack, rejects invalid or cyclic node references, dialect mismatch, and bad
provenance, then returns a `ValidatedProgram`. Keep construction and test-only
corruption helpers separate from validation. The evaluator may obtain a cloned
`Arc<PureProgram>` only through a crate-private accessor on
`ValidatedProgram`; it cannot accept or bypass validation with `PureProgram`.

#### Task 6, step 5: Run the bounded Core-composition gate

In `tests/architecture.rs`, compare:

1. feature payload modules with handwritten closed dialect wrappers;
2. the same public contracts with generated or generic injection helpers only
   if handwritten construction proves materially repetitive.

Also define a compile-time test-only operation-family interface with an
uninhabited pure operation type and one mock future operation family. Prove the
mock family can cross that boundary without editing literal, variable,
function, binding, application, or primitive payloads. Do not retain an
operation node in `PureExprKind`.

Separately, assemble a test-only shadow pure dialect that adds one mock pure
feature payload to the existing families. Record the feature module, closed
dialect assembly, validator dispatch, traversal dispatch, and consumer sites
that change. This is the pure-feature locality probe; it is distinct from both
the parser's mock operator and the future-operation-family boundary.

Record construction sites, exhaustive match sites, validator changes, and
compiler diagnostics in TASK-0006 Discoveries. Select the smaller mechanism
that preserves closed exhaustiveness and feature locality.

#### Task 6, step 6: Verify

Run:

```bash
cargo test --test core_validation
cargo test --test architecture
cargo xtask verify
```

#### Task 6, step 7: Commit

```bash
git add src/lib.rs src/types.rs src/core tests/core_validation.rs tests/architecture.rs docs/tasks/TASK-0006-implement-first-mini-ash-nucleus.md
git commit --no-gpg-sign -m "feat: add validated pure Core"
```

### Task 7: Deliver the primitive executable vertical slice

**Files:**

- Create: `src/elaborate.rs`
- Create: `src/eval/mod.rs`
- Create: `src/eval/value.rs`
- Create: `src/eval/machine.rs`
- Create: `src/driver.rs`
- Create: `src/render.rs`
- Create: `src/main.rs`
- Modify: `src/lib.rs`
- Create: `tests/primitive_vertical.rs`
- Create: `tests/cli.rs`
- Create:
  `tests/fixtures/first-stratum/valid/v001-precedence.ash`

#### Task 7, step 1: Write failing bidirectional primitive tests

Assert that literals and primitive operations synthesize the CP-0001 types,
that `true + 1` returns `TypeReason::OperatorOperand`, and that
the elaborator produces Core accepted by the independent validator.

Expose only:

```rust
pub fn synthesize(
    &mut self,
    expression: &ResolvedExpr,
    context: &TypeContext,
) -> Result<TypedNode, TypeError>;

pub fn check(
    &mut self,
    expression: &ResolvedExpr,
    expected: &Type,
    context: &TypeContext,
) -> Result<TypedNode, TypeError>;
```

These are methods on an `Elaborator` that owns a `CoreBuilder`.
`TypedNode` contains a `NodeId` and structural `Type`; completing
the program consumes the builder and returns one `UnvalidatedProgram`.

Semantic rule helpers return structured outcomes and remain independently
testable.

#### Task 7, step 2: Write failing machine tests

Define:

```rust
pub enum Control {
    Evaluate(NodeId, Environment),
    Return(Value),
}

pub struct Machine {
    program: std::sync::Arc<PureProgram>,
    control: Control,
    frames: Vec<Frame>,
    trace: Vec<TraceEvent>,
}

pub fn evaluate(program: &ValidatedProgram) -> Result<Evaluation, RuntimeFailure>;
```

Tests assert V-001, V-006, V-007, left-to-right trace order, and integers beyond
64-bit range. Expected initial failure: evaluator APIs do not exist.

#### Task 7, step 3: Observe the primitive vertical tests fail

Run `cargo test --test primitive_vertical` after each smallest added behavior.
The tests must fail because the elaborator or evaluator behavior is absent,
not because the test is malformed.

#### Task 7, step 4: Implement primitive elaboration

Implement literal and primitive feature rule functions, then make
`synthesize` dispatch to them. `check` calls synthesis and structural
type equality. Do not add constraint variables or a generic solver.

#### Task 7, step 5: Implement the first machine frames

Add distinct primitive-left and primitive-right frames owned by
`eval::machine`. One loop evaluates Core; Rust recursion does not represent
Ash evaluation. Values hold `Integer`, `bool`, unit, or later closures.

#### Task 7, step 6: Write the failing CLI smoke test

In `tests/cli.rs`, invoke `env!("CARGO_BIN_EXE_ash")` using
`std::process::Command`. Create the retained `v001-precedence.ash` fixture
containing `1 + 2 * 3`. It must produce `7 : Int\n`, empty stderr, and status
zero. Run `cargo test --test cli` and observe failure because the driver or
binary behavior is absent.

#### Task 7, step 7: Implement the driver and binary

```rust
pub struct Observation {
    pub value: Value,
    pub ty: Type,
}

pub fn run_source(source: SourceFile) -> Result<Observation, PipelineFailure>;
```

The driver calls every stage in order and validates Core before evaluation.
`PipelineFailure` retains stage-specific structured diagnostics; only the
CLI converts it to rendered text.
`main` accepts exactly one path. Use exit status 1 for rejected Ash
source and status 2 for invocation, input, or internal compiler failure.

#### Task 7, step 8: Verify the first executable increment

Run:

```bash
cargo test --test primitive_vertical
cargo test --test cli
cargo run -- tests/fixtures/first-stratum/valid/v001-precedence.ash
cargo xtask verify
```

Expected CLI output: `7 : Int`.

#### Task 7, step 9: Commit

```bash
git status --short
git diff -- src/lib.rs src/elaborate.rs src/eval src/driver.rs src/render.rs src/main.rs tests/primitive_vertical.rs tests/cli.rs tests/fixtures/first-stratum/valid/v001-precedence.ash
git add src/lib.rs src/elaborate.rs src/eval src/driver.rs src/render.rs src/main.rs tests/primitive_vertical.rs tests/cli.rs tests/fixtures/first-stratum/valid/v001-precedence.ash
git diff --cached --check
git commit --no-gpg-sign -m "feat: run primitive Mini-Ash programs"
```

### Task 8: Add strict immutable block bindings

**Files:**

- Modify: `src/elaborate.rs`
- Modify: `src/core/binding.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/eval/machine.rs`
- Create: `tests/bindings.rs`
- Create:
  `tests/fixtures/first-stratum/valid/v003-local-shadowing.ash`

#### Task 8, step 1: Write failing V-003 and scope-order tests

Test the exact V-003 source, an annotated primitive binding, and direct machine
trace assertions showing initializer-before-body evaluation. Require value
`2`, type `Int`, and distinct resolved binder identities.

#### Task 8, step 2: Run the focused test

Run `cargo test --test bindings`.

Expected: typing or evaluation fails because binding Core/machine support is
absent.

#### Task 8, step 3: Implement block elaboration

Fold surface bindings from right to left into nested typed
`BindingNode` values while processing source typing left to right. For
unannotated bindings, synthesize the initializer. For annotated bindings, check
it. Preserve generated origin links to the source binding and initializer.

#### Task 8, step 4: Implement the binding frame

Add:

```rust
Frame::Bind {
    binder: BinderId,
    body: NodeId,
    environment: Environment,
}
```

Evaluate the initializer in the incoming environment. Extend a new environment
only after a value returns.

#### Task 8, step 5: Verify

Run:

```bash
cargo test --test bindings
cargo run -- tests/fixtures/first-stratum/valid/v003-local-shadowing.ash
cargo xtask verify
```

Expected CLI output: `2 : Int`.

#### Task 8, step 6: Commit

```bash
git status --short
git diff -- src/elaborate.rs src/core/binding.rs src/core/dialect.rs src/core/validate.rs src/eval/machine.rs tests/bindings.rs tests/fixtures/first-stratum/valid/v003-local-shadowing.ash
git add src/elaborate.rs src/core/binding.rs src/core/dialect.rs src/core/validate.rs src/eval/machine.rs tests/bindings.rs tests/fixtures/first-stratum/valid/v003-local-shadowing.ash
git diff --cached --check
git commit --no-gpg-sign -m "feat: evaluate immutable bindings"
```

### Task 9: Add lexical functions, applications, and both global presentations

**Files:**

- Modify: `src/elaborate.rs`
- Modify: `src/core/function.rs`
- Modify: `src/core/binding.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/eval/value.rs`
- Modify: `src/eval/machine.rs`
- Modify: `src/render.rs`
- Create: `tests/functions.rs`
- Create: `tests/fixtures/first-stratum/valid/v002-equational.ash`
- Create: `tests/fixtures/first-stratum/valid/v002-operational.ash`
- Create: `tests/fixtures/first-stratum/valid/v004-capture.ash`
- Create: `tests/fixtures/first-stratum/valid/v005-higher-order.ash`
- Create: `tests/fixtures/first-stratum/valid/v008-mixed.ash`

#### Task 9, step 1: Write failing bidirectional function tests

Cover:

- anonymous function checking under an annotated binding;
- `TypeReason::FunctionNeedsContext` in synthesis position;
- application synthesis and argument checking;
- structural higher-order function types;
- both V-002 presentations elaborating to comparable function Core with
  distinct origins.

#### Task 9, step 2: Write failing closure and machine-order tests

Cover V-004 capture, V-005 higher-order application, V-008 nested application,
function-before-argument traces, and the final result of each V-002 form. Also
run an end-to-end program whose final expression is a global function and
require exact output `<function> : Int -> Int\n`, empty stderr, and success.

The closure contract is:

```rust
pub struct Closure {
    pub parameter: BinderId,
    pub body: NodeId,
    pub program: std::sync::Arc<PureProgram>,
    pub environment: Environment,
    pub origin: Origin,
}
```

No field may contain a Rust closure.

#### Task 9, step 3: Run the focused tests

Run `cargo test --test functions`.

Expected: function elaboration or machine support is missing.

#### Task 9, step 4: Implement shared function checking

Implement one rule function that receives parameter identity, expected domain,
expected codomain, body, and presentation origin. Both global presentations and
anonymous functions call it. Equational interfaces must expose one function
domain. Operational headers construct the same structural function type.

Whole-program elaboration folds globals into nested nonrecursive
`BindingNode` values around the result.

#### Task 9, step 5: Implement application frames and lexical closures

Add separate function-position and argument-position frames:

```rust
Frame::ApplyFunction {
    argument: NodeId,
    caller_environment: Environment,
}

Frame::ApplyArgument {
    closure: Closure,
}
```

Evaluate the body in the captured environment extended by the parameter. Do not
reuse the caller environment for the body.

#### Task 9, step 6: Implement canonical function observation

Render function results as `<function>`; render the structural type with
right-associated arrows and parentheses around a function-valued domain.

#### Task 9, step 7: Verify

Run:

```bash
cargo test --test functions
for file in tests/fixtures/first-stratum/valid/v002-equational.ash tests/fixtures/first-stratum/valid/v002-operational.ash tests/fixtures/first-stratum/valid/v004-capture.ash tests/fixtures/first-stratum/valid/v005-higher-order.ash tests/fixtures/first-stratum/valid/v008-mixed.ash; do cargo run -- "$file"; done
cargo xtask verify
```

Expected: each corpus fixture prints its CP-0001 value and type.

#### Task 9, step 8: Commit

```bash
git status --short
git diff -- src/elaborate.rs src/core/function.rs src/core/binding.rs src/core/dialect.rs src/core/validate.rs src/eval/value.rs src/eval/machine.rs src/render.rs tests/functions.rs tests/fixtures/first-stratum/valid
git add src/elaborate.rs src/core/function.rs src/core/binding.rs src/core/dialect.rs src/core/validate.rs src/eval/value.rs src/eval/machine.rs src/render.rs tests/functions.rs tests/fixtures/first-stratum/valid
git diff --cached --check
git commit --no-gpg-sign -m "feat: add lexical Mini-Ash functions"
```

### Task 10: Complete parser recovery and user-facing semantic diagnostics

**Files:**

- Modify: `src/parser/grammar.rs`
- Modify: `src/parser/expression.rs`
- Modify: `src/parser/project.rs`
- Modify: `src/resolve.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/diagnostic.rs`
- Modify: `src/render.rs`
- Create: `tests/diagnostics.rs`
- Create: `tests/fixtures/first-stratum/parse/*.ash`
- Create: `tests/fixtures/first-stratum/resolve/*.ash`
- Create: `tests/fixtures/first-stratum/type/*.ash`

#### Task 10, step 1: Write failing structural parser-diagnostic tests

Add exact P-001, P-002, and P-003 fixtures. Assert reason enum, primary span,
related spans, expected form, synchronization boundary, and exactly two
independent P-003 diagnostics.

Run `cargo test --test diagnostics` after each smallest parser-diagnostic
behavior and observe the expected failure before implementing recovery.

#### Task 10, step 2: Implement committed recovery

After consuming `fn`, a block opener, or an infix operator, keep the
owning grammar context. Recover the P-003 missing operand at the existing
closing brace without consuming it. Continue parsing the final expression and
report its unclosed group independently.

#### Task 10, step 3: Write failing resolution/type diagnostic tests

Add R-001, R-002, T-001 through T-004, equation-name mismatch, non-function
equational interface, and missing anonymous-function context. Assert structural
facts independently from rendered prose.

Run `cargo test --test diagnostics` after each smallest resolution or typing
behavior and observe the expected failure before implementing conversion.

#### Task 10, step 4: Implement stage-owned diagnostic conversion

Each phase maps its typed error to `Diagnostic<Reason>`. Rendering receives
only structured data and source files. Implement focused explanations, primary
labels, causal related labels, expected/found forms, and justified help.

#### Task 10, step 5: Add CLI failure tests

Assert empty stdout, nonzero status, stable category text, and the relevant
source labels for parse, resolution, and type failures. Do not snapshot terminal
color or gutters.

#### Task 10, step 6: Verify

Run:

```bash
cargo test --test diagnostics
cargo test --test cli
cargo xtask verify
```

#### Task 10, step 7: Commit

```bash
git status --short
git diff -- src/parser/grammar.rs src/parser/expression.rs src/parser/project.rs src/resolve.rs src/elaborate.rs src/diagnostic.rs src/render.rs tests/diagnostics.rs tests/cli.rs tests/fixtures/first-stratum
git add src/parser/grammar.rs src/parser/expression.rs src/parser/project.rs src/resolve.rs src/elaborate.rs src/diagnostic.rs src/render.rs tests/diagnostics.rs tests/cli.rs tests/fixtures/first-stratum
git diff --cached --check
git commit --no-gpg-sign -m "feat: report structured Mini-Ash diagnostics"
```

### Task 11: Add transformations, provenance, locality, and deep-machine evidence

**Files:**

- Create: `src/core/transform.rs`
- Modify: `src/core/mod.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/parser/grammar.rs`
- Modify: `src/elaborate.rs`
- Modify: `tests/architecture.rs`
- Create: `tests/semantics.rs`
- Create: `tests/provenance.rs`

#### Task 11, step 1: Write the failing identity traversal and transform tests

Require:

- identity traversal preserves exact typed Core and origins;
- constant folding of literal `+` and `*` nodes preserves the
  result type and records a generated origin caused by the original operation;
- transformed Core validates;
- pre/post transformation evaluation and traces agree on final observations.

Run `cargo test --test architecture` and `cargo test --test semantics` after
each smallest added behavior. Observe failure because traversal or the local
transform is absent before implementing either.

#### Task 11, step 2: Implement feature-local traversal

Each payload module implements its own child traversal. The closed dialect
assembly dispatches exhaustively. Implement only identity traversal and
literal-primitive folding; do not add an optimizer framework.

#### Task 11, step 3: Add provenance tests

Trace generated global bindings, functions, parameters, applications, and
checking operations back to equation/interface and operational-header/body
spans. Assert T-001 and T-004 causal labels survive elaboration.

#### Task 11, step 4: Add architecture-locality probes

Test-only probes must show:

- one mock operator changes its operator feature and closed parser table, not
  block/function/type parsers;
- one mock nested form changes its feature parser and closed prefix assembly,
  not infix parsing;
- one changed static rule outcome remains inside its owning rule helper;
- one foreign Core node represented only by the unchecked storage envelope is
  rejected at dialect validation;
- one mock pure feature extends a test-only shadow dialect through only its
  feature module and closed consumer dispatch sites;
- the operation-family compile-time probe remains separate from `PureExprKind`.

Record measured changed sites and any contrary evidence in TASK-0006.

Record a transition-ownership matrix mapping each executable Core feature to
its machine entry helper, frame variants, and return handler. The probe and
review must show that adding the mock pure feature reaches only its feature
transition helper and the closed evaluator dispatch, without extending one
all-feature transition function.

#### Task 11, step 5: Add deep-machine and large-integer tests

Construct validated Core with at least 10,000 nested additions without parsing.
Evaluate it on a small-stack test thread and assert explicit frame growth with
constant evaluator call depth. Cover literal, sum, product, equality, output,
and trace values beyond signed and unsigned 64-bit range.

#### Task 11, step 6: Verify

Run:

```bash
cargo test --test architecture
cargo test --test semantics
cargo test --test provenance
cargo xtask verify
```

#### Task 11, step 7: Commit

```bash
git add src/core src/parser/grammar.rs src/elaborate.rs tests/architecture.rs tests/semantics.rs tests/provenance.rs docs/tasks/TASK-0006-implement-first-mini-ash-nucleus.md
git commit --no-gpg-sign -m "test: establish Mini-Ash architecture evidence"
```

### Task 12: Complete the corpus and executable conformance matrix

**Files:**

- Create: `tests/corpus.rs`
- Modify: `tests/cli.rs`
- Complete: `tests/fixtures/first-stratum/valid/*.ash`
- Complete: `tests/fixtures/first-stratum/parse/*.ash`
- Complete: `tests/fixtures/first-stratum/resolve/*.ash`
- Complete: `tests/fixtures/first-stratum/type/*.ash`

#### Task 12, step 1: Build a table-driven failing corpus test

Represent each fixture as:

```rust
struct ValidCase {
    path: &'static str,
    expected_value: &'static str,
    expected_type: &'static str,
    expected_stdout: &'static str,
}

struct InvalidCase {
    path: &'static str,
    stage: Stage,
    reason: ExpectedReason,
}
```

List both V-002 presentations and every V-001 through V-008 case. List all
adopted P, R, and T cases plus the extra accepted boundary failures.

#### Task 12, step 2: Run and inspect the failing matrix

Run:

```bash
cargo test --test corpus
cargo test --test cli
```

Expected: any missing fixture or behavior is reported by case ID.

#### Task 12, step 3: Fill only missing conformance behavior

Fix the owning lexer, parser, resolver, typing rule, validator, machine frame,
renderer, or driver. Do not add special cases in the corpus harness.

#### Task 12, step 4: Add excluded-feature and host-failure cases

Cover tuples, match, multi-parameter functions, multi-binder equations,
recursion, forward references, polymorphic syntax, comments, semicolons,
negative literals, Unicode identifiers, BOM, bare CR, invalid UTF-8, missing
file, extra CLI arguments, and an injected internal validator failure.

#### Task 12, step 5: Verify

Run:

```bash
cargo test --test corpus
cargo test --test cli
cargo xtask verify
```

Expected: every named row passes, no invalid case reaches evaluation, no failure
writes success output, and no host panic occurs.

#### Task 12, step 6: Commit

```bash
git status --short
git diff -- src/lexer src/parser src/resolve.rs src/elaborate.rs src/core src/eval src/driver.rs src/render.rs tests/corpus.rs tests/cli.rs tests/fixtures/first-stratum
git add src/lexer src/parser src/resolve.rs src/elaborate.rs src/core src/eval src/driver.rs src/render.rs tests/corpus.rs tests/cli.rs tests/fixtures/first-stratum
git diff --cached --check
git commit --no-gpg-sign -m "test: complete Mini-Ash conformance corpus"
```

### Task 13: Write the normative specification and executable documentation

**Files:**

- Modify: `spec/README.md`
- Create: `spec/lexical-structure.md`
- Create: `spec/syntax.md`
- Create: `spec/name-resolution.md`
- Create: `spec/static-semantics.md`
- Create: `spec/elaboration.md`
- Create: `spec/dynamic-semantics.md`
- Create: `docs/tools/README.md`
- Create: `docs/tools/ash.md`
- Modify: `README.md`
- Modify: `src/lib.rs`
- Create: `tests/spec_examples.rs`

#### Task 13, step 1: Write failing executable specification-example tests

Extract or duplicate each normative source example as an explicitly named test
input. Assert its parse/type/value or rejection. Run
`cargo test --test spec_examples`; expected failure is missing examples or
unsupported documentation harness data.

#### Task 13, step 2: Split normative truth by concern

- `lexical-structure.md`: UTF-8, ASCII tokens, LF/CRLF, delimiter
  contexts, whitespace, invalid forms.
- `syntax.md`: the exact EBNF grammar, precedence, associativity,
  file result, blocks, both globals.
- `name-resolution.md`: stable lexical identities, sequential
  nonrecursive scope, shadowing, name agreement.
- `static-semantics.md`: type algebra and bidirectional rules.
- `elaboration.md`: grouping erasure, presentation convergence,
  nested global/block bindings, required provenance.
- `dynamic-semantics.md`: values, binding/application/primitive
  small-step rules, derived multi-step notation, and a derivation matrix for
  binding (V-003), primitive precedence (V-001), application (V-002), lexical
  capture (V-004), and nested application (V-008).

Every `ebnf` or `sequent` fence has a matching verbal explanation.
Each derivation names its corresponding executable test and explains the
rule sequence in prose.
Do not copy architecture, Rust types, evaluator frames, or parser mechanisms
into normative semantics.

#### Task 13, step 3: Update the specification index

Replace the no-language statement only after all normative files and tests are
present. Link every normative section from `spec/README.md`.

#### Task 13, step 4: Document the tool

Document `ash <source-file>`, UTF-8 input, stdout value/type form,
stderr diagnostics, exit 0/1/2 behavior, function rendering, and examples in
`docs/tools/ash.md`. Link it from `docs/tools/README.md` and the
root README. Update crate documentation so it describes implemented behavior
without making implementation details semantic authority.

#### Task 13, step 5: Verify prose, notation, and examples

Run:

```bash
cargo test --test spec_examples
markdownlint --disable MD013 -- README.md spec/*.md docs/tools/*.md
cargo xtask verify
```

Run the repository relative-link and anchor checker or the task's documented
manual equivalent. Inspect every formal fence without a renderer and confirm
that prose and notation agree.

#### Task 13, step 6: Commit

```bash
git add README.md src/lib.rs spec docs/tools tests/spec_examples.rs
git commit --no-gpg-sign -m "docs: specify the first Mini-Ash nucleus"
```

### Task 14: Close task evidence and prepare reviewed integration

**Files:**

- Modify:
  `docs/tasks/TASK-0006-implement-first-mini-ash-nucleus.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/proposals/README.md`
- Modify: `docs/trajectory.md`
- Modify: `docs/design/DN-0016-first-mini-ash-corpus.md`
- Remove after evidence is recorded:
  `docs/proposals/CP-0001-first-mini-ash-nucleus.md`
- Remove after evidence is recorded:
  `docs/tasks/TASK-0006-implement-first-mini-ash-nucleus.md`
- Remove after evidence is recorded:
  `docs/plans/2026-08-21-first-mini-ash-nucleus.md`

#### Task 14, step 1: Audit CP-0001 evidence line by line

Create a temporary checklist from every Required evidence bullet. Point each
item to exact tests, source modules, normative sections, tool documentation, and
dependency evidence. Any missing evidence returns to its owning earlier task.

#### Task 14, step 2: Run the complete fresh verification suite

Run:

```bash
cargo test --workspace --all-targets --all-features --locked
cargo audit
cargo deny check advisories sources bans
cargo metadata --locked --format-version 1 | jq -r '.packages[] | [.name, .version, (.license // "MISSING"), (.source // "workspace")] | @tsv'
cargo xtask verify
git diff --check
git status --short --branch
```

Also run Markdown lint, relative-link and anchor validation, formal-fence
validation, all CLI fixtures, and native tests available on the current host.
Record exact commands and results in TASK-0006.

#### Task 14, step 3: Request independent whole-change reviews

Require separate reviews for:

- language/specification agreement;
- Rust architecture, invariants, and failure handling;
- tests and corpus completeness;
- dependency policy evidence;
- documentation authority and links.

Resolve every blocking finding and rerun the complete suite.

#### Task 14, step 4: Record completion and lifecycle cleanup

Record final TASK-0006 Progress, Verification, Discoveries, and Deviations
evidence while the task still exists.

#### Task 14, step 5: Commit the task evidence

Inspect the task diff, then retain the evidence in history before lifecycle
cleanup:

```bash
git status --short
git diff -- docs/tasks/TASK-0006-implement-first-mini-ash-nucleus.md
git add docs/tasks/TASK-0006-implement-first-mini-ash-nucleus.md
git diff --cached --check
git commit --no-gpg-sign -m "docs: record first Mini-Ash evidence"
```

#### Task 14, step 6: Apply lifecycle cleanup

Remove the accepted proposal, completed task, and temporary plan from the
integration result, as required by the artifact lifecycle. Update indexes and
trajectory so `spec/` describes current Ash and no active task or proposal
remains.

#### Task 14, step 7: Verify and review the final cleaned tree

Rerun the complete step 2 suite, documentation checks, link and anchor checks,
formal-fence validation, and all CLI fixtures after cleanup. Request a final
independent whole-change review of the exact cleaned working tree. Resolve all
findings and rerun every check before staging.

#### Task 14, step 8: Commit the reviewed integration state

```bash
git status --short
git diff -- docs/tasks/README.md docs/proposals/README.md docs/trajectory.md docs/design/DN-0016-first-mini-ash-corpus.md
git add docs/tasks/README.md docs/proposals/README.md docs/trajectory.md docs/design/DN-0016-first-mini-ash-corpus.md
git add -u -- docs/proposals/CP-0001-first-mini-ash-nucleus.md docs/tasks/TASK-0006-implement-first-mini-ash-nucleus.md docs/plans/2026-08-21-first-mini-ash-nucleus.md
git diff --cached --check
git diff --cached --stat
git commit --no-gpg-sign -m "docs: complete the first Mini-Ash increment"
```

#### Task 14, step 9: Verify the committed result and stop before merge

Rerun the complete step 2 suite and confirm the worktree is clean at the
committed HEAD. Obtain an independent readiness review covering that exact
commit. Report the reviewed commit series, full verification evidence,
unresolved risks, and exact tree status. Do not merge until the user confirms.
The eventual merge commit must be GPG-signed.
