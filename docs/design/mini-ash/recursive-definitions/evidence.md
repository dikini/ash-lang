# Recursive Definition Integration Evidence

This report records implementation evidence for
[CP-0002](../../../proposals/CP-0002-recursive-function-definitions.md) and
compares it with the informative findings in
[DN-0019](../../DN-0019-primitive-feature-composition.md). It does not define
Ash semantics. CP-0002 authorizes the transition, and `spec/` becomes current
language truth only when the complete implementation branch merges.

## Scope and environment

The measurement covers `main...f72db57` on branch
`feature/recursive-definitions`. That checkpoint contains the implementation,
tests, corpus, and normative-document updates before this report.

| Property | Observation |
| --- | --- |
| Baseline | `main` at signed Mini-Ash merge `079b8eb` |
| Measured checkpoint | `f72db57509c070874d26865655948a78cb4d7d00` |
| Rust | `rustc 1.97.1 (8bab26f4f 2026-07-14)` |
| Cargo | `cargo 1.97.1 (c980f4866 2026-06-30)` |
| Host | Linux `x86_64`, kernel `7.0.0-29-generic` |

The production diff contains 1,305 added and 206 deleted lines in 16 files
under `src/`. Those raw counts include private tests and behavior-preserving
refactors. They locate integration pressure; they do not measure semantic
difficulty.

## Changed production boundaries

| Boundary | Files | Evidence and classification |
| --- | --- | --- |
| Tokens and concrete syntax | `lexer/token.rs`, `lexer/mod.rs`, `parser/mod.rs`, `parser/grammar.rs`, `parser/project.rs` | `rec`, `and`, two concrete node kinds, group parsing, recovery, shape validation, and projection are feature behavior plus closed syntax joins. |
| Surface and resolved syntax | `surface.rs`, `resolved.rs`, `resolve.rs` | Ordered declarations are a cross-stage representation change. Two-pass global and group allocation is semantic scope behavior. |
| Typing and lowering | `elaborate.rs`, `source.rs` | Simultaneous monotype installation, initialization safety, diagnostics, provenance, and lowering are required semantic behavior concentrated in an existing stage owner. |
| Typed Core | `core/recursion.rs`, `core/mod.rs`, `core/dialect.rs`, `core/validate.rs`, `core/transform.rs` | The group payload localized in one new file. Construction, variable-arity traversal, validation, scope analysis, and transforms remain explicit closed-dialect joins. |
| Evaluation | `eval/machine.rs` | Templates, recursive environment frames, lookup materialization, and entry transitions are semantic ownership and execution behavior, not registration plumbing. |

Only `src/core/recursion.rs` is a new feature-owned production file. This is
not a failure to package the feature: most of recursion's cost changes the
meaning of existing scope, declaration, validation, and environment
boundaries. Moving those policies behind callbacks would relocate rather than
remove their interactions.

One exact-name audit currently returns 38 locations in 10 production files:

```text
rg -n 'PureComputation::RecursiveBind|SurfaceLocalDeclaration::Recursive|ResolvedLocalDeclaration::Recursive|NodeKind::RecursiveBinding(Group|Member)|TokenKind::(Rec|And)' src
```

The hits include declarations, constructors, recognition, and consumers, so
38 is not an edit count. The query is useful because it finds the closed
representation joins without requiring control-flow knowledge. The narrower
`PureComputation::RecursiveBind` query finds 10 locations in four production
files and is the stable audit for every recursive Core dispatch join.

## What localized

The Core group owns only an ordered member array and its body. Each member owns
a typed binder and a function-node handle. That representation made the
feature-specific data and child-order contract small while retaining ordinary
function nodes, binder identities, types, and provenance.

The evaluator's recursive behavior also has a coherent local nucleus:

- one recursive environment-entry variant stores inspectable function
  templates and a lexical parent;
- lookup materializes an ordinary closure rooted at that definition frame;
- the frame does not own closures back to itself;
- the explicit machine continues to own control, so recursive calls do not add
  Rust call-stack or continuation representations.

The parser owns group recovery in the recursive grammar function, and typing
owns `recursion.unsafe-initializer` before ordinary initializer checking.
These policies are localized even though their representations cross stages.

## What necessarily crossed stages

Recursion changes declaration scope rather than adding one leaf expression.
The implementation therefore had to represent an ordered choice between an
ordinary binding and a recursive group in Surface and resolved syntax. It also
had to replace sequential global allocation with a two-pass scope operation.
These changes are semantic propagation, not accidental dispatch.

Typed Core required a new group form because lowering to nested ordinary
bindings would lose simultaneous scope. Its variable number of initializers
also exposed a fixed-child assumption shared by traversal and validation. The
resulting `child_count` and indexed `child_at` interface is generic and has
already removed incidental child-vector allocation from both transforms and
validation.

Elaboration remains the largest integration point. It simultaneously owns
bidirectional checking, annotation provenance, work-stack scheduling, scope
restoration, typed binder construction, and Core lowering. The compiler made
enum coverage visible, but deciding when all recursive monotypes enter the
context and when they leave required semantic inspection. Resolution has the
same smaller-scale pressure for binder allocation and recovery-safe scope
restoration.

## Maintenance mutations

Three deliberate, uncommitted mutations tested discoverability. Each was
reverted with a targeted patch, and `cargo check --locked --all-targets`
passed afterward.

| Probe | Initial compiler evidence | Complete discovery | Interpretation |
| --- | --- | --- | --- |
| Rename `RecursiveBindingMember::binder` | Eight errors in three production files: transform, validation, and evaluation | `rg -n 'member\.binder\(\)' src tests` also finds six assertions in two integration-test files | Rust immediately exposes production consumers. Because the library fails first, one exact search is still needed to see later test-target updates without iterating compilation. |
| Change `RecursiveBindingNode::child_at` from `Option` to `Result` | One actionable type mismatch in `core/dialect.rs` | `rg -n '\.child_at\(' src tests` shows that all other traversals consume the normalized `PureExprKind` contract | The feature-specific variable-arity contract has one central composition point. Validator and transform callers do not depend on the group representation. |
| Add a required field to `RecursiveFunctionTemplate` | Missing-field errors at two unique initializers in `eval/machine.rs`, one production and one private test | `rg -n 'RecursiveFunctionTemplate \{' src tests` returns exactly those sites plus the definition | The private concrete runtime representation gives precise compiler feedback and cannot compile partially updated construction. |

These probes show favorable mechanical maintenance for the new Core and
runtime APIs. They do not make semantic changes mechanical. For example,
changing a template field from provenance to captured type information would
still require deciding whether lookup, closure materialization, diagnostics,
or equality observe that fact.

## Simplification evidence

The implementation reused ordinary unary function nodes and one recursive
binding form for equational globals, inline operational globals, and explicit
local groups. This avoided a recursive-function subtype, implicit thunks,
general recursive values, recursive type equations, a second evaluator, and
continuation machinery.

Required annotations let the typechecker install a finite monomorphic
environment before checking bodies. Direct anonymous-function initialization
delays recursive lookup until application without inventing an initialization
order or black-hole state. These restrictions are semantic simplifications
with substantial representation benefit.

The 10,000-member hardening case initially took about 124 seconds. Stage
profiling found that Core provenance validation repeatedly computed source
locations by scanning line starts backward. Validating source identity,
bounds, and UTF-8 boundaries through `SourceFile::span` reduced the same test
to about 1.34 seconds. Recursion exposed this pre-existing scaling problem; the
fix is general and did not weaken provenance validation.

## Transfer to later data and ADT work

Several findings transfer:

- ordered declarations can admit future data/type declaration forms without
  returning to a binding-only block model;
- allocate-all-then-check is the reusable scope pattern for explicitly mutual
  declaration groups;
- variable-arity Core traversal now has one normalized composition point;
- stable binder references preserve acyclic Core ownership even when semantic
  references are cyclic;
- initialization safety should remain a separate judgment from expression
  typing.

The runtime template strategy does not transfer directly to cyclic constructor
data. Constructor-guarded recursion will need explicit allocation and
initialization semantics, and perhaps different ownership evidence. Pattern
syntax, exhaustiveness, type constructors, and data layout also create joins
that this function-only increment did not test.

## Comparison with the Float experiment

Both experiments support the same central distinction: behavior can localize
more readily than a representation that survives many stages. Recursion is the
stronger contrary case for treating every feature as a package. Its essential
behavior changes scope and environments owned by existing subsystems, so a
single feature directory would obscure important invariants.

The result still improves on ad hoc spread. Closed enums provide exhaustive
compiler feedback; exact searches find the remaining joins; recursive Core
child access has one composition point; and all surface presentations lower to
one existing function form plus one group form. The next increment should
continue to ask, in order:

1. Can the surface feature lower to existing semantic forms?
2. Which new fact must survive a stage boundary?
3. Can a general subsystem composition point carry that fact?
4. Which remaining exhaustive joins are useful invariant checks?

This evidence does not justify registries, generated sums, feature flags, or
separately distributed compiler extensions.
