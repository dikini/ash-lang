# First-stratum component convergence

> This convergence record is informative evidence governed by
> [DN-0016](../../../DN-0016-first-mini-ash-corpus.md). It does not accept
> syntax, semantics, or architecture. The accepted non-language outcomes are
> recorded separately in AD-0004 through AD-0008.

## Question

Do the completed specification, parser, static-semantics, Core, and evaluator
comparisons support one coherent Mini-Ash architecture, and which conclusions
are mature enough for architectural-decision review?

## Evidence reviewed

The audit compares the conclusions and decision boundaries from:

- [specification method](specification-method.md);
- [parser architecture](parser-architecture.md);
- [static-semantics organization](static-semantics-organization.md);
- [Core representation](core-representation.md);
- [evaluator architecture](evaluator-architecture.md).

It also checks those conclusions against the corpus grammar, typing rules,
small-step dynamics, diagnostics, representation invariants, AD-0001's Rust and
validation constraints, and DN-0016's feature-local growth rule.

## Converged data flow

The component evidence supports this staged flow:

```text
source text
  → spanned tokens and layout boundaries
  → error-bearing token-complete concrete syntax
  → recovery-free spanned surface AST
  → binder-resolved surface form
  → bidirectionally elaborated typed structured Core
  → independently validated Core
  → explicit first-order evaluation machine
  → value or structured runtime failure
```

Small-step operational rules remain outside this implementation flow as the
primary semantic account. Parser, elaborator, validator, and evaluator tests
check their components against the applicable rules and cases; executing an
implementation does not make it normative.

Each arrow establishes a fact used by the next stage:

| Boundary | Fact established | Failure boundary |
| --- | --- | --- |
| Source to tokens | Token kind, exact source span, delimiter and layout identity | Lexical diagnostic |
| Tokens to concrete syntax | Grammar grouping, precedence, missing forms, recovery context, complete source coverage | Structured parser diagnostics |
| Concrete syntax to surface AST | No missing or error node remains; presentation and required spans survive | Projection failure before resolution |
| Surface AST to resolved form | Every occurrence has a stable binder identity; lexical and file scopes hold | `R-001`, `R-002`, or another structured resolution reason |
| Resolved form to typed Core | Every node has a structural monotype; expected typing and presentation elaboration agree | `T-001` through `T-004` or another structured checking reason |
| Core construction or transformation to validated Core | Types, binder scope, dialect membership, and causal provenance are consistent | Internal compiler failure without source blame |
| Validated Core to machine result | Small-step evaluation order is represented by first-order frames | Structured runtime or resource failure |

No boundary relies on an error string to reconstruct a prior rule outcome.
Source origins and related locations cross boundaries as structured data.

## Cross-component consistency

### Grammar and static semantics

The parser records syntax without deciding semantic grouping that follows
types. Equational pattern lists and juxtaposed applications retain their source
shape; operational comma lists and tuple applications retain theirs. The typed
elaborator uses one structural `Function(domain, codomain)` type to distinguish
nested arrows from a product domain. No parser arity field can disagree with
that type.

Both function presentations remain distinct in concrete and surface syntax.
Presentation-specific elaboration calls shared function, pattern, coverage, and
Core-construction rules. Their typed semantic forms may converge while source
origins preserve the clause, explicit match, header, and body relationships
needed by diagnostics and tooling.

### Core and static semantics

Resolution's stable binder identities satisfy Core scope validation without
requiring stable identities for every syntax or Core node. Bidirectional
checking supplies the structural types stored on Core nodes. Core validation
recomputes enough facts to detect malformed construction, transformation, or
deserialization rather than trusting the elaborator because it ran first.

The Core comparison's feature-family boundary and the static comparison's
rule-family boundary are compatible. One closed Core dialect lists permitted
semantic features; one reviewable rule path owns each type, function-exposure,
pattern, coverage, and elaboration decision. Composition does not mean that an
open registry replaces exhaustive checking.

### Core and evaluator

The first pure Core uses no inhabited effect-operation family. Ordinary
functions, bindings, applications, primitive operations, and probe-only match
or product nodes remain direct typed structure. The evaluator consumes only a
validated dialect and represents lexical closures as Ash code plus an Ash
environment.

The explicit machine's frame family may be organized by the same Core feature
families. That organization can keep transition code local while the selected
machine dialect remains closed and reviewable. The comparison does not require
an arena: frames can identify code through recursive references, stable node
identities, or another storage choice tested during implementation.

### Small-step semantics and evaluator

The machine's frames are executable evaluation contexts corresponding to the
small-step congruence rules. This is an implementation relationship, not a
second semantic method. Result tests, event traces, and later differential tests
remain evidence that machine transitions agree with the primary small-step
account.

The current frame stack is not an Ash effect continuation. It cannot be
captured, resumed, duplicated, or discarded by an Ash program. Later handler
work must define those operations and track one-shot or other continuation
kinds in the type system before extending Core or runtime behavior.

### Diagnostics and every stage

The parser's token-complete error-bearing tree supplies delimiter and recovery
spans.
Resolution supplies definition-use and duplicate-definition relationships.
Typed elaboration supplies expected and found types plus the origin of each
expectation. Core validation distinguishes compiler failures from source
errors. The evaluator returns failures instead of using Rust panic behavior as
an Ash result.

This division supports plain explanations and focused corrections while
retaining precise primary and related spans. Rendering remains separate from
the structured reasons, so presentation changes do not redefine compiler rule
outcomes.

## Growth locality

The comparisons converge on a repeated organization:

```text
feature-local components
  + one explicit closed dialect assembly
  + validation at the stage boundary
```

For a future semantic feature, the parser may add prefix, infix, pattern, type,
or definition parsing; Core may add typed feature nodes; checking may add rule
handlers; and the machine may add frame transitions. Each selected dialect must
name the feature at its assembly point. Unrelated feature modules need not gain
placeholder cases.

An effect family adds different pressure. The Core computation boundary may be
parameterized by an operation family so ordinary pure feature nodes do not gain
one variant per effect family. This remains an architectural seam. Mini-Ash
does not add unreachable `Impure` nodes or effect machinery.

## Accepted decisions

The project accepted five non-language choices as separate architectural
decisions:

1. **[Primary semantic specification method](../../../../decisions/AD-0004-small-step-semantic-method.md).**
   Use one small-step operational account for dynamic semantics; derived traces,
   big-step explanations, and evaluators remain non-normative views checked
   against it.
2. **[Parser architecture](../../../../decisions/AD-0005-parser-architecture.md).**
   Separate lexing, use event-producing
   grammar-shaped recursive descent with one application/infix precedence
   layer, retain token-complete error-bearing concrete syntax, and project only
   recovery-free input to the resolver.
3. **[Front-end semantic boundaries](../../../../decisions/AD-0006-front-end-semantic-boundaries.md).**
   Resolve binder identity and scope before bidirectional typed elaboration;
   centralize semantic rules and structured failures; emit typed structured Core
   with causal provenance.
4. **[Typed Core architecture](../../../../decisions/AD-0007-typed-core-dialects.md).**
   Assemble feature-local typed nodes into named closed dialects, validate every
   retained boundary, keep the pure dialect independent of inhabited effect
   operations, and preserve an explicit future operation-family seam without
   selecting storage.
5. **[Evaluator architecture](../../../../decisions/AD-0008-explicit-evaluator-machine.md).**
   Execute validated Core with an explicit
   first-order control loop, frame data, inspectable closures, and structured
   failures rather than Rust recursion or closure-encoded language control.

These decisions are separable because each governs a stable boundary and has
independent verification evidence. Their acceptance does not accept provisional
Ash syntax or language semantics.

## Choices not ready for decisions

The current evidence does not select:

- the first user-visible source grammar or semantic increment;
- final-expression versus result-binding file structure;
- layout, semicolon, multiline equation, comment, or trivia rules;
- parser, concrete-tree, or diagnostic-rendering libraries;
- handwritten sums, generated injections, traits, macros, or another concrete
  Rust mechanism for Core feature composition;
- recursive ownership, arena storage, stable Core node identities, or inline
  versus side-table provenance;
- the eventual full type system, inference solver, generalization, effects on
  function types, or typed evidence passing;
- effect operations, handlers, continuation capture, continuation
  multiplicity, CPS, concurrency, or cancellation;
- integer range, overflow, runtime resource limits, or environment allocation;
- a first semantic proposal or implementation task.

These choices remain in design notes or require a later corpus stratum. An
architectural decision must not settle them incidentally.

## Next artifact sequence

AD-0004 now governs substantial normative dynamic-semantics work. AD-0005
through AD-0008 govern retained parser, front-end, Core, and evaluator
implementation work. Each remains independently revisable through a later
architectural decision if implementation evidence contradicts it.

The next language artifact is a change proposal for the first user-visible
semantic increment. That proposal must choose from the
provisional corpus, state the semantic delta, and require one executable path,
positive and negative tests, user-facing diagnostics, and the normative
specification update to land together. It must not treat this convergence
record as language authority.

## Retention boundary

This audit retains written comparison results and links their accepted
non-language outcomes. The Core and evaluator probes were deleted after their
evidence was recorded. No parser, resolver, typechecker, Core, evaluator,
executable, or semantic specification has been added to product code.
