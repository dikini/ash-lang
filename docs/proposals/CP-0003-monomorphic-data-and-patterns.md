# CP-0003: Monomorphic Data and Patterns

- ID: `CP-0003`
- Status: accepted
- Related: [AD-0004: Small-Step Semantic Method](../decisions/AD-0004-small-step-semantic-method.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [DN-0007: Data and Pattern Typing](../design/DN-0007-data-and-pattern-typing.md), [DN-0019: Primitive Feature Composition](../design/DN-0019-primitive-feature-composition.md), [TASK-0009: Implement Monomorphic Data and Patterns](../tasks/TASK-0009-implement-monomorphic-data-and-patterns.md)

> This proposal is not current Ash. Its accepted status authorizes TASK-0009;
> the specification remains authoritative until the complete change merges.

## Current behavior

Mini-Ash has structural `Int`, `Bool`, `Unit`, and unary function types. Files
contain function definitions and one result expression. Constructors, nominal
types, tuples, general patterns, explicit matches, and recursive data are not
available. Equations have one binder, operational functions have one parameter,
and recursive members must be direct anonymous functions.

## Proposed behavior

Mini-Ash gains nonempty monomorphic nominal algebraic data declarations. All
file type declarations are mutually visible, including self, forward, and
mutual references. A nominal identity combines the source identity with the
declaration index. Each constructor has a separate stable identity and a
globally unique spelling. Constructors have zero or one semantic payload;
multiple syntactic fields form one structural tuple payload.

Tuples contain at least two elements. `(expression)` and `(type)` remain
grouping, and `()` remains `Unit`. Payload constructors are ordinary unary
functions. A nullary constructor occurrence is a data value. Constructor
application, function application, and tuple elements evaluate strictly from
left to right. Integer equality remains the only equality operation.

Operational functions may declare one tuple domain with a comma-separated
parameter list, and applications may construct the corresponding tuple.
Anonymous `fn(left, right)` checks only when its expected domain is the matching
tuple type. Whitespace-separated equational patterns continue to consume one
arrow layer each, so curried equations remain distinct from one tuple pattern.
Contiguous clauses for one equation group must have the same positive pattern
count.

`match` has line-delimited arms. Equations, matches, and ordinary local `let`
use one typed pattern language containing binders, `_`, Boolean and unit
patterns, tuples, and nested constructors. Integer patterns, records, guards,
or-patterns, and as-patterns remain unavailable. A local pattern must be
semantically irrefutable.

One typed usefulness analysis checks matches and equation groups. It recursively
decomposes closed nominal sums, tuples, `Bool`, and `Unit`, reports a concrete
missing witness, and rejects redundant arms or clauses. Local irrefutability is
the same analysis applied to a single pattern.

Recursive initialization continues to admit direct anonymous functions. A data
member is safe only when rooted at a fully applied constructor of its declared
nominal type. A recursive occurrence may pass through constructor or tuple
construction, or occur under a function. Recursive-free expressions may be
leaves. Ordinary calls, primitives, matches, and blocks may not force or
transport a recursive occurrence.

Entering a recursive group allocates every data slot and installs every
function template before initialization. Guarded data initializers run in
source order and initialize their slots. Recursive data lookup returns its
location without dereferencing it. Matching and structural rendering follow
initialized aliases. Uninitialized access, alias loops, invalid locations, and
impossible match failure are structured internal runtime failures made
unreachable by accepted source.

## Semantic delta

The change adds monomorphic nominal sums, structural tuple products, ordinary
constructor values, typed patterns, total matches and equations, irrefutable
local destructuring, and explicitly allocated constructor-guarded cyclic data.
It extends recursive initialization safety without adding general laziness or
observable mutation.

## Affected specification areas

- [Lexical structure](../../spec/lexical-structure.md) adds reserved words,
  uppercase constructor and type identifiers, and punctuation.
- [Syntax](../../spec/syntax.md) adds data declarations, tuples, patterns,
  matches, clause groups, and tuple-domain function syntax.
- [Name resolution](../../spec/name-resolution.md) adds type and constructor
  identities, namespaces, and pattern scopes.
- [Static semantics](../../spec/static-semantics.md) adds nominal and tuple
  types, constructor typing, pattern checking, usefulness, and guarded
  recursive initialization.
- [Elaboration](../../spec/elaboration.md) adds registries, resolved types,
  structured patterns and matches, and shared lowering paths.
- [Dynamic semantics](../../spec/dynamic-semantics.md) adds tuples,
  constructors, matching, a heap, and recursive data initialization.

## Resulting specification truth

After implementation, tests, documentation, and specification changes merge,
Mini-Ash has the behavior described under Proposed behavior. Nominal equality
uses identity; tuple and function equality is structural. Resolved and Core
programs carry closed immutable type and constructor registries. Evaluation
owns a per-run heap, and observations render finite and cyclic structures
without exposing source-level object identity.

## Interactions

- AD-0005 keeps the new grammar and recovery in feature-owned parsers plus the
  closed dialect assembly.
- AD-0006 requires resolved identities, one type-equality rule, one typed
  pattern checker, and one usefulness analysis shared by presentations.
- AD-0007 permits structured pattern Core and requires registries, transforms,
  provenance, and independent malformed-Core rejection.
- AD-0008 requires explicit tuple, match, allocation, initialization, and
  rendering work rather than Rust recursion or closures.
- DN-0007 supplies evidence for distinct structural tuples, nominal ADTs,
  ordinary constructors, expected-type pattern checking, irrefutable bindings,
  and shared coverage. This proposal selects only the monomorphic tuple subset.
- DN-0019 and the retained recursion evidence require changed-site evidence and
  favor lowering through ordinary application, functions, bindings, and one
  structured match form before adding mechanisms.

## Non-goals

This proposal does not add polymorphism, type parameters, records, labels,
projections, rows, aliases, modules, opacity, empty types, unary tuples, integer
patterns, guards, or-patterns, as-patterns, pattern-compilation Core, decision
trees, layout optimization, garbage collection, effects, FFI, general laziness,
observable mutation, or stable source-level object identity.

## Required evidence

TASK-0009 must provide:

- positive, rejection, structured-diagnostic, trace, provenance, malformed-Core,
  transform, deep-stack, and executable-documentation tests for every proposed
  form and invariant;
- parsing and recovery evidence for declarations, constructor lists, tuples,
  matches, equations, exact spans, token completeness, and projection refusal;
- resolution evidence for two-pass nominal and constructor identity allocation,
  separate namespaces, duplicate rejection, recursive references, pattern
  scope, shadowing, and restoration after failure;
- typing evidence for nominal inequality, structural products, constructors as
  values, tuple versus curried functions, nested patterns, usefulness,
  irrefutability, clause arity, and guarded recursion;
- independent Core rejection for malformed registries, identities, constructor
  ownership and payloads, patterns, scope, coverage, provenance, handles,
  reachability, and ownership cycles;
- evaluator evidence for strict order, lexical capture, finite and cyclic data,
  mixed groups, exact structural rendering, structured impossible failures,
  explicit stacks, and safe destruction;
- validation and differential evaluation after identity and literal-folding
  transforms;
- updated normative specification and `ash` tool documentation with executable
  examples and stable diagnostic names;
- retained integration evidence linked from DN-0007 and DN-0019, including
  changed composition points and reverted API-mutation probes;
- `cargo xtask verify`, Markdown, relative-link, anchor, authority, and formal
  notation review.

If implementation exposes a missing semantic choice, work returns to this
proposal instead of making a local implementation decision.
