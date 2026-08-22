# Mini-Ash Closure Report

This report closes the Mini-Ash milestone described by
[DN-0015](../DN-0015-mini-ash-phase.md) and
[DN-0020](../DN-0020-ash-dialect-milestones.md). It records implementation and
simplification evidence; it does not define the language. The
[specification](../../../spec/README.md) remains authoritative.

## Retained dialect

Mini-Ash is one single-file, pure, rank-1 dialect. It contains:

- arbitrary-precision integers, Booleans, unit, unary functions, application,
  integer arithmetic, and integer equality;
- sequential local bindings, file-wide recursive functions, and explicit local
  recursive groups;
- structural tuples, parameterized nominal algebraic data, ordinary constructor
  values, typed patterns, exhaustive matches, and equational clauses;
- constructor-guarded cyclic data with finite structural observation; and
- implicit global quantification, conservative local anonymous-function
  generalization, first-order unification, and explicit typed Core operations.

The `ash` executable selects this dialect directly. There is no compatibility
mode, feature flag, second parser, alternate Core, or alternate evaluator.

## Stage boundaries

| Boundary | Facts retained by the next stage | Facts released |
| --- | --- | --- |
| Lexing to parsing | tokens, spans, logical line ends, lexical diagnostics | source scanning state |
| Concrete tree to Surface | admitted grammar shape and source spans | parser events and concrete nodes after successful projection |
| Surface to resolved | term, nominal, constructor, and type-parameter identities; resolved types; immutable registry | unresolved spellings and Surface program after successful resolution |
| Resolved to Core | zonked types, outer schemes, explicit type operations, typed patterns, registry, origins | inference variables, substitutions, and elaboration work state |
| Core validation to evaluation | authenticated nodes, registries, scope, types, coverage, guarded recursion, reachability | validator indexes and work sets |
| Evaluation to observation | result value plus the completed shared heap | machine control, continuations, and transient environments not reachable from the result |

These releases keep each predecessor from remaining live merely to supply a
fact that its successor already owns. The completed heap remains shared because
locations in data and captured environments are meaningful only with that heap.

## Simplification audit

### Constructs and lowering

Grouping disappears during elaboration. Equational and operational globals
converge on the same unary function and structured-match forms. Multi-field
constructor payloads and multi-parameter operational domains use structural
tuples. Local destructuring lowers to the same typed pattern and match machinery
used by source matches and equations. Constructor application remains ordinary
unary application.

Type inference stays private to elaboration. Zonked Core retains outer schemes
only through `TypeAbstraction` and `TypeApplication`; the evaluator erases both
without adding a runtime representation. Removing those Core forms would make
scheme scope, substitution, transform preservation, and malformed-Core
validation indirect, so the audit retains them.

No admitted behavior uses the earlier candidate pipeline, host-closure
evaluator, pattern-compilation Core, concrete-tree retention, Surface retention,
runtime type objects, or a second usefulness algorithm. Those mechanisms are
absent rather than dormant.

### Core versus library

Mini-Ash has no module or library boundary, so moving a primitive into a library
would be speculative. Integer primitives, tuples, functions, nominal data,
patterns, recursion, and rank-1 schemes remain Core language behavior. Modular
Ash will provide the first credible interface boundary for a core-versus-library
comparison.

### Budgets

- Lexing and event parsing share a cumulative syntax-work budget before
  retained tokens, diagnostics, and events.
- Every match, equation group, and irrefutability query shares cumulative
  coverage work and memoized-state limits.
- Resolution, elaboration, Core construction, and Core validation bound
  cumulative type work at 327,680 units and charge proportional cells before
  retention.
- Arena handles, source spans, recursive slots, and heap locations use checked
  numeric identities.

Resource exhaustion remains a structured internal result. It is not a
source-language typing or coverage judgment.

### Ownership and release

Core graphs use numeric handles rather than Rust ownership edges. Recursive
data use preallocated numeric heap slots and aliases. Evaluation freezes one
completed heap for observation; shared ownership keeps reachable locations
valid, while iterative matching, rendering, and destruction avoid host-stack
dependence at admitted depth.

The driver drops the concrete tree after Surface projection and drops Surface
after resolution. Elaboration does not store its inference substitution in
Core. Evaluation does not retain type-operation parameters or arguments.

### Maintenance sites

The parser grammar, surface and resolved expression families, `Type`, the pure
Core value and computation families, transform reconstruction, Core validation,
and evaluator dispatch are deliberate closed assembly points. The architecture
mutation tests enumerate their maintenance cost. Stable searches for token,
type, pattern, heap, and Core variants locate the same consumers without a
registration system.

The audit found no private behavior-preserving mechanism that could be removed
without either duplicating a retained judgment or making a boundary invariant
implicit. Cleanup during the increment removed recursive traversal from the
new deep type paths and reused the existing registry, typed-pattern,
usefulness, explicit-machine, provenance, and transform boundaries.

## Retained evidence

- [First-stratum convergence](first-stratum/comparisons/component-convergence.md)
- [Recursive-definition integration](recursive-definitions/evidence.md)
- [Data-and-pattern integration](data-and-patterns/evidence.md)
- [Rank-1 polymorphism integration](rank-1-polymorphism/evidence.md)

Together these reports explain the current behavior, crossed boundaries,
resource and ownership model, and the evidence that caused each retained
representation.

## Intentional exclusions

Mini-Ash does not contain modules, interfaces, imports, exports, aliases,
records, projection, strings, effects, handlers, resources, FFI, concurrency,
subtyping, overloading, type classes, higher-rank or higher-kinded polymorphism,
explicit expression type application, polymorphic recursion, runtime type
reflection, general laziness, pattern compilation, garbage collection, or
observable object identity.

These exclusions bound the retained dialect. They do not reject future design
work. Modular Ash begins at passive static modules and interfaces against this
completed input.
