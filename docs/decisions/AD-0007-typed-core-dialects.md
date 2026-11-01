# AD-0007: Typed Core Dialects

- ID: `AD-0007`
- Status: accepted
- Related: [AD-0006: Front-End Semantic Boundaries](AD-0006-front-end-semantic-boundaries.md), [AD-0008: Explicit Evaluator Machine](AD-0008-explicit-evaluator-machine.md), [DN-0002: Core Representation](../design/DN-0002-core-representation.md), [DN-0008: Typed Core and Elaboration](../design/DN-0008-typed-core-and-elaboration.md), [DN-0016: First Mini-Ash Corpus Stratum](../design/DN-0016-first-mini-ash-corpus.md), [first-stratum Core comparison](../design/mini-ash/first-stratum/comparisons/core-representation.md)

## Decision

Ash organizes Core as named typed dialects assembled from feature-local node
families. Each dialect has one closed assembly boundary that declares exactly
which nodes it permits. Consumers may compose feature-specific traversal,
validation, transformation, and evaluation logic while retaining exhaustive
reasoning over the selected dialect.

Every semantic node and binder exposes its structural type. Function types store
only a domain and codomain; curried and product-domain functions differ through
that structure rather than an independent arity. Nodes retain causal source
provenance sufficient for validation and diagnostics.

Each retained Core dialect has an independent validator. Validation checks node
types, binder scope, dialect membership, and provenance after compiler
construction and transformation, before the final representation is packaged.
Construction APIs may prevent common mistakes but do not replace that boundary.
A linked compiler-generated executable reconstructs this verified representation
without repeating the proof; [AD-0013](AD-0013-generated-native-bridges-and-program-builds.md)
defines that execution boundary.

Before publication, each checked module completes and retains its lowering,
evidence, closure layouts and cleanup metadata. These fragments are not yet
independently validated Core programs.
Linking relocates them into a new Core representation, which receives its
independent validation once. Importing a checked module does not repeat its
source-body proof or rebuild its metadata, and later consumers of unchanged
validated Core preserve that proof. A compiler transformation that changes Core
still validates its new result before packaging.

Core separates ordinary values and computations and provides a typed
operation-family boundary in the spirit of a Freer representation. The pure
Mini-Ash dialect instantiates that boundary with no inhabitable effect
operations. Adding a later operation family must not add one effect variant to
every ordinary pure feature or require unrelated pure consumers to interpret
that family.

Mini-Ash does not contain placeholder `Impure` nodes, handlers, effect
operations, or CPS regions. Future continuations are explicit first-order
compiler data rather than Rust closures, but their concrete form and semantics
require later decisions.

Recursive ownership, arena storage, stable Core node identities, and provenance
side tables remain replaceable implementation choices. They become stage
contracts only if later evidence shows a consumer that requires them.

## Context

The first corpus compared recursive typed sums of feature payloads, arena-owned
nodes with stable identities, and an operation-parameterized computation shape.
All represented lexical capture, preserved causal origins through a typed
simplification, and rejected the required malformed Core cases.

The recursive sum localized feature payloads and preserved exhaustive
validation but exposed construction and injection plumbing. The arena simplified
ownership and stable identity but still needed either one closed dispatch tag
or dynamic type erasure; storage alone did not compose semantic features. The
operation-parameterized form isolated future requests but left its pure syntax
enum closed.

The evidence therefore supported layers rather than one winning Rust type:
feature composition selects semantic structure, the value/computation boundary
isolates future operation families, and ownership selects storage. AD-0001
already requires explicit types, safe semantic representations, and validation;
this decision defines how those requirements apply to Core.

## Consequences

- Adding a pure language feature changes its feature family and each selected
  dialect that admits it, not every unrelated feature definition.
- A selected dialect remains closed and reviewable; feature composition does not
  imply an untyped open registry.
- Equational and operational functions can share Core structure while source
  provenance records their presentation differences.
- Typed structured patterns may remain in a Core dialect until an explicit,
  validated pattern-compilation transform justifies a decision dialect.
- Every retained semantic Core dialect must remain directly executable so
  transforms can receive differential evaluation evidence.
- Transformations declare their input and output dialects, preserve or rebuild
  causal provenance, and validate their results.
- The first implementation may use a small dialect-local Rust encoding if it
  preserves the accepted boundaries; it need not implement textbook Freer
  machinery.
- This decision does not choose concrete Rust sums, traits, macros, code
  generation, arenas, node IDs, effect semantics, continuation multiplicity,
  handlers, CPS reconstruction, or optimization dialects.

## Verification

Core implementation and every retained transform must show:

- complete typed representation of the applicable positive corpus cases;
- independent rejection of scope, node-type, application-type, dialect, and
  provenance violations;
- identity traversal and at least one local transform with validation and
  evaluation preservation;
- presentation-specific origins surviving convergence to shared function and
  match structure;
- exhaustive review of every node permitted by a selected dialect;
- locality evidence when adding one pure feature family;
- a compile-time or bounded architectural probe showing that a future operation
  family crosses the operation boundary without modifying unrelated pure
  feature definitions;
- no inhabited effect operation or unreachable handler machinery in the pure
  Mini-Ash dialect;
- no Rust closure as the sole representation of Ash functions or future
  continuations.
