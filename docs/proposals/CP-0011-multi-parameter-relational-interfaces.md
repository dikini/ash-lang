# CP-0011: Multi-Parameter Relational Interfaces

- ID: `CP-0011`
- Status: accepted
- Related: [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [AD-0009: Ordered Resolved-Global Binder Authority](../decisions/AD-0009-ordered-resolved-global-binder-authority.md), and [TASK-0018: Implement Multi-Parameter Relational Interfaces](../tasks/TASK-0018-implement-multi-parameter-relational-interfaces.md)

> This proposal is not current Ash.

## Current behavior

An interface declares exactly one fixed-kinded type parameter. Every method
value type must contain that parameter, and one method occurrence creates one
unary interface obligation. A global requirement, implementation head,
prerequisite, checked summary, selected evidence plan, linked validation fact,
and Core authentication fact consequently carries one interface argument.

Ordinary kind-aware unification may refine that argument before evidence
selection. Selection itself never solves an inference variable to make a
candidate applicable. It starts only after the complete unary goal contains no
inference variable and considers an identity-equal abstract requirement, exact
current-implementation evidence, and then the unique matching visible
implementation. Full-head overlap, orphan ownership, and generic prerequisite
decrease also inspect the one argument.

A global requirement may use only type variables that occur in the global
value type. Interfaces have no relational determination, associated outputs,
projection types, defaults, specialization, or runtime dictionaries.

## Proposed behavior

### Parameters and applications

An interface declares one or more ordered fixed-kinded parameters:

```ash
interface Convert<From, To> {
    convert : From -> To
}
```

The existing declaration-binder policy applies independently to each
parameter. Written order fixes canonical parameter order. Every parameter has
one resolved identity, spelling, fixed kind, origin, and declaration position.
An omitted kind annotation means `Type`; Ash does not infer an interface
parameter kind.

Every interface application supplies exactly one type argument per parameter
in declaration order. Each argument must have the corresponding parameter
kind. Constraints and implementation heads retain their existing syntax but
accept comma-separated argument lists:

```ash
Convert<Int, String>
```

The checked representation is one complete application:

```text
InterfaceApplication = InterfaceId + ordered interface arguments
```

Interface-application checking compares arity before checking any positional
argument kind. A missing or extra argument is `interface.argument-count` at the
complete application, with the selected interface declaration as related
authority. An arity-correct argument of the wrong kind retains `kind.argument`
at that argument. This ordering applies uniformly to requirements,
implementation heads and prerequisites, and method obligations. A body-free
summary with a malformed retained vector is instead an internal validation
failure because source checking has already established its arity.

Requirements, implementation heads, pending and frozen method occurrences,
evidence selections, body-free summaries, linked validation, elaboration, and
Core authentication retain that complete application. Multi-arity is not
encoded as one tuple argument or a nested unary interface application.

### One total determination edge

An interface may declare one determination edge after its parameter list:

```ash
interface Decode<Format, Source, Value> where (Format, Source) -> Value {
    decode : (Format, Source) -> Value
}
```

Each side names interface parameters, not types. A side with one parameter may
omit parentheses; a side with several parameters uses a comma-separated
parenthesized list. The names on each side must follow interface declaration
order. Both sides are nonempty and disjoint, and together they must contain
every interface parameter exactly once. The left side is the determinant key;
the right side is its complete dependent complement.

An interface cannot declare a second edge. The relation has no neutral
parameter, alternative key, transitive edge, reverse edge, or injectivity rule.
The checked fact retains only the ordered parameter records and an optional
ordered set of determinant declaration positions. The dependent positions are
derived as the complement. The source spelling does not impose an output-last
layout on the parameter vector.

### Method determinacy

The syntactic seed of a method is the set of interface parameters that occur in
its ordinary value type. With no determination edge, the seed must contain
every interface parameter. With an edge, the seed must contain every
determinant parameter; dependent parameters may occur anywhere in the value
type or may be absent.

For example, all three methods below are determined by `Collection`:

```ash
interface Collection<C, Element> where C -> Element {
    choose : C -> Option<Element>
    insert : (C, Element) -> C
    size : C -> Int
}
```

The role is relational. A dependent parameter is not tied to a function result
position. A method that omits any determinant parameter remains
`interface.method-parameter`. This increment adds no explicit source syntax
for supplying an interface application at a method occurrence.

### Improvement and evidence selection

Ordinary kind-aware unification runs first. For an interface with a
determination edge, improvement may start only when every determinant argument
contains no unsolved inference variable. It considers the first applicable
source in the existing evidence priority:

1. one abstract requirement with the same interface identity and
   identity-equal zonked key;
2. the exact current implementation with that key; or
3. the unique visible implementation whose independently freshened key
   first-order matches the known key.

The chosen source supplies the complete dependent tuple. Improvement is
mandatory when a source exists, including when ordinary checking already fixed
every dependent. It transactionally unifies the whole supplied tuple with the
pending application. A disagreement is
`constraint.determination-conflict`; its diagnostic retains the known key, the
source that established the expected tuple, and the conflicting tuple. A
failure publishes no partial inference solution. Improvement never refines or
guesses a key, uses a dependent argument to infer a key, inspects
prerequisites, constructs evidence, or records a selection.

After improvement, existing evidence selection starts only when the complete
application is zonked and inference-free. A determined obligation must also
have belonged to the pre-pass inference-free-key snapshot. An obligation
outside that snapshot is `constraint.ambiguous` for this closure even if
another obligation later makes its key and complete application inference-free;
it cannot bypass mandatory key consistency by entering full selection. An
eligible obligation matches the full application and retains the existing
abstract, exact-current, and concrete priority. An unresolved key is
`constraint.ambiguous`. If a known key has no improvement source and the
complete goal remains unresolved, the occurrence is also
`constraint.ambiguous`; `constraint.unsatisfied` remains owned by full-goal
selection. No-edge obligations retain their predecessor full-application
selection rule and do not participate in the determination snapshot.

Improvement is one isolated pass because the key determines the entire
complement. Before that pass mutates inference state, the checker snapshots
which pending obligations already have complete inference-free keys. Only
those obligations may improve, in source order. An output filled by one
obligation cannot unlock another obligation during this increment. The pass
does not create a general constraint store, edge closure, repeated saturation,
cross-obligation or cross-requirement propagation, or higher-order matching.

### Global requirements

A requirement without a determination edge keeps the current rule: every type
variable in its complete application must occur in the global value type.

For a determined requirement, every type variable in its key arguments must
occur in the global value type. A type variable that occurs only in dependent
arguments may remain requirement-only because the key determines it. The
explicit or implicit global binder policy still retains that variable and its
fixed kind in the complete checked scheme and Core abstraction. This relaxation
does not propagate information between distinct requirements.

One global or implementation header cannot contain two requirements for the
same interface with identity-equal keys. Identity-equal complete applications
retain `constraint.duplicate-requirement`; equal keys with different dependent
applications are `constraint.determination-conflict`. The checker does not
equate two independently declared requirement outputs or compute
cross-requirement closure.

### Implementations and coherence

An implementation head supplies a complete interface application. Its explicit
binder list is an ordered bijection with the free variables across the entire
head; an omitted list uses first-occurrence order across arguments. Every
dependent-head free variable must also occur in the determinant-key slice.
This syntactic coverage rule rejects a head whose output can vary independently
of its key:

```ash
interface Relation<A, B> where A -> B {
    relate : A -> Int
}

impl<B> Relation<Int, B> { // rejected
    relate value = value
}
```

It admits constants and first-order constructions whose variables come from
the key, such as `Relation<Int, Bool>` and `Relation<List<A>, A>`. This
increment does not use prerequisite evidence to establish coverage.

The predecessor bare-variable rule generalizes to the selection key. An
implementation whose every selection-key argument is a bare type variable is
`impl.variable-head`, even when a dependent argument is constant or structured.
At least one key argument must therefore have a primitive, nominal, function,
application, tuple, or other non-variable outer structure. A no-edge interface
uses its complete argument vector for this test.

Visible implementation coherence retains stable-identity deduplication and
scoped effective environments. For two distinct implementations of one
determined interface, the checker independently freshens both heads and
kind-preservingly unifies their key slices. If the keys do not unify, the pair
is coherent. If the complete heads also unify, the existing `impl.overlap`
failure owns the pair. Otherwise the pair is
`impl.determination-conflict`. The first module whose effective environment
combines the pair owns either failure and publishes no summary.

For an interface without an edge, existing full-head overlap remains the only
pair-coherence rule. Generic self-coverage and pair coherence do not use source,
dependency, import, or candidate order to choose a winner.

### Orphan ownership and prerequisite termination

The selection key of an interface application is its determinant slice when an
edge exists and its complete argument vector otherwise. A foreign-interface
implementation satisfies the orphan rule only when a local outer nominal
constructor occurs in that selection key. A local nominal that occurs only in
a dependent argument does not authorize the implementation.

Every prerequisite variable must continue to occur in the complete
implementation head. This proposal does not add prerequisite-only or
existential implementation binders.

Generic prerequisite decrease compares canonical selection-key tuples: the
determinant slice for a determined interface and the complete vector otherwise.
The two tuples must have the same width. At each declaration-order position,
the prerequisite component must be identity-equal to or a strict syntactic
subterm of the corresponding implementation-head component, and at least one
position must be strict. A different-width generic prerequisite is
`impl.prerequisite-not-decreasing`. This pointwise order is the predecessor
strict-subterm rule at width one.

A prerequisite is ground only when its complete interface application has no
free type variable. Ground prerequisites retain canonical active-goal cycle
detection over the full ordered application, never only its selection key. No
projection normalization participates in either rule.

### Summaries, evidence, and Core

A checked interface fact and every body-free mirror retain the ordered
parameter records and optional determinant positions. Summary admission and
linked validation authenticate arity, order, identities, kinds, origins,
positions, the complete application arguments, and every relationship already
authenticated for unary evidence. Determinant positions are declaration
metadata; freshened binder identities never replace them.

An evidence selection remains opaque and occurrence-owned. Its root retains
one complete `InterfaceApplication`. Current producers remain abstract
requirements, exact current implementations, and concrete implementations.
The proposal does not turn interface evidence into a universal proof, handler,
provider, or runtime witness.

Elaboration substitutes every interface parameter from the complete
application in declaration order before applying method-local arguments and
existing evidence. Generated method-evidence adapters retain their current
head-parameter then method-parameter order. Determination metadata adds no
type binder, evidence method, Core node, evaluator value, runtime dictionary,
registry, lookup, frame, transition, or failure mode. It erases before Core;
the independently validated Core retains only the complete types and
authentication relationships needed by ordinary method evidence.

### Failure ownership and resources

Parsing owns malformed parameter lists and determination syntax. Resolution
owns duplicate interface binders and an unknown name in a determination side.
Interface-application checking owns missing or extra arguments as
`interface.argument-count` before kind checking owns an arity-correct
positional `kind.argument`. Interface admission owns a repeated, omitted,
reordered, overlapping, or otherwise non-partitioning determination parameter
as `interface.determination-parameter`, and owns a method with an incomplete
seed as `interface.method-parameter`.

Implementation header admission owns syntactic self-coverage as
`impl.determination-coverage`, orphan status, and prerequisite decrease.
Effective-environment construction owns full-head overlap and distinct-output
key conflicts. Global and implementation requirement checking owns duplicate
complete applications and duplicate keys. Improvement owns dependent
disagreement as `constraint.determination-conflict`; improvement and selection
retain the other ambiguity and satisfaction ownership stated above. Linked
validation and Core validation own forged or inconsistent retained carriers
only after every earlier stage succeeds.

Within one source unit, failures have this causal precedence:

1. parsing and recovery;
2. name resolution;
3. interface-application arity, then positional argument kinds;
4. determination partition admission;
5. existing method-binder and method-kind checks, then method seed and
   function-shape checks;
6. implementation variable-head admission, prerequisite containment,
   determination coverage, orphan ownership, prerequisite decrease, and
   privacy in that order;
7. effective-environment pair coherence;
8. implementation method membership and bodies;
9. per-occurrence ordinary unification, unresolved-key ambiguity, atomic
   improvement and its dependent conflict, remaining dependent ambiguity,
   full-application selection, active-goal cycle detection, and unsatisfied
   evidence; and
10. whole-module method ambiguity and publication, followed by summary,
    linking, elaboration, and Core validation.

An earlier failure prevents publication to every later boundary. Existing
predecessor diagnostics within one listed family retain their current internal
order unless this proposal states a narrower rule.

The existing graph-wide interface-and-constraint ledger charges each retained
parameter and argument, determination position, key comparison, improvement
candidate, coherence pair, summary field, evidence fact, and validation visit
before publication. Type and kind copies charge their existing type-work
ledgers. Core construction and validation retain independent ledgers. Deep and
wide cloning, substitution, comparison, rejection, retry, and disposal remain
iterative or use bounded explicit work stacks. This proposal does not increase
a production resource limit.

## Semantic delta

- An interface declares a nonempty ordered parameter vector instead of exactly
  one parameter.
- Every interface application carries a complete ordered argument vector.
- An interface may declare one total determinant-key-to-complement relation.
- Method determinacy uses all parameters for an ordinary relation or the key
  for a determined relation.
- One isolated forward-improvement pass may fill dependent arguments from a
  key that was known before the pass without selecting evidence.
- Determined requirements may bind dependent-only variables, while their key
  variables must occur in the global value type.
- Implementation coverage, visible coherence, orphan ownership, and generic
  prerequisite decrease use the declared selection key.
- Summaries and linked validation authenticate complete vectors and determinant
  positions; Core and runtime behavior remain method-function evidence with
  type erasure.

## Affected specification areas

- [Syntax grammar](../../spec/syntax.md#grammar) changes interface parameter,
  determination, constraint, and implementation-application productions.
- [Interface, implementation, and requirement identities](../../spec/name-resolution.md#interface-implementation-and-requirement-identities) changes interface binder order, determination-name resolution, and complete application retention.
- [Interfaces and constrained schemes](../../spec/static-semantics.md#interfaces-and-constrained-schemes) changes interface well-formedness, method determinacy, requirements, and improvement.
- [Implementations](../../spec/static-semantics.md#implementations) changes head formation, coverage, coherence, orphan ownership, and prerequisite decrease.
- [Constraint satisfaction and checked evidence](../../spec/static-semantics.md#constraint-satisfaction-and-checked-evidence) separates isolated one-pass improvement from full-goal evidence selection.
- [Failure ownership and constraint resources](../../spec/static-semantics.md#failure-ownership-and-constraint-resources) adds vector, determination, improvement, and validation work.
- [Interface-evidence lowering](../../spec/elaboration.md#interface-evidence-lowering) substitutes complete interface applications while retaining existing method-evidence Core forms.
- [Generated interface evidence](../../spec/dynamic-semantics.md#generated-interface-evidence) records that the new metadata and type arguments erase without evaluator changes.
- [Current Ash](../../spec/README.md#current-ash) and executable examples describe relational interfaces only after implementation evidence closes.

## Resulting specification truth

After the complete product branch is integrated into `main`, current Ash has
multi-parameter method-only interfaces and an optional single total forward
determination edge. Complete ordered interface applications cross checking,
summaries, evidence, linking, and Core authentication. Improvement fills only
the dependent complement from an inference-free key and never chooses evidence
or reverses the relation. Evidence still lowers to ordinary functions and
erased type operations, and evaluation remains free of interface state.

## Interactions

Associated-output syntax can later introduce a named parameter and lower it to
one dependent position plus the same complete relational application. That
future feature still requires projection identity and elaboration; this
proposal does not add either.

Future effect APIs, handlers, and providers may reuse stable identities,
ordered applications, and selected first-order matching. Their rows,
continuation contracts, and dynamic resolution remain distinct semantics under
AD-0007 and AD-0008.

Future propositions and proofs may reuse typed identities and ordered
arguments. Proof authority, assumed versus proven status, and optimizer facts
must use a separate authenticated evidence family rather than implementation
selection.

Future existential packages may hide any application argument while preserving
its equality relationships with payloads and evidence. Complete applications
and encapsulated evidence producers prevent that work from rewriting interface
heads. Existentials still require separately proposed binders, pack and unpack
scope, Core forms, generativity, and evidence authority.

## Non-goals

This proposal does not add:

- associated-output declarations, projections, equations, or families;
- multiple, partial, chained, cyclic, reverse, or injective dependencies;
- neutral parameters or alternative determinant keys;
- projection or type-family normalization and termination;
- method or associated-output defaults;
- specialization, priority, negative implementations, or fallback selection;
- context-mediated implementation coverage;
- prerequisite-only or existential implementation binders;
- different-width generic prerequisite decrease in this increment;
- a general constraint store, higher-order matching, or type lambdas;
- source-visible dictionaries or first-class interface evidence;
- effect rows, handlers, providers, proof terms, propositions, existential
  packages, generative identities, or dynamic module loading;
- a new Core interface node, runtime lookup, evaluator state, or production
  resource-limit increase; or
- package manifests, persistent summaries, separate object linking, or a
  distributable artifact format.

## Required evidence

Implementation must provide:

- exact syntax, recovery, span, resolution, binder-order, arity, and kind tests
  for two- and three-parameter interfaces and applications;
- ordinary relations, single and composite keys, non-final dependent positions,
  and mixed `Type` and higher-kinded parameters;
- method-seed acceptance and rejection, known-key improvement, dependent
  agreement, atomic dependent-tuple conflict without partial inference
  publication, unknown-key ambiguity, pre-pass snapshot isolation, absence of
  cross-obligation unlocking even when the skipped goal later becomes complete,
  and dependent-to-key non-reversal;
- requirement-only dependent binders, duplicate complete requirements,
  duplicate keys, abstract evidence priority, and absence of cross-requirement
  closure;
- generic self-coverage, full-head overlap, distinct-output key conflict, stable
  identity deduplication, generalized all-bare-selection-key rejection, and
  first-combined-closure ownership;
- determinant-based orphan positive and negative cases and multi-argument
  equal-width pointwise generic prerequisite decrease, different-width
  rejection, and full-application ground cycles;
- local, imported, facade, re-export-diamond, private, hidden, opaque, and
  higher-kinded applications checked solely from body-free summaries;
- exact abstract, current, concrete, prerequisite, and polymorphic-method
  evidence with complete application and argument order;
- tampering matrices for missing, extra, reordered, wrong-kind, wrong-identity,
  wrong-position, mismatched-key, and mismatched-dependent summary, linked, and
  Core carriers;
- unchanged Core feature inventory, transforms, evaluator values, traces, and
  runtime failures, including one linked executable relational program;
- exact additive resource formulas, exact-success and one-short failures,
  atomic retry, wide vectors and closures, deep types, and small-stack accepted
  and rejected disposal;
- predecessor migration showing every unary interface is the width-one,
  no-edge case; and
- normative specification reconciliation, retained evidence, independent
  semantic and Rust/resource reviews, Markdown and link review, and the full
  repository verification gate.
