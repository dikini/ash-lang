# CP-0010: Method-Local Type Parameters

- ID: `CP-0010`
- Status: proposed
- Related: [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), [DN-0023: Interfaces and Implementations](../design/DN-0023-interfaces-and-implementations.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0009: Ordered Resolved-Global Binder Authority](../decisions/AD-0009-ordered-resolved-global-binder-authority.md), the [explicit-import evidence](../design/lib-ash/imports-evidence.md), and the [explicit-kind evidence](../design/lib-ash/kinds-evidence.md)

> This proposal is not current Ash.

## Current behavior

An interface method has no type-parameter list. Its type must contain the
interface parameter, contain no other free type variable, have kind `Type`, and
have `Function` as its outermost constructor. Resolution retains a free
method-local type candidate only so interface checking can reject it with
`interface.method-parameter`.

A method occurrence behaves as a one-requirement constrained rank-1 scheme.
Checking instantiates the interface parameter, records one occurrence-local
evidence obligation, and later selects one abstract or concrete method
function. Checked interface facts, body-free summaries, linked facts, and
evidence lowering retain a method monotype after substituting the selected
interface argument.

Every generated evidence binder is therefore monomorphic. A constrained
global's Core scheme flattens each required method into an ordinary function
domain. A generic implementation method uses one outer rank-1 scheme for its
implementation-head parameters, followed by monomorphic prerequisite evidence
domains and its source method type.

Core admits `Forall` only as one complete outer scheme. It rejects a scheme in
a function domain or codomain, tuple, constructor payload, pattern, ordinary
term binder, or other monotype position. Core type application instantiates
all binders of one outer scheme at once. These restrictions, together with the
absence of source `forall` and expression type application, keep source values
rank-1.

## Proposed behavior

### Method binders and kinds

An interface method may carry one explicit type-parameter list after its name:

```ebnf
interface_method ::=
  identifier [ type_parameters ] ":" type ;
```

The existing `type_parameters` and `type_parameter` productions apply. For
example:

```ash
interface Functor<F : Type -> Type> {
    map<A, B> : (A -> B, F<A>) -> F<B>
}
```

An absent method list binds no method-local parameter. A present list is
complete and ordered: its binders are distinct from one another and from the
interface parameter, every listed binder occurs in the method value type, and
every free type variable other than the interface parameter is listed. The
written list fixes scheme order. An omitted kind annotation means `Type`; Ash
does not infer a method-binder kind.

The interface parameter and method-local parameters scope over that method
signature only. An implementation equation does not inherit the interface's
method-parameter spellings. Its expected type carries rigid method-local
variables, but source annotations in the implementation body cannot name them
without a future explicit implementation-method binder form.

Resolved method binders receive canonical source identities in interface and
method declaration order, then written binder order. Their defining records
remain the authority for spelling, kind, origin, owner, and order. The method
type must still contain the interface parameter, synthesize kind `Type`, and
have `Function` as its outermost constructor.

### Method schemes and occurrences

Each checked interface method retains this scheme under its owning interface
parameter:

```text
MethodScheme = forall method_parameters. method_value_type
```

The method occurrence has the conceptual constrained scheme:

```text
forall interface_parameter method_parameters.
    Interface<interface_parameter> => method_value_type
```

Checking one occurrence instantiates every binder with a fresh inference
variable of the same fixed kind. Only the interface argument creates an
evidence obligation. The occurrence also retains the ordered, zonked
method-local arguments produced by ordinary checking. Evidence selection does
not choose, infer, or refine those arguments.

An unresolved interface argument remains `constraint.ambiguous` at the
occurrence's evidence-closure boundary. An otherwise unresolved method-local
argument remains `type.ambiguous` under the existing inference-closure rule.
This increment does not add method-determination or improvement rules.

Method schemes compare modulo one capture-free, order- and kind-preserving
renaming of their bound method parameters. Free interface, implementation-head,
nominal, and resolved source identities still compare exactly. Monotype
equality and unification do not become alpha-equivalence or higher-order
matching.

### Implementation methods

Checking an implementation substitutes its head argument for the interface
parameter and retains the method-local binders. Each method body checks once
under rigid implementation-head and method-local parameters. The conceptual
checked scheme is:

```text
forall implementation_head_parameters method_parameters.
    evidence(prerequisite_1) ->
    ... ->
    evidence(prerequisite_n) ->
    substituted_method_value_type
```

The two parameter sequences remain distinguishable even when their kinds or
spellings match. A direct recursive occurrence of the same implementation
method reuses its rigid method-local arguments; it cannot gain polymorphic
recursion. Other method occurrences instantiate their declared method schemes
normally.

Method membership, implementation overlap, orphan ownership, prerequisite
termination, exact-current evidence, and concrete selection keep their current
rules. Method-local parameters do not enter implementation heads or
prerequisite goals and cannot affect candidate choice.

### Summaries and linked authentication

A checked interface method and every body-free public mirror retain the
ordered method-binder records and the monotype body separately. Summary
construction retains the hidden identity and kind closure needed by a public
method scheme. Import admission authenticates the complete binder set, order,
owner, kinds, body scope, method identity, and provenance before a dependent
module checks solely from that summary.

The occurrence-local evidence field atomically retains the selected interface
argument, ordered method-local instantiation arguments, and selected evidence.
Linked evidence validation authenticates those arguments against the defining
method scheme, their kinds, the checked occurrence type, and the selected
`MethodId`. It also authenticates every implementation method's combined
parameter order and its relationship to the interface method scheme.

Validation produces the only capability that may authorize polymorphic Core
evidence. A missing, extra, reordered, wrong-kind, wrong-owner, mismatched, or
forged binder, method argument, `MethodId`, `ImplMethodId`, selection, or
adapter relation is an `evidence.validation.*` failure before Core synthesis.
Core synthesis does not select evidence again.

### Authenticated polymorphic Core evidence

The existing Core `Forall`, type abstraction, type application, function, and
application forms are sufficient. A constrained definition's derived Core
scheme may contain a method scheme only as one of its generated evidence
domains:

```text
forall definition_parameters.
    (forall method_parameters. substituted_method_value_type) ->
    ... ->
    source_value_type
```

A monomorphic method keeps its current ordinary function evidence domain.

An abstract selection lowers to its generated evidence binder. At a method
occurrence, Core type application instantiates that binder with the retained
method-local arguments before source term arguments apply.

A concrete or exact-current selection lowers through a generated adapter:

```text
type-abstract method_parameters.
    type-apply implementation_method
      <implementation_head_arguments, method_parameters>
      prerequisite_evidence...
```

The adapter exposes exactly the selected method scheme. It does not specialize
or copy the implementation body. Scheme comparison at its evidence boundary
uses the capture-free alpha-equivalence rule above.

Minimal immutable authentication facts derived from validated linked evidence
survive Core synthesis. They relate each polymorphic evidence position to its
owning constrained definition, requirement and method order, `MethodId`,
interface argument, method scheme, and, for an adapter, the selected
`ImplMethodId` and ordered instantiation relationship. The concrete Rust
representation is not language semantics.

Independent Core validation derives the expected method scheme from those
authenticated facts and canonical type-binder records. It requires every
nested scheme and polymorphic term binder to occur in one exact generated
evidence position, checks its owner and order, validates every adapter and
method type application, and consumes every authentication fact exactly once.
It does not trust a Core node flag or an unchecked copied scheme.

An authenticated evidence variable may be type-applied at a method occurrence
or forwarded to the matching generated evidence domain of another constrained
definition. No other term may introduce, accept, store, or return it. In
particular, nested schemes remain invalid in ordinary function parameters or
results, globals, local bindings, patterns, tuples, constructors, structural
type applications, and evaluator values. A missing, duplicate, unconsumed,
wrong-owner, wrong-position, wrong-method, wrong-kind, capture-producing, or
mismatched Core authentication relation is `core.validation.*` before
evaluation.

Core transformations preserve or rebuild the method authentication relation,
type abstractions, type applications, schemes, binder scope, and provenance,
then pass fresh independent validation. Method authentication facts, method
schemes, and all type operations erase before evaluation. The evaluator gains
no interface value, dictionary, type value, lookup, frame, transition, or
failure mode.

### Failure ownership and resources

Parsing owns malformed method binder-list syntax. Resolution owns duplicate,
unused, or unlisted binders in a present complete list and a binder that
duplicates the interface parameter. Interface checking retains
`interface.method-parameter` for an absent list with another free variable and
for a method that omits its interface parameter. Kind checking owns invalid
method-binder and method-type kinds. Existing type, constraint, implementation,
summary, linked-evidence, and Core judgments own failures only after their
inputs pass the earlier boundary.

Syntax retention charges the syntax budget. Binder records, method schemes,
instantiation arguments, substitution, adapters, and Core types charge the
owning type-work ledger. Summary, occurrence-evidence, selection, route, and
linked-authentication work charge the graph-wide constraint ledger. Core
construction and Core validation retain their separate cumulative ledgers.
Every proportional allocation or traversal charges before publication.

Deep kinds, types, schemes, adapter chains, transformations, validation,
rejection, and disposal use iteration or bounded explicit work stacks. The
implementation evidence must record exact additive formulas, exact-success and
one-short failure, atomic retry, and accepted and rejected teardown. A
production limit change requires proposal review rather than a local increase.

## Semantic delta

- An interface method may bind an explicit ordered list of fixed-kinded
  rank-1 type parameters.
- A method occurrence instantiates its interface and method-local parameters,
  while only the interface argument creates an evidence obligation.
- Implementation methods check under rigid method-local parameters and retain
  their combined head-and-method scheme order.
- Checked summaries and linked evidence authenticate method schemes and exact
  occurrence instantiation arguments.
- Core admits nested schemes only in authenticated compiler-generated method
  evidence positions and compares their bound method parameters by
  capture-free alpha-equivalence.
- Generated adapters make concrete implementation methods usable as
  polymorphic evidence without specialization or runtime dictionaries.
- Ordinary source and Core value positions remain rank-1, and evaluation
  remains type-erased.

## Affected specification areas

- [Syntax grammar](../../spec/syntax.md#grammar) adds the optional method binder
  list and updates the complete interface-method description.
- [Interface, implementation, and requirement identities](../../spec/name-resolution.md#interface-implementation-and-requirement-identities)
  and [Type binder identity and scope](../../spec/name-resolution.md#type-binder-identity-and-scope)
  define method-binder identity, order, completeness, and scope.
- [Kinds, monotypes, and schemes](../../spec/static-semantics.md#kinds-monotypes-and-schemes)
  distinguishes a method scheme from every source monotype position.
- [Inference and rank-1 restrictions](../../spec/static-semantics.md#inference-and-rank-1-restrictions)
  defines method instantiation, ambiguity, alpha-equivalence, escape
  prevention, and recursive rigidity.
- [Interfaces and constrained schemes](../../spec/static-semantics.md#interfaces-and-constrained-schemes)
  defines method schemes, binder completeness, method occurrences, and
  evidence obligations.
- [Implementations](../../spec/static-semantics.md#implementations) defines
  implementation-method checking and combined parameter order.
- [Globals and modules](../../spec/static-semantics.md#globals-and-modules) and
  [Failure ownership and constraint resources](../../spec/static-semantics.md#failure-ownership-and-constraint-resources)
  define summary publication, stage order, diagnostics, and bounded work.
- [Module linking and entry generation](../../spec/elaboration.md#module-linking-and-entry-generation),
  [Interface-evidence lowering](../../spec/elaboration.md#interface-evidence-lowering),
  [Explicit rank-1 operations](../../spec/elaboration.md#explicit-rank-1-operations),
  and [Validation boundary](../../spec/elaboration.md#validation-boundary)
  define retained occurrence arguments, adapters, authenticated nested schemes,
  transformations, and independent validation.
- [Type erasure](../../spec/dynamic-semantics.md#type-erasure) and
  [Generated interface evidence](../../spec/dynamic-semantics.md#generated-interface-evidence)
  define adapter erasure and the unchanged runtime boundary.
- [Specification overview](../../spec/README.md) gains one complete executable
  polymorphic-interface example and the new exclusion boundary.

## Resulting specification truth

After the complete product branch is integrated into `main`, an interface
method may quantify explicit fixed-kinded parameters outside its value
monotype. Each occurrence instantiates those parameters at rank 1 and retains
the exact instantiation used by checked evidence and Core lowering. A separate
dependent module can reconstruct and check the same method scheme from a
body-free summary.

A constrained definition may use one method evidence parameter at several
method-local instantiations. Concrete evidence reaches that slot through a
generated type-abstraction adapter over one selected implementation method.
Linked validation and independent Core validation each authenticate the method
identity, scheme, argument order, adapter, and ownership before the facts
erase.

No source annotation denotes a nested scheme. Source code cannot construct,
accept, store, or return a generally higher-rank value. Core admits a nested
scheme only where authenticated compiler-generated interface evidence requires
it. Every other term slot and every runtime value remains monomorphic.

## Interactions

Explicit kinds apply unchanged to method binders. Omitted annotations mean
`Type`; fixed higher-kinded method binders are allowed, but kind inference,
kind polymorphism, type lambdas, and higher-order unification remain absent.

The current outer-`Function` method rule remains necessary. Substitution and
method-local abstraction preserve the source method's callable body. Explicit
implementation imports and re-exports continue to control concrete evidence
availability independently from method instantiation. Alternate name and
authorization routes preserve the defining `MethodId`, method scheme, and
implementation identity.

The authenticated Core relation extends the same principle as ordered global
binder authority: unchecked Core cannot assert its own source ownership. It
does not change AD-0009's resolved-global row or make interface method binders
global abstraction owners. A separate architectural decision is required if
implementation work discovers a persistent Core representation choice not
already covered by AD-0007's private replaceable-storage boundary.

Method-local parameters supply pressure needed by later multi-parameter,
determination, and default-method comparisons. This proposal does not decide
those semantics. A later default adapter may reuse authenticated method
evidence only after its own accepted proposal.

Three broader approaches do not fit this increment:

- General higher-rank source schemes would let ordinary functions accept or
  return polymorphic values and would expand inference, annotations,
  diagnostics, and Core beyond the required interface evidence.
- Whole-program specialization of each constrained use would not represent a
  separately checked exported function that uses one method at several
  instantiations and would make correctness depend on final-link cloning.
- A new dictionary value or interface-specific Core node would add a second
  function, application, transform, validation, and runtime route when the
  existing typed Core operations can express the bounded evidence.

Authenticated nested schemes therefore add the one representation required by
the corpus while retaining one ordinary Core function and type-operation path.

## Migration

Every predecessor-valid interface, implementation, constrained global, import,
summary, linked program, and Core program remains valid without source edits.
An absent method binder list keeps its current meaning. A free method-local
candidate without an explicit list remains invalid with
`interface.method-parameter`.

The new explicit syntax makes previously rejected polymorphic method
declarations valid. No compatibility grammar, automatic method binder,
implicit higher-rank annotation, or second compiler path is added. The
migration corpus must record exact library and CLI observations for unchanged
programs and deliberate predecessor-failure-to-success cases.

## Non-goals

- Implicit method-local binders, method-local kind inference, kind
  polymorphism, type lambdas, higher-order unification, or impredicative
  instantiation.
- Source `forall`, expression type arguments, polymorphic annotations,
  first-class dictionaries, or general higher-rank function domains and
  codomains.
- Source-visible implementation-method binder spellings or method-level
  requirements.
- Polymorphic recursion, broad local generalization, or a new determination or
  improvement rule.
- Multi-parameter interfaces, associated outputs, functional dependencies,
  defaults, overrides, specialization, negative implementations, or fallback
  selection.
- New implementation import forms, module signatures, effects, handlers,
  providers, propositions, laws, proofs, packages, persistent artifacts,
  separate object linking, dynamic loading, or runtime registries.
- A new evaluator node, interface value, dictionary layout, method dispatch,
  or permanent public representation for Core authentication facts.

## Required evidence

Implementation must use the existing parser, resolver, fixed-kind engine,
bidirectional elaborator, implementation selector, body-free summaries, linked
validation, typed Core dialect, transformations, and evaluator. Every behavior
change follows a witnessed red-green-refactor cycle.

Positive evidence must include one higher-kinded interface whose method has at
least two local parameters and is used at two distinct instantiations inside
one separately checked constrained global. A concrete implementation and an
entry module must take that program through syntax, resolution, kinding,
checking, implementation membership, body-free summary checking, explicit
implementation selection, linking, occurrence validation, adapter synthesis,
independent Core validation, both retained transformations, erasure,
evaluation, library observation, CLI observation, and executable specification
examples.

Focused positive and negative evidence must cover:

- binder-list tokens, projection, recovery, spans, written order, distinctness,
  completeness, optional kinds, higher-kinded method parameters, and an absent
  list's unchanged meaning;
- canonical method-binder identity and source order across interfaces and
  surrounding declaration families;
- kind synthesis, fixed-kinded occurrence instantiation, inference closure,
  method-local ambiguity, interface-goal ambiguity, and no higher-order
  matching;
- implementation checking under rigid head and method parameters, same-method
  recursive rigidity, exact-current evidence, concrete evidence, generic head
  substitution, prerequisites, and method membership;
- detached summary checking, qualified and targeted method imports, explicit
  implementation imports, facades, diamonds, private and public interfaces,
  hidden and opaque kind closure, and stable defining identity;
- one polymorphic abstract evidence slot used at unrelated method
  instantiations and one concrete generated adapter with exact head, method,
  and prerequisite argument order;
- identity and literal-folding transformations followed by fresh independent
  validation and equal evaluation;
- exact library and CLI diagnostics, primary and related spans, causal labels,
  stable reasons, and deterministic failure precedence; and
- predecessor migration, all executable specification examples, and the
  combined interface corpus.

The excluded higher-rank routes require direct negative evidence. Source tests
must reject or keep unavailable source `forall`, explicit expression type
application, polymorphic parameter and result annotations, polymorphic tuple
or constructor fields, storage or return of an uninstantiated method scheme,
passing a method scheme to an ordinary parameter, implicit method binders,
method requirements, and polymorphic recursive self-use.

Summary and linked-evidence tampering must independently reject missing,
extra, duplicate, reordered, wrong-kind, wrong-owner, wrong-origin, or
wrong-spelling method binders; a method body with a free or escaped binder;
mismatched occurrence method arguments; wrong `MethodId` or `ImplMethodId`;
wrong adapter head, method, prerequisite, or argument order; and a selection
whose checked type does not equal its method scheme instantiation.

Core tampering must independently reject every nested-scheme route outside an
authenticated method evidence position; missing, duplicate, unconsumed,
wrong-owner, wrong-position, wrong-order, wrong-kind, wrong-method, or forged
authentication; a method adapter with capture, escape, shadowing, mismatched
scheme, wrong implementation binder, partial or reordered type application,
or wrong prerequisite application; and each malformed result after both
retained transformations. Positive alpha-renaming evidence must accept one
complete capture-free generated method-binder renaming.

Resource evidence must inventory every new syntax, binder, scheme, occurrence,
summary, linked, adapter, Core, transformation, and teardown carrier. It must
record exact additive formulas, exact-success and one-short atomic failure,
retry, deep and wide cases, and accepted and rejected disposal on a 256 KiB
stack without an unapproved production-limit change.

Retain a `docs/design/lib-ash/method-parameters-evidence.md` report naming the
implemented boundary, checkpoints, production and maintenance sites, summary
and Core authentication, tampering matrix, resource formulas, migration,
reviews, verification, and intentional exclusions. Update implementation,
tests, executable examples, normative specification, tool documentation,
DN-0025, trajectory, and retained evidence together.

Independent semantic, implementation and resource, and evidence-lifecycle and
specification reviews must have no unresolved actionable finding. Repeat every
affected review after corrections. Before lifecycle cleanup, run and inspect
`cargo xtask verify`, the complete all-target test inventory, Markdown lint,
relative-link checks, and `git diff --check`.
