# DN-0023: Interfaces and Implementations

- ID: `DN-0023`
- Status: exploring
- Related: [DN-0020: Ash Dialect Milestones](DN-0020-ash-dialect-milestones.md), [DN-0022: Passive Static Modules](DN-0022-passive-static-modules.md), [DN-0011: Modules, Providers, and Resolution](DN-0011-modules-providers-and-resolution.md), [DN-0006: Initial Type System](DN-0006-initial-type-system.md), [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), the [passive-module evidence](modular-ash/evidence.md), and the [interface implementation evidence](modular-ash/interfaces-evidence.md)

> This design note is informative. It records the exploration that led to the
> implemented method-only interface increment, but it does not define current
> Ash. The [specification](../../spec/README.md) is the source of current
> language behavior.

## Question

What is the smallest coherent type-class-like `interface` and `impl` increment
that exercises separately checked passive modules, constrained rank-1 code,
typed implementation selection, and explicit Core evidence without turning
modules into signatures or adding associated-type machinery prematurely?

## Result

Method-only interfaces and implementations now provide that increment. Ash has
one-parameter interfaces, explicit requirements on global signatures, private
and public implementations, direct-dependency implementation availability,
typed selection retained on checked occurrences, linked evidence validation,
and lowering through ordinary pure Core functions and applications. The
original interface increment's normative checkpoint is unsigned commit
`f783271`. The [current specification](../../spec/README.md) includes the
outer-`Function` correction retained by unsigned commit `089c54e`. After Task
6, the [interface implementation evidence](modular-ash/interfaces-evidence.md)
will record the final reviewed product checkpoint.

The evidence report records the implemented corpus, diagnostic and resource
boundaries, Core and evaluator locality, and the unspecialized generic evidence
trace. Current semantic details belong to the specification, not this retained
design account. Associated types, specialization, first-class dictionaries,
and runtime implementation lookup remain outside the implemented increment.

## Original boundary

When this exploration began, Modular Ash had passive declarations-only modules,
canonical module-qualified identities, direct imports, private and opaque
types, body-free checked export summaries, rank-1 schemes, and one linked pure
Core program. It had no interface declaration, implementation declaration,
constraint, associated projection, implementation selection, or source-level
evidence value.

Project prose then used *global interface* and *external interface* to mean a
function's declared type signature. The implemented specification uses *global
signature* so `interface` has one Ash meaning.

The remaining sections retain the original alternatives, selected model,
comparison cases, and future pressure. Statements about a candidate or
recommendation describe that exploration; they do not supersede the current
specification.

The passive-module boundary is the starting invariant:

```text
canonical module identity
    -> body-free checked dependency summaries
    -> separate resolution and checking
    -> dependency-ordered linked Core groups
    -> whole-program validation and evaluation
```

The proposed relationship was required to fit between checking and Core
construction:

```text
checked constraint + available checked impl facts
    -> satisfaction or structured rejection
    -> checked typed method evidence
    -> ordinary Core type and term application
```

Generated export summaries remain compiler artifacts. They do not become
source module signatures. Interface facts erase only after the judgment that
authenticates selection and constructs typed evidence.

## Constraints

### Preserve direct module dependencies

A module may use its own implementation declarations and public
implementation facts from modules it directly imports. A dependency's imports
do not become the importer's ambient implementation scope. Evidence already
selected inside a separately checked dependency remains valid in that
dependency's constrained or concrete Core.

Complete and targeted imports differ only in source-name bindings. Either form
names a direct dependency and therefore makes that dependency's public
implementation facts available. Implementations are anonymous typed facts,
not names selected by a targeted import.

### Resolve typed identities, not spellings

Interface, method, and implementation identities are qualified by their
defining module:

```text
InterfaceId = defining ModuleId + interface declaration
MethodId    = InterfaceId + method declaration
ImplId      = defining ModuleId + impl declaration
ImplMethodId = ImplId + MethodId
RequirementId = (global BinderId or ImplId) + requirement order
```

Aliases, alternate canonical paths, and equal display spellings cannot create
or satisfy a second relationship. Repeated routes to one `ImplId` deduplicate
before coherence checks.

### Keep constraint resolution separate

Type equality, type normalization, unification, and constraint satisfaction
remain separate rule responsibilities. Constraint selection never solves an
ordinary inference variable merely to make one implementation applicable. An
obligation whose type is not determined at its closure boundary is ambiguous.

The first implementation may keep scoped obligations and evidence holes inside
the existing elaborator. A persistent constraint IR, general constraint store,
or retained interface Core dialect requires additional evidence and, if it
becomes an architectural boundary, a separate architectural decision.

### Keep modules passive

An implementation declaration adds a checked static relationship. Importing
it performs no registration, initialization, runtime lookup, or dispatch-table
mutation. Dynamic loading, providers, registration, unloading, handlers, and
effects remain outside this increment.

## Candidate increments

### Method-only interfaces with typed evidence

The smallest candidate adds one-parameter interfaces, required methods,
explicit constraints on global signatures, local and public implementations,
generic structural implementations, and implicit source evidence made explicit
during elaboration.

This candidate exercises every new owning judgment: interface identity,
implementation availability, coherence, constraint satisfaction, separately
checked constrained exports, evidence construction, Core validation, and
execution. It is sufficient for the first core-versus-library comparison.

### Methods and associated types together

Adding associated types in the same product increment would also require
projection syntax, projection identity, normalization, equality with
unresolved projections, kind checking, cycle rules, summary representation,
and evidence-dependent type substitution. Those are separable questions.

Associated-type examples remain required design pressure. They should test
whether the method-only boundaries preserve the selected impl and its type
arguments long enough to add an associated output later. They do not justify
product associated types before a method-only corpus demonstrates a consumer.

### Specialization-only interfaces

Whole-program specialization could erase every implementation choice by
cloning constrained code for concrete callers. It does not represent a
separately checked exported function whose constraint remains abstract, and it
makes correctness depend on final-link optimization. This conflicts with the
implemented body-free summary boundary.

Specialization remains an optional validated transform after evidence-passing
Core works independently. It is not the semantic baseline.

### Explicit source dictionaries

A source-level dictionary value could make evidence selection explicit and let
callers store or choose implementations directly. Preserving interface identity
would require a compiler-generated nominal dictionary or another typed
first-class evidence representation; a structural tuple would erase identity
before source checking had authenticated it. Explicit dictionaries would also
need construction, naming, visibility, and ambiguity rules.

The selected candidate instead infers evidence in source and makes it
explicit only in checked elaboration and Core method arguments. This supports
separately checked constrained code without adding a new source value category.
No current corpus case needs to store or pass evidence independently from a
constrained function, so first-class dictionaries are deferred.

### Interfaces as module signatures

A source signature could describe a module's required and provided members.
That is a different abstraction. It would conflate module nameability and
opacity with constraint satisfaction and implementation selection. This
direction is rejected for the Modular Ash interface increment.

## Selected source model

### Declarations and constraints

An interface has one parameter of kind `Type` and one or more required method
signatures. Every method type contains that parameter and has `Function` as its
outermost constructor, so ordinary typing determines the requested interface
argument and every evidence slot is a function. Function types may also occur
inside the method domain or codomain. A method introduces no additional type
parameters or constraints. Methods have no default bodies in the first
increment.

The accepted change proposal specified one trailing `where` clause shared by
global signatures, operational headers, and impl heads. The earlier comparison
form is:

```ash
pub interface Equal<A> {
    equal : (A, A) -> Bool
}
```

The interface name shares the nominal type namespace. Its method names enter
the term namespace and must not conflict with another file-wide term binding.
A public interface exports its name and methods together. A private interface
and its methods remain local.

A global signature may carry an ordered nonempty constraint list:

```ash
pub same : (A, A) -> Bool where Equal<A>
same pair = equal(pair)
```

Multiple constraints use a comma-separated trailing `where` list. Every
constrained type variable must also occur in the value type so that a caller's
ordinary typing determines the requested implementation. Duplicate constraints
are rejected. Constraints are part of the checked rank-1 scheme and export
summary; they are not ordinary source types or runtime values.

An inline operational global carries the same ordered requirement list in its
header and produces the same constrained scheme. The accepted change proposal
selected one token placement for both presentations; equational and operational
globals do not have different constraint semantics.

An interface method behaves as a constrained term with the interface's
parameter and constraint. A complete import qualifies it by module alias, such
as `Equality.equal`. Targeted imports may bind the public interface name and
method term independently through their existing namespaces.

### Implementation declarations

An implementation supplies every required method exactly once. It supplies no
extra method, default, associated declaration, or independently public member.
Implementation method bodies reuse the existing equational function-body
rules; the interface supplies their signatures.

```ash
pub impl Equal<Int> {
    equal (left, right) = left == right
}
```

An implementation may bind type parameters through its head and state explicit
prerequisites:

```ash
pub impl Equal<Option<A>> where Equal<A> {
    equal (left, right) = match (left, right) {
        (None, None) => true
        (Some(left_value), Some(right_value)) => equal((left_value, right_value))
        _ => false
    }
}
```

The accepted change proposal selected this `where` spelling as part of its
complete grammar.

`impl` is private by default. `pub impl` publishes an anonymous implementation
fact in the defining module's checked export summary. A public implementation
must implement a public interface. Its head may retain a private local nominal
identity without exporting that type's source name; this permits inferred
composition over a hidden carrier. It may also mention public and opaque types.
Opacity never grants constructor access to an external implementation body.

Resolution allocates the `ImplId` and every `ImplMethodId` before any method
body is checked. It also allocates one hidden module-qualified `BinderId` for
each impl method and records its `ImplMethodId` mapping. Impl member heads do
not introduce ordinary lexical term bindings that shadow interface methods.
Occurrences such as `equal` inside an impl body resolve to the interface
`MethodId`; typed constraint resolution chooses prerequisite or current-impl
evidence from the inferred argument type.

All methods of one impl enter one simultaneous evidence scope. The current impl
may satisfy an obligation for its own head, allowing direct and mutual method
recursion; an obligation for a proper component of a generic head uses the
impl's declared prerequisite evidence instead.

Impl head variables are rigid while its methods check. Self evidence satisfies
only an obligation identity-equal to the current head under that same rigid
substitution; it does not freshly instantiate the generic impl. This prevents a
method of `impl I<Option<A>>` from using itself to satisfy
`I<Option<Option<A>>>` and bypassing the proper-subterm rule.

### Orphan and overlap rules

An implementation is legal only when its defining module owns either the
interface or the outer nominal constructor of the head type. A primitive head
has no source owner, so only the interface owner may implement an interface for
`Int`, `Bool`, or `Unit`. A bare type-variable head is rejected.

One module's effective implementation environment contains its local impls and
deduplicated public impls from direct dependencies. It must be coherent before
body checking: two distinct impls for the same interface are rejected when
freshened heads can unify. Prerequisites do not make overlap safe. Source or
import order selects only which conflict is reported first; it never selects a
winner.

The orphan rule and Ash's acyclic dependency graph make overlapping public
impls from distinct modules unreachable: unifying heads require a shared
interface and outer-head ownership pair, which only one defining module can
own. The checker still deduplicates direct implementation facts and rejects
overlap among admitted facts in an effective environment.

There are no priorities, negative impls, default impls, specialization rules,
or condition-entailment exceptions in this increment.

### Generic prerequisites and termination

Every type variable in an implementation prerequisite must occur in its head.
After freshening and alpha-normalizing a generic impl, the sole type argument
of every prerequisite must be a strict syntactic subterm of the impl head's
type argument. This admits structural evidence such as `Equal<A>` required by
`Equal<Option<A>>` and rejects rules that expand their own goals. A ground
prerequisite is exempt from the subterm test and uses the active-goal cycle
check below.

Ground prerequisite cycles can still cross interfaces. Resolution uses an
explicit worklist and an active-goal set keyed by canonical
`(InterfaceId, arguments)`. Re-entering an active goal is a constraint cycle,
not resource exhaustion. A graph-wide work budget separately bounds wide or
deep valid searches.

This structural decrease rule belongs only to the method-only increment.
Associated projections may change normalized type size and require a different
termination account.

## Satisfaction and checking

Interface checking authenticates parameter scope, distinct method names,
method signatures, and public/private consistency. Implementation checking
then:

1. resolves the interface and head types by identity;
2. checks the orphan rule and generic prerequisite restrictions;
3. checks overlap in the effective implementation environment;
4. substitutes the implementation head for the interface parameter;
5. checks method completeness and rejects extra members; and
6. checks each method body against the substituted method signature under its
   prerequisite evidence.

A module publishes no interface or impl summary facts until its complete body
checks, matching the existing all-or-nothing module summary boundary.

Instantiating a constrained scheme creates ordinary type inference variables
and ordered pending evidence obligations. Ordinary bidirectional typing first
determines the obligation arguments. At a definition closure boundary, each
obligation must be satisfied by:

- an identity-equal abstract constraint declared by the current global
  signature or current impl prerequisites; or
- exactly one implementation in the effective environment.

Identity-equal abstract evidence is considered first and shadows impl search.
This preserves the meaning of a caller-supplied constraint even when a generic
impl in the same environment could also match. Abstract evidence follows its
declaration order. Global requirement evidence precedes the source value
arguments of a constrained global. Impl prerequisite evidence precedes the
source value arguments of every impl method.

An unresolved inference variable does not cause implementation search to guess
a type. A local generalized function cannot infer and export a new constraint
in the first increment; it may use evidence already available from its
enclosing checked global. Recursive constrained globals reuse their declared
abstract evidence and do not acquire polymorphic recursion.

The entry module's `main` has an empty requirement list in addition to its
existing monomorphic `Unit -> R` contract. Every obligation in its body must
resolve to concrete available implementation evidence.

## Export summaries

A body-free checked summary adds:

- public interface identities, parameter metadata, ordered method identities,
  method schemes, and provenance;
- public impl identities, canonical heads, prerequisite constraints, ordered
  `ImplMethodId` to module-qualified `BinderId` mappings, checked method
  schemes, and provenance; and
- hidden nominal identity facts needed by public constraints, public interface
  method schemes, or impl heads, without source nameability or constructor
  access.

Implementation head parameters are bound summary metadata and may be
alpha-renamed by an importer. Summaries carry identities and checked schemes,
not implementation bodies. Candidate matching never uses display names.

Every constraint in a public global scheme names a public interface. Every
prerequisite of a public impl also names a public interface. Private interface
identities do not leak into summaries; a public impl may still retain a hidden
nominal head because existing summaries can carry that nominal identity without
making its spelling available.

Imported impl facts are available only in the directly importing module. They
are not copied into that module's export summary as new impl exports. A
constrained exported global retains its abstract constraint; a global whose
body selected concrete evidence retains per-occurrence `EvidenceSelection`
facts as structural annotations on the exact checked method or constrained-term
occurrences that require them. Core synthesis consumes the annotation attached
to that occurrence; it never joins a detached vector by span. The recursive
selection has two forms:

```text
EvidenceSelection =
    Abstract {
        requirement: RequirementId,
        methods: [MethodId]
    }
  | Implementation {
        impl: ImplId,
        substitution,
        prerequisites: [EvidenceSelection],
        methods: [ImplMethodId]
    }
```

The abstract form refers to ordered evidence parameters from a constrained
global or impl prerequisite. The implementation form records the matched type
substitution, recursively selected prerequisites, and ordered impl methods.
Later linking retains these facts without repeating implementation selection.
Linked interface-evidence validation authenticates them, and Core synthesis
then consumes them exactly once. The body-free summary exposes only the
constraints and impl facts a dependent needs.

## Core evidence and erasure

The selected elaboration flattens one logical interface
dictionary into ordered method evidence. Constraint order follows the source
signature; method order follows the interface declaration. Each evidence slot
is an ordinary function value.

Conceptually:

```text
parameters: [A]
requirements: [Equal<A>]
value type: (A, A) -> Bool

    lowers to

TypeAbstraction A (
    Function equal_method (
        Function pair (... equal_method pair ...))))
```

At a concrete call, constraint resolution supplies the selected impl's method
function binders. At an abstract call, it supplies the current constrained
global's evidence binders. Type application, evidence application, and value
application are ordinary existing Core operations.

Implementation methods become hidden source-backed Core globals. Resolution
allocates their module-qualified `BinderId` values alongside stable
`ImplMethodId` values, and checked summaries retain that mapping. The defining
checked module retains every method body and identity, so an exported impl
cannot refer to a missing linked definition.

A selected generic impl method is first type-applied with the head substitution
and then term-applied to each recursively selected prerequisite method in
declared constraint and method order. The result supplies one evidence slot for
the original obligation. The impl summary's checked method scheme and ordered
prerequisites make every intermediate application derivable and checkable.

A generic implementation method therefore accepts its prerequisite method
evidence before its source arguments. All impl-method binders join the defining
module's existing single recursive group with its ordinary globals. This
preserves global-to-method and method-to-global recursion. No runtime impl
registry, dictionary lookup, interface node, or evaluator dispatch rule is
required.

Typed elaboration produces the per-occurrence `EvidenceSelection` records and
stores them in graph-owned checked modules. Linking retains those selections in
the combined checked groups. Linked interface-evidence validation authenticates
the selections against the combined interface and implementation registries and
produces a validated capability before Core synthesis. Core synthesis consumes
the validated selections: it resolves stable `ImplMethodId` values through
retained module-qualified `BinderId` mappings and releases the selections after
constructing the applications.
These records extend the existing `CheckedModule` boundary; they are not a
separate typed surface tree, general constraint IR, or new Core dialect.

Before erasure, that interface-aware evidence validation checks:

- exact interface, method, impl, and nominal identities;
- ordered and complete method slots, even when slot types are structurally
  equal;
- head matching and recursively satisfied prerequisites;
- abstract `RequirementId` ownership, checked method schemes, substitutions,
  ordering, and provenance; and
- absence of unsolved inference variables.

For a generic impl it additionally checks the head type applications,
prerequisite evidence applications, and resulting method slot type at every
intermediate step.

After this judgment, interface and impl identities may erase. The independent
Core validator then authenticates the resulting type abstractions, evidence
binders, module-qualified impl-method binder scope, applications, recursive
scope, types, and Core provenance. This follows the same boundary as module
erasure: source relationships are checked before Core, and Core independently
validates the lower-level program it receives.

Impl selection is complete before evaluation. A generic evidence expression may
use type and prerequisite-evidence applications; existing pure machine frames
evaluate it to a function closure before the source value argument is applied.
Unspecialized evidence passing therefore introduces no runtime search or new
failure mode. The retained implementation evidence records its application
order and final observation as a baseline for any later specialized Core.

A future specialization transform may replace known evidence binders and
applications with selected method globals. The unspecialized evidence-passing
program remains executable and supplies the differential oracle.
Specialization is neither required for correctness nor part of this first
increment.

## Elaboration traces

These traces test the representation against the implemented separate-checking
and Core boundaries. Identity labels are abbreviated for readability; each one
denotes the stable qualified identity described above.

### A constrained summary crosses a module boundary

Suppose `equality.ash` defines public `Equal<A>` and:

```ash
pub same : (A, A) -> Bool where Equal<A>
same pair = equal(pair)
```

Checking `same` attaches `Abstract { requirement: same.0, methods: [equal] }`
to its `equal` occurrence. Its body elaborates conceptually to:

```text
same = /\\A. \\equal_evidence. \\pair. equal_evidence pair
```

The body-free summary exports `same` with its ordered `Equal<A>` requirement;
it does not export the body or an implementation choice. A caller that directly
imports a public `Equal<Int>` impl selects its `equal_int` method and constructs:

```text
same [Int] equal_int (1, 1)
```

The dependency was checked with abstract evidence. The caller supplies concrete
evidence without rechecking or specializing the dependency.

### A generic impl consumes prerequisite evidence

For `impl Equal<Option<A>> where Equal<A>`, the impl method has the conceptual
Core scheme:

```text
equal_option : forall A. equal_A -> (Option<A>, Option<A>) -> Bool
```

An `equal` occurrence over contained `A` values in that body receives
`Abstract { requirement: impl.0, methods: [equal] }`. Selection for an
`Equal<Option<Int>>` obligation records:

```text
Implementation {
    impl: equal_option_impl,
    substitution: [A := Int],
    prerequisites: [
        Implementation {
            impl: equal_int_impl,
            substitution: [],
            prerequisites: [],
            methods: [equal_int]
        }
    ],
    methods: [equal_option]
}
```

Core synthesis constructs the evidence function once:

```text
equal_option [Int] equal_int
```

It can then supply that function to a constrained callee. Selection and cycle
checking remain typed judgments; evaluation sees only existing applications.

### Same-typed slots retain method identity and order

For an interface whose ordered methods are:

```ash
first : (A, A) -> A
second : (A, A) -> A
```

both evidence slots have the same structural type. The constrained scheme still
orders them by `[first MethodId, second MethodId]`, and elaboration produces:

```text
/\\A. \\first_evidence. \\second_evidence. \\pair.
    second_evidence (first_evidence pair, second_evidence pair)
```

Swapping the two `ImplMethodId` values is rejected by interface-aware evidence
validation even though ordinary Core types alone would accept the swap.

### Recursive methods keep source and Core identities distinct

Suppose one impl defines two mutually recursive methods. Each body occurrence
resolves to its interface `MethodId`, then exact-rigid current-impl evidence maps
that occurrence to the corresponding `ImplMethodId`. Resolution has already
allocated module-qualified binders:

```text
impl.first MethodId  -> this_impl.first ImplMethodId  -> module first BinderId
impl.second MethodId -> this_impl.second ImplMethodId -> module second BinderId
```

Both hidden binders enter the defining module's ordinary recursive group. Calls
between them therefore use normal recursive Core references. A call on a proper
component of the generic head instead selects declared prerequisite evidence;
the lexical spelling does not choose between those cases.

### Abstract evidence passes through another constrained caller

If `all_same : List<A> -> Bool where Equal<A>` calls imported `same`, its
call-site selection is
`Abstract { requirement: all_same.0, methods: [equal] }`. The Core shape is:

```text
all_same = /\\A. \\equal_evidence. \\values.
    ... same [A] equal_evidence (...) ...
```

No impl search is repeated inside `same`, and the imported summary need not
expose its body. A concrete caller later selects one implementation and passes
the resulting method function into `all_same`; that same abstract slot flows
through every nested constrained call.

Together these traces preserve every source relationship until its owning
validation judgment and then use only existing Core binders and applications.
They exposed no unresolved representation question, so the increment did not
require a disposable compiler probe before the accepted change proposal.

## Associated-type pressure

The design comparison retains one illustrative case:

```ash
interface Iterator<I> {
    type Item
    next : I -> Option<Item>
}
```

One selected impl determines `Item`, and every occurrence of that projection
must denote the same type. A later associated-type design should compare
normalized outer type evidence, retained projection types, and their behavior
under separate module checking. DN-0023 selects none of those representations.
If source equality or separate checking needs unresolved projections to survive
longer, that would be evidence for an explicit projection type and
normalization boundary.

The method-only product increment reserves stable interface and impl identities
and keeps selection facts until evidence construction. It does not reserve
surface syntax, a placeholder Core node, or a dormant normalization engine for
associated types.

## Failure ownership and resources

Failures remain owned by the first judgment that can establish them:

- parsing owns malformed interface, constraint, and impl syntax;
- resolution owns interface and method names, access, identities, and imported
  summary authentication;
- interface and impl checking own malformed declarations, orphan violations,
  overlap, prerequisite admissibility, method membership, and method typing;
- constraint resolution owns unsatisfied, ambiguous, cyclic, and resource
  failures;
- linked interface-evidence validation owns forged or inconsistent retained
  evidence as `evidence.validation.*`; and
- Core validation owns malformed lowered binders, applications, types, scope,
  dialect membership, and provenance.

Constraint-satisfaction diagnostics retain the requirement use as primary and
relate the interface, selected or competing impl declarations, method
declaration, impl method, and import occurrence needed to explain the result.
A local orphan or overlap diagnostic uses the offending impl head as primary.
Equal display names from different modules remain distinct.

One graph-wide constraint budget charges proportional work before retaining:

- imported interface and impl summary metadata;
- implementation-environment construction and route deduplication;
- overlap comparisons and type traversal;
- obligations, candidate matches, prerequisite edges, active goals, and
  evidence nodes.

A future specialization experiment would own and report its separate
output-growth measurement; that cost is not part of the first product
increment's constraint budget.

Candidate traversal and diagnostic selection use deterministic dependency,
import, and source order. Prerequisite resolution and destruction use explicit
worklists at admitted depth.

## Original required comparison corpus

The original positive corpus required:

- a local method-only interface, concrete impl, constrained call, and exact
  observation;
- a public interface in one module, public impl in another, constrained
  generic function in a third, and monomorphic caller in the entry module;
- a separately checked constrained export that remains abstract until a caller
  supplies concrete evidence;
- a generic structural impl whose proper-subterm prerequisite resolves;
- one hidden-carrier impl that composes without exporting the carrier name;
- one opaque-type impl whose body cannot inspect representation;
- complete and targeted method imports plus automatic impl availability from a
  direct dependency;
- alternate routes that preserve one interface and impl identity;
- direct routes that deduplicate one implementation identity, plus synthetic
  checked facts that exercise effective-environment overlap;
- recursive and higher-order constrained functions that thread evidence;
- two same-typed method slots whose declaration order remains distinct in the
  checked evidence plan;
- paired equational and operational constrained globals using the same
  satisfaction rule;
- an explicit elaboration trace comparing implicit source evidence with the
  rejected first-class dictionary candidate; and
- a bounded representation trace comparing retained evidence with later
  specialization, without making specialization product behavior.

The original negative corpus required:

- a private interface access failure and a private impl unavailable to an
  importer, producing an unsatisfied obligation without leaking private
  metadata;
- a foreign-interface/foreign-type orphan and an unconstrained blanket impl;
- duplicate and generic-overlap local impls, plus authenticated
  effective-environment overlap facts;
- no transitive ambient impl through an intermediary import;
- unsatisfied and inference-ambiguous obligations;
- a constrained `main` and a public requirement naming a private interface;
- a rigid variable incorrectly solved to make an impl apply;
- expanding generic prerequisites and ground prerequisite cycles;
- missing, duplicate, extra, and wrongly typed methods;
- a failed module or impl body publishing no usable summary;
- equal-spelled identities from different modules failing to satisfy each
  other;
- malformed evidence plans with wrong or reordered method identities;
- malformed lowered Core evidence types, applications, recursive flow, scope,
  and provenance; and
- deterministic graph-wide budget exhaustion and deep stack-safe resolution.

The associated-type comparison should cover one resolved projection, one
ambiguous projection, one cycle, one wrong associated definition, and one use
across a module summary. These are design evidence, not required product cases
for the method-only increment.

## Selected increment and exclusions

The selected and implemented product increment contains:

- one-parameter method-only interfaces;
- required methods without defaults or method-local polymorphism;
- explicit constraints on rank-1 global signatures;
- private and public impls, including generic structural impls with explicit
  decreasing prerequisites;
- scoped direct-import availability, strict overlap rejection, and the orphan
  rule above;
- implicit source evidence made explicit as ordered method functions;
- interface-aware evidence validation followed by lowering into the current
  pure Core; and
- structured diagnostics and graph-wide resource accounting.

It excludes associated types, multi-parameter interfaces, higher-kinded
parameters, default methods, specialization as semantics, priorities, negative
impls, first-class source dictionaries, inferred local constraints, interface
objects, module signatures, import re-exports, dynamic loading, providers,
registration, unloading, effects, and runtime implementation lookup.

## Implemented boundary and future pressure

The accepted change proposal selected the method-only transition explored here,
and the implementation task completed it. The current
[specification](../../spec/README.md) now owns the grammar, checking, selection,
evidence, lowering, and evaluation rules. The retained
[implementation evidence](modular-ash/interfaces-evidence.md) maps the original
comparison corpus to tests and implementation boundaries.

The interface increment supplies the consumer needed by a separately
authorized core-versus-library audit. This note does not perform or authorize
that audit. Associated-type examples continue to pressure normalization and
separate checking, while specialization may later compare optimized Core with
the retained unspecialized evidence trace. Associated types, specialization,
first-class dictionaries, and runtime lookup remain future design questions,
not partially implemented behavior.
