# CP-0006: Interfaces and Implementations

- ID: `CP-0006`
- Status: accepted
- Related: [TASK-0012: Implement Interfaces and Implementations](../tasks/TASK-0012-implement-interfaces-and-implementations.md), [DN-0023: Interfaces and Implementations](../design/DN-0023-interfaces-and-implementations.md), [DN-0022: Passive Static Modules](../design/DN-0022-passive-static-modules.md), [DN-0020: Ash Dialect Milestones](../design/DN-0020-ash-dialect-milestones.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), and [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md)

> This proposal is not current Ash.

## Current behavior

Current Ash is the pure, rank-1 language with passive static modules defined by
the [specification](../../spec/README.md). Modules export globals and nominal
types through generated body-free summaries. Imports affect source visibility,
all admitted definitions link into one pure Core program, and the entry module
executes its local monomorphic `main : Unit -> R`.

Ash has no type-class-like interface declaration, implementation declaration,
constraint, implementation selection, associated type, or evidence value. The
specification and implementation still use *global interface* for a function's
declared type. This proposal renames that existing concept *global signature*
when needed to distinguish it from the new `interface` declaration.

## Proposed behavior

### Surface grammar

The proposal reserves `interface`, `impl`, and `where`. It adds no punctuation.
The module grammar gains interface and implementation declarations, and global
signatures may carry ordered requirements:

```ebnf
module ::= { import_declaration line_end } { module_declaration line_end } ;

module_declaration ::=
    type_declaration
  | interface_declaration
  | implementation_declaration
  | global_definition ;

interface_declaration ::=
  [ "pub" ] "interface" upper_identifier interface_parameter
  "{" line_end
  interface_method { line_end interface_method } [ line_end ]
  "}" ;

interface_parameter ::= "<" upper_identifier ">" ;
interface_method ::= identifier ":" type ;

implementation_declaration ::=
  [ "pub" ] "impl" interface_application [ where_clause ]
  "{" line_end
  [ impl_equation { line_end impl_equation } [ line_end ] ]
  "}" ;

impl_equation ::= identifier pattern { pattern } "=" expression ;

global_definition ::= equational_global | inline_operational_global ;

equational_global ::=
  [ "pub" ] global_signature line_end equation { line_end equation } ;

global_signature ::= identifier ":" type [ where_clause ] ;

inline_operational_global ::=
  [ "pub" ] "fn" identifier
  "(" typed_pattern { "," typed_pattern } ")"
  "->" type [ where_clause ] block ;

where_clause ::= "where" constraint { "," constraint } ;
constraint ::= interface_application ;

interface_application ::= interface_reference "<" type ">" ;
interface_reference ::=
    upper_identifier
  | upper_identifier "." upper_identifier ;
```

A `where` clause is nonempty, has no trailing comma, and remains on the
declaration header's logical line. It follows the complete value type in either
global presentation and the complete interface application in an impl head.
This gives constraints one placement without treating them as part of a result
type:

```ash
pub type Option<A> =
    None
    | Some(A)

pub interface Equal<A> {
    equal : (A, A) -> Bool
}

pub impl Equal<Int> {
    equal (left, right) = left == right
}

pub same : (A, A) -> Bool where Equal<A>
same pair = equal pair

pub fn same_operational(pair : (A, A)) -> Bool where Equal<A> {
    equal pair
}

pub impl Equal<Option<A>> where Equal<A> {
    equal (left, right) = match (left, right) {
        (None, None) => true
        (Some(left_value), Some(right_value)) => equal(left_value, right_value)
        _ => false
    }
}
```

An interface body is syntactically nonempty. An impl body may be empty so impl
completeness owns the resulting missing-method rejection. Impl equations reuse
the existing equational body grammar. Maximal contiguous equations with one
head spelling form one method definition. Repeating that method after another
method group is a duplicate definition.

Current unconstrained globals retain their exact grammar and semantics.

### Interface declarations

An interface declares one parameter of kind `Type` and one or more required
methods:

```ash
pub interface Equal<A> {
    equal : (A, A) -> Bool
}
```

Each method signature must contain the interface parameter and at least one
function arrow. It may contain no other free type variable, requirement, body,
default, or associated declaration. Method declaration order is semantic: it
determines the order of evidence slots.

The interface spelling occupies the module's nominal-type name namespace but
does not denote a value type. Interface applications occur only in constraints
and impl heads. Each method spelling occupies the ordinary file-wide term
namespace.

The namespace conflict matrix is:

- an interface name conflicts with a local or targeted nominal type, another
  local or targeted interface, and a file-wide module alias;
- a method name conflicts with a global, another method, or a targeted term
  binding, including a constructor renamed to the same lowercase spelling;
- interface names do not conflict with constructors or lowercase terms in
  their distinct namespaces; and
- one targeted uppercase selector may import a same-spelled interface and
  constructor together, preserving their distinct namespaces as existing
  type-and-constructor selectors do.

Existing `resolve.duplicate-type`, `resolve.duplicate-global`, and
`resolve.import-conflict` reasons own these conflicts. Any resolved non-interface
target in an interface position, including a nominal type or type parameter,
produces `resolve.interface-kind`. An interface in an ordinary value-type
position produces the existing `resolve.type-kind` reason rather than becoming
a nominal constructor or an unknown spelling.

Resolution allocates stable qualified identities:

```text
InterfaceId  = defining ModuleId + interface declaration
MethodId     = InterfaceId + method declaration
```

A public interface exports its identity, parameter, ordered methods, checked
method signatures, and provenance as one unit. A private interface and its
methods remain local. A public method signature may retain a hidden nominal
identity under the existing hidden-identity rules without exporting that
nominal's spelling or constructors.

An interface method is a constrained term. An occurrence of `equal` from the
example has the conceptual scheme `forall A. (A, A) -> Bool where Equal<A>`.
A complete import qualifies the public interface and methods under its alias.
A targeted import may bind the interface or any method independently in its
existing namespace. Imported identities never depend on aliases or routes.

### Constrained global schemes

A checked source scheme has three distinct fields:

```text
ConstrainedScheme =
    ordered outer type parameters
    ordered interface requirements
    source value type
```

Requirements are not `Type` variants and do not participate in ordinary type
equality or unification. Free uppercase variables in a global signature retain
their current implicit rank-1 binding. Their order follows first occurrence in
the value type and then the requirement list. A free uppercase name first found
only in a requirement is retained as that signature's candidate parameter so
requirement checking can reject it with
`constraint.undetermined-parameter`. Every type variable used by an accepted
requirement therefore occurs in the value type. Two identity-equal requirements
in one signature are rejected.

Equational and operational globals produce the same constrained scheme. A
public global requirement must name a public interface. A private global may
use a private interface from its own module. Requirements are explicit on
module-level signatures; checking never infers and exports a new requirement.

### Implementation declarations

An impl supplies every required method exactly once and no extra method. Method
groups may appear in any order; the interface declaration still determines
evidence order. The interface supplies each method's signature. Impl methods
cannot declare separate visibility, signatures, type parameters, requirements,
or defaults.

The free uppercase variables in an impl head become its ordered rigid type
parameters in first-occurrence order within that head. A free uppercase name
first found only in a prerequisite is retained as an invalid prerequisite
variable so impl checking reports `impl.prerequisite-variable`; it neither
binds another impl parameter nor becomes `resolve.unknown-type`. Every accepted
prerequisite variable therefore occurs in the head. A bare type-variable head
is rejected. Structural and primitive heads have no source owner; only the
interface owner may define those impls. For a nominal head, the impl's module
must own either the interface or the outer nominal constructor. This is the
orphan rule.

`impl` is private by default. `pub impl` exports an anonymous implementation
fact rather than a source name. A public impl must implement a public interface,
and each prerequisite must name a public interface. Its head may retain a
private nominal identity from its defining module. Importers receive that
identity only as hidden checked metadata; they receive no source spelling or
constructor access. Opaque types remain nameable without granting an external
impl body access to their constructors.

Resolution allocates every identity and hidden method binder before any global
or impl body is checked:

```text
ImplId       = defining ModuleId + impl declaration
ImplMethodId = ImplId + MethodId
BinderId     = defining ModuleId + hidden impl-method binder
```

Each `ImplMethodId` maps to one module-qualified `BinderId`. Impl method heads
do not introduce lexical term bindings. A method occurrence inside an impl body
still resolves to its interface `MethodId`; typed evidence selection determines
whether it uses prerequisite evidence or exact current-impl evidence.

All ordinary globals and impl methods in one module form one simultaneous
recursive scope. Each impl method checks against the interface method signature
after substituting the impl head. A generic impl method has the conceptual
checked scheme:

```text
forall head_parameters.
    evidence(prerequisite_1) ->
    ... ->
    evidence(prerequisite_n) ->
    substituted_method_type
```

Head variables remain rigid. Current-impl evidence may satisfy only the exact
current head under those same rigid variables. It does not freshly instantiate
the generic impl. Calls on proper components use declared prerequisite evidence.
This preserves the current prohibition on polymorphic recursion.

### Availability, overlap, and scoped coherence

A module's effective implementation environment contains:

- every local private or public impl in that module; and
- every public impl defined by a direct dependency.

Both complete and targeted imports make the direct dependency's public impl
facts available. Target selectors affect source names only. An imported impl is
not copied into the importer's summary and therefore does not become ambient in
the importer's dependents. Alternate routes to one `ImplId` deduplicate before
coherence checking.

For each interface, the checker freshens the bound variables of every pair of
distinct effective impl heads. If the heads unify, the module is incoherent and
is rejected before body checking. Prerequisites, declaration order, and import
order never choose a winner.

Module checking orders the owning judgments as follows:

1. resolution allocates identities and resolves all interface and impl headers;
2. interface declarations and impl headers are checked for visibility, kind,
   parameter use, variable heads, orphan ownership, and prerequisite
   admissibility;
3. only those admitted local headers join checked imported headers to construct
   the deduplicated effective environment and check overlap;
4. impl method membership and completeness are checked; and
5. ordinary global and impl method bodies are checked in deterministic source
   and method order.

An invalid local header therefore fails at its owning judgment and never
creates a secondary overlap conflict. Imported summaries contain only headers
admitted by the same sequence in their defining modules.

This rule provides scoped coherence. Two sibling modules may export overlapping
impls while no module imports both. A caller that directly imports one sibling
or the other deliberately selects different evidence through a different
dependency set. A module that imports both rejects the overlap.

There are no priority, negative, default, specialization, or condition-
entailment rules.

### Generic prerequisites and termination

After freshening and alpha-normalizing a generic impl, the sole type argument of
each non-ground prerequisite must be a strict syntactic subterm of the impl
head's type argument. The test compares resolved type structure and identities,
not source spellings. This admits `Equal<A>` as a prerequisite of
`Equal<Option<A>>` and rejects expanding rules. A ground prerequisite is exempt
from the subterm test.

Evidence selection uses an explicit worklist and an active-goal set keyed by
canonical `(InterfaceId, type argument)`. Re-entering an active goal is a
constraint cycle. The graph-wide interface-and-constraint budget below bounds
wide and deep valid selection. Cycle detection precedes resource exhaustion for
the same retained work.

### Constraint satisfaction

Instantiating a constrained term first instantiates its ordinary rank-1 type
parameters and creates one pending evidence obligation for each requirement in
source order. Ordinary bidirectional typing determines each obligation's type
argument. Selection does not solve an ordinary inference variable merely to
make an impl applicable.

At the enclosing global or impl-method closure boundary, each obligation must
be satisfied by:

1. an identity-equal abstract requirement from the current constrained global
   or impl prerequisites; or
2. when checking an impl method, exact current-impl evidence for the current
   rigid head; or
3. exactly one matching impl from the effective environment, including
   recursively satisfied prerequisites.

Abstract evidence is considered first and shadows impl search. Impl matching
may substitute only the matched impl's bound head variables. It cannot change
a rigid variable or guess an unresolved inference variable in the obligation.
An undetermined obligation is ambiguous; no match is unsatisfied; active
re-entry is cyclic.

The selection judgment has the inputs `abstract requirements`, optional
`current impl`, `effective impl environment`, `active goals`, and one resolved
`InterfaceId<type>` obligation. Its output is one `EvidenceSelection` or one
owned failure. Exact current-impl selection uses the impl's already abstract
prerequisite slots; it does not recursively select or freshly instantiate those
prerequisites. While checking that impl's methods, its `ImplId` is not considered
again in the general candidate branch. Other concrete selection traverses
prerequisites in declaration order. Because overlap was rejected for the
effective environment, concrete selection can produce at most one matching impl
after route deduplication.

A local generalized function cannot infer a new requirement. It may close over
abstract evidence from its enclosing checked global or use concrete evidence
available there. Recursive constrained globals reuse their declared abstract
requirements and do not acquire polymorphic recursion.

For an unannotated local anonymous-function initializer eligible for
`generalize_local`, typing closes and selects every evidence obligation before
choosing generalized inference variables. An obligation whose argument still
contains a would-be generalized inference variable is
`constraint.ambiguous` at its constrained occurrence. The checker never turns
that obligation into a local inferred requirement. Obligations in other local
forms retain the enclosing global or impl-method closure boundary under the
current monomorphic-local rules.

The entry `main` has an empty requirement list in addition to its existing
monomorphic `Unit -> R` contract. Entry failures retain the order missing,
polymorphic, wrong domain, open result, then constrained. Every obligation in a
well-shaped `main` body must select concrete evidence at its use site.

### Structural evidence ownership

Constraint selection happens once during checking. Every resolved method or
constrained-global occurrence carries a structural evidence slot. The slot is
empty after resolution, filled with ordered checked selections during typing,
owned by the resulting checked definition, and consumed when that exact
occurrence lowers to Core. Implementations may use a structurally equivalent
checked-definition form, but may not join a detached selection vector to
occurrences by source span or repeat selection during final lowering.

One requirement selection has this recursive form:

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

`RequirementId` combines the owning global `BinderId` or `ImplId` with the
requirement's declaration order. A constrained global occurrence owns one
selection per requirement in that scheme's order. A method occurrence owns the
single selection for its interface requirement.

Checked modules retain these structural annotations together with their source
definitions and schemes until program linking. They are an extension of the
checked-module boundary, not a source-visible dictionary, a persistent general
constraint IR, or a new Core dialect.

### Export summaries and linked registries

A body-free checked export summary adds:

- public interface identities, parameters, ordered method identities, checked
  method signatures, and provenance;
- public impl identities, alpha-renamable bound head parameters, canonical
  heads, ordered prerequisites, checked method schemes, ordered
  `ImplMethodId`-to-`BinderId` mappings, and provenance; and
- hidden nominal facts required by public global requirements, public method
  signatures, impl heads, or prerequisite types.

No interface or impl fact is published until the complete module checks. A
summary contains no impl method body or dependency private scope. Importers
match stable identities and checked types, never display names.

Program linking combines the defining interface and impl registries from all
checked modules alongside the current nominal and constructor registries. The
linked checked groups retain every structural evidence selection and defining
impl method body. Before Core synthesis, one interface-evidence validation
judgment receives those combined registries and selections. It authenticates:

- interface, method, impl, nominal, requirement, and binder identities;
- head matching, substitutions, prerequisite trees, and termination facts;
- availability of every selected impl in the direct effective environment of
  the checked occurrence's module;
- complete method slots in interface order, including same-typed slots;
- checked source and impl method schemes;
- abstract requirement ownership, scope, ordering, and provenance; and
- absence of inference variables or missing linked definitions.

This judgment validates recorded selections; it does not select candidates
again.

### Core lowering and evaluation

One logical interface requirement lowers to its method functions in interface
declaration order. Multiple requirements flatten in source requirement order.
A constrained global obtains the derived Core type:

```text
forall parameters.
    evidence(requirement_1) ->
    ... ->
    evidence(requirement_n) ->
    source value type
```

Here each `evidence(requirement)` expands to the interface's ordered method
types after substituting the requirement argument for the interface parameter.
Core synthesis emits outer type abstractions, then one ordinary function binder
for each flattened method slot, then the source function.

At a constrained global occurrence, lowering emits ordinary type application,
then applies every selected evidence function, before any surrounding source
value application. An abstract selection becomes the corresponding evidence
binder. An implementation selection maps each `ImplMethodId` through its
checked module-qualified `BinderId`; a generic method is type-applied with the
recorded head substitution and term-applied to recursively constructed
prerequisite evidence.

Every impl-method binder joins the defining module's existing Core recursive
group with ordinary globals. This preserves global-to-method, method-to-global,
and mutual method recursion without a cross-module recursive group.

After interface-evidence validation, interface, impl, method, and requirement
identities erase. The existing Core validator independently checks the produced
type abstractions, evidence binders, type and term applications, recursive
scope, types, registries, and provenance.

The pure Core dialect and evaluator gain no interface node, dictionary node,
impl registry, runtime lookup, dispatch rule, registration, or failure mode.
Generic evidence construction evaluates through existing pure type-erasure and
application frames to a function closure before the source value argument is
applied.

### Failures and resources

Failures remain owned by the first judgment that can establish them. Stable new
reason families include:

- parser-owned expected-form reasons for malformed interface, method,
  requirement, impl-head, and impl-method syntax;
- existing `resolve.duplicate-type`, `resolve.duplicate-global`,
  `resolve.import-conflict`, and `resolve.unavailable-export` reasons for
  interface, method, import, and access conflicts;
- `resolve.unknown-interface` for an absent impl or constraint target,
  `resolve.interface-kind` for any resolved non-interface target there, and the
  existing `resolve.type-kind` for an interface in a value-type position;
- `interface.method-parameter` and `interface.method-not-function` for a
  missing parameter occurrence, method-local type variable, or missing arrow;
- `constraint.duplicate-requirement`,
  `constraint.undetermined-parameter`, and `constraint.private-interface` for
  malformed global requirements;
- `impl.private-interface`, `impl.orphan`, `impl.variable-head`, `impl.overlap`,
  `impl.prerequisite-variable`, `impl.prerequisite-not-decreasing`,
  `impl.missing-method`, `impl.duplicate-method`, and `impl.extra-method` for
  implementation checking;
- existing `type.*`, `pattern.*`, and `coverage.*` reasons for impl method body
  failures;
- `constraint.unsatisfied`, `constraint.ambiguous`, and `constraint.cycle` for
  satisfaction;
- `internal.resource.constraint-work` for graph-wide constraint budget
  exhaustion; and
- `entry.main-constrained` for a constrained entry global.

`constraint.ambiguous` means that an obligation still contains an unresolved
inference variable at its closure boundary. Multiple matching impls are
`impl.overlap`, established while constructing the effective environment.
Ordinary unconstrained inference ambiguity remains in the existing `type.*`
family.

Publishing a requirement through a private interface uses
`constraint.private-interface` on the public global or
`impl.private-interface` on the public impl or prerequisite. A private impl
unavailable to an importer produces `constraint.unsatisfied` without exposing
the private impl's metadata. Malformed evidence plans or lowered Core are
internal compiler failures in `evidence.validation.*` or the existing Core
validation families.

Constraint diagnostics use the requirement occurrence as primary and relate
the interface, selected or competing impl declarations, method declaration,
impl method, and relevant import occurrences. A local orphan or overlap uses
the impl head as primary. An imported overlap uses the later direct import or
local impl in deterministic source order and relates both impl declarations.

One graph-wide interface-and-constraint budget persists from imported-summary
admission through effective-environment construction, checking, linking, and
interface-evidence validation. It charges proportional work before retaining or
visiting imported interface and impl facts, effective environments, route
deduplication, overlap comparisons, obligations, candidates, substitutions,
prerequisite edges, active goals, evidence nodes, linked registry entries, and
every validation identity, slot, substitution, prerequisite, type, scope, and
provenance check. Exhaustion at any of those stages is
`internal.resource.constraint-work`; there is no separate evidence-validation
resource family. Existing Core construction and Core validation budgets begin
after interface-evidence validation and remain separate. Candidate traversal
and diagnostics follow dependency, import, declaration, and method order. Deep
prerequisite selection, evidence validation, and destruction use explicit
worklists.

## Semantic delta

Ash gains one-parameter method-only interfaces, local and exported impl facts,
explicit global requirements, scoped coherence, typed implementation selection,
and implicit source evidence. Separately checked constrained globals remain
abstract in export summaries; callers supply evidence selected from their own
direct dependency environment.

Type equality, unification, rank-1 generalization, module identity, visibility,
opacity, linking, pure Core, and expression evaluation retain their current
rules. Constraints become a distinct checked-scheme field rather than a type.
Core receives additional ordinary function binders and applications only after
an interface-aware validator authenticates the source relationship.

## Affected specification areas

- [Lexical structure](../../spec/lexical-structure.md) adds three reserved words.
- [Syntax](../../spec/syntax.md) adds interface, impl, and `where` forms.
- [Name resolution](../../spec/name-resolution.md) adds stable interface,
  method, impl, impl-method, and requirement identities; namespaces; import
  access; and direct impl availability.
- [Static semantics](../../spec/static-semantics.md) adds constrained schemes,
  interface and impl checking, orphan and overlap rules, termination, evidence
  obligations, selection, and the empty-requirement entry contract.
- [Elaboration](../../spec/elaboration.md) adds retained structural selections,
  interface-evidence validation, flattened method evidence, impl-method group
  membership, and erasure.
- [Dynamic semantics](../../spec/dynamic-semantics.md) explains that generated
  evidence uses existing type erasure, function, recursive-binding, and
  application transitions without runtime selection.
- [Overview](../../spec/README.md) adds the implemented interface boundary and
  representative module examples.
- [The `ash` executable](../tools/ash.md) adds interface-related source failure
  observations but no invocation option or runtime loading behavior.

## Resulting specification truth

After implementation, tests, and specification changes merge together, Ash has
method-only type-class-like interfaces. A module may declare required method
relationships and anonymous implementations. Public interface and impl facts
cross body-free summaries with stable defining-module identities. A module sees
only its local impls and public impls from direct dependencies, and every such
environment rejects overlap.

Global constraints remain explicit in source signatures and implicit at calls.
Checking selects typed evidence once, validates the retained selection before
Core synthesis, and lowers it to ordinary method functions. Interface structure
has no runtime registry or dispatch rule. The entry `main` remains monomorphic
and cannot require caller-supplied evidence.

## Interactions

Interfaces use the implemented module identity, direct import, visibility,
opaque-type, hidden-identity, body-free summary, and dependency-ordered linking
boundaries. Import aliases and targeted source names do not alter interface or
impl identity. Public impls can compose over hidden carriers without making
those carriers nameable, and opaque constructors remain inaccessible outside
their defining module.

The existing rank-1 rule still quantifies only outer global schemes. Interface
requirements add outer evidence functions but do not permit higher-rank method
types, method-local polymorphism, inferred exported requirements, or
polymorphic recursion.

Same-typed evidence slots show why interface-aware validation must precede
erasure: ordinary Core types cannot authenticate method identity or slot order.
After that judgment, the accepted pure Core and evaluator boundaries are
sufficient.

This increment provides the interface consumer needed by the later Modular
core-versus-library audit. That audit may compare an existing Core behavior with
a library interface only after this proposal is implemented and specified.

## Non-goals

This proposal does not add:

- associated types, projections, normalization, multi-parameter interfaces, or
  higher-kinded parameters;
- default methods, specialization semantics, priorities, negative impls, or
  condition-entailment overlap exceptions;
- first-class source dictionaries, named impl values, interface objects, or
  runtime implementation lookup;
- inferred module-level requirements, constrained `main`, higher-rank methods,
  method-local type parameters, or polymorphic recursion;
- individual constructor exports, import re-exports, module signatures, module
  values, cross-module recursion, or a new module path rule;
- dynamic loading, providers, registration, unloading, initialization, effects,
  or runtime discovery;
- a new Core dialect, evaluator dispatch family, specialization transform, or
  dead-code elimination; or
- associated-type placeholder syntax or a dormant normalization engine.

## Required evidence

Implementation must provide:

- exact lexer, parser, concrete-tree, projection, recovery, and malformed-form
  cases for interface declarations, methods, constrained equational and
  operational globals, impl heads, prerequisites, and impl equations;
- stable module-qualified identity and namespace cases for interfaces, methods,
  impls, impl methods, requirements, complete imports, targeted imports,
  aliases, alternate routes, and diamonds;
- direct-only public impl availability, private impl invisibility, no impl
  re-export, hidden-head retention, public-interface closure, and failed-module
  summary atomicity;
- local, primitive, nominal, foreign-interface/foreign-type orphan, bare
  variable, duplicate, generic-overlap, co-imported conflict, and legal sibling
  alternative cases;
- proper-subterm generic prerequisites, expanding rejection, ground cycles,
  rigid head matching, abstract-evidence priority, unsatisfied and ambiguous
  obligations, and no inferred local or exported requirements;
- complete, missing, duplicate, extra, wrongly typed, recursive, mutually
  recursive, global-to-method, and method-to-global impl method cases;
- separate constrained exports, caller-supplied concrete evidence, generic impl
  prerequisite construction, higher-order evidence threading, and paired
  equational and operational observations;
- hidden-carrier and opaque-type implementations, including preserved opacity
  in an external impl body;
- structural checked-occurrence evidence proving that selection survives the
  checked-module boundary, is consumed by the exact occurrence, and is not
  repeated during final lowering;
- interface-evidence validator rejection of wrong identities, substitutions,
  prerequisite trees, missing or reordered same-typed slots, bad
  `ImplMethodId` mappings, scope, type, provenance, and inference escape;
- linked Core evidence that type applications precede evidence applications,
  evidence precedes source arguments, impl methods share their module recursive
  group, and no interface runtime node or registry exists;
- exact end-to-end observations for local, cross-module, generic, hidden,
  opaque, recursive, and caller-selected sibling cases;
- deterministic structured diagnostics with causal related labels and no
  private metadata leak;
- graph-wide exact-boundary resource cases for imported facts, overlap, wide
  candidate environments, deep valid prerequisite chains, cycles, evidence
  construction, validation, and small-stack destruction;
- a complete normative specification update, executable specification examples,
  tool and reason-code review, relative-link and authority review, and retained
  implementation evidence;
- `cargo xtask verify` with no failure; and
- a bounded unspecialized evidence trace that uses the current evaluator and
  supplies the baseline for a later, separately authorized specialization
  comparison.
