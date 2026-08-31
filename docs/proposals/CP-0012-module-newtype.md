# CP-0012: Module `newtype`

- ID: `CP-0012`
- Status: accepted
- Related:
  - [DN-0026](../design/DN-0026-effect-ash-resource-first-milestones.md)
  - [DN-0027](../design/DN-0027-effect-ash-program-design.md)
  - [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md)
  - [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md)
  - [AD-0007](../decisions/AD-0007-typed-core-dialects.md)
  - [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This proposal is not current Ash.

## Current behavior

Ash has module-level nominal `type` declarations. A declaration introduces one
module-owned nominal identity and one or more constructor identities. All
nominal declarations in a module form one mutually visible scope. Constructor
payloads may refer to their owner and to other declarations in that scope.

Private, public opaque, and public transparent declarations control whether a
dependent can name the nominal type and use its constructors. Imports,
re-exports, aliases, and hidden summary closure preserve the defining nominal
and constructor identities. Equal spellings or constructor shapes do not make
separate declarations equal.

A nullary constructor allocates one constructor cell when evaluated. A payload
constructor is an ordinary unary function; applying it allocates one
constructor cell containing its payload. Pattern matching inspects that cell.
Observation renders the constructor spelling and payload. Typed Core retains
constructor identities and payload types, and independent validation checks
the linked registry, constructor occurrences, patterns, coverage, and node
types before evaluation.

Ash has no representation-preserving nominal declaration, implicit coercion,
local type declaration, runtime-fresh type identity, effect row, resource
scope, or existential package.

## Proposed behavior

### Declaration and visibility

A module may declare a representation-preserving nominal type:

```ebnf
newtype_declaration ::=
  [ "pub" [ "opaque" ] ]
  "newtype" upper_identifier [ type_parameters ] "="
  upper_identifier "(" type ")" ;
```

`module_declaration` admits `newtype_declaration` beside the existing forms.
The declaration has exactly one constructor and exactly one representation
field. The constructor spelling must equal the nominal spelling, as in
`newtype UserId = UserId(Int)`. A missing constructor, nullary constructor,
second field, or second constructor is malformed `newtype` syntax. A distinct
constructor spelling is `resolve.newtype-constructor-name` at that spelling and
relates it to the nominal declaration. The `newtype` keyword is reserved; an
identifier with that exact spelling no longer parses where a lowercase
identifier is required.

The existing declaration visibility modes apply unchanged:

- `newtype` keeps both the nominal name and constructor private;
- `pub opaque newtype` exports the nominal name but withholds the constructor;
  and
- `pub newtype` exports the nominal name and constructor.

The constructor has no independent visibility. An accessible constructor may
occur as a value or pattern. Opacity continues to reject constructor access at
name resolution rather than relying on a later representation check.

### Identity, parameters, and representation

Each declaration receives one fresh module-owned `NominalTypeId` in the
existing cross-declaration source order and one constructor identity under that
owner. Imports and re-exports preserve both identities. A `newtype` does not
derive equality from its representation, so two declarations over the same
representation remain distinct from each other and from that representation.

The existing ordered declaration parameters and fixed kinds apply. Omitted
kind annotations mean `Type`. Parameters scope over the representation field.
The fully applied representation must have kind `Type`; this increment adds no
kind inference, kind polymorphism, or higher-rank representation.

The representation is a type template under those parameters. Substituting
arguments in the fully applied nominal type substitutes the same arguments in
the representation. A representation may use primitive types, parameters, and
ordinary or other `newtype` nominals subject to normal scope and kind rules.

The directed graph whose vertices are module `newtype` declarations and whose
edges record a `newtype` identity occurring anywhere in another `newtype`'s
representation must be acyclic. A declaration therefore cannot contain its
own identity directly or through only `newtype` representation edges. This
bounded rule rejects zero-storage representation cycles. It does not change
ordinary nominal recursion, and it does not follow through an ordinary data
declaration merely because that declaration later refers back to the
`newtype`.

The first cycle edge in declaration and representation traversal order owns
`newtype.recursive-representation`. The diagnostic identifies the rejected
occurrence and the declarations completing the cycle. Kind failures precede
cycle analysis because only kind-correct representation applications enter the
graph.

### Wrapping, matching, and typing

An accessible `newtype` constructor has the same source-level rank-1 scheme
shape as a one-field payload constructor:

```text
forall parameters. representation -> owner<parameters>
```

Applying it performs an explicit wrap. It is the only direct source operation
that creates the nominal value; ordinary type checking never treats the
representation and nominal type as equal. Functions that expose another
construction route must use that constructor explicitly in their defining
source.

An accessible constructor pattern performs an explicit unwrap. It has exactly
one subpattern and is irrefutable for its owner. Function parameters and local
bindings may therefore use it where an irrefutable pattern is required. Match
coverage treats it as the sole constructor of its nominal owner without adding
a runtime tag test. A pattern cannot match the representation type directly,
and an opaque or unavailable constructor remains unusable.

Ordinary nominal mismatch, application, pattern, coverage, and causal-span
rules otherwise remain unchanged. The new declaration does not add implicit
subtyping or a general coercion relation.

### Interfaces

A `newtype` is a nominal type for implementation ownership, overlap, matching,
and evidence selection. Code may declare an explicit implementation whose head
has the `newtype` as its permitted local outer nominal.

The representation supplies no implementation evidence. An implementation
for `Int` does not satisfy a goal for `UserId` when
`newtype UserId = UserId(Int)`. Wrapping and unwrapping do not copy, lift, or
select evidence, and the increment adds no local implementation search or
runtime interface lookup.

### Summaries and linked authentication

Resolved and checked nominal facts distinguish ordinary data from `newtype`.
The compiler's authenticated, body-free summary retains one canonical hidden
fact containing the declaration kind and identity, owner, ordered parameter
records, sole constructor identity and same spelling, representation template,
visibility and access, and origin. The representation remains compiler
authority until every linked conversion that depends on it has crossed
independent Core validation.

A public transparent source projection exposes the constructor scheme and the
representation facts needed to check dependent wrapping and matching. A public
opaque source projection exposes the stable nominal identity, parameters, and
kind but withholds the constructor and representation. Its hidden canonical
fact still records that the sole same-spelled constructor belongs to that owner,
its access is withheld, and its representation and provenance authenticate
linked Core. A private declaration has no public source projection, while its
canonical fact remains available to authenticated linking of its defining
module. Hidden compiler facts do not create a source name, constructor access,
coercion, or interface evidence.

Import admission and linking authenticate the declaration kind, identity,
owner, parameter order and kinds, constructor cardinality and identity,
representation, access, and provenance. Alias and diamond routes must agree on
those defining facts. A missing, reordered, substituted, visibility-changing,
or forged fact is rejected before Core synthesis under the existing summary or
linked-validation ownership.

### Core representation and erasure

Elaboration lowers source wrapping and matching to explicit typed
representation conversions. A conversion records:

- the `newtype` nominal identity;
- wrap or unwrap direction;
- one child expression;
- causal source provenance.

The conversion belongs to the pure dialect's existing erased static-operation
boundary. It is not an effect operation, ordinary data constructor, unchecked
cast, or runtime value. Resolution and linked summary validation remain the
exclusive authorities for source constructor access and import routes, as they
are for ordinary constructors. Core validation derives the conversion relation
from the linked canonical `newtype` fact and the existing child and enclosing
expression type annotations rather than retaining copied type fields.

A constructor occurrence in value position elaborates to an ordinary unary
function whose parameter has the substituted representation type and whose
body is a wrap conversion. For a parameterized declaration, existing Core type
abstraction and application use fresh generated type binders. The function
body applies the nominal to those variables in declared order. Validation
matches each fresh binder to the canonical declaration parameter record by
position and kind. The canonical record remains the authority for the ordinary
declared-order substitution from canonical parameters to the applied fresh
variables, which derives the expected representation. Validation neither binds
nor replaces the canonical parameter identities. The generated function uses
ordinary Core scope, type, provenance, traversal, validation, and application;
this increment adds no constructor-function Core variant or evaluator rule.

For wrapping, the child has the substituted representation type and the result
has the applied nominal type. Unwrapping reverses those types. Independent Core
validation checks the nominal owner, complete parameter application, kinded
substitution, direction, child type, result type, declaration and source
provenance, and the canonical representation relation. It does not re-decide
source access or import routing. It rejects an ordinary constructor identity
used as a representation conversion and rejects a `newtype` constructor
lowered through the allocating ordinary-constructor Core route.

Identity traversal and primitive folding preserve or rebuild conversions and
their authentication facts, then return to independent validation. Evaluating
a validated representation conversion immediately enters its child without
inspecting conversion metadata and returns that value without allocating,
tagging, or copying it. This contract does not prescribe whether the
implementation shares dispatch with another erased operation.

A malformed or unauthenticated conversion is `core.validation.*` and cannot
reach evaluation. No production heap-inspection API is added. Structural Core
inspection and an internal evaluator allocation observation establish that
wrap and unwrap allocate no constructor cell.

### Runtime observation

A wrapped value has exactly the representation's runtime storage. The
`newtype` name and constructor do not remain as runtime tags and do not affect
value rendering. A program whose result type is `UserId` over `Int` therefore
observes the integer representation while its separately reported source type
remains `UserId`.

Nested ordinary data in a representation retains its existing structural
rendering and allocation. Only the `newtype` wrapper is absent. Evaluation
gains no value-level registry entry, conversion-time registry lookup,
`newtype`-specific runtime state, module value, wrapper equality test, effect
state, provider state, or new runtime failure. The linked nominal registry may
retain the checked `newtype` fact as static validation and observation
authority, as it retains ordinary nominal facts.

### Failure ownership and resources

Lexing owns the reserved keyword. Parsing owns malformed declaration shape and
recovery. Resolution owns duplicate type or constructor spelling,
`resolve.newtype-constructor-name`, unknown types, inaccessible constructors,
and stable declaration identity. Kind checking owns invalid parameter and
representation kinds. Static nominal admission owns
`newtype.recursive-representation` after kind checking. Ordinary type and
pattern checking own nominal mismatches. Summary admission, linked validation,
Core construction, and Core validation own malformed or forged facts only
after earlier source checks succeed.

Within one module, admission first authenticates imported facts, then allocates
and freezes declaration identities and parameter kinds. It next kind-checks all
ordinary constructor payloads and all `newtype` representations in combined
cross-declaration source and structural type order. Only after every such type
is kind-correct does it build and traverse the `newtype`-only representation
graph in declaration and representation order. Interface checking and every
later module stage follow that pass. A mixed-error corpus fixes this precedence
between payload kind errors, representation kind errors, cycles, and later
failures.

Syntax events charge the syntax ledger. Declaration and constructor records,
representation types, substitution, summaries, conversion nodes, and Core
types charge their existing owning structural or type-work ledgers. Summary
and linked fact traversal charge the applicable graph-wide ledgers. Every
proportional allocation or traversal charges before publication.

The module checker's existing cumulative type-work ledger owns representation
graph construction and traversal; this is not interface constraint work. Each
discovered representation occurrence, retained edge or owner-index entry,
pending-stack entry, and visited or active-state entry charges one type-work
unit before retention or traversal. Exhaustion reports
`internal.resource.type-work`. Failure publishes no checked module or summary,
releases the partial graph iteratively, and permits a retry with the same
logical input and a replenished budget.

The implementation task must derive exact additive formulas for each new
carrier, then retain exact-success, one-unit-short atomic failure, retry, and
deep accepted and rejected teardown evidence. Representation graph traversal
must be bounded and iterative. This proposal does not authorize a production
limit increase.

## Semantic delta

- The reserved `newtype` declaration form introduces one
  representation-preserving nominal identity with exactly one same-spelled
  constructor and one field; a distinct constructor spelling receives
  `resolve.newtype-constructor-name`.
- Existing private, public opaque, and public transparent visibility controls
  its nominal and constructor access.
- Its parameterized representation has kind `Type` and cannot participate in a
  cycle made only of `newtype` representation edges.
- Accessible wrapping and matching are explicit, typed, and irrefutable;
  nominal and representation types remain unequal.
- Interface implementations remain explicit and evidence does not lift from
  the representation.
- Linked compiler facts and independently validated pure Core authenticate
  wrap and unwrap before both erase without runtime allocation.
- Runtime value observation renders the representation while source type
  observation retains the nominal `newtype`.

## Affected specification areas

- [Lexical tokens](../../spec/lexical-structure.md#tokens) reserves `newtype`.
- [Syntax grammar](../../spec/syntax.md#grammar) adds the declaration form and
  describes its exact constructor and visibility syntax.
- [Imports and namespaces](../../spec/name-resolution.md#imports-and-namespaces),
  [Type and constructor scope](../../spec/name-resolution.md#type-and-constructor-scope),
  and [Public, private, and opaque declarations](../../spec/name-resolution.md#public-private-and-opaque-declarations)
  define `newtype` identities, namespace conflicts, access, imports, and
  re-exports.
- [Kinds, monotypes, and schemes](../../spec/static-semantics.md#kinds-monotypes-and-schemes),
  [Tuples and constructors](../../spec/static-semantics.md#tuples-and-constructors),
  and [Patterns, matches, and coverage](../../spec/static-semantics.md#patterns-matches-and-coverage)
  define representation admission, constructor schemes, wrapping, irrefutable
  unwrapping, and coverage.
- [Implementations](../../spec/static-semantics.md#implementations),
  [Constraint satisfaction and checked evidence](../../spec/static-semantics.md#constraint-satisfaction-and-checked-evidence),
  [Globals and modules](../../spec/static-semantics.md#globals-and-modules), and
  [Failure ownership and constraint resources](../../spec/static-semantics.md#failure-ownership-and-constraint-resources)
  define explicit interface evidence, module admission order, diagnostics, and
  resources.
- [Surface erasure](../../spec/elaboration.md#surface-erasure),
  [Module linking and entry generation](../../spec/elaboration.md#module-linking-and-entry-generation),
  [Explicit rank-1 operations](../../spec/elaboration.md#explicit-rank-1-operations),
  and [Validation boundary](../../spec/elaboration.md#validation-boundary)
  define representation facts, conversions, transforms, and independent Core
  authentication.
- [Initial configuration](../../spec/dynamic-semantics.md#initial-configuration),
  [Type erasure](../../spec/dynamic-semantics.md#type-erasure),
  [Tuples, constructors, and matches](../../spec/dynamic-semantics.md#tuples-constructors-and-matches),
  and [Observation](../../spec/dynamic-semantics.md#observation) define
  allocation-free execution and representation rendering.
- [Specification overview](../../spec/README.md) gains a complete example and
  records the unchanged exclusions.

## Resulting specification truth

After the complete product checkpoint integrates into `main`, a module
`newtype` declaration introduces a stable nominal identity over one kind-`Type`
representation. The reserved form requires exactly one same-spelled constructor
and one field; a distinct spelling is
`resolve.newtype-constructor-name`. Its constructor explicitly converts between
the representation and the distinct nominal type where visibility permits.
Imports, aliases, and re-exports preserve the defining identity; opacity
withholds conversion access without weakening linked authentication.

Each conversion crosses an independently validated pure Core boundary.
Evaluation reuses the representation value and allocates no wrapper cell. A
`newtype` remains statically nominal but has no runtime tag, value-level
registry entry, conversion-time lookup, or constructor rendering.

An implementation for the representation does not satisfy a constraint for
the `newtype`. Code must declare each required relationship explicitly under
the existing interface and implementation rules.

## Interactions

Ordinary nominal scope, import identity, higher-kinded declaration parameters,
method-local parameters, relational improvement, evidence selection, and
linked authentication continue to use exact identities. `newtype` extends the
nominal registry and erased static-operation boundary; it does not add a second
resolver, kind checker, constraint solver, Core validator, or evaluator.

The acyclic `newtype`-representation graph is narrower than ordinary recursive
data. It prevents a zero-storage cycle without selecting a general recursive
representation or storage policy. A later proposal may broaden this boundary
only with construction, erasure, and termination evidence.

Local `newtype` will require a lexical identity owner rather than another
module declaration ordinal. The module checkpoint must keep conversion
authentication expressed in terms of an identity and its defining fact so a
later owner class can extend the registry boundary without changing runtime
semantics.

Resource acquisition may later establish a fresh identity at runtime and may
retain a handle or witness. This proposal's module declaration instantiates
once in the statically linked program and leaves no runtime identity. It does
not decide acquisition freshness, ownership, escape, cleanup, or provider
evidence.

Existential packages may later permit a hidden identity and operations to
escape together. Current hidden and opaque module values continue to cross
boundaries only through existing checked schemes. This proposal does not add
pack or unpack and does not infer that every future lexical identity must be
unable to escape.

Proof evidence may reuse provenance and independent-validation patterns, but a
`newtype` conversion is not proof, interface, provider, or handler authority.
No carrier introduced here may authenticate those later authority families.

Three broader approaches do not fit this increment:

- Encoding `newtype` as an attribute on ordinary `type` would retain allocating
  constructor and match paths whose semantics depend on a hidden flag.
- General implicit representational coercion would spread conversion through
  unification, application, interfaces, and abstraction instead of keeping it
  at explicit constructor and pattern sites.
- An evaluator-special ordinary constructor would retain runtime nominal
  classification and a second allocation rule. The typed erased-operation
  boundary authenticates the same conversion before runtime without that
  persistent distinction.

## Migration

Every predecessor-valid source remains valid except one that used the exact
lowercase spelling `newtype` as an identifier. Such a spelling now receives the
ordinary reserved-keyword lexical or parse failure and must be renamed.

All existing `type` declarations retain their allocation, recursion,
constructor, pattern, rendering, visibility, summary, Core, and runtime rules.
The implementation must preserve their exact source, CLI, resource, and tamper
corpus. No existing declaration is inferred or migrated to `newtype`.

## Non-goals

This proposal does not add:

- local type or local `newtype` declarations;
- runtime-fresh identity, resource acquisition, ownership, usage, lifetime, or
  cleanup;
- effect APIs, rows, handlers, continuations, providers, or hooks;
- implicit coercion, generalized representational equality, or interface
  evidence lifting;
- local implementations, implementation shadowing, or changed overlap and
  orphan rules;
- general recursive `newtype` representations;
- existential packages, ML-like module signatures, proof evidence, or dynamic
  loading;
- a runtime nominal registry, wrapper tag, wrapper allocation, heap inspection
  API, or special `newtype` rendering; or
- a general storage, ABI, or foreign representation guarantee.

## Required evidence

### Source and semantic corpus

- Parse private, public opaque, and public transparent forms with exactly one
  same-spelled constructor and one field. Reject every excluded shape with
  token-complete recovery or the named resolution failure and stable spans.
- Show that two declarations over `Int` remain unequal and that neither equals
  `Int` without explicit constructor use.
- Exercise kinded parameters, wrapping, constructor-as-function use,
  irrefutable function and binding patterns, explicit matches, and the chosen
  acyclic representation rule.
- Pass an unparameterized and a parameterized constructor as a first-class
  value, return it from a function, and apply it after traversal through an
  ordinary binding. Confirm lowering to the authenticated generated unary
  function and wrap body without an allocating constructor node.
- Preserve identity and access through qualified imports, targeted imports,
  renames, direct re-exports, and facade diamonds. Transparent routes admit
  wrapping and matching; opaque routes reject both constructor uses.
- Pass a private hidden carrier through existing exported operations without
  exposing its name or representation.
- Admit an explicit interface implementation for a `newtype`. With only an
  implementation for its representation, report `constraint.unsatisfied` for
  the nominal goal.
- Preserve every affected ordinary nominal, kind, interface, recursion,
  pattern, coverage, module, and diagnostic predecessor case.

### Authentication and Core corpus

- Tamper independently with declaration kind, owner, identity, parameter
  identity, order and kind, representation-variable binding and substitution,
  constructor cardinality, identity, same spelling, owner and provenance,
  representation, withheld access, origin, conversion direction, child type,
  result type, and canonical source relation. Reject each mutation before
  evaluation at its owning summary, linked, or Core boundary. Summary and link
  admission own source access and route authentication; Core owns only the
  canonical conversion relation after that admission.
- Prove that ordinary constructors cannot claim representation conversion and
  `newtype` constructors cannot reach allocating ordinary-constructor Core.
- Preserve every conversion through identity traversal and literal folding,
  then pass fresh independent validation.
- Show structurally that lowered wrap and unwrap use the erased static-operation
  boundary and contain no allocating constructor node for the `newtype`.
- Run an internal evaluator allocation observation named
  `eval::machine::tests::module_newtype_wrapper_allocates_no_constructor_cell`.
  It must distinguish representation allocation from wrapper allocation
  without creating product heap-inspection API.
- Execute scalar, tuple, ordinary nominal, parameterized, nested, and deep
  representations. Confirm representation value rendering, nominal source type
  rendering, deterministic traces, and no new runtime failure.
- Keep the pure dialect closed: no effect operation, handler, provider, hook,
  continuation, scheduler, or runtime identity family appears.

### Resources, lifecycle, and review

- Record exact additive resource formulas for syntax retention, identity and
  representation facts, the type-work-owned representation graph, summaries,
  linking, conversion construction, transformations, and Core validation.
- At each new retained compiler carrier, demonstrate exact success,
  one-unit-short atomic failure, retry with the same logical input, and deep or
  wide stack-safe accepted and rejected teardown.
- Confirm that a pure program using no `newtype` retains its preceding Core
  inventory, evaluator trace, heap behavior, observation, and resource
  boundary.
- Update every affected specification section, executable specification
  example, CLI/tool statement, corpus manifest, and retained effect-ash evidence
  report in the same product checkpoint.
- Obtain independent semantic/specification, compiler/Core, Rust/resource,
  documentation, and simplification reviews. Correct every critical or
  important finding and rerun affected evidence.
- Audit the result against local and runtime generativity, existential identity
  escape, proof-authority separation, and the later resource-scope composition.
  Record residual risk without importing those later semantics.
