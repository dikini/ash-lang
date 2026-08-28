# CP-0009: Explicit Kinds and Higher-Kinded Parameters

- ID: `CP-0009`
- Status: accepted
- Related: [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [AD-0009: Ordered Resolved-Global Binder Authority](../decisions/AD-0009-ordered-resolved-global-binder-authority.md), the [approved design record](../plans/2026-08-26-explicit-kinds-design.md), and [TASK-0016](../tasks/TASK-0016-implement-explicit-kinds-and-higher-kinded-parameters.md)

> This proposal is not current Ash.

## Semantic base

This proposal is based on commit `a1647ff`, the completed explicit-import
increment retained by the
[explicit-import evidence report](../design/lib-ash/imports-evidence.md). That
checkpoint is now integrated as `main@a1647ff`. “Current behavior” below means
the current specification and implementation at that predecessor checkpoint;
the explicit-kinds transition remains an authorized implementation target, not
current Ash.

## Current behavior

On the semantic base, Ash keeps kinds internal. Every source type
parameter and inference variable has kind `Type`. A nominal declaration with
`n` parameters has an internal `n`-argument constructor kind, but resolution
requires every source nominal application to be saturated. A parameter cannot
appear in type-function position, and no constructor-kinded type survives
resolution.

Nominal declarations carry explicit unkinded parameter lists. Interfaces carry
one unkinded parameter. Globals and implementations bind free uppercase type
variables implicitly in first-occurrence order. Global schemes and Core type
abstractions retain parameter identities without source-declared kinds. Core
type applications accept one kind-`Type` monotype per quantified parameter.

Resolution owns current saturation and type-parameter application failures.
Ordinary type checking, implementation matching, export summaries, linked
evidence validation, and independent Core validation therefore receive only
kind-`Type` source types.

## Proposed behavior

### Kind and binder syntax

Ash gains source syntax for `Type` and right-associative function kinds.
Parentheses group kinds. Every declaration-level type binder uses the same
parameter syntax:

```ebnf
type_parameters ::=
  "<" type_parameter { "," type_parameter } ">" ;
type_parameter ::= upper_identifier [ ":" kind ] ;
kind ::= kind_atom [ "->" kind ] ;
kind_atom ::= "Type" | "(" kind ")" ;
interface_parameter ::= "<" type_parameter ">" ;
```

`Type` remains an ordinary `upper_identifier` outside `kind_atom`; it is not a
new globally reserved word. Kind parsing recognizes that spelling contextually.
A nominal declaration named `Type` therefore remains legal.

Nominal declarations use `type_parameters`, and an interface keeps the exact
single-parameter `interface_parameter` production. Extra interface parameters
remain parser-owned failures. Equational and inline operational globals may
place a list after the global name. Implementations may place a list after
`impl`:

```ebnf
global_signature ::=
  identifier [ type_parameters ] ":" type [ where_clause ] ;
inline_operational_global ::=
  [ "pub" ] "fn" identifier [ type_parameters ]
  "(" typed_pattern { "," typed_pattern } ")"
  "->" type [ where_clause ] block ;
implementation_declaration ::=
  [ "pub" ] "impl" [ type_parameters ]
  interface_application [ where_clause ]
  "{" line_end
  [ impl_equation { line_end impl_equation } [ line_end ] ]
  "}" ;
```

An omitted kind annotation on an explicit binder means `Type`. A global
explicit list is an ordered bijection with the free variables of its value type
and requirements. The list order becomes scheme order. No extra or unlisted
binder is admitted, and the existing determination rule still requires every
requirement variable to occur in the value type.

An implementation explicit list is an ordered bijection with the free variables
of its head argument. The list order becomes head-parameter order. Every
prerequisite variable remains a member of that set; prerequisite-only variables
remain `impl.prerequisite-variable`. A listed variable used nowhere is
`resolve.unused-type-parameter`. An unlisted free header variable remains
`resolve.unknown-type`, and a duplicate remains
`resolve.duplicate-type-parameter`. Nominal declarations retain their current
declaration-owned parameter order and may retain phantom parameters. An
interface method still has no method-local binder list, so any variable other
than its one interface parameter remains `interface.method-parameter`.

A global or implementation without a binder list preserves current implicit
first-occurrence binding, with every implicit binder fixed at kind `Type`.
That compatibility form cannot acquire a function kind from use. The absence
of kind inference is a semantic boundary of this increment, not a permanent
language principle. A later proposal may add bounded declaration-local kind
inference independently from kind polymorphism and higher-order unification.

### Kinds and application

The source kind algebra contains `Type` and function kinds. `->` associates to
the right. The declaration-kind environment `DELTA` maps
every in-scope `TypeVariableId` to exactly one kind. The transient inference
environment `OMEGA` maps every live `InferenceVariableId` to exactly one fixed
kind. The nominal environment `XI` maps every accessible `NominalTypeId` to its
constructor kind. The interface environment `IOTA` maps every accessible
`InterfaceId` to its canonical single parameter `(TypeVariableId, Kind)`
record. A nominal declared with parameter kinds `k_1` through `k_n` has the
right fold `k_1 -> ... -> k_n -> Type`.

The total synthesis judgment `DELTA; OMEGA; XI |- type => kind` has the
following rules. `all_type` requires each listed monotype to synthesize `Type`.

```sequent
family kind-synthesis:
  K-Primitive :=
    primitive in {Int, Bool, Unit}
    ===>
    DELTA; OMEGA; XI |- primitive => Type

  K-Variable :=
    DELTA(variable) = kind
    ===>
    DELTA; OMEGA; XI |- variable => kind

  K-Inference :=
    OMEGA(inference) = kind
    ===>
    DELTA; OMEGA; XI |- inference => kind

  K-Nominal :=
    XI(nominal) = kind
    ===>
    DELTA; OMEGA; XI |- nominal => kind

  K-Application :=
    DELTA; OMEGA; XI |- function_type => argument_kind -> result_kind
    DELTA; OMEGA; XI |- argument_type => argument_kind
    ===>
    DELTA; OMEGA; XI |- Apply(function_type, argument_type) => result_kind

  K-Tuple :=
    all_type(DELTA, OMEGA, XI, elements)
    ===>
    DELTA; OMEGA; XI |- Tuple(elements) => Type

  K-Function :=
    DELTA; OMEGA; XI |- domain => Type
    DELTA; OMEGA; XI |- codomain => Type
    ===>
    DELTA; OMEGA; XI |- Function(domain, codomain) => Type

  K-Value-Type :=
    DELTA; OMEGA; XI |- monotype => Type
    ===>
    DELTA; OMEGA; XI |- value monotype ok

  K-Interface-Argument :=
    IOTA(interface) = (parameter, parameter_kind)
    DELTA; OMEGA; XI |- argument => parameter_kind
    ===>
    DELTA; OMEGA; XI; IOTA |- constraint Interface(argument) ok
```

An unsaturated constructor always synthesizes its derived kind. A partial
application always synthesizes its residual kind. It fails only when an
application premise or an owning value-type rule requires a different kind.
Constructor payloads, global and method value types, pattern and term binder
types, source expression types, entry results, and ordinary Core value
annotations use `K-Value-Type`. Source and inferred requirements, method
obligations, implementation heads and prerequisites, and evidence goals use
`K-Interface-Argument`; the argument must synthesize the selected interface
parameter's declared kind, which need not be `Type`. An interface application
is a constraint and has no monotype kind of its own. A legacy interface
parameter has the default kind `Type`, so its applications recover predecessor
behavior.

The CST and surface tree preserve one named application with its source
argument vector and spans. During resolution, every admitted named application,
whether headed by a nominal constructor or type parameter, folds left into
repeated unary `Type::Application(function, argument)` nodes. Resolved
provenance retains one application step and argument span per fold. No
saturated-nominal semantic form survives that boundary. Rendering may retain
conventional `Name<A, B>` notation. Equality treats `Application` structurally
and injectively; substitution, unification, implementation matching, summary
authentication, and Core validation use only this canonical tree.

For strict-subterm termination, both the function and argument of an
`Application` are immediate strict children. This changes no predecessor
kind-`Type` result, but defines the new residual-kind cases.

### Kinded checking and inference variables

Parsing retains kind syntax and binder annotations. Resolution assigns stable
identities and resolves names and declaration sorts. It no longer enforces
nominal saturation or rejects every type-parameter application. Using an
interface as an ordinary type constructor remains a resolution sort error.
Resolution also owns a duplicate explicit binder or an unbound uppercase name
under a complete explicit binder list.

Imported nominal kinds come only from authenticated body-free summaries. After
resolution allocates all local nominal and parameter identities, kind checking
derives and freezes every local nominal constructor kind before checking any
local constructor payload, global signature, interface method, or
implementation header. This preserves mutually visible nominal declarations
and dependency, declaration, binder, and type traversal order. Successful
checking freezes the kinded facts used by later stages. The first kind rule
that can establish a failure owns it; ordinary unification, evidence selection,
and Core synthesis do not reclassify a source kind error.

Resolved declaration checking uses an empty `OMEGA`. Each type inference
variable is registered in `OMEGA` with one fixed monomorphic kind before the
variable can enter a type. Instantiating an outer scheme copies the
corresponding declared binder kind. Unification and the occurs check consult
that same entry, and unification checks kinds before solving a variable. It may
solve a higher-kinded inference variable with a constructor or partial
application of the same kind. It does not infer a kind, synthesize a type
lambda, abstract over mismatched application arguments, change the variable's
kind, or recover a missing or conflicting registry entry. The occurs check
traverses both children of every application. Zonking removes every inference
variable before a checked summary, linked fact, or Core program is retained.

A scheme is distinct from a monotype and has no ordinary kind. It has the shape
`forall (A_1 : k_1) ... (A_n : k_n). body`, with distinct binders and a body
that satisfies `K-Value-Type` under the extended `DELTA`. A scheme cannot occur
as a type-application argument, term-binder type, tuple element, function
domain or codomain, or other monotype. An eligible anonymous-function local may
generalize eligible inference variables of any fixed monomorphic kind. Those
binders remain outer scheme binders; no `forall` appears beneath a term-function
arrow. Recursive and otherwise ineligible locals keep their current
monomorphic behavior.

Implementation overlap and evidence matching use the same kind-preserving
first-order application structure. Freshening preserves every binder kind.
Evidence selection begins only after the complete goal contains no inference
variable. Matching may substitute only the independently freshened candidate
implementation's declared head variables; it never solves or refines an
inference variable retained in the goal. Current full-head overlap,
strict-subterm prerequisite, cycle, and deterministic selection rules remain
in force over the canonical representation.

### Retained facts and module boundaries

The defining kinded binder record is canonical for each resolved
`TypeVariableId`. A nominal type-constructor kind is derived from its ordered
parameter records; a retained cache, if any, must equal that derivation. A data
constructor retains a kind-checked rank-1 term scheme, not a separate
“constructor kind.” Type occurrences retain identities rather than duplicate
authoritative kinds. Inference kinds live only in the elaborator's transient
inference registry. Inference variables never enter a checked summary or
validated Core; only zonked monotypes and fixed scheme-binder kinds cross those
boundaries.

Checked schemes bind ordered `(TypeVariableId, Kind)` pairs. Nominal,
interface, implementation, requirement, substitution, and selected-evidence
facts retain the identities and binder kinds needed to authenticate their
types. Export summaries retain public kinds and the hidden kind and identity
closure required by public schemes, data constructors, interfaces,
implementation heads, prerequisites, and selected evidence.

Import admission checks an immutable body-free summary without dependency
bodies. It preserves the defining identity and canonical binder kind and
rejects a duplicate or mismatched binder kind, invalid nominal-kind derivation,
unbound type variable, kind-invalid public or hidden type, and kind-invalid
implementation fact as an internal dependency-summary failure. Qualified or
targeted aliases, opacity, implementation-only selection, public facades,
transitive routes, and dependency diamonds cannot recompute a kind or replace
one defining kind with a local fact. Linked interface-evidence validation then
authenticates the kinded schemes, heads, substitutions, prerequisites, selected
method types, and authorization facts before Core synthesis.

### Core boundary

Checked Core monotypes use the same unary `Type::Application` algebra. This is
distinct from the existing Core `TypeApplicationNode`, which is an erased
expression operation that simultaneously instantiates one outer rank-1 scheme.
Outer schemes and `TypeAbstractionNode` retain ordered kinded binder lists. One
`TypeApplicationNode` supplies one monotype argument per binder in order; each
argument must synthesize the binder's kind, and its result is simultaneous
substitution into the kind-`Type` scheme body. This increment does not curry
Core abstractions or instantiations into unary expression operations.

Resolved Core type binders agree with their canonical registry records.
Generated Core binders are owned by their local abstraction and must agree with
the matching outer scheme binders. Ordinary Core value binders and monomorphic
expression annotations satisfy `K-Value-Type`; the annotation on a type
abstraction is the well-formed outer scheme rather than an ordinary monotype.
Type abstraction, simultaneous instantiation, substitution, alpha-renaming,
scope checking, construction, and both retained transforms preserve all binder
kinds and canonical applications.

Independent Core validation receives linked Core, immutable kinded nominal and
data-constructor registries, and the existing identity and provenance inputs.
It synthesizes monotype kinds and checks schemes rather than trusting
elaborator results. It rejects forged nominal parameter order or kind,
nominal-kind derivations, resolved and generated binder relationships,
structural application domains and results, outer-scheme and abstraction
agreement, Core type-argument counts and kinds, simultaneous substitution
results, inference-variable escape, and constructor-kinded ordinary value
annotations before evaluation.

Kinds and type operations still erase. Evaluation gains no kind value, type
value, runtime lookup, interface object, frame, or transition. The evaluator's
existing nominal-shape inspection migrates mechanically to the canonical
`outer_nominal` operation; this is not a semantic or state-machine change.

### Diagnostics and resources

Kind checking reports structured reasons for:

- `kind.not-applicable` when an applied type does not synthesize a function
  kind;
- `kind.argument` when a type-application argument differs from the function
  kind's domain or an interface-application argument differs from the selected
  interface parameter kind; and
- `kind.expected-type` when an owning value-type rule finds a kind other than
  `Type`.

Resolution reports duplicate, unused, and unbound explicit binders with
`resolve.duplicate-type-parameter`, `resolve.unused-type-parameter`, and
`resolve.unknown-type`. Existing implementation and interface rules retain
`impl.prerequisite-variable` and `interface.method-parameter` ownership.

Each diagnostic retains the causal application, argument, value-type, or binder
site; the declaration site when it explains the found kind; and structured
expected and found kinds. Diagnostic rendering does not infer these fields from
text.

Kind traversal, clone, equality, hashing, rendering, substitution,
unification, matching, summary admission, Core admission, transform rebuilding,
validation, and disposal use iteration or explicit bounded work stacks. The
resource ledgers are:

- lexer token, diagnostic, and parser-event retention charge syntax work;
  projection receives no mutable ledger and remains bounded by the admitted
  CST and structural-depth check;
- resolved kind checking, elaboration, and retained kind cloning charge the
  owning resolution or checking type-work budget;
- interface, implementation, evidence, and linked-authentication traversal or
  comparison charge the graph-wide constraint budget; retaining a structural
  type, substitution, or kind clone additionally charges the applicable
  type-work budget; and
- Core construction, transform rebuilding, and independent Core validation use
  their existing independent type-work ledgers.

The independent Core validator keeps one cumulative ledger across registry,
envelope, graph, binder, node, term-scope, and type-scope validation, but this
increment raises that ledger's numeric capacity from `TYPE_WORK_LIMIT` to
`3 * TYPE_WORK_LIMIT`. Core construction, transform rebuilding, and every
other phase retain `TYPE_WORK_LIMIT`. This is a bounded implementation-resource
policy change, not an Ash semantic change, a ledger reset, or a separate Kind
allowance. The retained depth-96 generic-prerequisite pipeline now consumes
275,398 predecessor units plus 145,151 required Kind units, or 420,549 total.
The retained width-32,767 Core validation and disposal witness now consumes
`22 * width + 7`, or 720,881 units. A validator-local capacity of 983,040
preserves both unchanged predecessor witnesses without making either measured
result a brittle limit boundary.

One unit is charged per visited or retained `Kind` node, per visited or retained
canonical `Type::Application` node, and per binder-kind record before storage.
An arrow schedules and charges both child visits. A compared kind pair charges
one comparison unit in its owning traversal ledger. Retaining a record charges
one record unit plus every type and kind node it copies. Each owning operation
must publish its complete additive formula in tests and the retained evidence,
including explicit work-stack or index storage already charged by that
boundary. Exact success, one-short failure, stable reason and precedence, and
transactional teardown are required; a failed operation retains no partial
fact. Existing deterministic dependency, import, declaration, binder, and type
traversal order determines the first failure.

## Semantic delta

- Declaration binders may state monomorphic function kinds in source.
- Globals and implementations gain optional complete explicit binder lists.
- Omitted explicit kind annotations and legacy implicit binders mean `Type`;
  kind arrows are never inferred in this increment.
- Nominals and type variables may occur unsaturated or partially applied when
  their synthesized residual kind satisfies the owning rule.
- Source type application becomes one kind-checked operation instead of a
  saturated-nominal-only resolution form.
- Type inference, implementation matching, summaries, linked evidence, and
  Core retain and authenticate fixed kinds.
- Eligible local bindings may generalize inference variables of any already
  fixed monomorphic kind at the outer rank-1 scheme boundary.
- Source terms remain rank-1, every runtime monotype remains kind `Type`, and
  evaluation semantics remain unchanged.

## Affected specification areas

- [Syntax grammar](../../spec/syntax.md#grammar) gains kind and shared binder
  productions and binder placement on globals and implementations.
- [Type and constructor scope](../../spec/name-resolution.md#type-and-constructor-scope)
  stops defining saturation as a resolution responsibility and defines kinded
  binder identity retention.
- [Imports and namespaces](../../spec/name-resolution.md#imports-and-namespaces)
  retain and authenticate public and hidden kind closure without dependency
  bodies.
- [Global scope](../../spec/name-resolution.md#global-scope) distinguishes
  complete explicit binders from legacy implicit kind-`Type` binders.
- [Static semantics](../../spec/static-semantics.md) defines the kind language,
  canonical application judgment, value-type contexts, kinded inference, and
  structured failures.
- [Inference and rank-1 restrictions](../../spec/static-semantics.md#inference-and-rank-1-restrictions)
  admits fixed higher-kinded inference variables without kind inference, kind
  polymorphism, or higher-order unification.
- [Interfaces and constrained schemes](../../spec/static-semantics.md#interfaces-and-constrained-schemes)
  checks the single interface parameter and method types against declared
  kinds.
- [Implementations](../../spec/static-semantics.md#implementations) defines
  kinded explicit and legacy binders, canonical matching, and kind-preserving
  prerequisite, overlap, orphan, and selection behavior.
- [Failure ownership and constraint resources](../../spec/static-semantics.md#failure-ownership-and-constraint-resources)
  adds kind-checking ownership and bounded kind work.
- [Explicit rank-1 operations](../../spec/elaboration.md#explicit-rank-1-operations)
  carries kinds on Core scheme binders and simultaneous instantiations while
  monotypes use unary structural application.
- [Module linking and entry generation](../../spec/elaboration.md#module-linking-and-entry-generation)
  authenticates kinded summaries, evidence, and linked checked facts.
- [Validation boundary](../../spec/elaboration.md#validation-boundary)
  independently validates kinded registries, binders, substitutions, and value
  annotations.

## Resulting specification truth

After the complete product branch is integrated into `main`, Ash has the
monomorphic kind language `Type | kind -> kind`. Declaration type parameters
may carry explicit kinds, and all omitted annotations mean `Type`. A complete
explicit binder list controls a global or implementation's parameters; a
legacy header binds only free kind-`Type` variables.

Every checked monotype occurrence has one derivable kind. Type application is
valid exactly when its function has a matching function kind. Partial
constructors may cross declarations, summaries, constraints, implementations,
and Core only when their synthesized residual kinds satisfy the owning rule.
Every ordinary source and Core value monotype has kind `Type`. Outer rank-1
schemes have kinded binders and a kind-`Type` monotype body but have no ordinary
kind and cannot occur in monotype positions.

Kinded first-order unification and implementation matching may substitute
constructors and partial applications for same-kinded variables, but cannot
synthesize type lambdas or infer kinds. Linked evidence validation and Core
validation independently reject forged kind relationships before evaluation.

## Interactions

The existing single interface parameter may now be higher-kinded. Its method
types may apply that parameter, but the existing rule still requires every
method to mention the interface parameter and expose a top-level function.
Method-local parameters are unchanged and remain unavailable.

The current orphan rule uses one structural operation:

```text
outer_nominal(Nominal(identity)) = identity
outer_nominal(Application(function, argument)) = outer_nominal(function)
outer_nominal(other) = none
```

The owner is stable for bare, partial, and saturated nominal constructors. A
local nominal constructor used at residual function kind therefore establishes
the same defining owner. Primitive, structural, and variable heads have no
nominal owner. The evaluator and validators reuse this operation for nominal
shape inspection.

Strict-subterm prerequisite comparison visits both children of canonical
applications. Overlap, evidence selection, and summary authentication observe
the same application and binder identities. They do not introduce higher-order
matching. Explicit implementation import and re-export keeps controlling
availability independently from kind checking.

Opacity controls constructor term and pattern access, not a nominal identity's
kind. Hidden nominal and binder kinds may remain in body-free summaries without
making their spellings or constructors accessible.

The change generalizes the current rank-1 type algebra but does not add nested
term schemes. Instantiating a kinded outer parameter creates one same-kinded
first-order inference variable. One simultaneous Core type-application
operation instantiates the complete ordered outer binder list. Erasure keeps
runtime behavior unchanged.

## Non-goals

- Kind inference, kind metavariables, defaulting unsolved kinds, or
  generalization over kind variables in this increment. This exclusion is
  phase-dependent and does not reject a later bounded inference proposal.
- Kind polymorphism, higher-rank kinds, dependent kinds, row kinds, or runtime
  reflection of kinds.
- Type lambdas, higher-order unification, impredicative types, source `forall`,
  explicit term type application, or higher-rank source values.
- Method-local type parameters or authenticated polymorphic method evidence;
  those belong to the next prepared `lib-ash` increment.
- Multi-parameter interfaces, associated outputs, functional dependencies,
  defaults, specialization, packages, persistent artifacts, or separate
  linking.
- A compatibility grammar, a second semantic type representation, or evaluator
  semantic and state-machine changes. Mechanical canonical-shape migration is
  in scope.

## Required evidence

Implementation must use the existing parser, resolved-surface, bidirectional
checking, evidence, linked-validation, Core, and evaluator pipeline. It must
replace the saturated nominal representation with one canonical application
form rather than retain parallel normal forms.

Positive and negative tests must cover:

- contextual `Type`, arrows, grouping, annotation omission, exact
  single-parameter interfaces, complete binder lists, recovery, exact spans,
  and both global presentations;
- exact binder-set and order laws for globals and implementations, phantom
  nominal parameters, unchanged method-local rejection, and every structured
  duplicate, unused, unbound, prerequisite-only, and undetermined failure;
- total kind synthesis for primitives, variables, bare nominals, unary
  applications, tuples, term functions, and every owning value-type boundary;
- derived nominal kinds, higher-kinded nominal, interface, global,
  implementation, and eligible generalized-local parameters, nested and
  partial applications, and outer scheme well-formedness;
- fixed-kinded inference allocation before use, structural and injective
  first-order constructor and partial-application solutions, occurs checks,
  missing or conflicting transient registry entries, complete zonking, and
  cases that would require a type lambda;
- generic implementation heads, both application subterms, strict-subterm
  prerequisites, full-head overlap, stable bare/partial/saturated orphan
  ownership, inference-free selection goals, and abstract and concrete evidence;
- immutable body-free local and imported witnesses for nominal parameter kinds,
  interface parameter kinds, global scheme binders, implementation head and
  prerequisite binders, method schemes, and hidden closure through direct,
  qualified, targeted, implementation-only, facade, transitive, and diamond
  routes after dependency bodies are unavailable;
- dependency-summary mutation of every new public and hidden kind field,
  duplicate or mismatched canonical binders, invalid nominal-kind derivation,
  unbound variables, and kind-invalid global, interface, data-constructor, and
  implementation facts, all rejected before local checking or Core;
- linked-evidence mutation of kinded schemes, heads, substitutions,
  prerequisites, selected method types, and authorization relationships before
  Core synthesis;
- independent Core mutation distinguished between unary structural monotype
  application and simultaneous `TypeApplicationNode` instantiation, including
  nominal parameter order, binder kind and provenance, nominal-kind derivation,
  variable scope and shadowing, application domain and result, outer scheme and
  abstraction agreement, type-argument count and kind, simultaneous
  substitution, inference escape, and every ordinary kind-`Type` annotation;
- one positive higher-kinded linked program through Core construction, both
  retained transforms, independent revalidation, erasure, evaluation, and
  exact library and CLI observations;
- `kind.not-applicable`, `kind.argument`, and `kind.expected-type` reasons with
  positive and negative higher-kinded requirement and implementation-head
  arguments, primary and related spans, expected and found kinds, deterministic
  precedence, library API observations, and CLI rendering independently from
  policy; and
- migration of every predecessor-valid omitted kind and implicit global or
  implementation binder without edits, preserving first-occurrence order and
  kind `Type`; no legacy header silently gains a function kind.

Migration must also inventory deliberate stage and reason changes. In
particular, predecessor failures for an unsaturated nominal and `A<Int>` move
from resolution to their exact kind-checking reasons. `Type` remains usable as
a nominal spelling outside a kind annotation. The complete predecessor corpus,
specification examples, CLI, Core-validation, and evaluator observations remain
otherwise unchanged.

Safe teardown of canonical application spines requires deliberate Rust API
refinements. `Observation` dismantles its result type iteratively when dropped.
Rust therefore no longer exposes its owned `value` or `ty` fields for direct
move, overwrite, or by-value destructuring. `Observation::value` and
`Observation::ty` provide borrowing access. `Observation::into_value`,
`Observation::into_type`, and `Observation::into_parts` provide consuming
access. A consumed value remains paired with the evaluation heap through
`ObservationValue`, and `ObservationParts` dismantles an unconsumed type
iteratively. A caller that
takes ownership of a type can use `discard_type_iteratively` for the same
stack-safe disposal.

`TypeContext::insert` also dismantles a displaced binding fact iteratively and
no longer returns its raw result type. All product callers already ignore that
return. Returning the recursive type would let an otherwise safe ignored value
use Rust's recursive drop path. These refinements change Rust source
compatibility, not Ash semantics, rendered observations, or evaluator behavior,
and their teardown uses no unsafe code.

The same overwrite boundary applies to public checked owners whose automatic
drop dismantles structural types iteratively. `CheckedRequirement::argument`,
`ConstrainedScheme::value_type`, `CheckedInterfaceMethodFact::value_type`, and
`CheckedImplementationFact::argument` replace mutable raw fields with borrowing
accessors. Construction and mutation remain compiler-owned. This is the same
Rust source-compatibility refinement and does not change the represented Ash
facts.

Public carriers without automatic `Drop` retain caller-managed type ownership.
Code that extracts a potentially deep type from one of those carriers must use
`discard_type_iteratively`; this increment does not convert every recursive
type carrier into an automatic-drop API. The distinction is an ownership and
source-compatibility boundary, not an Ash semantic distinction.

An exhaustive retained site map must list every source, surface, resolved,
checked, summary, evidence, registry, Core-binder, Core-pattern, and Core-node
type-bearing position with its kind environment, synthesis or checking owner,
required result kind or scheme rule, structured failure, budget ledger, and
disposal owner. An architectural test or equivalent closed-inventory review
must fail when a `Type` variant or type-bearing Core site is added without kind
coverage.

Resource evidence must publish each operation's additive formula and prove
exact success, one-short failure, failure reason and precedence, transactional
retention, and accepted and rejected teardown. Deep and wide success and
rejection must run on a 256 KiB stack for construction, clone, equality,
hashing, rendering, kind checking, substitution, occurs checking, unification,
implementation matching, summary/import/link admission, Core construction,
both transforms, independent validation, and disposal. Wide source argument
vectors must exercise their deep folded unary application tree.

Core-validation evidence must additionally prove the validator-local 983,040
capacity at its exact and one-short boundaries, retain one cumulative ledger
through every validation pass, leave failed charges atomic, and pass the
unchanged depth-96 generic-prerequisite pipeline and width-32,767 Core disposal
witnesses on 256 KiB stacks. The construction and transform limits remain
327,680.

Retain a `docs/design/lib-ash/kinds-evidence.md` report that names the final
semantic boundary, production and maintenance sites, exact resource results,
tampering coverage, migration results, and intentional exclusions. Update the
syntax, name-resolution summary and scope rules, static semantics, elaboration
and linking, overview, tool diagnostics, design, and trajectory documentation
from implemented and tested behavior.

The final checkpoint runs and reads the complete output of:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --workspace --all-targets --all-features
cargo clippy --locked --workspace --all-targets --all-features -- -D warnings
cargo test --locked --workspace --all-targets --all-features -- --list
cargo xtask verify
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Independent semantic, implementation, diagnostics, resource, and specification
reviews must have no unresolved correctness issue. Only then may the branch
retain the evidence report and normative updates and remove CP-0009, TASK-0016,
its execution plan, and this temporary design record. This increment does not
create a `lib-ash` tag; the complete milestone remains open. The branch remains
based on the integrated predecessor and unmerged until this increment closes.
