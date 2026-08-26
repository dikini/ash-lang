# CP-0009: Explicit Kinds and Higher-Kinded Parameters

- ID: `CP-0009`
- Status: proposed
- Related: [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), and the [approved design record](../plans/2026-08-26-explicit-kinds-design.md)

> This proposal is not current Ash.

## Current behavior

Current Ash keeps kinds internal. Every source type parameter and inference
variable has kind `Type`. A nominal declaration with `n` parameters has an
internal `n`-argument constructor kind, but resolution requires every source
nominal application to be saturated. A parameter cannot appear in type-function
position, and no constructor-kinded type survives resolution.

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
```

Nominal declarations and the single interface parameter use this syntax.
Equational and inline operational globals may place a list after the global
name. Implementations may place a list after `impl`:

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

An omitted kind annotation on an explicit binder means `Type`. An explicit
binder list is complete: each free type variable in the declaration header is
listed exactly once, and no implicit binder is added. A global or
implementation without a binder list preserves current implicit
first-occurrence binding, with every implicit binder fixed at kind `Type`.

The compatibility form does not infer kinds. A higher-kinded parameter always
requires an explicit binder and annotation in this increment. This is a
phase-dependent boundary, not a permanent rejection of kind inference. A later
proposal may add bounded declaration-local kind inference independently from
kind polymorphism.

### Kinds and application

The source kind language is:

```text
kind ::= Type | kind -> kind
```

`->` associates to the right. Primitive types have kind `Type`. A nominal
constructor declared with parameter kinds `k_1` through `k_n` has kind
`k_1 -> ... -> k_n -> Type`. A type variable has its binder's declared kind.

Type application is unary and left-associative in the checked type algebra.
The kind rule is:

```sequent
K-Application :=
  |- function_type : argument_kind -> result_kind
  |- argument_type : argument_kind
  ===>
  |- function_type<argument_type> : result_kind
```

Surface comma-separated nominal applications project to repeated unary
application. Rendering may retain conventional `Name<A, B>` notation. Type
equality, substitution, unification, implementation matching, summary
authentication, and Core validation use only the canonical application tree.

An unsaturated or partially applied constructor is valid only where the
surrounding rule expects its residual kind. A constructor-kinded type is not a
value type. Constructor payloads, global and method value types, pattern and
term binder types, expression types, entry types, and evaluator observations
must have kind `Type`.

### Kinded checking and inference variables

Parsing retains kind syntax and binder annotations. Resolution assigns stable
identities and resolves names and declaration sorts. It no longer enforces
nominal saturation or rejects every type-parameter application. Using an
interface as an ordinary type constructor remains a resolution sort error.
Resolution also owns a duplicate explicit binder or an unbound uppercase name
under a complete explicit binder list.

Before ordinary type checking consumes a resolved declaration, kind checking
derives nominal constructor kinds, installs declared binder kinds, and
synthesizes or checks every resolved type kind. Successful checking freezes the
kinded declaration facts used by later stages. The first kind rule that can
establish a failure owns it; ordinary unification, evidence selection, and Core
synthesis do not reclassify a source kind error.

Each type inference variable receives one fixed kind when allocated.
Unification is first-order over the canonical application tree and checks kinds
before solving a variable. It may solve a higher-kinded inference variable
with a constructor or partial application of the same kind. It does not infer
a kind, synthesize a type lambda, abstract over mismatched application
arguments, or change the variable's kind. The occurs check traverses
applications at every kind.

Implementation overlap and evidence matching use the same kind-preserving
first-order application structure. A candidate match may solve only the
candidate implementation's declared head variables. Selection does not solve
an unrelated goal inference variable merely to make a candidate apply. Current
full-head overlap, strict-subterm prerequisite, cycle, and deterministic
selection rules remain in force over the canonical representation.

### Retained facts and module boundaries

Checked schemes bind ordered `(TypeVariableId, Kind)` pairs. Nominal,
interface, implementation, requirement, and inference facts retain the kinds
needed to authenticate every type occurrence. Export summaries retain public
kinds and the hidden kind and identity closure required by public schemes,
constructors, interfaces, implementation heads, prerequisites, and selected
evidence.

Import admission preserves the defining identity and checked kind. Qualified
or targeted aliases, opacity, implementation-only selection, public facades,
and dependency diamonds cannot recompute a kind or replace one defining kind
with a locally derived fact. Linked interface-evidence validation authenticates
the kinded schemes, heads, substitutions, prerequisites, selected method types,
and authorization facts before Core synthesis.

### Core boundary

Core type binders carry kinds. Core uses the same canonical unary type
application. Type abstraction, application, substitution, alpha-renaming,
scope checking, and construction are kind-aware. A Core value binder and every
Core expression annotation still require kind `Type`.

Independent Core validation receives linked Core, immutable kinded nominal and
constructor registries, and the existing identity and provenance inputs. It
synthesizes kinds from those inputs rather than trusting elaborator results. It
rejects forged binder kinds, constructor kinds, application relationships,
substitution results, and constructor-kinded value annotations before
evaluation.

Kinds and type operations still erase. Evaluation gains no kind value, type
value, runtime lookup, interface object, frame, or transition.

### Diagnostics and resources

Kind checking reports structured reasons for:

- applying a type whose kind is not a function kind;
- supplying an argument whose kind differs from the function kind's domain;
- using a constructor-kinded type where a value type of kind `Type` is
  required.

Resolution reports duplicate explicit binders and unbound type names under a
complete explicit binder list with its existing structured scope ownership.

Each diagnostic retains the causal application, argument, value-type, or binder
site; the declaration site when it explains the found kind; and structured
expected and found kinds. Diagnostic rendering does not infer these fields from
text.

Kind traversal, clone, equality, hashing, rendering, substitution,
unification, matching, summary admission, Core admission, validation, and
disposal use iteration or explicit bounded work stacks. Lexing, concrete-tree
construction, and projection charge the existing syntax budget. After
projection, every retained or visited kind node and every kind-aware application
operation charges the existing type-work resource family at the stage that
owns it. Core construction and independent Core validation retain separate
budgets. Existing deterministic dependency, import, declaration, binder, and
type traversal order determines the first failure.

## Semantic delta

- Declaration binders may state monomorphic function kinds in source.
- Globals and implementations gain optional complete explicit binder lists.
- Omitted explicit kind annotations and legacy implicit binders mean `Type`;
  kind arrows are never inferred in this increment.
- Nominals and type variables may occur unsaturated or partially applied when
  the expected residual kind admits them.
- Source type application becomes one kind-checked operation instead of a
  saturated-nominal-only resolution form.
- Type inference, implementation matching, summaries, linked evidence, and
  Core retain and authenticate fixed kinds.
- Source terms remain rank-1, every runtime value type remains kind `Type`, and
  evaluation remains unchanged.

## Affected specification areas

- [Syntax grammar](../../spec/syntax.md#grammar) gains kind and shared binder
  productions and binder placement on globals and implementations.
- [Type and constructor scope](../../spec/name-resolution.md#type-and-constructor-scope)
  stops defining saturation as a resolution responsibility and defines kinded
  binder identity retention.
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
  carries kinds on Core type binders and applications.
- [Validation boundary](../../spec/elaboration.md#validation-boundary)
  independently validates kinded registries, binders, substitutions, and value
  annotations.

## Resulting specification truth

After the complete product branch is integrated into `main`, Ash has the
monomorphic kind language `Type | kind -> kind`. Declaration type parameters
may carry explicit kinds, and all omitted annotations mean `Type`. A complete
explicit binder list controls a global or implementation's parameters; a
legacy header binds only free kind-`Type` variables.

Every checked type occurrence has one derivable kind. Type application is
valid exactly when its function has a matching function kind. Partial
constructors may cross declarations, summaries, constraints, implementations,
and Core only when their residual kinds match. Every source and Core value type
has kind `Type`.

Kinded first-order unification and implementation matching may substitute
constructors and partial applications for same-kinded variables, but cannot
synthesize type lambdas or infer kinds. Linked evidence validation and Core
validation independently reject forged kind relationships before evaluation.

## Interactions

The existing single interface parameter may now be higher-kinded. Its method
types may apply that parameter, but the existing rule still requires every
method to mention the interface parameter and expose a top-level function.
Method-local parameters are unchanged and remain unavailable.

The current orphan rule recognizes the outer nominal identity of a partial or
saturated canonical application. A local nominal constructor used at residual
function kind still establishes the same defining owner. Primitive, structural,
and variable heads still have no nominal owner.

Strict-subterm prerequisite comparison, overlap, evidence selection, and
summary authentication observe canonical applications and binder identities.
They do not introduce higher-order matching. Explicit implementation import
and re-export keeps controlling availability independently from kind checking.

Opacity controls constructor term and pattern access, not a nominal identity's
kind. Hidden nominal and binder kinds may remain in body-free summaries without
making their spellings or constructors accessible.

The change generalizes the current rank-1 type algebra but does not add nested
term schemes. Instantiating a kinded outer parameter still creates one
first-order inference variable and one explicit Core type operation. Erasure
keeps runtime behavior unchanged.

## Non-goals

- Kind inference, kind metavariables, defaulting unsolved kinds, or kind
  generalization in this increment. This exclusion is phase-dependent and does
  not reject a later bounded inference proposal.
- Kind polymorphism, higher-rank kinds, dependent kinds, row kinds, or runtime
  reflection of kinds.
- Type lambdas, higher-order unification, impredicative types, source `forall`,
  explicit term type application, or higher-rank source values.
- Method-local type parameters or authenticated polymorphic method evidence;
  those belong to the next prepared `lib-ash` increment.
- Multi-parameter interfaces, associated outputs, functional dependencies,
  defaults, specialization, packages, persistent artifacts, or separate
  linking.
- A compatibility grammar, a second type representation, or evaluator changes.

## Required evidence

Implementation must use the existing parser, resolved-surface, bidirectional
checking, evidence, linked-validation, Core, and evaluator pipeline. It must
replace the saturated nominal representation with one canonical application
form rather than retain parallel normal forms.

Positive and negative tests must cover:

- kind tokens, arrows, grouping, annotation omission, complete binder lists,
  recovery, exact spans, and both global presentations;
- derived nominal kinds, higher-kinded nominal, interface, global, and
  implementation parameters, nested and partial application, and every
  kind-`Type` value context;
- legacy implicit kind-`Type` headers and rejection of silently inferred
  higher-kinded use;
- fixed-kinded inference allocation, first-order constructor and partial
  application solutions, occurs checks, and cases that would require a type
  lambda;
- generic implementation heads, strict-subterm prerequisites, full-head
  overlap, orphan ownership at residual kind, abstract and concrete evidence,
  and selection that does not guess a goal variable;
- private, public, opaque, and hidden kind facts through qualified, targeted,
  implementation-only, facade, and diamond imports;
- linked-evidence tampering and independent Core tampering for binder,
  constructor, application, substitution, and value-context kinds;
- structured diagnostic reasons, primary and related spans, expected and found
  kinds, deterministic precedence, library API observations, and CLI rendering;
- exact and one-short syntax-work charges for kind syntax and type-work charges
  for every retained later-stage fact, plus deep and wide construction, clone,
  equality, substitution, rendering, linking, validation, and disposal on a
  256 KiB stack; and
- all predecessor corpus, migration, specification-example, library API, CLI,
  Core-validation, evaluator, formatting, lint, documentation, and full
  repository verification gates.

Retain a `docs/design/lib-ash/kinds-evidence.md` report that names the final
semantic boundary, production and maintenance sites, exact resource results,
tampering coverage, migration results, and intentional exclusions. Update the
syntax, name-resolution, static-semantics, elaboration, overview, tool, design,
and trajectory documentation from implemented and tested behavior. Independent
semantic, implementation, diagnostics, resource, and specification reviews must
have no unresolved correctness issue before proposal and task cleanup.
