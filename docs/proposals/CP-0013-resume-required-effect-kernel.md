# CP-0013: Resume-required effect kernel

- ID: `CP-0013`
- Status: proposed
- Related:
  - [DN-0009](../design/DN-0009-effects-handlers-and-continuations.md)
  - [DN-0026](../design/DN-0026-effect-ash-resource-first-milestones.md)
  - [DN-0027](../design/DN-0027-effect-ash-program-design.md)
  - [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md)
  - [AD-0004](../decisions/AD-0004-small-step-semantic-method.md)
  - [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md)
  - [AD-0007](../decisions/AD-0007-typed-core-dialects.md)
  - [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This proposal is not current Ash.

## Current behavior

Ash is pure. Its semantic type algebra contains primitive, nominal,
application, tuple, and two-child function types. Expression typing records a
value type but no computation effect. A function call has no latent effect row,
and global and eligible local schemes quantify only ordinary fixed-kinded type
variables.

The source language has no effect declaration, operation request, handler,
resume form, or effect-row syntax. The linked entry program cannot request an
interpretation. Its deterministic small-step configuration contains the heap,
environment, control, and ordinary continuation needed by pure evaluation.

Core separates values from computations behind a typed operation-family
boundary. The pure executable dialect instantiates that boundary with no
inhabited operation. Its independent validator rejects any foreign operation.
The explicit evaluator uses first-order frames, but those frames are not Ash
continuations and cannot be captured or resumed by a program.

## Proposed behavior

### Kernel boundary

Ash gains module-owned effect APIs, identity-bearing open and closed effect
rows, explicit operation requests, ordered lexical handlers, and one
non-escaping resume capability per active operation clause. Every accepted
clause consumes that capability exactly once along each normally completing
control-flow path.

This first kernel makes four deliberate restrictions:

- a handler is syntax, not a first-class value;
- a handler covers every operation of one exact effect instance;
- a handler preserves the handled computation's value type and has an implicit
  identity return for ordinary completion; and
- an operation clause cannot return normally without resuming, retain its
  resume capability, or resume more than once.

The restrictions remove handler construction effects, partial discharge,
result-type transformation, abortive completion, and escaping control from the
first checkpoint.

### Syntax

The keywords `effect`, `perform`, `handle`, `with`, and `resume` become
reserved. This is a source migration: an existing binder with one of those
spellings must be renamed. A module may declare an effect API with zero or more
type parameters and one or more operations:

```ebnf
module_declaration ::=
    type_declaration
  | interface_declaration
  | implementation_declaration
  | effect_declaration
  | global_definition ;

effect_declaration ::=
  [ "pub" ] "effect" upper_identifier [ type_parameters ]
  "{" line_end
  effect_operation { line_end effect_operation } [ line_end ]
  "}" ;
effect_operation ::= identifier ":" type ;
```

Each operation type must have exactly one outer function domain. Its domain and
result are ordinary value types. The operation's requested effect comes from
its owner and is not written in the operation signature. Operation-local type
parameters, requirements, associated outputs, defaults, and operation bodies
are absent.

Function results may carry an effect row. A missing row means the empty row:

```ebnf
type ::= atomic_type | atomic_type "->" computation_type ;
computation_type ::= type [ "!" effect_row ] ;
kind_atom ::= "Type" | "EffectRow" | "(" kind ")" ;
effect_row ::=
  "{"
    [ effect_instance { "," effect_instance } [ "|" row_variable ]
    | "|" row_variable ]
  "}" ;
effect_instance ::= effect_reference [ type_arguments ] ;
effect_reference ::=
  upper_identifier | upper_identifier "." upper_identifier ;
row_variable ::= upper_identifier ;

inline_operational_global ::=
  [ "pub" ] "fn" identifier [ type_parameters ]
  "(" typed_pattern { "," typed_pattern } ")"
  "->" computation_type [ where_clause ] block ;
```

Function arrows remain right-associative. `!` attaches to the complete
computation codomain immediately to its left after parentheses are applied.
Thus `A -> B -> C ! {E}` is a pure call from `A` returning a function whose
call from `B` may request `E`. `A -> (B -> C) ! {E}` is a call which may
request `E` while returning a pure function. Parentheses can contain a function
type with its own latent row. Equational signatures already contain complete
function types; inline operational result positions change from `type` to
`computation_type` as shown above. Operation declarations continue to require
one outer function type whose own operation result has no row annotation.

`EffectRow` is a new binder kind. In this increment it is valid only as a
complete global or generalized-local binder kind, not as the domain or
codomain of a kind arrow. Nominal, interface, implementation, effect, and
method parameter lists continue to admit only their existing ordinary kinds.
A row tail must resolve to a global or eligible-local parameter of kind
`EffectRow`. An effect argument continues to have its declared ordinary kind.
For example:

```ash
effect State<S> {
    get : Unit -> Int
    put : Int -> Unit
}

relay<R : EffectRow> : (Unit -> Int ! { | R }) -> Int ! { | R }
relay action = action ()
```

The three expression forms integrate into the existing precedence grammar as
follows:

```ebnf
expression ::=
    block
  | function_expression
  | match_expression
  | handler_expression
  | resume_expression
  | equality_expression ;
primary_expression ::=
    integer
  | boolean
  | unit
  | unqualified_term_reference
  | qualified_term_reference
  | perform_expression
  | parenthesized_expression ;
perform_expression ::= "perform" operation_reference primary_expression ;
operation_reference ::= effect_reference [ type_arguments ] "." identifier ;
handler_expression ::=
  "handle" expression "with" effect_instance
  "{" line_end
  handler_clause { line_end handler_clause } [ line_end ]
  "}" ;
handler_clause ::= identifier pattern "=>" expression ;
resume_expression ::= "resume" expression ;
```

`perform` has primary-expression precedence after consuming its one primary
operand. `handle` and `resume` have the same loose prefix boundary as `match`;
their bodies extend to their delimiter or the end of the surrounding
expression. A handled or resumed expression must be parenthesized to serve as
an application or infix operand. Therefore `resume x + y` resumes with
`x + y`, while `(resume x) + y` resumes with `x` and then adds `y`. A
non-primary operation argument is parenthesized. Each handler clause names one
operation of the handled API and supplies one irrefutable domain pattern.
`resume` is valid only in the dynamic clause body selected by the nearest
enclosing handler. It does not name or construct a value.

This complete shape handles two operations and returns `42`:

```ash
effect Cell {
    read : Unit -> Int
    write : Int -> Unit
}

main : Unit -> Int
main () = handle (perform Cell.read ()) with Cell {
    read ignored => resume 42
    write value => resume ()
}
```

The pure `main` signature is valid because the handler discharges `Cell`.

### Effect and operation identity

Resolution allocates an `EffectId` from the defining `ModuleId` and effect
declaration order. Each operation receives an `OperationId` from its owner and
operation declaration order. Aliases, imports, re-exports, and equal spellings
or signatures do not change or equate those identities.

An effect instance is one `EffectId` plus its complete ordered type-argument
vector. It is well formed only when argument count and positional kinds match
the declaration. Two instances are equal only when their effect identities and
all zonked arguments are structurally equal. Distinct applications of one API,
such as `State<Left>` and `State<Right>`, may occur in the same row and are
independent requirements.

Effect declarations occupy the shared uppercase nominal-type/interface/effect
name namespace. Complete imports expose public effects under the module alias.
Targeted imports and public re-exports preserve effect and operation identities.
Operations occupy only their effect-local namespace; they do not create
unqualified term bindings. A local effect conflicts with a nominal type,
interface, effect, targeted uppercase binding, or module alias of the same
spelling. Two operations of one effect cannot share a spelling.

Private and public visibility applies to the whole API. A private effect and
its operations are usable only in the defining module. A public effect exports
its identity, parameters, operation identities, and operation types. An
operation has no independent visibility.

### Computation types and rows

The semantic boundary distinguishes a value type `A` from a computation type
`A ! epsilon`. `epsilon` is an `EffectRow`, not an ordinary value type. A
function value stores one value domain and one computation codomain. The
source type `A -> B` therefore means `A -> (B ! {})`; existing source remains
pure at the type boundary. The newly reserved keyword spellings are the only
source migration introduced by this proposal.

An effect row is an unordered idempotent set of effect instances with at most
one open tail. Row order affects rendering and diagnostics only through a
canonical identity-and-argument order. It never determines evaluation or
handler order. Repeated requests for one instance create one row member.

A written row that contains two members which resolve and unify to the same
effect instance is `effect.duplicate`. Compiler-inferred union instead
coalesces equal members. This distinction rejects redundant source claims
without giving repeated operations multiplicity.

An open row `{E | R}` carries the lacks constraint `E not-in R`. More
generally, its tail lacks every known member written before it. Substitution,
unification, and generalization preserve those constraints. This makes exact
subtraction deterministic: removing `E` from `{E | R}` yields `R`, and `R`
cannot conceal a second equal `E`.

Rows support these operations:

- equality modulo member order and idempotence;
- kind-preserving substitution through effect arguments and a row tail;
- unification of known members and open tails while preserving lacks
  constraints;
- union, which coalesces equal members and retains at most one distinct open
  tail after substitution when every added known member is already known to be
  absent from that tail; and
- exact removal of one effect instance.

This kernel does not retain qualified row-union or membership constraints in a
scheme. If a union would contain two distinct unsolved open tails, or would add
a known member `E` to a tail which does not already carry `E not-in R`,
inference reports `effect.row-union-ambiguous`. The latter rejection is
necessary because `{ | R } union {E}` cannot become `{E | R}` when `R` might
already contain `E`: adding the lacks fact would reject a valid idempotent
instantiation.

An expected row may supply the required lacks fact, an annotation may make two
operands share one tail, and instantiation may close one tail. Closed unions
and `{ known members | R }` unions whose added members are already absent from
`R` retain a principal result. This boundary avoids silently strengthening or
equating independent tails and leaves general qualified row constraints to a
later proposal if source evidence requires them.

There is no row ordering, multiplicity, difference by API shape, effect
subtyping, effect masking, or implicit removal. A checking context may weaken a
minimal inferred row by adding requirements, but inference retains the least
row established by the expression rules.

### Inference and schemes

Expression synthesis and checking produce a value type and computation row:
`GAMMA |- expression => A ! epsilon` and
`GAMMA |- expression <= A ! epsilon`. Literals, variables, function creation,
and constructor creation are pure. Strict compound expressions union the rows
of their evaluated children in the existing left-to-right order. A match adds
the scrutinee row and the union of all arm rows. A block adds each initializer
row and the remainder row.

Function checking moves the body's row into the function's latent computation
codomain while function creation itself remains pure. Application adds the
rows used to evaluate the function and argument to the function's latent row:

```sequent
T-Effectful-Function-Check :=
  pattern <= domain => bindings
  exhaustive([pattern], domain)
  GAMMA, bindings |- body <= codomain ! body_effects
  ===>
  GAMMA |- fn(pattern) { body }
    <= Function(domain, codomain ! body_effects) ! {}

T-Effectful-Apply :=
  GAMMA |- function => Function(domain, codomain ! call_effects) ! function_effects
  GAMMA |- argument <= domain ! argument_effects
  result_effects = function_effects union argument_effects union call_effects
  ===>
  GAMMA |- function argument => codomain ! result_effects
```

The rules preserve existing strict evaluation order; row union does not claim
that operations commute.

Global schemes and eligible local function schemes may quantify variables of
kind `EffectRow`. Explicit global parameters list them with
`: EffectRow`. The omitted global parameter policy discovers their first row
occurrences along with ordinary type occurrences. Instantiation freshens both
ordinary and row parameters with their fixed kinds and lacks constraints.

Eligible local anonymous-function generalization extends the existing rank-1
rule to unsolved row inference variables not free in the environment. Other
local bindings remain monomorphic. Row variables cannot appear in ordinary
value positions, interface applications, nominal arguments, or patterns.
Every inference and row inference variable must be solved or generalized
before a checked summary or Core program is retained.

### Operation typing

For `perform E<arguments>.op operand`, resolution fixes the exact `EffectId`
and `OperationId`. Substituting the effect arguments into the declared
operation type yields `parameter -> result`. The operand checks against
`parameter`; the request returns `result` and adds the exact effect instance to
the operand's row:

```sequent
T-Perform :=
  operation_type(E<arguments>.op) = parameter -> result
  GAMMA |- operand <= parameter ! operand_effects
  request_effects = operand_effects union { E<arguments> }
  ===>
  GAMMA |- perform E<arguments>.op operand => result ! request_effects
```

An operation request does not select a handler during typing and does not name
a provider. Its row records the interpretation requirement that remains after
the operand has been evaluated. If the operand has an open row which does not
already exclude the requested instance, synthesis owns
`effect.row-union-ambiguous`; checking against an expected row with the
necessary lacks fact may resolve it.

### Handler and resume typing

A handler targets one exact, well-kinded effect instance and must contain
exactly one clause for every operation owned by that effect, in any source
order. Missing and duplicate clauses are static failures. Each clause pattern
checks against the substituted operation domain and must be irrefutable.

For an input computation `A ! ({E<arguments>} union rho)`, handling removes
only that exact instance from the input. The output row `epsilon_out` contains
`rho` plus requirements introduced directly by clause evaluation. An operation
of another identity forwards through the handler and remains in `rho`. An
operation of the same exact instance performed by a clause is outside the
current handler and is therefore re-added to `epsilon_out`.

For an operation `op : P -> Q`, its clause receives a `P` pattern. Within that
clause, `resume value` checks `value` against `Q`, consumes the clause's unique
resume capability, and has computation type `A ! epsilon_out`. All clauses
check against the same `A ! epsilon_out`. Ordinary completion of the handled
body passes its `A` value through without a source return clause.

```sequent
T-Handle :=
  GAMMA |- body => A ! ({ E<arguments> } union rho)
  clauses cover each operation of E exactly once
  for each op_i : P_i -> Q_i,
    GAMMA, bindings(pattern_i : P_i);
      resume(Q_i, A, epsilon_out)
      |- clause_i <= A ! epsilon_out, consumes-resume-once
  rho subset-of epsilon_out
  ===>
  GAMMA |- handle body with E<arguments> { clauses }
    => A ! epsilon_out

T-Resume :=
  active-resume = resume(Q, A, epsilon_out)
  GAMMA |- value <= Q ! value_effects
  value_effects subset-of epsilon_out
  ===>
  GAMMA; active-resume |- resume value => A ! epsilon_out, consumes-resume
```

The row constraints choose the least `epsilon_out` satisfying the body
remainder and every clause. Effect weakening permits a clause with fewer direct
requirements to check against that shared output row.

Resume usage is a separate structural dataflow judgment over the resolved
clause body. Sequential composition passes a not-yet-consumed or consumed
state in evaluation order. Every match arm receives the state left by its
scrutinee and must produce the same outgoing state. The complete clause must
produce consumed on every normally completing path. A nested function body,
recursive member, or nested handler clause cannot capture the capability.
`resume` outside its owning clause, an unconsumed normally completing path, and
a use in the consumed state are rejected. Divergence before the syntactic use
remains ordinary divergence; the rule does not claim termination or convert
divergence into discard.

The capability has no source type, binder spelling, tuple or constructor form,
function argument form, return form, storage form, or polymorphic form. This
syntactic and structural boundary is the kernel's non-escape rule.

### Handler order and forwarding

Handlers form an ordered lexical stack. A request is intercepted by the
nearest active handler for the exact effect instance. Row order never changes
that search.

Handlers are deep. When a request selects a handler:

1. evaluation captures the typed control between the request and that handler;
2. the selected clause runs with that handler absent from the active stack;
3. another request for the same instance in the clause reaches the next outer
   matching handler, if any;
4. `resume` consumes the capability and reinstalls the selected handler around
   the captured remainder; and
5. when the resumed remainder produces its handled result, control returns to
   the clause after the `resume` expression.

When search crosses intervening nonmatching handlers, their boundaries and
ordinary inner control become part of the captured continuation. They are
absent while the selected outer clause runs. Resume first reinstalls the
selected handler and then the captured inner boundaries in their original
outer-to-inner nesting order. Those inner scopes unwind normally while the
resumed computation returns. Control then returns to the selected clause with
the selected and intervening handlers absent; only handlers outside the
selected boundary remain active. A request made directly by the selected
clause therefore cannot be intercepted by an intervening captured handler.

An unknown effect passes outward without changing or reordering the captured
computation. Two nested handlers for one identity therefore remain observably
ordered, and a clause may deliberately delegate a same-identity request to an
outer handler.

### Elaboration and typed Core

Checked module summaries retain body-free effect declarations, parameters,
operation identities and substituted schemes, visibility, and provenance.
Import admission and linking authenticate those facts just as they
authenticate other stable module-owned identities. They do not retain a
handler registry or provider choice.

Elaboration produces a production effect Core dialect with typed request,
handler, clause, and resume families. Each effectful node exposes its value
type and row. The dialect uses the accepted value/computation operation-family
boundary; it does not add effect cases to each pure value family. The existing
pure executable dialect keeps an uninhabited operation family and rejects all
effect nodes.

The effect Core validator independently checks:

- effect and operation identity, arguments, kinds, and substituted types;
- every node's value type and row equation;
- complete handler coverage and exact-instance discharge;
- clause pattern scope and type;
- one owning resume scope, input type, result type, and output row;
- structural exactly-once use and non-escape;
- handler nesting, provenance, dialect membership, and reachability; and
- an empty effect row at the linked entry boundary.

Construction APIs do not replace those checks. Every retained identity or
folding transform traverses the effect families, preserves or rebuilds their
authentication data, and returns to independent validation.

The concrete effect dialect chosen by this proposal keeps resume as a
clause-scoped Core operation, not an ordinary Core value or Rust closure. It
does not expose evaluator frames as Core data. A later accepted architectural
decision may change storage without changing these typed boundaries.

### Dynamic semantics and evaluator

The normative small-step configuration extends with an ordered active-handler
stack and explicit captured-continuation data. The latter contains only the
validated control segment, environment boundary, result contract, handler
boundary, and one live/consumed state required by the selected request. It is
distinct from the ordinary continuation stack even if the evaluator moves
owned frame data into it.

Operation evaluation first evaluates the operand. A request then finds the
nearest exact-instance handler, captures the intervening control, and enters
the selected clause with one live resume capability. Resume first evaluates
its argument, atomically marks the capability consumed, reinstalls the handler
and captured control, and eventually returns the handled result to the clause's
surrounding control. No transition clones a captured continuation.

The explicit evaluator implements those transitions with first-order Rust
data and its existing host-stack-independent control loop. It does not use a
Rust closure as the continuation representation or silently treat all current
frames as capturable.

A source program reaches evaluation only when the linked entry row is empty.
An unmatched request, absent capability, second consumption, or forged capture
boundary after successful validation is an internal malformed-Core or machine
invariant failure, not a new source-level runtime outcome. The kernel adds no
operation failure, exception, cancellation, or abort transition.

### Failure ownership and resources

Lexing owns reserved keywords. Parsing owns malformed declarations, rows,
requests, handlers, clauses, and resume syntax. Resolution owns duplicate or
unknown effects and operations, namespace conflicts, visibility, stable
identities, row-tail scope, and `resume` outside a clause.

Effect argument arity precedes positional kind checking. Kind checking owns an
invalid effect argument, row tail, or forbidden use of `EffectRow`. Row
formation owns duplicate written members and unsatisfiable lacks constraints.
Ordinary expression typing owns operation operands and function latent rows.
Handler checking owns target membership, clause coverage, clause patterns,
shared result and output rows, and resume usage. Module entry checking owns a
nonempty linked entry row. Summary, linked, Core, and machine validation own
forged retained facts only after source checking succeeds.

New syntax, identities, type and row nodes, constraints, summaries, Core nodes,
handler stack entries, and captured continuation cells charge the existing
ledger for their owning stage before retention. Row operations and validation
use iterative worklists and charge each retained member, pending pair, and
lacks relation. The implementation task must derive exact formulas for those
new carriers and retain exact-success, one-unit-short atomic failure, retry,
and deep stack-safe evidence where the carrier is proportional. This proposal
does not increase a production limit or introduce a separate speculative
resource system.

## Semantic delta

- Module-owned generic effect declarations introduce stable API and operation
  identities without selecting providers.
- Function codomains and expression judgments carry identity-bearing open or
  closed effect rows of kind `EffectRow`; absent source rows remain empty.
- Rows are unordered idempotent sets with exact-instance equality, open-tail
  lacks constraints, unification, union, weakening, and exact removal.
- Explicit requests add their exact effect instance.
- Ordered exhaustive lexical handlers discharge one exact instance, forward
  unknown effects, and may reintroduce effects from their clauses.
- Every operation clause has one non-value resume capability which must be
  consumed once on each normally completing path and cannot escape.
- Deep resumption reinstalls the selected handler around captured control and
  returns to the clause after the resumed computation completes.
- A separate validated effect Core dialect and explicit-machine transitions
  implement the kernel while the pure dialect retains no inhabited effect
  operation.
- A linked entry computation must have an empty row; validated execution has no
  unhandled-operation source outcome.

## Affected specification areas

- [Lexical tokens](../../spec/lexical-structure.md#tokens) reserves the five
  kernel keywords.
- [Syntax grammar](../../spec/syntax.md#grammar) adds declarations, rows,
  computation codomains, requests, handlers, clauses, and resume.
- [Imports and namespaces](../../spec/name-resolution.md#imports-and-namespaces),
  [Interface, implementation, and requirement identities](../../spec/name-resolution.md#interface-implementation-and-requirement-identities),
  [Type binder identity and scope](../../spec/name-resolution.md#type-binder-identity-and-scope),
  and [Local scope](../../spec/name-resolution.md#local-scope) gain effect,
  operation, row-tail, handler, and resume identity and scope rules.
- [Kinds, monotypes, and schemes](../../spec/static-semantics.md#kinds-monotypes-and-schemes),
  [Functions and application](../../spec/static-semantics.md#functions-and-application),
  [Blocks](../../spec/static-semantics.md#blocks),
  [Inference and rank-1 restrictions](../../spec/static-semantics.md#inference-and-rank-1-restrictions),
  [Globals and modules](../../spec/static-semantics.md#globals-and-modules), and
  [Failure ownership and constraint resources](../../spec/static-semantics.md#failure-ownership-and-constraint-resources)
  gain computation rows, row inference, kernel typing, entry closure, and
  failure precedence.
- [Surface erasure](../../spec/elaboration.md#surface-erasure),
  [Module linking and entry generation](../../spec/elaboration.md#module-linking-and-entry-generation),
  and [Validation boundary](../../spec/elaboration.md#validation-boundary)
  gain effect summaries, effect Core lowering, and independent validation.
- [Initial configuration](../../spec/dynamic-semantics.md#initial-configuration),
  [Application](../../spec/dynamic-semantics.md#application), and new effect
  sections define the handler stack, request, forwarding, capture, and resume
  transitions under AD-0004.
- [Ash tool contract](../tools/ash.md) describes effectful source failures and
  preserves the existing successful entry observation.

## Resulting specification truth

After the complete product checkpoint integrates into `main`, Ash programs may
declare typed effect APIs, expose latent open or closed requirements in
function types, request operations, and discharge exact effect instances with
ordered lexical handlers. The type system rejects a linked entry with an
outstanding requirement and rejects any operation clause that can complete
normally without consuming its non-escaping resume capability exactly once.

The normative small-step semantics defines deep ordered handling and one-shot
resumption. Independently validated effect Core and the explicit evaluator
implement the same transitions. After renaming any binder that uses a newly
reserved keyword, programs that use no effect syntax retain empty rows, the
closed pure Core dialect, and predecessor observations.

## Interactions

Effect type parameters reuse current fixed-kinded type binders and structural
type equality. A later integrated local nominal identity may instantiate an
effect parameter, but this proposal neither depends on nor defines local
identity.

Interfaces and effect declarations may share module identity, kind, summary,
and validation infrastructure. An interface requirement is still static
evidence, while an effect row is a computation requirement. Neither converts
to the other, and handlers do not search for implementations.

The next checked-discard checkpoint may add an alternative consuming use for
the resume capability. This proposal deliberately gives it one authenticated
scope and one-shot state to extend; it does not predefine capture classes or
discard safety.

Future resource scopes need exact effect-instance discharge and observable
continuation boundaries. They do not change this checkpoint's row order,
handler order, or resume-required behavior.

## Non-goals

This proposal does not add:

- checked discard, abortive handlers, exceptions, cancellation, or unwinding;
- escaping, suspended, stored, duplicable, replayable, or multi-shot
  continuations;
- first-class handlers, handler values, handler construction effects, return
  clauses, result-type-changing handlers, or partial operation coverage;
- resources, providers, local implementations, runtime interface lookup,
  hooks, cleanup, protocols, transactions, or foreign calls;
- dynamic loading, runtime effect registration, open operation namespaces, or
  runtime handler selection by API shape;
- row multiplicity, ordered rows, effect subtyping, effect masking, effect
  aliases, qualified row-union constraints, effect-row-indexed declarations,
  associated effect types, operation-local polymorphism, or higher-kinded row
  constructors;
- concurrency, async execution, suspension, generators, or scheduling; or
- a disposable prototype, second evaluator, general CPS conversion, or
  optimizer permission to reorder handlers.

## Required evidence

The product transition must retain:

- grammar, precedence, recovery, keyword migration, reservation, identity,
  import, re-export, visibility, and same-spelling distinct-identity cases for
  effect APIs and operations;
- kind, equality, substitution, unification, union, weakening, lacks,
  duplicate, generalization, instantiation, unrelated-open-tail ambiguity, and
  rendering cases for open and closed rows;
- pure, closed-effect, open-row relay, higher-order latent-row, branch union,
  and two-distinct-instances typing cases;
- exact operation operand and result typing, exhaustive handler coverage,
  unknown-effect forwarding, exact-instance discharge, same-instance
  reintroduction, and a rejected nonempty entry;
- nested different-effect and same-effect traces showing nearest-handler order,
  clause execution outside the selected handler, handler reinstatement during
  resume, and return to the clause afterward;
- one resume, one resume in every match arm, rejected zero and double use,
  rejected nested-function and nested-handler capture, and rejected resume
  outside its clause;
- normative one-step rules and representative multi-step derivations that
  agree with source and evaluator observations;
- complete effect Core construction, independent row and identity forgery
  rejection, transform-then-revalidate evidence, and rejection of effect nodes
  by the pure dialect;
- deep request, handler, forwarding, and resumption evaluation on a small host
  stack, with no Rust closure as the continuation carrier;
- exact applicable resource boundaries, atomic failure, retry, and iterative
  teardown for each new proportional carrier;
- predecessor source, CLI, specification-example, Core transform, evaluator,
  interface, module, and resource tests; and
- independent semantic, architecture, implementation/resource, documentation,
  and simplification review before transition cleanup or integration.

The task must implement the accepted rules directly. No experiment is part of
this evidence plan. If implementation instead exposes a semantic gap, work
returns to this proposal rather than resolving it in code.
