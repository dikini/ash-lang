# DN-0043: Shorter Surface Alternatives

- ID: `DN-0043`
- Status: exploring
- Related: [DN-0005](DN-0005-surface-function-definitions.md),
  [DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md),
  [DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md),
  [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md)

> This design note catalogues possible shorter surface forms. It defines no
> current Ash semantics, selects no final grammar, and authorizes no product
> implementation. The agreed discussion constraints below guide exploration;
> they are not accepted language changes. This discussion is independent of
> the common resource workstream and adds no requirements to other workstreams.

## Question

Which Ash features could offer shorter alternatives while retaining their full
descriptive forms? For each feature, compare omission of recoverable syntax,
word or symbol synonyms, alternative binding and scope forms, and ordinary
library abstractions where current types can express them.

The aim is a catalogue of the solution space. Effect-operation requests and
mutable variables as resources provide acceptable reference compromises;
they do not select one abbreviation policy for every feature.

## Context

Current authority remains the specification:

- [Effect typing](../../spec/static-semantics.md#effects) distinguishes an exact
  operation request from an ordinary call with a latent effect row. `perform`
  requests an operation; it does not identify a particular handler body.
- [Request execution](../../spec/dynamic-semantics.md#effect-handlers-and-completion)
  selects the nearest accepting boundary for the exact instantiated identity.
- [Resource typing](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
  separates scope-owned release from reusable non-owning access. Acquisition
  introduces a rigid identity, a handle, sealed evidence and an interpreter.
- [Native-buffer acquisition](https://github.com/dikini/ash-lang/blob/2766e8260e2590d9ebdca7abd699115b3cd02a8a/spec/static-semantics.md#scoped-native-buffers)
  returns `Outcome<body_result>`. Failure creates no body scope; nested outcomes
  remain nested.
- [Surface syntax](../../spec/syntax.md#grammar) currently requires `perform`,
  a written resource identity and a resource body block. It admits no mutable
  variable declaration or assignment form.
- [Core elaboration](../../spec/elaboration.md) retains exact request identities,
  resource relationships and completion operations for independent validation.

[DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md#surface-forms-derived-from-the-contracts)
explores mutable-variable syntax against shared mediated access, linear state
threading and uniqueness checking. It does not implement or select one of those
models. The same source convenience may need different checked elaborations.

## Constraints

These are agreed constraints for this exploration:

- Retain the current full descriptive syntax. Short forms are additional choices.
- Recover an action from resolved declarations and checked contracts, rather than
  treating a familiar spelling as authority.
- Inference may discover authority established by a checked contract. It cannot
  manufacture copying, sharing, borrowing, movement, disposal or completion
  authority.
- A well-resolved access with no permitted action is a type error. If several
  permitted actions remain possible after checking, unresolved ambiguity is also
  a type error. A diagnostic may suggest explicit disambiguation.
- Every accepted program determines one authorized action at each access.
  Runtime selection of the nearest exact handler remains defined execution,
  rather than unresolved static ambiguity.
- Explicit syntax selects an action and still requires that action to typecheck.
  Writing a marker cannot repair missing authority.
- Preserve evaluation order and multiplicity, exact identities, rows, captures,
  acquisition failure, completion order and result wrapping.
- Keep resource declaration and access separate. Recognizing access does not
  establish another acquisition or another owner.
- Keep syntax errors and name-resolution failures in their existing phases. The
  authority and ambiguity criteria do not reclassify every failure as typing.

## Candidate directions

All short-form examples in this note are illustrative, unimplemented spellings.
Code fences marked `text` do not claim executable Ash syntax. Current full forms
remain the reference for candidates that abbreviate implemented behavior.

### Effect-operation requests

For an effect declaring `read : Unit -> A`, the current full application is:

```ash
read_number : Unit -> Int ! {Read<Int>}
read_number () = perform Read<Int>.read ()
```

The declaration of `Read` would be supplied by the surrounding module or import.
Compare these shorter spellings:

```text
read_number () = Read<Int>.read ()
read_number () = !Read<Int>.read()
```

`Read` resolves to an effect, `Int` fixes its instance and `read` selects its
operation. Recognizing that direct application need not inspect a handler or
guess from the result's effect row. An ordinary effectful function remains an
ordinary call.

| Option | Information retained | Tradeoff |
| --- | --- | --- |
| Optional `perform` | The resolved operation target determines the request. | Least syntax; readers may need declaration context. |
| Symbol synonym such as prefix `!` | A visible direct-request marker and exact target. | Short cue; needs precedence rules and shares punctuation with effect rows. |
| Keyword and symbol, marker required | Every direct request has a cue. | Less omission; shorter marked form remains available. |
| Omission, keyword and symbol | Authors choose compactness or a visible assertion. | More equivalent spellings and style variation. |

The marker continues to assert an operation target. It must not silently apply
to an ordinary function. A candidate symbol consumes the same one operand as
`perform`; parentheses can group that operand. Curried applications, tuple
operands and function-valued operation results require explicit grouping tests.

Accepting a direct call does not decide whether bare `Read<Int>.read` is a
first-class value, or whether effect arguments may be omitted. Those are
separate choices. `perform` currently marks direct requests; ordinary calls
such as `read_number ()` can already reach handlers without that marker.

### Resource declaration

The current full cell form is:

```ash
resource cell<R> c = 41 {
    Cell.read c
}
```

This fragment assumes the builtin API imported as `Cell`. The initializer runs
before acquisition introduces `R` and `c`. The scope owns release; `c` supplies
access while the owner is live.

| Option | Short-form sketch | Information still required |
| --- | --- | --- |
| Omit the written identity | `resource cell c = 41 { body }` | Generate a fresh rigid identity; allow a written name when source needs it. |
| Omit the keyword in a recognizable header | `cell<R> c = 41 { body }` | The header must uniquely denote an acquisition, including its provider. |
| Use a mutable-binding declaration | `var x = 41` or `let mut x = 41` | Specify the mutable resource, access contract and owner scope. |
| Scope a sequential declaration over the block remainder | A resource declaration followed by ordinary local declarations. | Define nesting, completion order and the result of the whole remainder. |
| Offer a short word or symbol marker | A marked acquisition header with a body. | Preserve acquisition recognition and ownership; no symbol is selected here. |
| Use a scoped library combinator | A provider invokes a body under acquired authority. | Express fresh identity, non-escape and completion in its checked contract. |

The mutable-variable pressure case is:

```text
{
    var x = 41
    x := x + 1
    x
}
```

An acceptable candidate keeps the declaration's mutability cue, can infer its
payload type and generate an unnamed acquisition identity, and specifies a
lexical owner scope. `var` and `let mut` remain alternative spellings. Mutability
is not retroactively inferred from a later assignment to an ordinary `let`.

Replacing a resource's additional body block with the enclosing block remainder
can remove nesting. It needs a fixed scope rule; inferred last use alone does
not determine completion. An inner block can express an earlier closing point.
Fallible providers must retain declared failure behavior and result wrapping.
Native buffers prevent treating every acquisition as a successful ordinary
binding. No convenience spelling silently flattens their outcomes.

Ordinary handle types cannot alone distinguish acquiring ownership from storing
an existing alias. The current fixed provider designators are contextual syntax,
not general resource declarations. A future library-defined provider requires
its own checked acquisition contract. A scoped combinator also needs a way to
relate its body to a fresh identity; current rank-1 arrows do not automatically
supply that abstraction.

### Resource access and mutable payloads

For a mutable binding, bare `x` in a value position may stand for a payload read,
and `x := value` may stand for replacement. The declaration and operation
contracts must determine those actions. They do not require a repeated resource
keyword, provider name or identity annotation.

| Option | Benefit | Constraint |
| --- | --- | --- |
| Explicit operation calls through access values | Reads, replacement and sharing remain visible. | Repeated operation syntax can dominate ordinary arithmetic. |
| Bare reads and explicit assignment | Compact mutable-variable use. | Reads and replacement must be authorized and uniquely determined. |
| Symbol or word synonyms for individual actions | Short explicit copy, take, borrow or access forms. | Each synonym retains the operation's checked contract. |
| Infer a local action from its full checked context | Can omit otherwise redundant markers. | Missing authority and remaining ambiguity are type errors. |

For a copied integer, `let y = x` saves a snapshot. Sharing the resource uses a
distinct access expression; `access x` is an illustrative spelling. Bare `x`
should not switch between reading contents and sharing storage merely because
a parameter annotation changes. A closure reading `x` retains resource access;
a closure retaining an earlier copied integer retains only that snapshot.
Escape checks must preserve the difference.

Restricted payloads are a useful design constraint. A read cannot fabricate copy
authority; replacement cannot silently discard old contents without authority.
Take, borrow, copy and replace stay distinct where their contracts differ.
Missing authority remains a type error even with explicit syntax. Unresolved
choice between permitted actions is also a type error, with possible advice to
write an explicit action. No accepted program retains that ambiguity.

Repeated source operations can elaborate to shared mediated access, linear
successors or checked unique permissions. Convenient syntax does not choose
one model or prove its invariants. Each read occurs where written; a shorthand
cannot silently cache `x + x` as one read or duplicate an assignment operand.

### Catalogue of other features

The following review extends the solution space. These candidates have not
received the discussion agreement recorded for requests and mutable access.
Each retains its full form and needs a separate semantic comparison before a
proposal. The table identifies families of alternatives rather than a priority
order or final set of spellings.

| Feature | Options to compare | Boundary to preserve |
| --- | --- | --- |
| Handler installation | Reordered header; sequential scope; short marker. | Exact target, exhaustive clauses and interpretation extent. |
| Handler completion | Symbol synonyms; marked resuming clauses. | One authorized resume or discard on each completing path. |
| Cleanup | Sequential `cleanup`; short word; delayed-code block. | Action evaluation, captures, effects and one invocation owner. |
| Hook registration | Sequential `register`; short word or symbol. | Exact chain, callback context, ordering and removal. |
| Hook roots | Sequential `hook`; short marker; checked target omission. | Exact chain boundary, including nested roots. |
| Anonymous functions | Arrow forms; expression bodies; operator sections. | Function creation, parameter grouping and capture behavior. |
| Sequencing | Intermediate expression lines; discard-binding synonym. | Evaluation once in order, with ordinary type checking. |
| Boolean branching | `if` expression; conditional symbol form. | One scrutinee, exhaustive branches and compatible results. |
| Exact evidence | Single-method body; compact supplied equations. | Complete interface application and evidence authority. |
| Small declarations | Single-member effect/interface/implementation forms. | Declaration kind, identities, parameters and complete membership. |
| Type and row notation | Single-effect rows; explicit inference holes. | Exact identities, solved arguments and public contracts. |
| Nominal wrappers | Short `newtype` header; explicit unwrap shorthand. | Nominal distinction and constructor visibility. |
| Imports | Combined spelling of explicit name and evidence selection. | Independent visibility and implementation channels. |

#### Handler installation and completion

Current [handler syntax](../../spec/syntax.md#grammar) is
`handle body with E { clauses }`. A header-first alternative could place the
exact target and clauses before the body. A sequential `handle E { clauses }`
could scope over the enclosing block remainder. A word or symbol marker could
also abbreviate the existing structure. These choices shorten different costs:
repetition, distant delimiters and nested blocks. None infers a handler merely
because a row contains its effect.

For completion, compare a short synonym for `resume` or `discard` with a
distinct clause marker that expands to an explicit resume. For example:

```text
read ignored =>> 42
```

This illustrative marked clause would expand to `read ignored => resume 42`.
The marker distinguishes it from the current general clause body. It must
retain [continuation checking](../../spec/static-semantics.md#effects), including
argument evaluation, non-escape, branch agreement and exactly-once consumption.
Resuming and abandoning remain distinct actions; no default discard is inferred.

Silently interpreting an ordinary clause result as the resumed value would
confuse the operation result with the complete handler result. Those types may
even be equal. A separately marked clause can express the choice without
allowing unresolved action ambiguity. Multi-step clauses retain the full form.

#### Cleanup actions

Current [cleanup](../../spec/static-semantics.md#scoped-cleanup-actions) writes
`cleanup action { body }`. Compare:

- A sequential `cleanup action` covering the block remainder.
- A shorter word or symbol synonym for the same retained callable and scope.
- A delayed-code form such as `defer { expression }`, which explicitly constructs
  the required `Unit -> Unit` action.
- A library helper where its callback contract can express the same obligations.

The first two can retain current eager evaluation of the action expression and
later invocation of its resulting function. Delaying an expression is a
different abbreviation: its wrapper must define what is captured at registration
and what is evaluated at completion. Capturing a copied value and reading a
mutable resource later are observably different. Every form preserves structural
completion order, cleanup effects, surviving interpreter requirements and the
barrier against capturing an enclosing resume capability.

The word `defer` would not make an arbitrary expression safe to discard or
authorize omission of an owner. The body, action and pending close operation
retain their own completion checks.

#### Hook registration and roots

Current [hook forms](../../spec/static-semantics.md#synchronous-typed-hooks) are
`register H transformer { body }` and `hook H { body }`. Compare sequential
declarations covering the block remainder, short word or symbol synonyms, and
target-argument omission when the checked context determines one exact instance.

The transformer's type `P -> P` cannot alone identify `H`: several hook APIs can
share the same payload type. Unresolved target choice must fail checking rather
than select a nearby name. A registration still evaluates its transformer once
before entering the scope, preserves outer-before-inner callback order, and
removes its owner once. Its callback uses registration-site interpretation.

A root is an explicit chain boundary. A nested root for the same exact instance
cuts off outer registrations, so eliding a root merely because another root is
active would change behavior. Inferring a target and implicitly creating a root
are different options; publication does not by itself establish a root scope.

Sequential cleanup, registration, root and resource forms could share a rule
that wraps the following lexical remainder. That common presentation does not
erase their different typing, completion and result contracts. In particular,
hook scopes must not be converted into body functions that change resume scope.

#### Anonymous functions

Current [functions](../../spec/static-semantics.md#functions-and-application)
write `fn(patterns) { body }`. Compare arrow synonyms, expression-body forms and
operator sections. For example:

```text
value => value + 1
\value -> value + 1
```

Both sketches could denote the same function as `fn(value) { value + 1 }`.
Tuple-domain parameter lists must remain distinct from curried functions.
Expected typing, pattern coverage and closure dependencies remain checked.

The current local-generalization rule recognizes syntactic anonymous-function
initializers. A synonym must count as the same function form at that boundary;
otherwise abbreviation could change polymorphism. Ordinary application
initializers stay monomorphic. Operator sections additionally need an explicit
account of which operands are evaluated or captured at function creation and
which are evaluated on each call.

#### Sequencing and Boolean branching

Current [blocks](../../spec/static-semantics.md#blocks) sequence local declarations
and finish with one result expression. An intermediate expression line could
abbreviate `let _ = expression`; a short discard-binding marker is another
option. The final line remains the block result. Evaluation occurs once in
source order, and an unused expression still needs a complete checked type.
This is ordinary sequencing, not a new selectable bind or computation wrapper.

Ignoring a result does not establish payload disposal authority. If a later
resource model restricts weakening, the abbreviated discard must fail wherever
its full form would fail. Implicit asynchronous work or cleanup is outside this
option.

An `if condition then left else right` expression or a conditional symbol form
could abbreviate a complete two-arm Boolean
[match](../../spec/static-semantics.md#patterns-matches-and-coverage). It evaluates
the condition once and preserves result typing, branch rows and continuation or
ownership checks. A library function with eager ordinary arguments cannot by
itself abbreviate selective branch evaluation. General pattern matches retain
their full form; omitting an arm is not part of this comparison.

#### Exact evidence and small declarations

A single-method [local evidence declaration](../../spec/static-semantics.md#scoped-exact-evidence)
could offer a compact method body instead of a braced equation set. A shorter
method-head spelling is another option when the exact interface declaration
determines the sole method. Multi-method interfaces could allow compact complete
equations without omitting membership checks.

The complete interface application, active local nominal key and contextual
method parameters remain required facts. Short syntax cannot infer an unrelated
implementation, create missing evidence, or expose a polymorphic method scheme
as an ordinary first-class value. A method body still sees only the preceding
evidence scope and cannot gain implicit self or sibling evidence.

Single-operation effect declarations, single-method interfaces and single-method
implementations could also offer one-line forms without body braces. Retain the
declaration's explicit category, parameter and kind contracts, stable member
identity, visibility and complete method set. An equal signature does not turn
an interface method into an effect operation. This option saves delimiters;
inferring public signatures from bodies is a separate semantic change.

#### Type arguments, rows and inference holes

For a closed row containing one exact effect, `! E<A>` could abbreviate
`! {E<A>}`. An open tail needs a distinct spelling so that an effect instance
cannot be confused with a row variable. Empty-row omission and omitted global
binder lists already have current meanings; preserve those meanings.

Other candidates are explicitly marked inference holes for type arguments or
kinds, and omitted effect arguments at requests or handlers where checking
determines one complete exact instance. A result type can constrain a `Read<A>`
operation's argument; phantom parameters or several matching instances can leave
the request ambiguous. Such ambiguity is a type error, never a default to the
nearest installed handler.

[Current inference](../../spec/static-semantics.md#inference-and-rank-1-restrictions)
already rejects unsolved variables before retaining checked facts. Extending
inference sites needs new evidence. In particular, an omitted declaration kind
currently means `Type`; it does not request kind inference. An explicitly marked
hole could offer an additional mode without changing that existing default.
Exact evidence headers currently require complete inference-free arguments;
abbreviating them needs its own proposal rather than borrowing operation rules.

#### Nominal wrappers and imports

For [newtypes](../../spec/name-resolution.md#type-and-constructor-scope), a short
header such as `newtype UserId = Int` could retain the nominal declaration and
generate its same-spelled one-field constructor. An explicit `unwrap value`
could abbreviate a sole-constructor match where the constructor is accessible.
Construction is already compact through `UserId(value)`.

Neither candidate creates implicit representational coercion, interface evidence
or resource authority. Unwrapping an opaque imported newtype remains rejected.
Choosing `newtype` automatically for a one-constructor ordinary `type` would
change its representation contract and is outside a spelling abbreviation.

Current [imports](../../spec/name-resolution.md#imports-and-namespaces) already
provide targeted names and local renames. A combined item could shorten explicit
selection of an interface name and its implementation channel, but its marker
must still request both channels. Ordinary method or interface imports must not
silently select implementations. Wildcard imports and inferred evidence imports
would change visibility and selection policy; they need separate evaluation.

### Cross-feature comparison

The catalogue exposes several independent dimensions:

- Word or symbol synonyms change the visible spelling of an explicit action.
- Unique reconstruction removes syntax while keeping its checked information.
- Generated names omit identities that source does not need to mention.
- Sequential scope forms replace additional braces with a fixed lexical extent.
- Contextual short bodies retain an explicit feature marker while eliding
  repeated parameters, method names or delimiters.
- Library abstractions reuse ordinary checked functions where those contracts
  express the required scope, evaluation and authority.

These dimensions can combine. A feature may retain its full form, offer a
symbol synonym, and permit some argument omission while still requiring an
ownership marker. No candidate is selected merely because another feature
supports the same dimension. Compare useful reductions with punctuation reuse,
reader context, formatting and diagnostic costs.

## Evidence and experiments

The discussion establishes acceptable exploration constraints, not tested
short-form implementations. Current request, resource and ownership evidence
transfers only to the checked forms it covers. New syntax needs evidence that
its elaboration reaches those forms without changing their contracts.

Compare full and short forms through parsing, resolution, typing, independent
Core validation, transforms and execution. Count tokens and nesting alongside
readability, diagnostics, checking cost and retained Core structure.

Required comparison cases include:

- Exact requests, ordinary effectful calls, renamed imports, nested handler
  selection, operand grouping and function-valued operation results.
- Two acquisitions, generated identities, same-site reentrant execution,
  initializer order and fallible acquisition without body execution.
- Mutable snapshots, aliases, copied captures, access captures and rejected
  escape through closures, aggregates or operation payloads.
- Missing copying or disposal authority, ambiguous permitted actions, explicit
  disambiguation that succeeds, and explicit markers that still fail typing.
- Branches and repeated updates with the selected ownership model, followed by
  exactly the completion required on normal or admitted abandoned paths.
- Handler-clause result versus resume-input types, explicit abandonment, nested
  continuation barriers and short-form clauses that still fail completion checks.
- Cleanup initializer versus delayed expression evaluation, registration-site
  callback context, nested hook roots and closing order under sequential scopes.
- Lambda generalization, tuple versus curried parameters, single evaluation of
  discarded expressions and selective evaluation of conditional branches.
- Complete evidence membership, opaque constructor access, phantom arguments,
  row tails and unchanged explicit implementation-import selection.

No prototype is authorized by this catalogue. If one later becomes necessary,
name its feature, exact semantic question, full-form comparison and positive
and negative cases first. Discard its parser and runtime scaffolding after the
comparison; retain only reusable evidence unless a proposal authorizes product
implementation.

## Open questions

- Which candidates shorten common programs enough to justify another spelling?
- Which markers help readers recognize direct requests or ownership boundaries?
- When does source need a name for a generated acquisition identity?
- Which mutable access model and payload contracts should a later proposal use?
- How should shorter scopes expose acquisition and completion failure results?
- Can library contracts express a candidate without a new surface construct?
- What precedence, formatting and diagnostic rules keep each short form clear?
- Which scope forms share a presentation rule while retaining distinct contracts?
- Which declaration or inference abbreviations require more than a spelling
  change, and how should that extra semantic scope be recorded?
