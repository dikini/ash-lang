# CP-0018: Synchronous Typed Hooks

- ID: `CP-0018`
- Status: accepted
- Related: [DN-0012](../design/DN-0012-coeffects-and-hooks.md),
  [DN-0026](../design/DN-0026-effect-ash-resource-first-milestones.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md), and
  [safe-resource evidence](../design/effect-ash/resource-scope-evidence.md), and
  [TASK-0028](../tasks/TASK-0028-implement-synchronous-hooks.md)

> This proposal is accepted but is not current Ash. The user approved the full
> contract, including transforming subscribers, registration order, handler
> placement, scoped removal and pre-cleanup exits. The user separately authorized
> implementation, tracked by TASK-0028; the feature is not implemented yet.

## Current behavior

`main` remains separate from the Effects Ash integration branch. This proposal
starts from locally integrated checkpoint `13a92b5`, not from an assumption that
the milestone is current on `main`.

The [branch specification](../../spec/README.md) admits exact effect instances,
ordered handlers, non-escaping one-shot resume or checked discard, and one
scope-owned mutable cell. It separately tracks stored resource dependencies
and required control completion. A selected handler clause runs outside its
own handler and the intervening captured frames; resume restores those frames.
Lexical type and row instantiation survives that movement.

Ordinary handlers can already compose transformations by forwarding a request,
transforming its result, then resuming. They do not introduce a registration
resource or a required deregistration boundary. There is no hook syntax,
registration handle, subscriber registry, implicit publication, or general
cleanup. The resource checkpoint supplies transferable lifetime and control
evidence, not an already implemented hook mechanism.

## Proposed behavior

### Typed names reuse effect APIs

A hook API is an ordinary effect declaration with exactly one operation named
`publish`, whose declared domain and result are the same value type. For example:

```ash
effect Adjust<T> {
    publish : T -> T
}
```

Equality must hold under the declaration's own generic parameters, before any
use-site instantiation. `Convert<A, B>` with `publish : A -> B` is not a hook
API, even at `Convert<Int, Int>`. Ordinary structural type equality applies;
equal newtype representations do not establish equal payload types.

Use the existing effect identity, operation identity, parameter kinds, import
and re-export rules. An exact hook is, for example, `Adjust<Int>`; another
declaration or another exact instantiation is a different hook. No new identity
namespace, effect-row parameter kind, builtin module, provider relation, or
first-class hook witness is introduced. In particular, effect declaration
parameters retain their current exclusion of kind `EffectRow`.

Publication is the existing expression `perform Adjust<Int>.publish value`.
Its operand is evaluated once and its result has the same payload type. The
request retains the ordinary exact hook requirement in its effect row. Loading
a module makes its API and functions available; it registers nothing.

### Empty-chain and registration scopes

Add two expression forms. Here `effect_instance`, `primary_expression` and
`block` have their existing grammar meanings. Both forms are primary expressions;
a non-primary transformer expression must be parenthesized.

```ebnf
hook_expression ::= "hook" effect_instance block ;
registration_expression ::=
  "register" effect_instance primary_expression block ;
```

`hook` and `register` become reserved keywords. `publish` remains an ordinary
operation identifier. Both targets must resolve to an exact instance of a hook
API as defined above. The forms introduce no user-visible term or type binder.

`hook H { body }` supplies the empty chain for `H`. It is an identity handler:
publication returns its payload unchanged if no intervening registration or
ordinary handler intercepts it. A nested `hook H` starts a separate chain and
cuts off registrations outside that root for exactly `H`. Other instances keep
their existing handlers. Leaving the inner root restores the surrounding chain.

`register H transformer { body }` first evaluates `transformer` exactly once in
the preceding context. It then acquires one scoped registration and executes
the body with that registration active. The transformer must be an ordinary
function from the instantiated payload type to itself; it may perform effects.
Normal body completion removes the registration once and returns the body's
result, which need not have the payload type. The registration cannot be stored,
returned, transferred, manually removed, or independently invoked by source.

Unused scopes are valid: `hook H { 42 }` does not require an actual publication.
Like a cell scope, each new form removes an explicitly present `H` from its
body row and leaves a row in which `H` is provably absent unchanged. Absence
means a closed row without `H`, or an open row without `H` whose tail already
has the corresponding lacks fact. An unconstrained open tail retains the
existing exact-removal ambiguity; this rule neither silently masks a possible
request nor invents a lacks constraint. It does not change ordinary `handle`
admission when its body lacks the target.

### Transformation and order

A registration forwards the incoming payload to the older chain, applies its
transformer to the returned payload, then resumes its own publication. The
following existing-Ash handler fragment describes the order, not the complete
lifetime lowering. `callback` denotes the already evaluated transformer, and
all introduced names are fresh:

```ash
handle body with H {
    publish input => {
        let previous = perform H.publish input
        let next = callback previous
        resume next
    }
}
```

An empty-chain root uses `publish input => resume input`. The registration's
completion owner surrounds its generated handler; it must not be erased by
this explanatory expansion.

For registrations A then B, publication computes B(A(payload)). Registration
order is the sole priority rule: older, outer registrations run first. There
are no numeric priorities, equal-priority tie rules, or runtime reordering.
Repeated registration of the same callback creates separate entries and invokes
it once per participating entry. The empty chain is the identity function.

This proposed program returns `8`; the new scope forms are not executable yet:

```ash
effect Adjust {
    publish : Int -> Int
}

increment : Int -> Int
increment value = value + 1

double : Int -> Int
double value = value * 2

main : Unit -> Int
main () = hook Adjust {
    register Adjust increment {
        register Adjust double {
            perform Adjust.publish 3
        }
    }
}
```

Observation is a transformer that performs its observation and returns its
input unchanged. A returned error constructor, if part of the payload type, is
an ordinary value passed to the next transformer. Hooks introduce no rejection
result, implicit short-circuit, rollback, or access to the publisher's resume
capability. A source handler may deliberately interpret an operation differently;
registration neither replaces nor weakens ordinary handler semantics.

### Effect rows and handler placement

The transformer expression's evaluation effects remain outward. Its function's
latent effects enter the registration's outward row, together with the body's
non-target effects and the forwarded exact requirement `H`. The registration
does not discharge `H`: an outer root or ordinary handler must do so. These
requirements are retained even if that body never publishes, following the
conservative checking of generated clauses. An unused effectful transformer
does not execute, but its possible effects remain in the checked contract.

The root removes exactly `H` when present, as specified above. It does not remove
subscriber logging, resource operations, or another hook instance. Use existing
least-row, weakening, open-tail and lacks constraints; there is no dynamic collection of
unknown subscriber effects or new row-union rule. Generic functions and imported
transformer factories retain ordinary instantiation and capture summaries.

Handlers surrounding a registration interpret its callback effects. Handlers
installed only inside its body at the publication site are captured while the
callback executes, so they do not intercept those effects. The callback uses
its saved lexical term/type environment, while requests use the active handler
context at the registration boundary. Creating the callback under a handler
does not store that handler in an ordinary closure.

This distinction is intentional. For example, if an outer `Log` handler returns
`1` and a handler around publication inside the registration returns `2`, logging
performed by the subscriber selects the outer handler. Users place publication
explicitly before or after work in an operation clause; no automatic before/after
hooks are inserted. Forwarding through an older exact source handler retains
that handler's ordinary result, capture and completion behavior.

### Registration changes during publication

Registration is scoped chain extension, not mutation of a global callback list.
The original publication retains its pending registrations and evaluated
callbacks in ordinary explicit control. Installing a registration during a
callback does not insert it into that pending sequence.

A nested publication sees the then-active enclosing chain. Because a callback
runs outside its own generated handler, that chain contains the older active
prefix, not that registration or younger registrations still held in captures.
A temporary registration inside the callback participates in publication inside
its own body, and disappears on normal exit. A nested root cuts off that prefix.

For A then B, a same-hook request inside B can invoke A again, but does not
re-enter B. A same-hook request inside A reaches the root unless A temporarily
installs another registration. These nested requests are separate publications;
they do not replay the already completed prefix of the original publication.
Explicit recursive source calls may still diverge. No recursion ban or scheduler
is introduced, and no copied whole-chain snapshot is required.

### Identity, dependencies and deregistration

Each registration scope has a compiler-owned lexical owner and each successful
execution acquires a distinct runtime registration activation. Neither is a
source-inspectable value. Repeated execution of one source site does not merge
its live registrations. The owner retains the active callback entry and its
dependencies; normal exit makes that entry unavailable. An ordinary external
copy of the callback remains an ordinary function, not a live registration.

Place the registration owner outside its generated handler. Selecting the
registration captures its handler and publisher-side frames, while its callback
still runs inside its own live owner. Forwarding may move younger owners and
their pending callbacks into captures. Resume restores them without reevaluating
the transformer, reacquiring registration, or duplicating a completion owner.

Reuse the existing owner-relative stored-dependency and control analyses, with
registration owners added to required completion. A callback may capture cells,
selected evidence, or identity-indexed operations whose owners surround its
registration. The same handles may be reused while those owners remain live.
Returned results and request operands must satisfy every crossed resource owner,
including through aggregates, imported factories and identity-free function types.

Forwarding first means the original payload must be safe for every older
recipient it reaches. A later transformer that would erase a dependency does
not make an earlier unsafe transfer legal. Even the empty identity root gains
no exemption from the current rejection of temporary outward lending.

Conversely, a transformer may add a stored dependency without changing the
payload type: it may return a function that captures a live cell. That result is
admitted while its owner surrounds the registration and restored recipient,
and rejected if it later escapes that owner. `Payload -> Payload` is not a proof
that input and output have equal dependency sets.

An ordinary closure containing a request to a static hook identity does not
capture the active registration chain. A later call uses the then-active chain.
Actual stored resource or identity dependencies remain subject to their existing
escape rules. This proposal adds neither a first-class chain nor an ownership
package that could retain a removed registration.

### Completion before general cleanup

| Path | Proposed behavior |
| --- | --- |
| Normal registration-body return | Deregister exactly once, then return the checked result. |
| Nested normal return | Deregister inner before outer; no destructor callback. |
| Callback return | Pass its transformed payload inward and continue once. |
| Outward request followed by resume | Retain captured registrations and resources; restore them once with their existing identities. |
| Subscriber-local checked discard | Admit only when the generated clause and every surrounding owner still complete. |
| Discard abandoning a registration, pending resume, or skipped completion outside its capture | Reject statically under the existing checked-discard contract. |
| Divergence | Remain divergent; no guarantee of eventual deregistration. |
| Internal allocation/work/capacity failure | Publish no partial new registration; dispose owned runtime memory safely, without a source cleanup transition or rollback of earlier callback effects. |

Subscribers receive no surrounding resume capability. Any handler they invoke
still obeys ordinary one-shot rules. Effects can capture and immediately resume
control as the current kernel permits; this is not an asynchronously suspended
or escaping subscriber. Source abort, exception, cancellation and general
subscriber-failure exits remain unavailable. A callback cannot bypass required
registration completion merely because its declared row is pure.

### Lowering, validation and resource accounting

Root and publication dynamics use existing exact handlers and requests. Retain
one explicit registration owner around the generated forwarding behavior, with
its evaluated callback, exact hook relation and source origin. Reuse the Effect
operation-family and explicit machine; do not add a second callback evaluator,
machine-global registry, or inhabited hook carrier to Pure Core. The concrete
sharing with cell-scope ownership is implementation work, not a general resource
declaration mechanism authorized by this proposal.

Retain the typed scope distinction needed for the new forms' absent-target row
rule. An unqualified existing Core handler still requires an explicitly present
target in its body's synthesized row; checking against a larger row does not
change that least row. The hook-scope lowering and independent validator must
therefore carry and verify their own scope contract rather than fabricate a
request, inflate a literal's row, or wrap the body in a function that would
change enclosing resume scope. No general weakening carrier or relaxation of
ordinary source-handler admission is required by this proposal.

Absence in an unspecialized row does not justify erasing a scope. For an API
`Mark<T>` with `publish : Int -> Int`, a body requesting `Mark<T>` inside
`hook Mark<U>` can reach that root when a later call instantiates `T` and `U`
equally. Registration has the same possible coincidence. Preserve saved lexical
instantiation and exact runtime selection, and account for that possibility in
dependency and control inference. Generic parameters are not fresh acquisition
brands, which retain their existing static separation.

Independent validation authenticates the hook API shape, exact instantiation,
owner, callback type/row, generated handler and required completion. It rejects
detached owners, altered forwarding order, changed callback/result relations,
or forged origin claims. Stored-dependency and control safety are reconstructed
from actual linked Core, including after identity and folding transforms; source
checks and imported summaries are not trusted as final permissions.

Acquisition prepares the callback entry and all fallible state before publishing
the active registration. Live-registration accounting includes owners retained
in captures, not just active handlers. Capture/resume moves ownership without
changing that count; normal deregistration releases capacity once. Stale or
duplicated internal activation facts reject before invocation or mutation.
No source-visible stale-registration outcome is introduced.

Use existing owning compiler and evaluator work ledgers. Charge every new scan,
retained relationship, frame and chain step before proportional work or storage.
Publication over N participating registrations invokes N callbacks and performs
the corresponding forwarding/resume steps, in addition to ordinary handler
search and callback work. Do not promise constant publication cost, impose an
uncharged priority sort, or copy the full chain per update. Exact implementation
formulas belong to the later task and its owning tests.

Deep publication, return, capture and internal-failure disposal use iterative
ownership and bounded host stack. Hook-free Pure programs acquire no hook
registry, registration frame or live-registration allocation. New analysis must
preserve ordinary private Pure-program locality and imported summary authority.

Malformed forms belong to lexing/parsing; unknown targets belong to resolution.
Kind, ordinary type/row and structural continuation failures retain precedence.
An otherwise well-formed non-hook API target reports `type.hook-api` at that
target. Callback mismatches use ordinary type errors with the registration and
payload contract identified. Escape retains `type.resource-escape`; unsafe
discard retains `effect.discard-unsafe` with its registration or pending-owner
label. Capacity exhaustion reports `runtime.resource-capacity`; forged checked
or Core relationships remain internal validation errors.

## Alternatives and downstream pressure

Plain user-written forwarding handlers already express ordering, but not the
required registration owner and deregistration obligation. The proposed forms
retain that missing boundary while sharing the ordinary operation semantics.
A centralized mutable registry would need additional effect-budget, lifetime,
mutation and dispatch rules. Calling every subscriber under publisher-side
handlers would also be different semantics, not equivalent handler sugar.

Transformation was selected over observation-only callbacks. Numeric priority,
arbitrary removal and publisher-context dispatch are excluded choices, not
unfinished parts of this contract. Libraries can choose registration nesting;
this does not claim to implement arbitrary runtime priority sorting.

Explicit code, environments, pending calls and completion owners leave a place
to retain state if a later proposal admits suspension. No current callback API
requires a host-synchronous call stack, but this proposal does not establish
future suspension or cleanup rules. Proof authority stays separate from hook
identity and registration. Existential packaging would require an explicit
transfer/elimination contract; no extra witness or ownership machinery is added
for it now. No experiment is required to adopt this proposal; any unresolved
semantic contradiction returns to proposal review before implementation.

## Semantic delta

Add `hook` and `register` expressions and scoped registration completion.
Qualify named hook APIs through existing endomorphic single-operation effects;
retain existing publication syntax, exact identities and handler placement.
Define first-registration-first transformation, nested-publication visibility,
explicit empty-chain roots and normal-exit deregistration. Permit provably
absent-target body rows for these scopes without changing ordinary handler
admission or synthesized least rows. Preserve cell lifetime, effect erasure
boundaries, one-shot completion and no-cleanup discard.

## Affected specification areas

- [Lexical structure](../../spec/lexical-structure.md) and
  [syntax](../../spec/syntax.md): two reserved words and expressions.
- [Name resolution](../../spec/name-resolution.md): exact target resolution and
  registration-owner scope; no new hook declaration or import activation.
- [Static semantics](../../spec/static-semantics.md): API shape, transformer
  types, rows, dependencies, completion, diagnostics and resource bounds.
- [Elaboration](../../spec/elaboration.md): handler lowering and authenticated
  registration ownership, independent validation and transformed Core.
- [Dynamic semantics](../../spec/dynamic-semantics.md): registration activation,
  forward/transform/resume order, nested roots and normal deregistration.
- [Specification overview](../../spec/README.md) and
  [tool guide](../tools/ash.md): resulting boundary and executable examples.

## Resulting specification truth

After the complete implementation is separately integrated into `main`, Ash
admits named typed synchronous transformation hooks with scoped registration,
visible subscriber effects and checked resource/control lifetimes. Empty roots
preserve payloads, participating registrations transform in outer-to-inner
order, and normal scope exit deregisters once. It still supplies no asynchronous
hook, general cleanup or foreign provider. This accepted proposal changes none
of those current specification facts by itself.

## Interactions

Preserve passive module availability, exact effect and nominal identity,
generic type/row instantiation, lexical evidence capture, handler interception,
stored dependency propagation and one-shot restoration. A source handler for
the same effect can intercept or terminate forwarding under ordinary rules;
hooks do not gain sealed cell-provider or future proof authority. Resource
callbacks depend on actual live owners, not hook-name matching or type erasure.

## Non-goals

No observation-only second API, arbitrary input/output type changes, numeric
priorities, first-class registration tokens, manual removal, transferred or
weak registrations, public chain snapshots, implicit module registration,
universal event bus, publisher-context dispatch, dynamic loading, scheduler,
parallel fan-out, async completion, escaping or multi-shot continuations,
abort/exception semantics, general cleanup, foreign provider, proof language,
existential package, general ownership syntax, main merge, push or milestone tag.

## Required evidence

These are required future observations, not tests already run for this proposal.

| Case | Required positive and negative observations |
| --- | --- |
| HOOK-01: API and syntax | Generic/facade hook API succeeds; distinct declarations/instances remain separate. Reject multiple operations, wrong operation name, unequal declared domain/result including `Convert<Int, Int>`, bad kinds and malformed scopes. Verify the two new keyword collisions explicitly. |
| HOOK-02: Identity and scope | Empty root returns its payload; unused scopes check with closed absent-target rows and open tails already known to lack the target, while unconstrained tails remain ambiguous. Independent Core and both transforms preserve these rows without fabricated requests or changed resume scope. A nested exact root excludes outer registrations and restores them on exit. For `Mark<T>.publish : Int -> Int`, generic `Mark<T>` and `Mark<U>` requests/scopes distinguish equal from unequal later instantiations, including resource/control safety. A request without an enclosing matching interpretation remains an outward effect. |
| HOOK-03: Ordered transformation | Outer increment then inner double maps 3 to 8, reversed nesting maps 3 to 7. Observe intermediate payloads, repeated registration and initializer-once timing. Exiting an inner registration removes only that entry; later publication observes the remaining chain. |
| HOOK-04: Effects and handler placement | Subscriber effects remain visible, including unused registration's conservative row and open-row helper/factory cases. Outer versus publisher-local `Log` handlers distinguish callback placement; omission of the required outer interpretation rejects a pure entry. Preserve ordinary exact source interception. |
| HOOK-05: Nested publication and scoped changes | A request inside B sees older A, not B or captured younger entries. A temporary registration affects only nested publication in its body; a nested root cuts off the older prefix. Original pending callbacks finish once, without replay or late insertion. |
| HOOK-06: Captured values and transformed dependencies | Repeatedly access a cell surrounding registration. Admit copied results and a newly resource-dependent function payload while its owner remains live; reject its later escape. Reject outward dependent input before any transformer can erase it. Cover tuples, projections, selected evidence, opaque/imported factories and metadata-only captures. |
| HOOK-07: Control and normal release | Observe nested deregistration order. An outward resource-free request captures and resumes pending registrations once without reacquisition. Reject abandonment, duplicate completion and skipped owners outside the immediate capture; admit subscriber-local discard that preserves all completion. Distinguish repeated activations of one source site. |
| HOOK-08: Independent authority | Source, summary, linked and Core negatives for wrong hook/instantiation/callback/owner/forwarding relationships. Both identity and folding transforms revalidate and execute ordering, resource and imported-factory controls; hidden dependency or forged completion permission never authorizes execution. |
| HOOK-09: Resources and failure | Exact/one-short compiler work and live-registration capacity, fresh retries, release/reuse, captured owners counting as live, preflight failure without partial acquisition, and stale/duplicated internal activation rejection. Measure chain traversal and callback work separately. Deep success and internal failure inside a subscriber dispose registrations, cells and pending control on a small stack without running cleanup callbacks. |
| HOOK-10: Migration and tools | Existing effect, capture/discard, resource, local-newtype, interface and ordinary Pure cases retain their contracts and limits. Hook-free Pure locality remains measured. The documented complete program has exact CLI output `8 : Int` and empty stderr; new rejection examples have exact phase-owned diagnostics. |

The user approved the complete contract after independent semantic and
documentation review, including order/priority, handler placement, nested chain
visibility, scoped-only removal and pre-cleanup exits. This acceptance is not
evidence that the future implementation passes the required cases.

TASK-0028 and its temporary plan name the test-first increments, owning work formulas and
review gates. Require independent semantic and Rust/resource reviews at no more
than high reasoning, medium documentation review, `cargo xtask verify`, Markdown
lint, link/authority and formal-notation checks, plus a simplification review.
Retain implementation evidence before removing transition artifacts and follow
the local milestone lifecycle. Keep commits unsigned until instructed otherwise.
The original nine-unit forecast remains a relative scope weight, not measured
expenditure or an implementation authorization.
