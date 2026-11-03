# CP-0032: Row-Indexed Handler Contexts

- ID: `CP-0032`
- Status: accepted
- Related: [DN-0059](../design/DN-0059-compositional-contracts-and-evidence.md),
  [DN-0060](../design/DN-0060-typed-data-and-control-roadmap.md),
  [DN-0061](../design/DN-0061-effects-and-resources-first-slice.md).

> Accepted together with the
> [effects elaboration proposal](../design/effects-resources/effect-interface-elaboration-proposal.md)
> as one package that may authorize implementation tasks. The change is not yet
> implemented and does not describe current Ash. Its examples use current effect
> declarations; parameterless examples must be migrated when the companion
> effects declaration change is implemented.

## Current behavior

An effectful function declares its effect requirements in its effect row. A
function may quantify over an open row and pass an effectful function through
that boundary. At execution, a request selects the nearest applicable handler
in the active control. A caller need not install that handler locally: it may
propagate the requirement in its own row.

Current Ash permits an `EffectRow` variable as a row tail, but not as an
ordinary nominal type or interface argument. It therefore cannot express a
handler context as a value type indexed by an effect row. See the current
[kind](../../spec/static-semantics.md#kinds-monotypes-and-schemes),
[row](../../spec/static-semantics.md#computation-types-and-effect-rows) and
[effect](../../spec/static-semantics.md#effects) rules.

Interface checking already selects implementation evidence and elaboration
passes the corresponding method evidence across checked boundaries. It does
not provide the row-indexed handler context proposed here. See
[interface evidence lowering](../../spec/elaboration.md#interface-evidence-lowering).

## Proposed behavior

Introduce a typed handler context indexed by an effect row. In this proposal,
`Context<R>` is conceptual notation for that type, not proposed surface syntax.
The context supplies the applicable handler values and their operation
contracts for the effects required by `R`. It also accounts for existing
default and builtin provisions; a private allocation requirement does not
become a user-installed source handler.

The context is analogous to interface dictionary evidence: a checked boundary
states what is required, and the caller supplies the corresponding evidence.
A handler value is distinct from implementation evidence. Several handler
values can share one implementation while supplying different captured values.
This analogy does not assume that current Ash has first-class dictionaries.

Use one mechanism for a known collection of effects and an open row. A
function generic over `R` can receive and forward `Context<R>` without
enumerating `R` or inspecting the called function's body. Ordinary effectful
calls retain their current source syntax. The proposed effects elaboration
supplies an invocation-time context to a fixed-result function and composes its
returned computation with the caller's remaining work through `bind`; see the
[effects elaboration proposal](../design/effects-resources/effect-interface-elaboration-proposal.md#elaboration).

### Row parameters

Permit effect rows as kind-checked arguments to value-type constructors and
interface contracts where required for contexts and handler methods. Support
the corresponding row binders in implementations and methods where their
contracts require them. Substitution must preserve exact effect identities,
row equality and existing lacks constraints. An effect row remains a type-level
argument; this does not turn a row into an ordinary runtime value.

Extending the permitted argument kinds alone does not define a context. The
type system and typed Core must also express its entry contracts and the
context operations below. This proposal does not prescribe new surface syntax
or require contexts to be constructed explicitly by Ash programmers.

### Context shape

Represent `Context<R>` as a compiler-generated, typed collection of handler
entries indexed by `R`. The index states the effect requirements; it is not a
runtime row value. An entry supplies the applicable handler value and its
implementation evidence for one exact effect instance. It also carries that
installation's boundary result type, output row and operation contracts. Two
entries can have different boundary types and rows.

For example, a view of `Context<{Ask, Log | R}>` exposes an `Ask` entry, a
`Log` entry and an opaque `Context<R>` tail. The existing row formation rule
establishes that those exact `Ask` and `Log` instances are absent from `R`.
A function that knows only `R` can pass its tail on without enumerating it.
The example omits any implicit allocation requirement for clarity.

The view is not a layout determined by written row order. Elaboration supplies
the typed view required by each use, reusing established row and interface
evidence. When a slot's layout is known, generated Core can access it directly.
The proposal does not require runtime effect-name lookup, a separate runtime
allocation for every view, or a user-written context declaration. Typed Core
must support the construction, projection and adaptation of these views;
permitting a row argument in a nominal type alone is insufficient.

### Context views and composition

A context view relates a checked row requirement to the corresponding handler
values and implementation evidence. It supports the following operations:

1. **Select and forward.** Given a context for an explicitly known effect and
   an open tail, select the handler for that exact effect instance and forward
   the tail as a context for the tail row. A generic function may forward an
   entirely abstract context unchanged. Selection must respect the operation's
   checked handler contract.
2. **Supply a call.** A call supplies the view required by the callee's checked
   row, including when the caller has additional requirements. A higher-order
   function passes its invocation-time context to an effectful function
   argument. Checking the call uses the argument's established type and
   evidence, not its body.
3. **Install a handler.** The handler body receives a view in which its new
   handler is selected for that exact instance. The surrounding view remains
   available outside the boundary. Nested installations of the same effect
   select the inner value within its scope, even when the values share an
   implementation.
4. **Resume a captured computation.** The continuation retains the context
   applicable to its captured computation. The handler clause's own context
   follows the separately proposed installation-time rule in the effects
   proposal. An ordinary function value does not capture a handler merely
   because it was defined within its scope.

An explicit member of an open row is already required to be absent from its
tail. The view for that member may therefore expose a known prefix and retain
the rest as an opaque tail. Rows are unordered: equal rows with different
written order must produce compatible views. A caller and callee may use
different layouts only when their typed view or projection establishes the
correspondence. A known slot can be accessed directly; an abstract tail must
not be assigned a guessed numeric offset. The representation may share existing
values and evidence rather than copy a whole context.

### Deriving the context views

Write `Entry(E)` for the checked association between an exact effect instance
and one installed handler entry. This is notation for the entry contract, not
a new source type. The following operations define the proposed typed views:

- **Formation:** if `rho` has kind `EffectRow`, `Context<rho>` has kind `Type`.
- **Known entry:** a view of `Context<{E | rho}>` supplies an `Entry(E)` and a
  `Context<rho>`. Forming that row already requires `E` to be absent from
  `rho`. The entry retains its own boundary result, output row and operation
  evidence.
- **Call:** given established evidence that the callee's row is included in
  the caller's row, elaborate a view of the caller's context for the callee.
  Forward an abstract common tail without inspecting it. Equal rows produce
  compatible views regardless of their written order.
- **Installation:** for a body requiring `{E} union rho`, take the checked
  view of the installation context for `rho` and form the body view with the
  new `Entry(E)`. After instantiation, every body-view occurrence equal to the
  new exact `E` selects the new entry. Retain the installation context for the
  handler clause and for code outside the handler. If it also contains an
  outer `E` entry, that entry remains in the retained context; it is not a
  second member of the body row.
- **Instantiation:** substitute row and effect arguments in the view while
  preserving kinds, exact identities and lacks facts. If two parameterized
  instances become equal, both uses select the nearest applicable installation
  of that exact instance. Boundary ordering is preserved; a previously chosen
  symbolic slot must not select an outer handler after instantiation makes an
  inner handler applicable. The instantiation supplies checked exact-instance
  equality or inequality evidence to the view update, or specializes the view
  using the same established substitution. When a caller's arguments are
  themselves abstract, it forwards the decision as evidence or defers it to a
  later instantiation; it must not choose equality or inequality prematurely.
  Fully erased arguments without equivalent evidence cannot decide this case.

The call and installation rules use the already checked row and handler
contracts. A view or its checked projection may share entries with the source
context. Neither operation rechecks their implementations. Existing builtin and
default providers use their established contracts rather than requiring a
fabricated source handler. `{E} union rho` is the current row union: known
parameterized instances that are distinct before substitution may coalesce
afterwards. The lacks requirement applies to an actual open tail, not to an
assumed inequality between all symbolic known instances.

### Elaborating selection after instantiation

For an installation of `E<B>`, elaborate its body context as an overlay of the
new `Entry(E<B>)` on the enclosing context. The overlay carries the installed
entry's lexical instantiation and a checked view of the enclosing context.
Its result is a context for the admitted union of the body requirements and
`E<B>`; it does not assume arbitrary open-row unions are valid.

For a request for `E<A>`, the overlay compares the exact instantiated effect
identity and arguments of the request and installation, each under its own
lexical instantiation:

1. If they are equal, select the new entry. The equality witness transports
   its operation and boundary contract to the requested exact instance.
2. If they differ, combine that inequality with membership in the overlay to
   establish membership in the enclosing context, and select from that
   context. If the membership cannot be established, the composition is not
   accepted.

The installed instance itself selects the new entry directly. A generic
function receives its context, row membership evidence and type instantiation;
it forwards them across an opaque call without inspecting the callee. If a
comparison remains abstract, the overlay retains both keys and resolves it
after instantiation; specialization may resolve it earlier. The checked Core
comparison must cover the same exact identities and nested type and row
arguments as [current effect execution](../../spec/dynamic-semantics.md#type-instantiation-and-erasure).
It must not guess a slot from a symbolic type or use an unchecked cast. A
runtime representation may fuse an overlay or use a known slot when it
preserves these rules.

The following current Ash program tests the instantiation rule. The same
generic `get` returns `20` when `A` and `B` are both `Unit`, and `11` when
`A` is `Unit` and `B` is `Bool`:

```ash
effect Ask<T> {
    ask : T -> Int
}

get<A, B> : (A, B) -> Int ! {Ask<A>}
get (a, b) = handle ({
    let x = perform Ask<A>.ask a
    let y = perform Ask<B>.ask b
    x + y
}) with Ask<B> {
    ask ignored => resume 10
}

main : Unit -> (Int, Int)
main () = {
    let same = handle (get ((), ())) with Ask<Unit> {
        ask ignored => resume 1
    }
    let distinct = handle (get ((), true)) with Ask<Unit> {
        ask ignored => resume 1
    }
    (same, distinct)
}
```

When the instances are equal, the inner handler supplies both answers. When
they differ, the outer handler supplies the first and the inner supplies the
second. The program evaluates to `(20, 11) : (Int, Int)`.

### Current Ash evidence for an open row

Current Ash can forward an ordinary context value and an open effect row
through the same generic function. This complete program evaluates to
`31 : Int`:

```ash
effect Ask {
    ask : Int -> Int
}

effect Log {
    record : Int -> Unit
}

newtype AskContext = AskContext(Unit)
newtype LogContext = LogContext(Unit)

interface AskOp<C> {
    request : (C, Int) -> Int ! {Ask}
}

interface LogOp<C> {
    write : (C, Int) -> Unit ! {Log}
}

impl AskOp<AskContext> {
    request (context, value) = perform Ask.ask value
}

impl LogOp<LogContext> {
    write (context, value) = perform Log.record value
}

forward<C, R : EffectRow> : (C, C -> Int ! {| R}) -> Int ! {| R}
forward (context, action) = action(context)

question : AskContext -> Int ! {Ask}
question context = request(context, 10)

notify : LogContext -> Int ! {Log}
notify context = {
    let _ = write(context, 7)
    20
}

main : Unit -> Int
main () = {
    let first = handle (forward(AskContext(()), question)) with Ask {
        ask value => resume (value + 1)
    }
    let second = handle (forward(LogContext(()), notify)) with Log {
        record value => resume ()
    }
    first + second
}
```

The same `forward` passes either `C` to its action and propagates that action's
row `R`. The existing compiler does not establish a relationship between `C`
and `R`; it rejects a nominal `Context<R>` with an `EffectRow` argument as
`kind.expected-type`. The interface methods above still invoke current effect
requests. Thus this is evidence for forwarding, not an implementation of the
proposed row-indexed context or the effects-to-interfaces conversion.

### Deriving a handler boundary contract

Consider a handler installed for an exact effect instance `E`. Its body has
result type `A`; after removing `E`, its other effect requirements are `rho`.
Let `epsilon` be the handler's output row. For every operation `op_i` of `E`,
substitute the instance arguments into its declared type, giving
`op_i : P_i -> Q_i`.

The current [handler and resume rules](../../spec/static-semantics.md#effects)
give these obligations:

- The handled body's result, normal handler result and every clause result are
  `A`. There is no separate return clause.
- The residual body requirements `rho` and each clause's requirements fit in
  `epsilon`. A direct request by a clause may introduce `E` again.
- A request of `op_i` supplies a `P_i`. Resumption supplies a `Q_i` to the
  captured computation and returns `A` with output row `epsilon` to the
  clause.

Consequently, the generated handler invocation supplies `P_i`, the ordinary
function `k : Q_i -> A ! epsilon`, and scoped evidence for the same request's
owner; it returns `A ! epsilon`. For a discard site, the request also supplies
the close row `delta` and its checked close evidence. All operations at this
installation share its `A` and `epsilon`; each request supplies its own `k`
and owner.
Existing one-shot and nonescape discipline is intended, but ordinary function
typing cannot yet fully check one-shot use. This is an accepted known issue until general usage properties
are available; it does not authorize escape or remove cleanup requirements.
The boundary chooses `A` and `epsilon`: an implementation for one boundary
may inspect its specific `A` after calling `k`. It need not implement the
operation for every possible answer type.

An ordinary method with a discard site is checked once and quantifies over
each request's cleanup row `delta`. Its per-request evidence states that close
is admitted and that its residual row after clause-local handling fits
`epsilon` at each discard site.
The adapter passes that row and the established evidence with the owner.
The [discard context and evidence rules](../design/effects-resources/effect-interface-elaboration-proposal.md#discard-context-and-evidence)
specify how the site supplies the context and how the evidence is composed.
Distinct requests can have different cleanup rows; their unhandled rows need
not fit `epsilon` before local handling.
The same generated operation interface uses the owner for
[private Store retain](../design/effects-resources/effect-interface-elaboration-proposal.md#private-store-retain).

### Different boundaries in one call

This current Ash program has an outer `Ask` handler with result `Int` and an
inner `Log` handler with result `Bool`. The request for `Ask` crosses the
`Log` boundary through the separately declared function `get`. It evaluates
to `120 : Int`:

```ash
effect Ask {
    ask : Int -> Int
}

effect Log {
    record : Int -> Unit
}

get : Int -> Int ! {Ask, Log}
get value = {
    let answer = perform Ask.ask value
    let _ = perform Log.record answer
    answer + 1
}

main : Unit -> Int
main () = handle ({
    let flag = handle ({
        let answer = get 0
        answer == 2
    }) with Log {
        record value => {
            let result = resume ()
            match result {
                true => false
                false => true
            }
        }
    }
    match flag {
        true => 10
        false => 20
    }
}) with Ask {
    ask value => {
        let result = resume (value + 1)
        result + 100
    }
}
```

The `Ask` clause resumes with `1`. The resumed `get` performs `Log`, then
returns `2`. The inner body returns `true`; the `Log` clause turns it into
`false`. The outer body consequently returns `20`, and the `Ask` clause adds
`100`.

Write `epsilon_ask` and `epsilon_log` for the respective output rows. At
their requests, the ordinary continuation functions have these contracts:

- `Ask`: `Int -> Int ! epsilon_ask`. Its continuation includes the inner
  `Log` boundary and the outer body's match, ending at the `Ask` boundary.
- `Log`: `Unit -> Bool ! epsilon_log`. Its continuation ends at the `Log`
  boundary, before the outer body's match. The `Log` body's unhandled `Ask`
  requirement is included in `epsilon_log`.

`epsilon_ask` has neither explicit `Ask` nor `Log` in this example; implicit
default allocation still follows the current rules. The two entries therefore
cannot share one context-wide answer type or assume one context-wide output row.
The same source `get` also runs with `Log` outside `Ask`, without changing its
definition. A tested program using both arrangements returns `140 : Int`:
`120` from the arrangement above and `20` from the reversed arrangement.

### What a context entry must establish

For an exact effect instance, a checked context entry must associate:

1. The installed handler boundary's identity, its `A` and `epsilon`, and its
   applicable handler value and implementation evidence.
2. Each operation's instantiated `P_i` and `Q_i`, and its method contract for
   `P_i`, `Q_i -> A ! epsilon`, and the request's cleanup function, returning
   `A ! epsilon` for that *same* boundary.
3. Evidence, at a request, that its captured segment ends at that boundary,
   produces its `A ! epsilon`, restores intervening handlers on resumption and
   excludes work outside that boundary. The generated `k` is the ordinary
   function for that segment.

Different entries must be able to hide different boundary types and rows from
an opaque caller while retaining their association with the relevant handler
and control. Conceptually an entry can package its boundary-specific types
existentially; this is a requirement on the checked relationship, not a claim
that current Ash supports that package or a decision on its representation.
Boundary identity matters even if two boundaries happen to have equal types.

### Caller-independent request conversion

The row-indexed context selects an entry; the continuation also has to stop at
that entry's boundary. The accepted design derives the composition using a
typed representation of a computation. It retains the agreed ordinary
continuation functions and caller-independent function definitions. It is a
proposal for the Core representation, not current Ash syntax or a claim that
the compiler already implements it.

Write `Comp<chi, A>` for a computation returning `A` whose requirements fit
the row `chi`. It has two outcomes:

- `done(a)` returns `a : A`.
- `request(b, op, p, k, owned)` records a request to selected boundary `b`.
  For the operation's instantiated contract `op : P -> Q`, `p` has type `P`
  and `k` is an ordinary function `Q -> Comp<chi, A>`. `owned` records the
  captured control and resources using the existing ownership and close path.
  The request carries checked evidence connecting `b`, `op`, the exact effect
  instance, its row membership and the types `P` and `Q`.

`b` identifies the particular live handler installation, not merely the
handler's source declaration: recursive calls can have several active
installations of the same declaration. Each installation supplies distinct
scoped identity evidence. Requests and forwarding retain that evidence.

`Comp` is a proposed generated Core representation of the computation type;
it is not a new continuation type or a required source declaration. A typed
request packet must keep the operation's parameter and result types associated
with its continuation, including when the operation is hidden behind a row
parameter. That requires an existentially scoped or equivalent typed packet;
an untyped tag and cast is not sufficient. These outcomes describe behavior,
not a requirement to allocate a runtime tree. A lower-level representation may
replace them if it preserves the same checked contracts and behavior.

### Source function values and application

Use fixed-result functions as the canonical Core contract for source function
values. Write `V(T)` for the translation of a source value type `T`. Every source
arrow translates as follows:

```text
V(A -> B ! rho) = (Context<rho>, V(A)) -> Comp<rho, V(B)>
```

This is schematic Core notation, not source syntax. Here `rho` is the complete
checked source row, including any default requirements. The translated function,
called its worker, receives its invocation-time context and argument and returns
a computation of its source result type. Translate source arrows recursively
through function domains and results, tuples, nominal payloads and
representations, value-type arguments and ordinary interface method types.
Preserve defining identities, kinds and the exact effect-instance keys, row
substitution and lacks facts. Translating a callable does not widen an effect
argument or change its identity.

Source scheme binders remain at their corresponding checked scheme boundaries.
A monomorphic source function value has no additional binder for its caller's
answer type or row. This same worker contract applies when a function crosses
an opaque parameter, result or data-field boundary. A worker receives its
context when called; defining or returning an ordinary closure does not capture
the handler selection at its definition. Generated handler methods retain the
separately proposed installation-time context.

The earlier boundary contracts use source types. In generated Core, translate
their operation parameter, reply and boundary result types with `V`. A generated
resume continuation is already a Core function
`V(Q) -> Comp<epsilon, V(A)>` retaining the context of its captured computation;
do not apply the source-arrow translation to it again. The same applies to
generated sequencing functions and handler adapters. Packet, sequencing and
adapter equations use already translated Core value types.

For sequencing, `bind` takes a `Comp<chi, A>` and an ordinary function from
`A` to `Comp<chi, B>`, producing `Comp<chi, B>`. Its equations are:

- `bind(done(a), f) = f(a)`.
- `bind(request(b, op, p, k, owned), f)` is a request for the same boundary,
  operation and operand, with continuation `fn(q) { bind(k(q), f) }` and
  ownership extended to cover the newly captured work in `f`.

The notation states Core equations; it is not Ash source code. The second
equation appends the caller's remaining work to the request's continuation
without opening or rechecking the function that made the request. The generated
function retains the invocation-time context of the suspended work and the
environment of `f`. When the captured continuation is one-shot, forwarding
moves its authority into the new packet; it must not duplicate that authority.
Ownership extension composes established scope and resource facts through the
existing path without rechecking certified constituent fragments.

Both inputs use a common row `chi`, established by the general function-effect
compatibility and row-inference rules. More precisely, if the first computation
requires `rho` and the second requires `sigma`, the checker must establish
that both rows are included in `chi`. Weaken each computation using those
established facts before applying `bind`. For closed inputs, infer the least
row satisfying both inclusions and any surrounding constraints. Do not leave a
free inference variable in Core. If independently abstract tails cannot be
composed under the existing row rules, retain the current ambiguity rejection;
do not silently equate them. Supporting a broader class of independent open-row
constraints is outside this proposal.

At a source application, preserve evaluation of the function expression and
then its argument before invoking the worker. For their evaluated values, the
following rule composes the call with the caller's remaining work. Here `chi`
is the common row established by the existing inclusion and inference rules,
`project` supplies the worker's checked context view, and `widen` preserves the
computation's selected boundaries, operation payloads and owned control.

```sequent
T-Worker-Call :=
  worker : (Context<rho>, V(A)) -> Comp<rho, V(B)>
  argument : V(A)
  context : Context<chi>
  w : rho subset-of chi
  after : V(B) -> Comp<chi, Z>
  ===>
  bind(widen(worker(project(context, w), argument), w), after) : Comp<chi, Z>
```

The caller's answer type `Z` and row `chi` belong to this composition, not to the
stored worker type. A call with no remaining work uses `done` as its sequencing
function. Checked function-effect compatibility adapters project contexts and
widen worker results by this same contract; nested domain and result coercions
follow the companion proposal's directional compatibility rule. None of these
operations opens or rechecks the worker's body.

### Handler adapters

For a handler boundary `b` of effect instance `E`, let its body be a
`Comp<({E} union rho), A>`, its output a `Comp<epsilon, A>`, and `rho` be included
in `epsilon`. Write `handle_b` for its generated handler adapter. It uses the
handler's installation context and interface implementation:

1. `handle_b(done(a)) = done(a)`.
2. For a request targeted at `b`, generate the continuation
   `fn(q) { handle_b(k(q)) }` and scoped evidence for the owner of that same
   delimited control. Call the matching interface method with its operand,
   this ordinary function, that owner and the method's applicable evidence.
   The continuation has type `Q -> Comp<epsilon, A>`
   and the method returns `Comp<epsilon, A>`. Do not apply `handle_b` to the
   method's result: the clause runs outside its own boundary.
3. For a request targeted at a different boundary, forward the same request
   with continuation `fn(q) { handle_b(k(q)) }` and ownership extended to
   cover the intervening handled control. Its exact effect requirement must be
   established in `epsilon` by the residual-row and view rules.

Inside the handled body, the context must select `b` for each request whose
instantiated exact instance is `E`, unless a more local handler for that
instance is active. A request to an outer installation of the same instance
cannot be forwarded from that body while `b` is the applicable handler.
Requests made directly by the clause use its installation context outside `b`.
The forwarding case checks its output-row membership; it must not drop an
unhandled requirement merely because its target is different.

Context selection and override compare exact effect identities after argument
instantiation. The adapter compares the selected live boundary identity with
`b`; two installations of the same exact effect still have distinct boundary
identities. A successful boundary comparison supplies checked equality evidence
linking the packet's selected entry, operation types, `A` and `epsilon` to this
boundary. It is not a search by effect spelling and does not use an unchecked
cast. In the forwarding case the added function reinstalls the intervening
handler on resumption. In the matching case the function ends at the selected
boundary. A clause can itself request `E`: it uses the captured installation
context and its result is not recursively handled by the same `handle_b`.
This is an instance of interpreting algebraic operations by a handler; see
[Plotkin and Pretnar, *Handling Algebraic Effects*](https://arxiv.org/abs/1312.1399).
That account motivates the adapter equations, but does not establish their
correspondence to Ash's resource and control rules.

In the `Ask`-outside-`Log` example, `handle_Log` forwards the `Ask` request
with a continuation that reinstalls `Log`. The `Ask` method receives an
`Int -> Comp<epsilon_ask, Int>`. When that function continues and `Log` is
requested, the `Log` method receives a `Unit -> Comp<epsilon_log, Bool>`. It
flips `true` to `false`; the outer body returns `20`, and the `Ask` method adds
`100`. With the handlers reversed, the same elaborated `get` emits the same
requests; the adapters are applied in the reversed order and the source result
is `20`. No caller-specific handler order is added to `get`'s signature.

For the source `get` above, let `rho` be its complete checked row, including
default allocation. Its worker has type
`(Context<rho>, Int) -> Comp<rho, Int>`. Its request for `Ask` continues locally
by requesting `Log`, whose continuation returns `done` of the final integer.
The caller uses the application rule to compose that computation with its own
`after : Int -> Comp<chi, Z>`. Each intervening handler adapter supplies its own
boundary result type through the rules above. An open row is forwarded through
the worker's context view without enumerating its tail. No operation
implementation is selected again merely because `bind` or `handle_b` forwards
its established evidence.

At a `handle` expression, body elaboration returns its computation with the
body's fixed result type. Apply `handle_b` to that computation, then use `bind`
to compose the handler's result with the continuation outside the boundary.
Given established evidence `w : epsilon subset-of chi` for that composition,
the translation is:

```text
bind(widen(handle_b(elab_body(body, body_context)), w), after)
```

Here `after` uses the caller's common row `chi`. Putting `after` inside the
handled body instead would make it part of `k`, which changes the behavior when
the handler continues after `resume` or discards the captured computation.

This current Ash program checks that placement. `get`'s own handler returns
`101`, after which its caller multiplies that result by `2`:

```ash
effect Ask {
    ask : Unit -> Int
}

get : Unit -> Int
get () = handle (perform Ask.ask ()) with Ask {
    ask ignored => {
        let result = resume 1
        result + 100
    }
}

main : Unit -> Int
main () = {
    let value = get ()
    value * 2
}
```

It evaluates to `202 : Int`. Putting the caller's multiplication inside the
handler continuation would instead produce `102`.

### One callback and different boundary results

This source program uses one monomorphic callback under a `Bool`-result handler
and then an `Int`-result handler. It uses a parameterized effect satisfying the
companion declaration rule and evaluates to `(true, 2) : (Bool, Int)`:

```ash
effect Ask<T> {
    ask : T -> Int
}

exercise : (Unit -> Int ! {Ask<Unit>}) -> (Bool, Int)
exercise action = {
    let flag = handle (action () == 1) with Ask<Unit> {
        ask ignored => resume 1
    }
    let number = handle (action ()) with Ask<Unit> {
        ask ignored => resume 2
    }
    (flag, number)
}

request : Unit -> Int ! {Ask<Unit>}
request () = perform Ask<Unit>.ask ()

main : Unit -> (Bool, Int)
main () = exercise request
```

Let `rho` be the callback's complete checked row. The translated parameter is
`action : (Context<rho>, Unit) -> Comp<rho, Int>`. The first call composes its
result with `fn(n) { done(n == 1) }`, producing a `Bool` computation; the second
uses its `Int` computation directly. The contexts select different installed
entries, but both calls use the same fixed worker type. The callback needs no
new source instantiation or generated caller-answer binder. The same recursive
translation applies when the callback is returned by a function or stored in a
data field. This example checks source behavior; the generated Core contract
still requires implementation evidence.

The rewrite intends to preserve the one-shot and nonescape discipline for its
generated functions and packets. Until suitable general usage properties are
available, ordinary function typing does not fully check one-shot use; this is
an accepted known issue, not a proved part of the Core certificate. At the
matching boundary, the packet's accumulated ownership identifies all the
delimited work and resources in the generated `k`, including frames added by
`bind` and forwarding. At an ordinary discard site, the generated `complete`
uses the explicitly supplied owner and close evidence for that same control;
`discard_control(k, complete)` invokes the existing owned-close path rather
than simply dropping `k`. The clause then continues with `Unit`, subject to
the existing cleanup ordering, effects and safety checks. This is the agreed
stop-gap until resources and completion are expressed in the type system.

Preserve source provenance for generated packets, functions and adapter
applications. The system-level correspondence and required source-to-Core
checks must establish the implementation against the current semantics, except for
the separately proposed handler-context change and the stated checking gap.

## Semantic delta

- Effect rows become admissible as the specified type and interface arguments;
  the current kind and substitution restrictions are extended accordingly.
- Typed Core gains the contracts and checked operations needed to construct,
  pass, select and scope row-indexed handler contexts. Each entry carries the
  derived contract of its own boundary. The proposed computation packets,
  sequencing and handler adapter express continuation composition; their
  operation payloads require typed existential scoping or an equivalent
  general representation.
- Source function values translate recursively to fixed-result workers taking
  their invocation-time contexts. Call-site widening and `bind` compose caller
  work without adding caller answer or row quantification inside value types.
- Ordinary Ash call syntax and existing effect-row identity and equality are
  retained. The handler-context semantic change considered by the effects
  proposal is separate from this type-system proposal.
- No current interface implementation is required to be selected again merely
  because its evidence crosses a context boundary. Check new composition
  obligations using established facts; do not recheck certified bodies.
- The initial rewrite accepts a known gap: ordinary function typing does not
  fully verify one-shot use of generated continuations. General usage
  properties are future work; the Core certificate must not claim this fact.

## Affected specification areas

- [Kinds, monotypes and schemes](../../spec/static-semantics.md#kinds-monotypes-and-schemes):
  row-kinded parameters, applications and substitution.
- [Effect rows](../../spec/static-semantics.md#computation-types-and-effect-rows):
  the relationship of row equality and lacks facts to context views.
- [Interfaces](../../spec/static-semantics.md#interfaces-and-constrained-schemes) and
  [effects](../../spec/static-semantics.md#effects): operation contracts,
  evidence and scoped handler selection.
- [Elaboration and typed Core](../../spec/elaboration.md): context construction,
  passing, checked projections, recursive source-arrow translation, call-site
  sequencing and source provenance.

## Resulting specification truth

After the complete change is implemented and integrated, the specification
states how row arguments form context types and how typed contexts are passed,
viewed and scoped. It states the checked relationship between each entry and
its applicable handler contract. It does not describe the proposal itself as
current behavior before that transition.

It also states the fixed-result contract for translated source functions at
every value boundary, and how calls compose returned computations with caller
work using established row evidence.

## Interactions

The separately proposed function-effect compatibility and row-inference rules
remain prerequisites for the effects elaboration. A context type does not by
itself solve inference of a shared row. This proposal preserves the current
ambiguity rejection for independently open rows when their composition cannot
be established. Packets still require checked membership evidence.

The context index is a row of requirements, not a stack of handlers. Scope and
the supplied values determine which installed handler is applicable.

The companion [effects declaration change](../design/effects-resources/effect-interface-elaboration-proposal.md#effect-declaration-change)
requires effect parameters to be nonempty and used. Existing source examples,
tests and libraries using the old declarations must be migrated as part of the
same package; their current behavior is not a compatibility requirement.

Diagnostics for every rewrite must identify the original source construct and
relevant contract when an error is detected after elaboration. Preserve the
source provenance and established boundary facts needed for this without
reopening checked implementations.

## Non-goals

This proposal does not by itself change the current handler semantics, select
a new continuation type, define resource cleanup, or decide future multishot
and discardable continuation behavior. The elaboration proposal records those
separate obligations.

## Required evidence

- Show one checked row-polymorphic function called with different effect rows,
  including a higher-order function argument, with the appropriate context
  forwarded in each call and no rechecking of its body.
- Check recursive source-arrow translation for function-valued parameters,
  returned functions and data fields. Use the same opaque monomorphic callback
  under both `Bool`- and `Int`-result handler boundaries with invocation-time
  contexts and no added caller-answer or row quantification in its value type.
  Check context projection and computation widening before call-site `bind`,
  including valid and invalid row inclusions and nested function coercions.
- Check known-prefix selection and opaque-tail forwarding, valid and invalid
  lacks constraints, exact parameterized effect identities, equal rows written
  in different orders, and a callee requiring a subset of the caller's row.
- Check nested installations of the same effect, shared implementations with
  different handler values, restoration of the outer view, and preservation of
  default and builtin provisions.
- Show that handler entry types and boundary-specific result and output rows
  are checked; reject a mismatched operation or context. Establish how the
  chosen view representation crosses an opaque or separately compiled boundary.
- In the corresponding effects elaboration, check interleaved handlers, deep
  resumption, work after `resume`, and a handler installed inside a callee whose
  captured continuation excludes work outside its boundary.
- Check actionable diagnostics from source through elaborated Core, including
  errors at calls and handler clauses. Update the implementation, tests and
  current specification together when the proposal is delivered.
