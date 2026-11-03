# Effects as Interfaces: Elaboration Proposal

- Status: accepted
- Related: [DN-0061](../DN-0061-effects-and-resources-first-slice.md),
  [CP-0032](../../proposals/CP-0032-row-indexed-handler-contexts.md).

This proposal records the accepted effects elaboration from DN-0061. It is
accepted together with CP-0032 as one package and may authorize implementation
tasks. The change is not yet implemented; the
[specification](../../../spec/README.md) remains current language truth.
Resources and cleanup beyond the stated bridge remain future work.
The examples use current Ash; their correspondence is evidence
for the illustrated case, not a proof of the general translation. Examples
with parameterless effects describe the current language and must be migrated
when the proposed declaration change is implemented. The manually written
continuation examples illustrate bounded compositions; the canonical
fixed-result function contract is specified under [elaboration](#elaboration).

## Purpose and scope

Keep effect declarations, `perform`, `handle`, `resume` and `discard` as
surface forms. Express handler contracts and implementations using interfaces
and implementations, and express a request's continuation as a function.
Use generic functions for `perform`, `resume` and `discard` during
elaboration.

The proposal covers effect and handler elaboration. Existing resource
checking, resource scope and cleanup remain in use. In particular, the
proposal does not replace or duplicate the existing resource cleanup
implementation. Its connection to the proposed function account of `discard`
uses the per-request completion defined below.

Each declaration, function and previously checked fragment remains opaque at
its boundary. Typed Core must carry the types, rows, evidence and remaining
obligations required to check a new composition. Checking that composition
reuses established facts; it does not recheck certified constituent bodies.

## Current behavior and intended change

Current Ash gives effects and operations their own exact identities. A request
evaluates its operand, then selects the nearest matching handler in the active
control. A selected clause receives a structural resume capability; the
capability is not an ordinary source function. Resuming restores the selected
handler and intervening control. Discard consumes the same owner and uses the
existing owned-close machinery. See the current
[static](../../../spec/static-semantics.md#effects),
[elaboration](../../../spec/elaboration.md#effect-core-lowering) and
[dynamic](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
rules.

The accepted treatment keeps nearest matching handling for requests, deep
resumption, normal body return and clause execution after resume. It proposes
one change to handler context: a clause's effect implementations are those
available when its handler is installed, rather than being selected anew from
the active context when the clause runs. An implementation introduced inside
the clause has its own scope. The handler retains its installation context;
the request's continuation is a separate function supplied to the method.

The current structural capability is one-shot and nonescaping. The translation
intends to preserve that discipline, but ordinary function types do not fully
check one-shot use of generated continuations. The effects work accepts this
known issue until general linear, affine or other suitable usage properties
can express and check the required discipline. It must not claim that ordinary
Core type checking has proved that property or the corresponding unconditional
correctness guarantee. This does not authorize continuation escape, change the
existing cleanup requirement, or decide future multishot and discard behavior.

### Effect declaration change

Every effect declaration must declare at least one parameter. Every
declared effect parameter must occur in at least one operation signature of
that effect, in a parameter or result type. Occurrence is checked across the
whole declaration: a parameter need not occur in every operation. This changes
current Ash, which permits parameterless effects and unused effect parameters.

Elaboration creates the interface and operation contracts for the declared
effect. The generated handler-entry input carries the complete effect identity
and its ordered arguments in every operation method's type. Consequently,
an operation need not itself mention every effect parameter for its generated
interface method to retain the complete instance key. For example, an entry
type indexed by the declaration and all its parameters can occur in each method
input; this is a generated contract, not required source syntax. Exact identity
is the effect declaration plus its ordered arguments after substitution, so
arguments that become equal identify the same effect instance. The handler
result type and output row remain boundary parameters, rather than being
inferred from the effect's parameters.

Existing Ash programs, tests, fixtures, builtins and documentation containing
parameterless effects or unused effect parameters must be migrated as part of
the change. Failing examples are expected until then; compatibility with their
old declarations is not required.

## A worked example

This current Ash program evaluates to `111 : Int`:

```ash
effect Ask {
    ask : Int -> Int
}

main : Unit -> Int
main () = handle ({
    let value = perform Ask.ask 5
    value + 1
}) with Ask {
    ask input => {
        let result = resume (input * 2)
        result + 100
    }
}
```

The request supplies `5`. The clause resumes with `10`; the remaining body
adds `1` and returns `11` to the clause. The clause then adds `100`.

The following separate Ash program manually writes the corresponding interface
call and continuation. It also evaluates to `111 : Int`:

```ash
interface Ask<A, B> {
    ask : (A, A -> B) -> B
}

resume_control<A, B, E : EffectRow> : (A -> B ! {| E}, A) -> B ! {| E}
resume_control (k, value) = k(value)

perform_control<P, Q, R, E : EffectRow> : ((P, Q -> R ! {| E}) -> R ! {| E}, P, Q -> R ! {| E}) -> R ! {| E}
perform_control (operation, argument, k) = operation(argument, k)

discard_control<A, B, E : EffectRow, F : EffectRow> : (A -> B ! {| E}, Unit -> Unit ! {| F}) -> Unit ! {| F}
discard_control (k, complete) = complete(())

impl Ask<Int, Int> {
    ask (input, k) = {
        let result = resume_control(k, input * 2)
        result + 100
    }
}

main : Unit -> Int
main () = {
    let k : Int -> Int = fn(value) {
        value + 1
    }
    perform_control(ask, 5, k)
}
```

Here `k` is the rest of the handled body. `perform_control` applies the
selected interface method, and `resume_control` calls `k`. The implementation
can use the returned `Int` before returning its own result. The example
manually constructs `k` and uses a global implementation; it does not itself
elaborate an arbitrary request or install a local handler.
Its two-input `perform_control` and method show only the resume case; the full
generated contract also supplies the request's scoped owner evidence.

`discard_control` is included to show the proposed generic call shape. Its
`complete` argument is explicitly supplied; the program does not exercise
it. Current Ash does not establish that an arbitrary function passed as
`complete` corresponds to `k`, nor does that library definition by itself
invoke the existing structural discard operation.

### A request inside a separately checked function

The source function `get` performs `Ask`, adds one to the response, and
returns to its caller. Its caller doubles the result inside the handler:

```ash
effect Ask {
    ask : Int -> Int
}

get : Int -> Int ! {Ask}
get input = {
    let value = perform Ask.ask input
    value + 1
}

main : Unit -> Int
main () = handle ({
    let result = get 5
    result * 2
}) with Ask {
    ask input => resume (input * 2)
}
```

The following interface program illustrates explicit continuation composition
using current Ash:

```ash
interface Ask<A, B> {
    ask : (A, A -> B) -> B
}

perform_control<P, Q, R, E : EffectRow> : ((P, Q -> R ! {| E}) -> R ! {| E}, P, Q -> R ! {| E}) -> R ! {| E}
perform_control (operation, argument, k) = operation(argument, k)

impl Ask<Int, Int> {
    ask (input, k) = k(input * 2)
}

get<R> : (Int, Int -> R) -> R where Ask<Int, R>
get (input, after) = {
    let k : Int -> R = fn(value) {
        after(value + 1)
    }
    perform_control(ask, input, k)
}

main : Unit -> Int
main () = {
    let after : Int -> Int = fn(result) {
        result * 2
    }
    get(5, after)
}
```

Both programs evaluate to `22 : Int`. The manually written `get` receives
`after`, its caller's remaining computation, and requires `Ask<Int, R>`
evidence. Its `k` first adds one, then calls `after`. It passes that
composed function to the operation. The implementation supplies `10` to
`k`, which computes `(10 + 1) * 2`.

The caller supplies its established continuation and interface evidence; it
does not reopen or recheck `get`. The answer type `R` and the evidence
requirement cross this manually written boundary. The example uses an empty
outward row and one handler. In the canonical conversion below, `get` instead
returns a fixed-result computation and the caller composes its continuation
through `bind`.

### One implementation and two handler values

An effectful function can be called with different installed handlers for the
same effect. This current Ash program evaluates to `13 : Int`:

```ash
effect Ask {
    ask : Int -> Int
}

get : Int -> Int ! {Ask}
get value = {
    let answer = perform Ask.ask value
    answer + 1
}

main : Unit -> Int
main () = handle ({
    let outer = get 0
    let inner = handle (get 0) with Ask {
        ask value => resume (value + 10)
    }
    outer + inner
}) with Ask {
    ask value => resume (value + 1)
}
```

The following manually elaborated interface program also evaluates to
`13 : Int`. Both handler values use the same implementation:

```ash
newtype AskHandler = AskHandler(Int)

interface Ask<H, R> {
    ask : (H, Int, Int -> R) -> R
}

impl<R> Ask<AskHandler, R> {
    ask (AskHandler(amount), value, k) = k(value + amount)
}

get<H, R> : (H, Int, Int -> R) -> R where Ask<H, R>
get (handler, value, after) = {
    let k : Int -> R = fn(answer) {
        after(answer + 1)
    }
    ask(handler, value, k)
}

main : Unit -> Int
main () = {
    let outer_handler = AskHandler(1)
    let inner_handler = AskHandler(10)

    let after_outer : Int -> Int = fn(outer) {
        let after_inner : Int -> Int = fn(value) {
            value
        }
        let inner = get(inner_handler, 0, after_inner)
        outer + inner
    }

    get(outer_handler, 0, after_outer)
}
```

The outer call supplies `AskHandler(1)` and the inner call supplies
`AskHandler(10)`. The same `Ask<AskHandler, R>` implementation uses the value
passed to that call. The manually written `get` adds one to the answer and
then calls the continuation supplied by its caller. This example demonstrates
handler-value passing and continuation composition, not the canonical function
translation or a general account of effect rows and handler boundaries.

### Discard

For comparison, this current Ash handler discards its captured computation:

```ash
effect Ask {
    ask : Int -> Int
}

main : Unit -> Int
main () = handle ({
    let value = perform Ask.ask 5
    value + 1
}) with Ask {
    ask input => {
        let _ = discard
        input + 100
    }
}
```

It evaluates to `105 : Int`: `value + 1` is not run, and the clause continues
after discard. The interface elaboration must preserve that behavior
while connecting `discard_control` to the existing owned-close operation.

## Operation and handler contracts

For an effect operation `op : P -> Q`, the generated handler invocation
supplies a `P`, a continuation function `Q -> A ! epsilon`, and the
request's scoped owner evidence; the method returns
`A ! epsilon`. `Q` is the result supplied to the requesting computation; `A`
is the result of the handled computation. The owner is compiler-only checked
Core evidence for this request's live control, not a source value or a new
continuation type. It is scoped to the selected clause and grants neither
close nor Store transfer by itself. For an ordinary clause that can discard,
`delta` is the captured control's cleanup row, supplied with close evidence;
a private clause does not need an unused close row. The clause's requirements
account for invoking the generated `complete` under the existing close and
local handling rules. The output row `epsilon` also accounts for the other
effects that remain after handling and effects of the clause. Calling a
continuation does not by itself name the handled effect as an outward
requirement.

An ordinary method with a discard site is checked once, while `delta` may
differ for each request. Its contract therefore quantifies over `delta` and
takes a checked `Close(owner, delta, site)` evidence premise for each discard
site. This compiler-generated Core premise relates the selected owner, its
close plan and the site's surviving context; it is an added evidence contract,
not a feature claimed of current source interfaces. A boundary entry records
the method-specific premises, and its adapter passes their witnesses for the
same request owner when invoking the method. At each `discard` site, the
contract requires the residual effects of `delta` after the clause's local
handling to fit `epsilon`; the adapter supplies the matching row and evidence.
This constraint preserves clause-local handling of cleanup effects and does not
require the unhandled `delta` itself to be included in `epsilon`. The required
row and evidence representation is part of the proposed Core and interface
support, and its correspondence with the current discard checks must be
validated.

At an ordinary `discard` site, the elaborator constructs
`complete : Unit -> Unit ! delta` from that same owner and its checked close
evidence. Neither the owner nor `complete` is captured when the handler is
installed. The earlier interface examples show resume-only calls with just
`P` and `k`; they illustrate that case rather than the full generated
invocation contract.
Private Store-associated handlers use the same owner input for
[retain](#private-store-retain), while sharing the operation interface.

Effect parameters retain the meaning and exact identity of their declaration.
They are not automatically the method's answer type or output row. The same
effectful function may be used under boundaries with different answer types
and rows. [CP-0032](../../proposals/CP-0032-row-indexed-handler-contexts.md#deriving-a-handler-boundary-contract)
derives that `A` and `epsilon` belong to the selected handler boundary. A
method required to work for every `A` is not equivalent to a clause that
depends on one particular answer type. CP-0032 derives the
caller-independent composition for the matching continuation.

Open rows are required: the continuation can perform effects not listed in
the handler implementation. Its row and the method's own requirements must be
represented and composed at the boundary. The
[row audit](first-slice-rule-resolution.md#effect-row-parameter-audit) records
the current restriction and compiler discrepancy for interface and
implementation row parameters.

Interface methods are the operations declared for that interface; no method
is required on every interface. The elaboration uses the existing interface and
implementation mechanisms. It does not select an additional Core interface
qualifier. The generated handler-entry input carries the complete exact effect
instance into each operation's interface contract, as required by the
declaration rule above.

## Required prerequisite: function-effect compatibility and row inference

The effects proposal requires a general type-system rule for using functions
with different declared effect rows in one generic composition. This is not
an effect-handler-specific elaboration rule. Current Ash permits
[computation-level effect weakening](../../../spec/static-semantics.md#computation-types-and-effect-rows),
but matches function-value types by equality rather than widening their latent
effect rows.

The proposed compatibility rule permits a value of type `A -> B ! E` where
`A -> B ! R` is expected when `E` is contained in `R`, subject to the
ordinary checks on `A` and `B`. It changes the effects permitted by the
expected type, not the function's behavior. Type compatibility must preserve
its direction in nested positions; an exact identity or equality constraint
is not replaced by row inclusion.

At a generic call, instantiate a declared row parameter with an inference
variable and collect its constraints from all arguments and the surrounding
context before choosing a row. For `combine(first, second)`, when `first`
requires `{Read}` and `second` requires `{Log}`, the constraints are
`{Read} subset-of R` and `{Log} subset-of R`. In the absence of other
constraints, the least solution is `{Read, Log}`. Both occurrences and the
result use that same `R`; they do not receive independent rows. The earlier
test rejects this call with `type.argument` under current rules.

Inside the already checked generic definition, `R` remains abstract. At each
call, solve its instantiation using established argument types rather than
rechecking their bodies. Respect explicit row arguments, expected results,
exact effect identities and arguments, kinds, scope, lacks and equality
constraints. A conflicting requirement rejects the composition. Typed Core
must carry the selected row and the checked compatibility needed at that
boundary. The coercion rules below do not recheck argument bodies.

This prerequisite does not by itself solve composition of independently open
rows. Their least union may not be representable in the current row form.
[CP-0032](../../proposals/CP-0032-row-indexed-handler-contexts.md#caller-independent-request-conversion)
retains the current ambiguity rejection when a common row cannot be established,
without assuming that the independent tails are equal.

### Core evidence for function-effect compatibility

For a checked source function `f : A -> B ! rho`, let `f_core` be its
fixed-result worker under
[CP-0032's recursive value translation](../../proposals/CP-0032-row-indexed-handler-contexts.md#source-function-values-and-application)
`V`. Given checked inclusion evidence `w : rho subset-of sigma`, emit the
typed Core coercion
`weaken_fn(f_core, w) : (Context<sigma>, V(A)) -> Comp<sigma, V(B)>`.
On application it projects the supplied `Context<sigma>` to `Context<rho>`
using `w`, calls `f_core` once with that view, and widens its resulting
`Comp<rho, V(B)>` to `Comp<sigma, V(B)>`. Computation
widening preserves a completed value; for a request it preserves the selected
boundary, operation, operand and owned control while widening its continuation.
The coercion carries both rows and the checked inclusion or a checked Core
node with equivalent premises. It does not inspect the function body. A
backend may fuse or erase the adapter only when it preserves the projection and
computation behavior, including handler and ownership identity.

Compatibility is directional. An actual `D1 -> C1 ! rho` fits an expected
`D2 -> C2 ! sigma` when `D2` fits `D1`, `C1` fits `C2`, and `rho` is included
in `sigma`. Nested function positions use the same rule, reversing direction
at each domain. Other value types, nominal applications and effect arguments
retain their current equality requirements. Core records the corresponding
nested coercions, rather than assuming the values have identical calling
conventions. An adapter applies the domain coercion before the call and the
result coercion to its completed result.

For this package, construct an inclusion witness from established row facts:
each known source instance must be present in the target; an open source tail
must be the same established tail in the target. The empty closed row is
included in every well-formed row. Compare exact identities after substitution
and check the existing kind, scope and lacks premises. An abstract tail does
not by itself prove that it contains a particular effect. Existing equality or
inclusion evidence may supply an otherwise unavailable fact; independently
abstract tails are not silently equated.

At a generic call, instantiate each scheme binder once with a fresh
kind-correct inference variable. Collect compatibility constraints from all
arguments and the expected result, reversing direction through function
domains; also retain equality, lacks, kind, scope and occurs constraints. Solve
equalities, collect representable lower bounds for each inferred row, and
choose their least representable union under the existing partial row rules.
Known target members already covering a source member do not need to be added
to the inferred tail. A source instance is covered only when equality is
established; place it in the tail only when the target's required lacks facts
are established. If it could later equal a known target member and neither
case is established, reject the ambiguous constraint. Propagate bounds
between inference variables as needed.
Reject an unrepresentable union or an unproved abstract-tail relationship
under the existing ambiguity policy. Check every upper bound and remaining
constraint after substitution. An unconstrained variable follows the existing
generalization or ambiguity rules; it is not silently assigned an empty row.
Explicit Core row arguments and source expected types constrain the same
solution; this does not introduce explicit row-argument syntax in source.

For example, callbacks requiring `{Read}` and `{Log}` yield the shared
inferred row `{Read, Log}` and one inclusion witness for each callback. If an
expected type fixes that row to `{Read}`, the call is rejected. Two independent
rigid tails do not imply a representable union. Core carries the solved row in
the type application and checks each emitted witness at the new composition.

## Elaboration

The proposed calling convention uses ordinary functions and interface evidence.
Elaborate each source function definition once to a fixed-result worker:
`V(A -> B ! rho) = (Context<rho>, V(A)) -> Comp<rho, V(B)>`.
[CP-0032](../../proposals/CP-0032-row-indexed-handler-contexts.md#source-function-values-and-application)
defines this recursive value translation and its application rule, including
source arrows in parameters, results and data fields. Source scheme binders
remain at their checked boundaries; a monomorphic function value acquires no
caller-answer or row binder. The worker's invocation-time context supplies
handler values and evidence for its checked row, including known effects and
an opaque open tail. Ordinary surface calls remain as written: the caller
supplies the required context view, widens the returned computation using
established row evidence, and composes its remaining work through `bind`.
An effectful function can propagate its requirements without a locally
installed handler; a completed program must discharge those requirements.

At a request the worker emits a typed packet with its selected boundary and
local continuation. Call-site `bind` and handler forwarding compose suspended
work until the matching handler adapter supplies the delimited continuation to
the selected method. A nested handler supplies a handler value for its scope;
a continuation retains the context needed by the computation it resumes.
Ordinary source function values receive their effect context when called.
Generated handler methods retain their installation-time context. A request
does not rewrite its callers or recheck an opaque function body.
Current Core does not yet perform this rewrite. Compatibility with already
compiled functions using the current convention is not required by this
package; affected programs and dependencies are rebuilt with the new convention.

[CP-0032](../../proposals/CP-0032-row-indexed-handler-contexts.md#caller-independent-request-conversion)
derives the boundary contracts and packet, sequencing and handler
adapter rules. Elaboration constructs the handler's ordinary Core continuation
`V(Q) -> Comp<epsilon, V(A)>`; it need not turn a source `resume` capability
into a function. That generated continuation is already Core and is not
translated again as a source arrow. The implementation must be checked against
Ash's operational semantics and the existing discard and cleanup path.

### Row-indexed handler context

The proposed type-system change and its review requirements are recorded in
[CP-0032](../../proposals/CP-0032-row-indexed-handler-contexts.md).

Use one context mechanism for both multiple known effects and an open row.
Conceptually, `Context<R>` is the type of the handler context for effect row
`R`; this notation describes the proposed relationship, not current Ash
syntax. The proposed context is a compiler-generated typed collection of
handler entries, with typed views for known entries and an opaque open tail.
A context for `{Ask, Log}` supplies the applicable handler for each
exact effect instance. A function polymorphic over `R` receives and forwards
the corresponding context without enumerating its unknown effects. The
request's continuation is a separate function supplied to the operation method;
an ordinary worker returns its fixed-result computation.

At an ordinary call, elaborate the caller to supply the context required by
the callee's checked row. At an operation, select the handler value for its
exact instance from that context. Installing a handler provides a context for
its body with the new handler applicable to that instance; leaving the scope
uses the surrounding context. A continuation retains the context applicable to
its captured computation. Handler values can share an interface implementation.
Context selection and forwarding use the established row and handler
contracts; they must not inspect or recheck opaque function bodies.

Rows are unordered requirements: handler nesting and selection come from the
context and its scope, not an ordering in the row. Context handling must also
account for established default and builtin provisions, including private
default allocation, without treating every row member as a user-installed
source handler. The effect-row index does not determine the handler's answer
type or the continuation and clause output rows.

Ash currently permits a global function to quantify and forward an open effect
row, but does not permit an `EffectRow` variable as an ordinary nominal or
interface argument. In particular, `Context<R>` is not currently expressible
as the proposed row-indexed value type. See the current
[kind rules](../../../spec/static-semantics.md#kinds-monotypes-and-schemes).
The earlier requirement to use an open row in an effect interface and the
context both motivate
support for row parameters at type and interface boundaries. Specify the
necessary type-system and Core support, including selection, scoped replacement
and forwarding of context entries. Do not assume that accepting a row argument
alone defines those operations or resolves independent open-row composition.
The separate function-effect compatibility and row-inference prerequisite
above remains required.

The fixed two-handler context below is a current Ash illustration of context
passing with manually written continuations. It returns `11 : Int`; its `Log`
implementation ignores the recorded value. The concrete tuple does not model
an arbitrary open-row context or the canonical packet conversion.

```ash
newtype AskHandler = AskHandler(Int)
newtype LogHandler = LogHandler(Unit)
newtype Context = Context((AskHandler, LogHandler))

interface Ask<C, R> {
    ask : (C, Int, Int -> R) -> R
}

interface Log<C, R> {
    record : (C, Int, Unit -> R) -> R
}

impl<R> Ask<AskHandler, R> {
    ask (AskHandler(amount), value, k) = k(value + amount)
}

impl<R> Log<LogHandler, R> {
    record (handler, value, k) = k(())
}

get<R> : (Context, Int, Int -> R) -> R
get (Context((ask_handler, log_handler)), value, after) = {
    let after_ask : Int -> R = fn(answer) {
        let after_log : Unit -> R = fn(ignored) {
            after(answer + 1)
        }
        record(log_handler, answer, after_log)
    }
    ask(ask_handler, value, after_ask)
}

main : Unit -> Int
main () = {
    let context = Context((AskHandler(10), LogHandler(())))
    let finish : Int -> Int = fn(answer) {
        answer
    }
    get(context, 0, finish)
}
```

### Elaboration rules

1. **Declaration and implementation.** For each effect operation, construct
   the interface method contract above. Elaborate the handler's clause into
   its implementation method, with the operation argument, `k` and its
   scoped request-owner evidence as inputs.
   A handler's ordinary lexical dependencies follow ordinary scope rules.
2. **Boundary.** A `handle` expression supplies the applicable implementation
   and delimits the continuation. Ordinary body completion passes its result
   through. Preserve exact effect identity and the handler's installation
   context.
3. **Request.** Evaluate the operand before the request. Emit a typed packet
   containing the selected exact-instance boundary, operand, local continuation
   and owned control. Call-site `bind` and handler forwarding extend the
   suspended computation using established contracts. At the matching boundary,
   the adapter constructs `k` for that complete delimited computation,
   preserving its environment and intervening handler order. It supplies the
   per-request owner for the same control and applies the method to the
   operand, `k` and owner. Schematically, for
   the actual delimited context `C`, `C[perform E.op x]` corresponds to
   `E_op(x, fn(q) { C[q] }, owner)`. `E_op` is the method of the
   nearest applicable exact-instance handler; the selected clause's own effect
   context follows the proposed installation-time rule. The notation describes
   the relationship, not a complete Ash expansion: the function must carry the
   selected handler and intervening evidence needed when it is called. Compose
   the caller's continuation only as far as the selected boundary; work outside
   a handler installed inside the callee is outside that handler's capture.
4. **Resume.** Elaborate `resume value` to `resume_control(k, value)`. Calling
   `k` restores the selected handler and intervening control; after that
   computation returns, the remainder of the clause continues. Subsequent
   requests in the resumed computation remain deeply handled.
5. **Discard.** From the request's owner and close evidence generate
   `complete` for the same captured control as `k`, with its cleanup effect
   row, and elaborate `discard` as
   `discard_control(k, complete)`. Completion invokes the existing owned-close
   operation for that captured control, returns `Unit` and lets the clause
   continue. Preserve existing discard admission, close ordering, cleanup
   effects and outside-completion rules; do not run the abandoned computation.

### Source diagnostics

The [roadmap's requirement for all rewrites](../DN-0060-typed-data-and-control-roadmap.md#properties-of-a-fragment)
applies to this elaboration. Preserve source origins for generated calls,
continuations, handler values, effect requirements and interface methods
through the Core path. Report failures in terms of the source program, with
the relevant call, operation or handler and, where useful, the declaration
that states its contract. Generated names must not replace actionable source
locations.

For example, if `main` calls `get` without handling its `Ask` requirement,
identify the call and the declared effect row. An intermediate function may
legitimately propagate `Ask` without installing a local handler; only report
a missing handler where the requirement must actually be discharged. If a
handler clause fails its operation contract, identify that clause and the
operation declaration. Use recorded contract origins across opaque boundaries
without rechecking the function body or inventing an unavailable call chain.
Check negative examples at both source and post-elaboration boundaries.

### Rows

For a handler of the exact instance `E`, let `rho` be the body's remaining
row after handling `E`, and let `epsilon_out` be the handler's output row.
The current rules require `rho` and the requirements of every clause to fit
`epsilon_out`; `resume` produces the handler's result with that shared row.
A request made directly in a clause can introduce `E` again. A discard has its
own cleanup row, and the clause must account for it after any applicable local
handling.

The worker contract carries the source function's checked row and fixed result
across value boundaries. Call-site composition uses established inclusions into
its common row. The method contract separately carries its boundary-specific
continuation and clause output rows. For example, if the body still requires
`IO` and the clause requires `Log`, the output must account
for both. With open rows, checking must also preserve exact effect arguments,
lacks facts, weakening and the premises for union and removal. Current row
union can be ambiguous for independently open tails; current schemes do not
retain general row-union or membership constraints. The elaboration uses
established row compatibility without inspecting a checked function's body.
Interface and implementation row binders remain the separately recorded
[support gap](first-slice-rule-resolution.md#effect-row-parameter-audit).

### Interface evidence

In the manually written `get` example, the requirement `Ask<Int, R>` is evidence
supplied to the checked function. In the canonical conversion, the worker
receives its row-indexed context. At a handler boundary, the handler value and
implementation evidence are supplied for its exact effect instance. Multiple
handler values can share one interface implementation. Inside that boundary,
calls forward the relevant context; a continuation also carries what is needed
to resume its own computation. The handler clause's own effect context follows
the separate proposed installation-time rule.

The implementation must be checked for nested and interleaved handlers, including
the same exact effect installed more than once. The current scoped-evidence rules
reject identical simultaneously active keys and give abstract requirements
priority over lexical evidence. This does not prevent distinct handler values
from sharing an implementation, as the example above shows. CP-0032 derives
the proposed context views that select and pass the nearest applicable handler
value, while retaining the current local-nominal restriction for this work.
The current
[forwarding and deep-resume example](../../../spec/dynamic-semantics.md#forwarding-and-deep-resume-effect-001)
is a check on the result: an `Ask` request crosses a `Mark` handler, and the
resumed computation must still use `Mark`.

### Existing discard

The current [Core discard](../../../spec/elaboration.md#effect-core-lowering)
is a clause-scoped operation naming a live control owner. The library function
`discard_control(k, complete)` only calls its `complete` argument. The two
are not connected by the tested program, and a current source closure cannot
capture the clause's structural `discard` operation.

The elaborator associates `k` and the request's explicit scoped owner evidence
with the same captured control. At the discard site it constructs `complete`
from that owner and its existing close authority.
`resume_control(k, value)` resumes that control, while
`discard_control(k, complete)` invokes its existing owned-close operation.
Because current structural `Discard` cannot occur inside a source closure,
the compiler-generated `complete` uses an internal owner-explicit close entry
that invokes the same owned-close machinery. Its owner operand is scoped to
the selected clause and cannot be forged by source code. This entry point and
the corresponding typed Core contract must be added for the rewrite.
The close returns `Unit` and the clause continues without running the abandoned
computation. The current close row and safety checks remain applicable. The
association's physical representation is an implementation choice; it must
preserve the explicit Core contract and must not repeat established checks.

This connection is a stop-gap for the effects work. It is intended to remain
only until resource ownership and completion can be expressed and checked
through the type system. The resource work must then establish the replacement
and cover the existing consumers before retiring the corresponding legacy
path; the bridge is not the intended final account of discard.

### Discard context and evidence

`Context<R>` supplies effect implementations to the cleanup computation, as
it does to any other effectful computation. It does not itself establish which
resources are owned by the captured control or whether closing them is safe.
Those are existing owned-close facts and remain part of the resource stop-gap.

The elaboration and checking contract is:

1. A checked fragment exports its request and owned-control summary, including
   applicable capture cases, ordered close contributions, resource and
   outside-completion dependencies, and any obligations whose subjects are
   outside the fragment. Where these facts are already established, preserve
   their evidence; do not inspect the fragment again. Unknown facts are
   obligations, not empty plans or successful checks.
2. `bind` and handler forwarding compose those summaries for the newly formed
   captured segment, preserving case guards, structural order, live owner
   identities and the outside completion. This checks the new relationships;
   it does not reconstruct the constituents. The matching handler adapter
   associates the resulting segment and its close evidence with both `k` and
   the owner for the selected request.
3. Existing discard admission determines whether each covered capture can be
   closed, whether outside and running completion survive, and which
   interpreters are valid at each close position. It also computes the least
   residual close row `delta` from the covered cases using the existing
   partial row and cleanup rules. Carry the resulting checked facts, or the
   precisely scoped outstanding obligations, through the same opaque
   boundaries as the request. A complete executable must discharge them; an
   effect row alone cannot supply them.
4. A clause is checked once with abstract `delta`. At each `discard` site,
   elaborate `discard_control(k, complete)` using the `Context<delta>` view
   for that site's current clause context. Its locally installed handlers
   discharge the effects they handle; remaining effects must fit the handler
   output row. The checked site contract records these row and context
   requirements. At a request, instantiate that contract with the close row
   and evidence for the same captured segment; reject the new composition if
   its requirements cannot be established.
5. Each cleanup action receives the appropriate context view for its own
   position in the existing ordered close. Action-local handling, retained
   builtin interpreters, removed captured handlers and surviving clause
   handlers keep their current distinct roles. The context cannot reinstate a
   discarded source handler merely to make its cleanup effect available. A
   removed nearest source or generated handler remains relevant to the
   existing compatibility check; an outer same-instance handler cannot replace
   it to admit an incompatible action. Closing one position may change the
   context for the next, so the discard site's view is not blindly reused.

The established contracts and actual dynamic owner remain correlated with the
same request: a same-typed `complete` for a different capture is insufficient.
The scope and production of close-plan and outside-completion evidence are
described in the existing [close derivation](first-slice-close-rules.md#build-the-owned-close-in-structural-order).
Those resource derivations identify outstanding producers; the effects
elaboration must not claim they are established merely by constructing a
`Context`. In particular, the current linked analysis does not already export
all the required compositional summaries. Their producers must be implemented:
the existing analysis can establish a fragment's facts once, but a new
composition must consume its retained summary instead of rechecking the
fragment. If a required summary cannot yet be produced, retain an obligation
or reject that composition; do not certify an unproved close.

### Private Store retain

The existing private Store path has a different completion from ordinary
discard. A private clause may `resume` or, for a `Unit` operation reply,
`retain`; it cannot discard. It receives the same scoped owner evidence as an
ordinary clause, but that evidence grants neither operation on its own.
At a permitted `retain` site, the compiler constructs
`retain_control : Unit -> Key<N> ! {Drive<N>}` for that same owner and the
authenticated Store. A private operation with a non-`Unit` reply has no retain
site and receives no retain function or transfer authority. This shares the
operation interface without an invalid dummy completion.

Elaborating `retain` invokes that function. Since current structural
`Retain(handler, owner)` cannot be captured by a source closure, its generated
body invokes an internal owner-explicit Store transfer entry with the same
admission and execution as `Retain`. That entry reserves and moves the owned
capture into the actual Store, consumes the clause owner, returns its key to
the clause and continues the clause suffix. It neither invokes `k` nor closes
the capture. The owner is scoped to the selected private clause and cannot be
forged by source code. The typed Core contract and entry point must be added;
existing source restrictions still prevent a private `discard`, an out-of-scope
retain or access across a capability barrier.

The transferred segment includes the rewritten continuation, its handler
contexts, resource and nested-owner state, and the established Store admission
facts. The internal Store seam must represent that segment as owned control;
an arbitrary function value alone is not a Store capture. Existing `advance`
and `advance_with_drive` restore it with `()`, a fresh root and the existing
result adapter, or return `None` for an absent or spent key. The Store's
descriptor, actual activation, interpreter identity, driver admission, root
and release rules remain in force. Admission and restoration use the contexts
of this proposal, including its installation-time handler-clause change.
See [scoped retained control](../../../spec/static-semantics.md#scoped-retained-control)
and its [execution rules](../../../spec/dynamic-semantics.md#scoped-retained-control-execution).

## Remaining work

- Implement the recursive fixed-result worker contract at all source value
  boundaries and compose calls through context projection, checked computation
  widening and `bind`. Cover one opaque monomorphic callback used under both
  `Bool`- and `Int`-result handlers, returned callbacks and callbacks stored in
  data, including invocation-time contexts and nested function coercions.
- Implement and validate the proposed general function-effect compatibility
  and row-inference rules, then use their established facts in the effect
  elaboration.
- Establish correspondence of the computation packets, continuation
  composition and handler adapters with the source-to-Core and execution
  paths, including nested handling and captured boundaries.
- Implement and validate the derived boundary types, row composition and
  exact effect identities, including each handler's requirements.
- Implement and validate the derived row-indexed context views, handler
  selection, scoped replacement and forwarding. Cover multiple effects, open
  rows and nested handling, including implementation evidence at installation.
  The current local-nominal restriction remains in place for this work.
- Verify source-oriented diagnostics through every effects rewrite, including
  failures reported after elaboration and across opaque boundaries.
- Implement the per-request association of `k` and `complete` with existing
  resource cleanup; do not infer that ignoring a function performs discard.
  Record the accepted one-shot checking gap until general use properties are
  implemented.
- Implement the private Store completion and the owned-control seam for the
  rewritten capture, retaining its existing admission and restoration rules.
- Migrate effect declarations, tests and documentation affected by the new
  parameter formation rule, and check the generated interface instance keys.
- Establish correspondence with the current effect rules and execution, except
  for the proposed handler-context change. Cover normal return, clause code
  after resume, forwarding, repeated requests and discard, including existing
  resource cleanup. Check each new composition using established contracts.
