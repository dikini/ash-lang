# First Slice: Introducing and Sequencing Requests

This record develops the request and sequencing facts used by the
[request/capture judgment](first-slice-request-capture-judgments.md) and its
[worked example](first-slice-request-capture-judgments.md#one-certified-computation-different-contexts).
It follows an ordinary `perform` and a nonrecursive single-variable binding.
Function definition and application remain outside the slice; their established
computation judgments are inputs. The candidate judgments are not current Ash
syntax, implemented Core certificates or a complete calculus. The
[specification](../../../spec/README.md) is authoritative for current behavior.

## Why the continuation matters

Consider a checked computation `e` followed by `s`:

```ash
let x = e
s
```

The [binding steps](../../../spec/dynamic-semantics.md#bindings) put a pending
binding frame around `e`. If `e` requests an operation, a handler may capture
that frame. If it resumes the request, the reply enters the rest of `e`; only
if `e` then returns normally is its result bound to `x` and `s` entered. A
later request inside the rest of `e` also has `s` pending. A discard that
abandons the binding frame never enters `s` through that frame.

The operation reply and the final value bound to `x` need not be the same
value, or even have the same type. The reply has the operation's result type;
the residual computation may make more requests or transform it before `e`
returns. The type-system account must carry the actual reply's relevant facts
into that residual and the actual final result's facts into `s`.

An internal handler in `e` can discard an inner capture and still return from
`e` normally. In that case the binding continues. It is abandonment of the
**pending binding frame** that prevents this particular continuation from
entering `s`.

## Current source-to-Core path

| Current path | Input and output | Candidate disposition |
| --- | --- | --- |
| [Request elaboration](../../../src/elaborate.rs#L13966) | The resolved exact operation and checked operand produce a Core request with the substituted result type and operand row union the requested instance. The operand is evaluated first. | Reuse the operand's established type and behavior; the request rule introduces the operation's request and reply contract without checking the operand again. |
| [Block checking and lowering](../../../spec/static-semantics.md#blocks) | Source checks a binding's initializer before its remainder, with the binder in scope only in the remainder. The [elaboration](../../../spec/elaboration.md#surface-erasure) puts a nonrecursive Core binding around that remainder. | Compose the certified initializer with the certified remainder under its binder and explicit assumptions. Generalized and pattern bindings use their own rules; this record does not redefine them. |
| [Core binding validation](../../../src/core/validate.rs#L10754) | Checks the initializer against the binder type and the binding result against the body type; other validation handles scopes, rows and effects. | The new binding rule must establish these type and scope relationships as well as behavior. Current Core checking is not already certificate reuse. |
| [Current control construction](../../../src/core/capture.rs#L2214) | Typed Core children become ordered control; a [request](../../../src/core/capture.rs#L2914) has operand control followed by its request event. Module checking uses imported callable summaries and later follows their graph in the consuming context. | Derive the new computation's behavioral judgment from the established constituent judgments and the binding or request rule. Do not reconstruct the same constituent behavior by inspecting its body or a graph of it. |
| [Core capture validation](../../../src/core/validate.rs#L13857) | Where its gate applies, current linked Core validation reconstructs and checks capture relationships from the assembled nodes. | Check the new composition from certified Core constituent judgments, without verifying them again. Exact per-consumer replacement and current validation authority remain unresolved. |

The existing [row-lifting convention](../../../spec/static-semantics.md#row-lifting-for-existing-expression-rules)
unions a block's initializer and remainder rows. A row is unordered: it records
possible requirements, not which work is pending at a particular request.
Static row inclusion also does not assert that every listed request occurs.

## Candidate behavioral interface

Write `GAMMA; L, entry |- e : A ! epsilon ; B_e` for a checked computation
and its behavior under stated assumptions. `GAMMA` contains lexical typing
facts. `L` contains only assumptions established to remain valid across this
composition; `entry` describes the relevant initial state and may change
during evaluation. This follows the metanotation in the
[request/capture record](first-slice-request-capture-judgments.md#candidate-boundary-contracts).
`B_e` must cover the applicable possible behaviors, including:

- normal return cases with the particular result, its dependency facts and
  the relevant resulting owner, control and completion facts;
- request cases with exact operation and instantiation where established,
  payload facts, conditions, and a residual contract indexed by the actual
  admissible reply and its resulting facts; and
- other relevant possibilities, including unknown behavior and non-return,
  without treating either as a proved return or an absent request.

These are conservative cases, not claims that each member executes. Cases and
their conditions must cover the relevant executions and preserve correlations.
A residual can make further requests, return or fail to return; this record
does not assume deterministic residual behavior or a finite case list.

For the following rules, `Seq` is a **candidate type-level behavior
composition**, not an Ash expression, a new Core operation or a selected data
structure. It combines established behavior judgments. The rules do not grant
permission to replay a graph of a certified constituent to infer its behavior.
The exact representation, coverage argument and checking procedure remain to
be defined.

## Candidate rule: a binding

Suppose `e` has type `A`; `s` has result type `C` and is checked once under a
fresh `x : A` and symbolic assumptions `psi(x, state, deps)` about the
initializer's actual normal result and the context at that return. Those
assumptions include any value dependencies and owner or completion facts
needed by `s`. They concern the post-initializer state: an owner available at
entry may have been consumed before the remainder starts. The binding
composition must establish that every applicable normal result of `e` supplies
`psi`, or retain the missing relationship as an explicit obligation. It must
also satisfy the ordinary type, scope, owner and partial row-union rules.

The following is a candidate rule for this one binding form. `normal_fits`
names the required relation between the initializer's covered normal returns
and the remainder's conditional premises. `bind` in the conclusion denotes
the ordinary binding composition; `(x, state, deps) -> B_s` denotes one
parametric established judgment, not a decision about Ash's type syntax. This
rule covers the monomorphic single-variable binding only; pattern and
generalized bindings keep their own rules. The variable is fresh in the
enclosing context, initializer type and result contract. The remainder's
ordinary type, scope and row must be established without relying on `psi`;
only its behavioral facts may be conditional on those post-return assumptions.
The ordinary and behavioral projections come from one certified remainder,
not two checks of its body. `L` is reused only where its stability has been
established. Conditions about the initial state do not automatically hold in
the resulting state. `state` and `deps` are fresh symbolic indices of the
single parametric remainder judgment, not requests to check the body once per
possible runtime result. The `psi` shown here does not depend on entry; in the
normal-return rule it is the four-argument predicate that ignores its entry
argument. For each applicable capability crossing the binding, the
[structural usage judgments](first-slice-continuation-use-trace.md#candidate-usage-judgments)
of the constituents must also compose. They are components of their
established typing judgments, not another traversal of either constituent.
Capabilities introduced and discharged within a constituent remain governed
by that constituent's rules.

```sequent
J-Bind-Behavior :=
  x is fresh for GAMMA, A, C, epsilon_e and epsilon_s
  GAMMA; L, entry |- e : A ! epsilon_e ; B_e
  GAMMA, x : A; L |- ordinary(s) : C ! epsilon_s
  GAMMA, x : A; L, psi(x, state, deps) |- behavior(s) : B_s(x, state, deps)
  ordinary(s) and behavior(s) are projections of one certified judgment of s
  state and deps are fresh symbolic indices for the remainder judgment
  GAMMA; L, entry |- normal_fits(B_e, psi)
  for each applicable crossing capability k, entry supplies u_k and U(k, e, u_k, m_k) and U(k, s, m_k, t_k)
  epsilon = epsilon_e union epsilon_s
  ===>
  GAMMA; L, entry |- bind(x, e, s) : C ! epsilon ; Seq(B_e, (x, state, deps) -> B_s)
```

The remainder's judgment is conditional on its binder and post-state
assumptions; it is not checked again for every value returned by `e`. A new
binding instantiates that established judgment and proves the relationships
needed for its particular initializer. `normal_fits` must relate each covered
return's actual value, post-state, dependency facts and condition from the
same case and activation; it cannot combine independently possible facts as
though they were an exact result. It must use the certified interface rather
than reanalyzing `e`. The type, freshness and row premises are the
single-binder instance of the existing [block rules](../../../spec/static-semantics.md#blocks)
and [row lifting](../../../spec/static-semantics.md#row-lifting-for-existing-expression-rules).
Union must be defined; an ambiguous row union cannot satisfy this rule.
`normal_fits` has a candidate rule, but still needs a checkable representation
and justification.
The displayed inference applies only when all premises are established. A
missing premise leaves an obligation; this record does not define an open
judgment form that would carry it to a later stage.
The [normal-return judgment record](first-slice-normal-return-judgments.md)
develops the candidate compatibility relation and applies it to both bindings
and request operands. The usage premise checks structural state compatibility
even when the initializer is known not to return normally; it does not assert
that a normal return occurs. Applying `U-Sequence` to those established
judgments supplies `U(k, bind(x, e, s), u_k, t_k)` for each applicable owner.

For this rule to be useful, `Seq` must have these behavior-preserving laws,
justified against the operational steps:

| Covered case of the initializer | Required case of the binding |
| --- | --- |
| `e` requests `r` with residual family `rho_e` | Preserve `r`, its conditions and payload facts. The full pending control composes the applicable `rho_e(reply)` with the binding and established `B_s` at `e`'s normal exit. Preserve the binding's saved context and relevant owners. A separate boundary-selection judgment determines which part is captured and which stays outside. |
| `e` returns a value `v` normally | Bind that actual `v` and its resulting facts to the remainder's established conditional judgment. The pending binding frame is discharged before `s` runs. |
| The entered remainder requests an operation | Preserve its own request and residual facts, under the corresponding initializer-return conditions and substitutions. Do not re-enter or replay `e`. |
| `e` diverges, or the pending binding frame is abandoned | Do not claim that this frame enters `s`. Other branches and other established completion obligations remain accounted for. |
| The initializer or remainder has an unknown relevant case | Preserve a covering unknown case or an explicit obligation. Do not turn missing behavior into a proof of absence. |

The initializer's request reply and post-reply facts are passed together to
`rho_e`. The account must preserve `e`'s local boundaries and, when an inner
handler selects the request, the selected clause's continuation after resume.
Only `e`'s eventual normal result, not necessarily the reply itself, becomes
`x`. Actual reply, result and state facts can differ. Certified cases are
reusable conditional facts, not predictions that a particular branch runs. The
laws must cover all relevant cases, not just one convenient request or return.
The [sequencing-cases record](first-slice-sequencing-cases.md) spells out the
normal-return, non-return, failure and unknown alternatives and their relation
to the request case below.

## Candidate rule: carry a request through a binding

Suppose one established case of `B_e` describes a possible request `r` under
condition `phi`. Its facts include the request's payload, dependencies,
instantiation and activation, its ordered local control `K_e`, and a residual
family `rho_e` indexed by an applicable interpreter context, an admissible
reply and its relevant resulting facts. The case and its condition describe an
upper bound: neither asserts that a request or reply actually occurs. `K_e`
must retain local handlers, owners and their completion states; it is not
necessarily all captured by the handler ultimately selected.

Let `F` be the remainder's single established conditional judgment. Let `a` be
a fresh symbolic binding-entry state, including its activation, scoped over
the rule; `entry_a(s0)` means `entry(s0) and s0 = a`. Let `f(a)` stand for the
pending binding context from that same entry: its pre-binding lexical
environment, activation, `F` and the relevant owner and completion facts.
`Seq_f(a)` is the same candidate behavior composition as `Seq`, with that
binding context made explicit; it is not a proposed data structure or Core
operation. The following rule lifts one already established request case after
the premises of `J-Bind-Behavior` have been established. `z` denotes that
case's symbolic, correlated payload, request state and local witnesses; the
rule scopes it to the case, allowing multiple possibilities for one entry.
`h` is a symbolic applicable
interpreter context, including a source handler's clause continuation where
relevant. `q`, `state_q` and `deps_q` are symbolic actual-reply indices,
restricted by the residual's assumptions and `h`'s reply contract.
The conditions, request facts and local witnesses remain correlated and
scoped to this same case and activation. `h` must be an admissible selection
for that request, with its own associated continuation; it does not assert
that selection or resumption occurs.

```sequent
J-Bind-Request-Case :=
  a is a fresh symbolic entry state; entry_a(s0) = entry(s0) and s0 = a
  GAMMA; L, entry_a |- request_case(B_e(a), phi(a, z), r(a, z), K_e(a, z), rho_e(a, z))
  the premises of J-Bind-Behavior hold for B_e(a), F and binding context f(a)
  under the same case's phi(a, z) and scoped facts, for every admissible h, q, state_q, deps_q, established facts entail the composition premises for rho_e(a, z, h, q, state_q, deps_q), F and f(a)
  ===>
  GAMMA; L, entry_a |- request_case(Seq_f(a)(B_e(a), F), phi(a, z), r(a, z), K_e(a, z) ++ f(a), (h, q, state_q, deps_q) -> Seq_f(a)(rho_e(a, z, h, q, state_q, deps_q), F))
```

`K_e(a, z) ++ f(a)` places the pending binding outside the initializer's local
control; it does not choose an interpreter. The
[nearest-boundary rules](first-slice-nearest-boundary-judgments.md#candidate-composition-rules)
determine where that ordered context is split into the selected capture and
outside control. If the handler is inside `e`, the binding may remain
outside its capture. `rho_e` must describe the rest of the **whole
initializer**, through its eventual normal return if any. In particular, when
the selected handler is inside `e`, it must include the selected clause's
continuation after `resume`; it is not merely the captured inner segment.
The binding follows the initializer's final result, not the reply. An outer
handler's clause continuation remains in its proper position outside any
binding frame captured by that handler.

The residual family accepts only a reply and state justified by the selected
interpreter's contract. When that residual produces another request, the
binding remains pending and the same composition applies to that request.
When the initializer eventually returns normally, the actual result and its
facts instantiate `F`. If the pending binding frame is abandoned, that frame
does not enter `F`. An inner handler can instead discard a capture that does
not include the binding and then return normally from `e`. That no-reply case
needs its own covered behavior; it is not established by the reply-indexed
family in this rule.

The rule uses the established request case and remainder; it does not inspect
their implementations or traverse their summaries to reconstruct their facts.
The original normal-return compatibility can be reused for a residual only
when its established coverage includes that residual under the applicable
reply and handler context. Otherwise that relationship remains an obligation,
and the displayed unconditional conclusion cannot be derived. The universal
premise is a symbolic proof from the certified interfaces, not a check of the
constituents per execution or a requirement that the handler resume. One
lifted case is not a coverage proof: every applicable case and unknown
behavior must remain covered. The representation and the system-level
correspondence with the operational steps remain to be established.

For example, take this schematic binding and assume an outer handler resumes
`Ask.ask` with `4`:

```ash
let x = {
    let n = perform Ask.ask ()
    n + 1
}
use(x)
```

The reply `4` enters the initializer's residual. If that residual returns
normally, it returns `5`; the binding then enters the established remainder
with `x = 5`. A subsequent request in the initializer would still have the
binding pending. If the selected handler instead discards a capture containing
the binding, this binding does not call `use`. The example assumes the
ordinary contracts for arithmetic and `use`; their definitions are outside
this slice.

If the handler is instead inside the initializer, its clause may do more work
after the resume:

```ash
let x = handle (perform Ask.ask ()) with Ask {
    ask ignored => {
        let v = resume 1
        v + 1
    }
}
use(x)
```

Here the initializer returns `2`, so the binding enters `use(2)`. The
resumed inner segment returning `1` does not yet mean that the whole
initializer has returned.

This follows the [binding steps](../../../spec/dynamic-semantics.md#bindings),
which save the pre-binding environment, and the
[request, resume and discard steps](../../../spec/dynamic-semantics.md#effect-handlers-and-completion).
The existing [nested forwarding test](../../../tests/effect_runtime.rs#L806)
illustrates restoration before a later request and subsequent clause work.
The [inner discard test](../../../tests/effect_runtime.rs#L596) illustrates
why discarding an inner capture need not abandon an outer binding. These tests
were inspected, not run, and do not establish this proposed rule.

## Candidate rule: introduce a request

For `perform E<arguments>.op operand`, the
[static request rule](../../../spec/static-semantics.md#effects) supplies the
instantiated operation domain `P`, result `Q`, and the operand's row union the
exact requested instance. The
[operational request step](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
saves the request's lexical instantiation before evaluating the operand. It
selects an interpreter only after the operand returns.

Let `I_lexical` be the source/Core effect instance, expressed in its lexical
type context. The operation's static `P -> Q` contract is instantiated at
that instance. For each actual entry, `theta` is the instantiation saved from
that entry's environment; the requested runtime instance is
`instantiate(I_lexical, theta)`. The type-level row remains expressed using
`I_lexical`. These are related views of the same request, not a claim that a
single runtime activation is fixed by the source site.

Let `Req(I_lexical, op, p, theta)` be a candidate primitive behavioral
contract for the already evaluated operand `p`, that lexical instance,
operation `op` and saved instantiation `theta`. It introduces a request case
for the corresponding runtime instance, with payload facts from the actual
operand result. If an applicable
interpreter supplies a reply `q : Q`, its residual returns that actual reply
with the reply's established dependency and resulting-context facts. `Q`
alone does not prove resource independence. The source handler, builtin or
native interpretation supplies its own reply facts; missing facts remain
premises. `Req` does not select a handler or assert that the request is
resumed.

The following candidate rule composes the certified operand with that request
contract. The primitive request judgment is a type-level account of the
existing request, not an additional Core operation. `normal_fits` requires
each applicable operand return to provide the payload and post-state premises
under which the parameterized request contract is established. The saved
`theta` preserves the lexical instantiation, not a claim that any owner named
by it remains live after operand evaluation. As above, `L` contains only
established stable facts; the operand's entry-state facts are not implicitly
available at its return. `state` and `deps` are fresh symbolic indices of the
parameterized request judgment. `a` is a fresh symbolic entry state, including
its activation, and `theta(a)` is the instantiation saved at that entry. The
predicate `entry_a(s0)` means `entry(s0) and s0 = a`. The fresh symbolic `a`
scopes over all the rule's premises and conclusion. The operand judgment and
request contract are parameterized by that same entry; this does not check the
operand separately for each activation.

```sequent
J-Perform-Behavior :=
  a is a fresh symbolic entry state; entry_a(s0) = entry(s0) and s0 = a
  theta(a) = saved_instantiation(a)
  GAMMA; L, entry_a |- operand : P ! epsilon_o ; B_o(a)
  GAMMA; L |- operation(I_lexical, op) : P -> Q
  GAMMA, p : P; L, psi(a, p, state, deps) |- primitive_request(I_lexical, op, p, theta(a)) : Q ! {I_lexical} ; B_req(a, p, state, deps, theta(a))
  state and deps are fresh symbolic indices for the request judgment
  GAMMA; L, entry_a |- normal_fits(B_o(a), psi)
  epsilon = epsilon_o union {I_lexical}
  ===>
  GAMMA; L, entry_a |- perform I_lexical.op operand : Q ! epsilon ; Seq(B_o(a), (p, state, deps) -> B_req(a, p, state, deps, theta(a)))
```

As in the binding rule, `normal_fits` must use the established operand
judgment and correlate each applicable returned payload, post-state,
dependencies, condition and activation. The inference applies only once all
premises are proved. Each request case associates `I_request` with the same
entry's saved `theta(a)`, with
`I_request = instantiate(I_lexical, theta(a))`; it does not substitute a
post-operand environment. The same entry index is carried through any operand
residual until the primitive request is introduced.
This construction must cover both of these situations:

1. If evaluating the operand requests another operation, that earlier request
   has a residual that continues the operand and then, **only if the operand
   returns**, introduces the `I_lexical.op` request. The saved `theta` remains the
   one from before operand evaluation.
2. If the operand returns normally, its actual result and relevant facts become
   the `I_lexical.op` payload. The operation may then be interpreted, captured and
   resumed or discarded under the applicable separate rules.

An operand that diverges or whose pending request frame is abandoned does not
cause the later request through that frame. The unioned row still describes
the static requirements of the whole expression; it does not claim that the
later request occurs on every path.

## Returning to the example

In the [two-context example](first-slice-request-capture-judgments.md#one-certified-computation-different-contexts),
let the already established invocation behavior for `ask ()` contain a
possible `B.ask` request with residual `rho_ask`. In the context where
`resume ()` is inside the body of the `B` handler, the candidate binding rule
combines that established request case with the established remainder:

```text
on B.ask:  residual of ask, then the pending A resume
```

The nearest-boundary and capture judgments then place that pending remainder
inside the `B` capture while the `A` owner remains outside it. The discard rule
must reject or retain the unproved outside-completion premise. When the `A`
resume follows the whole `B` handler instead, it is outside that capture. The
same callable facts are reused; each new composition establishes its own
binding and boundary relationships. The example does not assert that the
current compiler publishes or reuses these proposed certificates.

## What remains to be established

The candidate rules identify introductions and compositions, but they do not
yet prove that `Seq`, `Req`, result cases or their assumptions are expressible
and checkable in Ash. Define their type-level form and coverage, including
conditional binders, recursive or unknown behavior, actual replies and owner
activations. Establish their correspondence with the operational steps and
the in-scope narrow-correctness obligations through separate system-level
proofs. Identify every current consumer's replacement before retiring a check;
the existing graph and Core validator still have other consumers and remain
in force.

The existing [direct and helper request cases](../../../tests/effect_diagnostics.rs#L163),
[skipped outside completion](../../../tests/effect_diagnostics.rs#L210), and
[imported caller suffix cases](../../../tests/effect_modules.rs#L178) are
relevant evidence to inspect. They were not run for this record and do not
prove the proposed judgments or certificate reuse.
