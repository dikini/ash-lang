# First Slice: Facts at Normal Return

This record refines `normal_fits` in the
[request and sequencing judgments](first-slice-request-sequencing-judgments.md#candidate-rule-a-binding).
The same relation applies to an ordinary binding's initializer and to a
`perform` operand. It is a candidate type-system judgment, not current Ash
syntax, an implemented certificate or a completed soundness proof. The
[specification](../../../spec/README.md) remains authoritative for current
behavior.

## The question

Suppose a checked computation `e` may return a value to a following
computation `s`. The judgment for `s` can be checked once under symbolic
assumptions about that value and the state in which it is received. The new
composition must establish that **every relevant normal return** of `e`
provides those assumptions. It uses the established judgment of `e`; it does
not check `e` again.

For `perform`, the same question applies to the operand: every relevant
normal result must satisfy the primitive request contract's assumptions.
Operation identity, the saved lexical instantiation, type, row and later
interpreter checks remain separate premises. This is one normal-return
compatibility relation with different consumers, not a second analysis for
request operands.

The [binding semantics](../../../spec/dynamic-semantics.md#bindings) enter the
remainder only after the initializer returns normally. An operation reply can
first enter a residual computation that performs more work; it is the
initializer's eventual result, not necessarily that reply, that the binding
receives. Abandoning the pending binding frame does not supply a normal result.

## What a return case must say

The behavioral judgment of `e` needs a certified **cover** of its possible
normal returns. A return case is a relation containing, as relevant:

- the entry and activation to which it applies, with its guard and assumptions;
- the particular returned value and its ordinary type;
- that value's relevant dependency facts;
- the resulting owner, control and completion facts; and
- any locally scoped witnesses needed to justify those facts.

These fields describe one correlated case: a value from one possible return
cannot be combined with the dependency or owner state of another as if the
combination were an established exact fact. A deliberately coarser cover may
include additional combinations, but it must be treated as an upper bound and
must not justify a stronger conclusion than its facts prove. Two executions of
one lexical acquisition are not automatically one activation.

A listed case does not assert that the case occurs. The cover must include
every relevant concrete normal return; an unknown behavior must include a
suitable unknown-return possibility or leave coverage unproved. It is not an
empty set merely because no result is known. Conversely, a complete
certificate establishing that no normal return is possible makes the normal
return obligation vacuous; ordinary checking of the remainder and other
applicable rules still apply. This is not a claim that the checker can decide
termination.

Entry and return are different points. A fact such as “owner `a` is
available” at entry does not imply that it is available at return. An entry
fact may be retained as a historical fact about the entry state; only a
proved postcondition may be used as a fact about the resulting state. Stable
lexical assumptions `L` are reused where their stability has been established.

## Candidate entailment rule

Let `return_cover(B_e, Cases)` mean that the already certified behavioral
judgment `B_e` supplies a sound cover of normal-return cases. Let
`case_i(s0, v, s1, d, w)` describe one case's condition and facts for entry
`s0`, returned value `v`, post-state `s1`, dependencies `d` and locally scoped
witnesses `w`. The relation between them comes from the same case and
activation. `psi(s0, v, s1, d)` is the following computation's stated
post-return requirement; it may refer to the same entry as a historical index.
An entry-independent requirement simply ignores `s0`.

The following is a candidate logical rule. The variables in each case premise
are fresh symbolic variables: the premise establishes the implication for all
values and worlds represented by that case, rather than checking the
initializer separately for each execution. `entry(s0)` describes the entry
point; it is not an assertion that entry-state facts still hold at `s1`.

```sequent
J-Normal-Fits :=
  GAMMA; L, entry |- return_cover(B_e, Cases)
  GAMMA |- psi is well scoped for the entry, returned value, state and dependencies
  for each case_i in Cases,
    GAMMA, s0, v : A, s1, d, w_i; L, entry(s0), case_i(s0, v, s1, d, w_i) |- psi(s0, v, s1, d)
  ===>
  GAMMA; L, entry |- normal_fits(B_e, psi)
```

The rule can be applied only after its premises are established. A case's
guard is an assumption **for that case**, not a fact that the case occurs or a
globally true proposition. An outcome may be omitted from the proof only when
its infeasibility is established. If one case represents several concrete
returns, its implication must cover all of them. Hidden witnesses are local to
their case: `psi` and the enclosing conclusion cannot expose them unless an
independently valid scoped interface permits it.

The rule is schematic. It does not choose a finite case representation,
require enumerating every runtime value, or claim that Ash can decide all
implications. A missing cover, an unknown case that does not establish `psi`,
or an unproved implication leaves an obligation. It cannot justify the
unconditional conclusion. The exact form for transporting an open obligation
is not selected here.

For a request operand, the same rule establishes
`normal_fits(B_operand, psi_request)`, where `psi_request` is the established
primitive request contract's payload and post-state requirement. The
[perform rule](first-slice-request-sequencing-judgments.md#candidate-rule-introduce-a-request)
uses the same symbolic entry in the cover and in the requirement, preserving
the lexical instantiation saved at that request's entry. The return entailment
does not infer it from the post-operand environment or prove that a named owner
is still live.

## Example: a consumed capability

Inside a clause whose owner `a` is available, consider an initializer
`resume ()`. On any normal return from that initializer, the applicable
[one-shot rule](../../../spec/static-semantics.md#effects) says `a` is
consumed. A following computation can use that established post-return fact;
it cannot reuse the entry fact that `a` was available.

For example, assume the operation reply and handler answer both have type
`Unit`. In the following schematic clause, the second resume needs `a` to be
available, but the initializer's normal-return case supplies `a` consumed:

```ash
ask ignored => {
    let _ = resume ()
    resume ()
}
```

If a normal return from the first resume is possible, the implication required
by `normal_fits` does not hold. The current
[structural usage check](../../../src/elaborate.rs#L30759) rejects the
corresponding double-use case as `effect.resume-already-consumed`, even when
the first resume cannot return normally; the
[existing diagnostic test](../../../tests/effect_diagnostics.rs#L461) covers
that shape. If the first resume cannot return normally and this is established,
the normal-return obligation is vacuous. The binding's separate structural
usage premise still requires the remainder to accept the first resume's
outgoing `consumed` state. Since the second resume requires `available`, the
composition is rejected without deciding whether the first resume returns.
The premise composes established usage judgments; it does not check either
constituent again. This candidate account does not claim that current Core
already carries this proof.

## Example: same ordinary type, different dependency facts

A resource-dependent closure and an independent closure can both have type
`Unit -> Int`. If a following boundary needs to establish that the returned
closure does not depend on a particular closing owner, the ordinary type alone
cannot prove its assumption. A complete return case for the independent
closure can establish the needed fact; a feasible dependent case does not.
An unknown case remains an obligation unless its own facts establish
independence or its infeasibility is proved.

The [generic-cell snapshot case](../../../tests/resource_scope_typing.rs#L1614)
illustrates this distinction. An earlier read returns an independent closure;
a later replacement retains the outer cell, so a later read can return a
dependent closure of the same ordinary type. The earlier snapshot's fact is
not changed by the replacement, and it cannot be substituted for the later
read's fact. The relevant
[resource rules](../../../spec/static-semantics.md#generic-cell-foundation)
concern the actual returned value and activation.

## Before and after

| Existing producer or consumer | Fact needed at the boundary | Candidate disposition |
| --- | --- | --- |
| [Source continuation usage](../../../src/elaborate.rs#L30759) and [Core scope analysis](../../../src/core/validate.rs#L12690) | A capability's incoming and outgoing usage, including sequencing and paths. | Reuse the initializer's established usage facts to establish the remainder's incoming assumptions; compose the remainder's established outgoing usage separately. The current source and Core checks are distinct paths; no individual check is yet shown removable. |
| [Value dependency analysis](../../../src/core/capture/value.rs#L7303) and [resource result checking](../../../src/core/capture/value.rs#L6184) | Dependencies of a particular possible result relative to the owner it crosses or closes. | Supply established, appropriately scoped return facts and prove the new boundary's independence premise. The full mapping of unknown behavior and every consumer remains open. |
| [Request and reply analysis](../../../src/core/capture/value.rs#L5120) | Actual reply facts feed the suspended request, which may subsequently produce a different result. | Preserve the established reply, residual and eventual-return relationships; apply the same normal-return entailment only when the operand or initializer actually returns. |

The current graph and Core validator have other consumers and remain in force.
These candidate judgments do not yet decide their representation or prove
which checks can be retired. The existing tests cited above were inspected,
not run for this record. Soundness of the return cover, entailment,
substitution and sequencing against the operational semantics requires
separate system-level justification; successful type checking must then be
strong enough, with the other slice rules and stated premises, for the narrow
program-correctness guarantee.
