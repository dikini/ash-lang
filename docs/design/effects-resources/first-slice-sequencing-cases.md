# First Slice: Sequencing Behavior Cases

This record develops the individual behavior cases needed by the
[binding judgment](first-slice-request-sequencing-judgments.md#candidate-rule-a-binding).
The rules are candidate type-system rules, not current Ash syntax or an
implemented checker. They compose established judgments for a monomorphic
single-variable binding. The [specification](../../../spec/README.md) remains
authoritative for current Ash.

## What the rules compose

For `let x = e; s`, let `B_e` be the established behavior of `e`, and let
`F(v, state, deps)` be the one established judgment for `s` under its symbolic
value and post-state assumptions. The pending binding context `f` saves its
pre-binding lexical environment and the relevant activation, owner and
completion facts. A case is an upper bound under its own guard and correlated
facts, not a claim that execution reaches that case. Entry, local witnesses,
payloads, states and dependencies must not be mixed between cases or
activations.

The [binding judgment](first-slice-request-sequencing-judgments.md#candidate-rule-a-binding)
checks ordinary types, freshness and row union, `normal_fits`, and the
structural usage interface. These premises are required even when an
initializer has no normal return. The rules here describe the resulting
behavior; they do not relax those typing premises or choose a concrete
representation for a behavior contract.

Write `case(B, phi, outcome)` for an established covered alternative under
guard `phi`, and `continue_under(B, phi, F)` for the conditional use of the
already established remainder. These schematic judgments preserve `phi` and
its locally scoped witnesses. Their implementation must not inspect or
reanalyze `e` or `s`. One alternative is not a coverage proof; the combined
contract must cover every relevant alternative, including unknowns.

## Normal return

When a covered initializer return supplies `v`, its post-state `state` and
its dependencies `deps`, the binding applies `F` to those correlated facts.
The rule uses the existing `normal_fits` proof to establish the assumptions
under which `F` was checked. It uses the binding's saved environment plus the
new binding, not the environment in which the initializer happened to return.

```sequent
Seq-Return :=
  GAMMA; L, entry |- case(B_e, phi, return(v, state, deps))
  GAMMA; L, entry |- normal_fits(B_e, psi)
  F is the certified conditional behavioral projection of s under psi
  the remaining premises of J-Bind-Behavior hold
  ===>
  GAMMA; L, entry |- continue_under(Seq_f(B_e, F), phi, F(v, state, deps))
```

`normal_fits` establishes an implication for every covered return; it does not
make `phi` globally true or prove that `e` terminates. The resulting behavior
of `F` remains guarded by that same return case. This corresponds to
[`E-Let-Continue`](../../../spec/dynamic-semantics.md#bindings).

Once `F` is entered, each of its already established cases contributes a
case of the composed behavior. `chi` is the remainder case's own condition;
the implication is conditional on the same initializer result, witnesses and
facts that allowed `F` to be entered. `outcome` retains the remainder case's
actual value or request, local control, residual, dependencies and other
applicable facts. This rule does not assert that either guard occurs.

```sequent
Seq-Remainder-Case :=
  GAMMA; L, entry |- continue_under(Seq_f(B_e, F), phi, F(v, state, deps))
  GAMMA; L, entry, phi |- case(F(v, state, deps), chi, outcome)
  ===>
  GAMMA; L, entry |- case(Seq_f(B_e, F), phi /\ chi, outcome)
```

The pending binding has already been discharged: a request in the remainder
does not capture that binding frame or re-enter `e`. The rule carries normal
returns, requests and their residuals, non-return, failures and unknown cases
according to their respective contracts; it cannot turn unknown behavior into
an absence fact. Witnesses remain locally scoped. Failure disposal and any
effects it produces still need their own applicable covered behavior.

## Requests and their continuations

For a request during `e`,
[`J-Bind-Request-Case`](first-slice-request-sequencing-judgments.md#candidate-rule-carry-a-request-through-a-binding)
preserves the established request case and puts `f` outside the initializer's
local control. Boundary selection determines what is captured. If an
admissible reply continues the initializer, its whole residual behavior is
composed with `F`; `F` begins only at an eventual normal result. Further
requests retain the binding context. The request case and residual's
composition premises remain conditional on their original case, actual reply
and interpreter context.

This rule covers the reply branch. When an inner handler discards without a
reply, its handler judgment must instead supply the behavior of its clause and
eventual handler result. If that produces a normal result of `e`, `Seq-Return`
applies. If the discarded capture contains `f`, that binding's remainder is
not entered. The capture and discard rules determine which situation applies;
discard alone is not proof that the whole initializer fails to return.

## Non-return, failure and unknown behavior

An established non-return alternative of the initializer does not enter the
binding's remainder. This is a behavior fact, not permission to ignore the
structural usage premise for that remainder. `nonreturn` includes only the
non-return behavior the established case covers; it is not a synonym for a
failure or an unknown result.

```sequent
Seq-Nonreturn :=
  GAMMA; L, entry |- case(B_e, phi, nonreturn)
  the premises of J-Bind-Behavior hold
  ===>
  GAMMA; L, entry |- case(Seq_f(B_e, F), phi, nonreturn)
```

The current semantics also has internal failures. If a covered initializer
outcome is a failure, the binding does not enter `F` through a successful
return. `fail_before_remainder` records the originating failure, not a promise
that the eventual host report has the same reason: failure disposal and its
own failures remain governed by their applicable semantics. The rule cannot
silently relabel failure as divergence or prove the whole program safe.
Whether the final type system excludes every relevant internal failure is a
separate, unresolved narrow-correctness obligation.

```sequent
Seq-Failure :=
  GAMMA; L, entry |- case(B_e, phi, failure(reason))
  the premises of J-Bind-Behavior hold
  ===>
  GAMMA; L, entry |- fail_before_remainder(Seq_f(B_e, F), phi, reason)
```

This is an intermediate fact, not a complete final-outcome case. The
composition must also cover the applicable failure disposal, observations and
possible later failure; this record does not yet define that behavior.

An unknown alternative must continue to cover every relevant possibility it
represents: return into the pending remainder, a request with that remainder
pending, non-return or a possible failure. It is not evidence that any one of
these happens, or that any is absent. If its interface cannot establish a
required composition premise, that premise remains an obligation and no
unconditional binding judgment follows. No new rule can infer safety from a
missing summary.

## Coverage and evidence

The cases above and the linked request and handler rules are obligations on a
single composition; they are not a choice to analyze an initializer once per
case. The checker must reuse its certified behavior and the single conditional
remainder judgment. If the initializer has several alternatives, it must
prove the applicable compatibility of each represented alternative, while
preserving their guards and correlations. How Core represents these contracts
and how the checker derives the necessary coverage and entailments are still
open. Until those are established, the rules do not justify retiring a current
analysis.

The operational account is the [binding](../../../spec/dynamic-semantics.md#bindings)
and [handler](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
steps. Current [Core control construction](../../../src/core/capture.rs#L2214)
and [linked validation](../../../src/core/validate.rs#L13857) reconstruct
relationships from Core; the candidate rules state how to use already
established relationships instead. Their coverage and correspondence with
those steps, and the full treatment of failures, require separate
system-level justification.
