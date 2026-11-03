# First Slice: One-Shot Continuation Use

This working trace refines V3 in the
[verification audit](first-slice-verification-audit.md#continuations-and-closing-control).
It maps one existing check from operational behavior through source and Core
verification to candidate type judgments. It does not define a new Ash
calculus or establish the full effects-and-resources slice. Current semantics
come from the specification; the proposed judgment below is design work.

## Behavior and correctness obligation

On a source-handler request, the
[operational semantics](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
moves the selected handler and intervening control into a live clause-owned
capture. `resume` requires the matching owner to be live before evaluating its
operand. After the operand returns, the owner must still be live; resume then
marks it consumed, restores its captured control in lexical
order, and retains the surrounding clause continuation. A consumed clause may
return. There is no current transition that makes the same owner live again.

The corresponding [static rules](../../../spec/static-semantics.md#effects)
give an ordinary clause a local capability `resume(Q, A, epsilon_out)`. A
normally completing clause must consume it exactly once with `resume` or
`discard`; the operand of `resume` must leave it available before `resume`
consumes it. The clause cannot capture the enclosing capability in an
anonymous function, recursive member, supplied method or nested handler
clause. The private Store-associated `retain` form is outside this trace; its
current usage is a boundary that must remain supported by its own rules.

The type-system account must rule out reaching a resume with no matching live
owner, using the same one-shot owner twice, or normally leaving an ordinary
clause without its required completion. It must preserve the matching owner
and captured control facts across the operand. It must also type the operand
at `Q`, the resume result at `A`, and its effects at `epsilon_out`.

These obligations are necessary, not sufficient, for narrow program
correctness. They do not establish that discarded control is safely closable,
that resource and cleanup obligations are respected, or that all program
boundaries and execution failures have been accounted for. Those are separate
premises and rules in the slice or established outside it. The execution
guarantee depends on all applicable rules and the separately justified
correspondence between typing and operational semantics.

## Current source and Core checks

| Check | Input and result | Meaning and disposition |
| --- | --- | --- |
| [Source clause usage](../../../src/elaborate.rs#L30759) | A resolved clause, its owner and initial `available` state; it visits expressions in evaluation order and requires final `consumed`. A missing use is `ResumeNotConsumed`, a second use is `ResumeAlreadyConsumed`. | Candidate usage judgments must establish the same one-shot relationship. The current traversal is an analysis to replace for the in-scope path, not a new traversal the type system must reproduce. |
| [Source branching](../../../src/elaborate.rs#L30964) | Check the match scrutinee first; give each arm the same incoming state and require equal outgoing states. Mismatch is `ResumeNotConsumed`. | A match rule must compose the scrutinee judgment with each certified arm judgment and establish a common outgoing usage fact. |
| [Source barriers](../../../src/elaborate.rs#L30994) | Reject an occurrence of the outer owner in a nested function, recursive member, supplied method or nested handler clause as `ResumeCapture`. A nested clause's own owner does not consume the outer one. | The enclosing capability must not be assumed available inside these opaque boundaries. The relevant checked boundary judgment must establish the absence of that capture; ordinary function typing stays outside this slice. |
| [Source resume typing](../../../src/elaborate.rs#L14147) | Resolve an active matching owner and check the operand against its input type; create a resume node marked consumed and give it the handler answer type. The initial node row comes from the operand. | The handler's later row processing determines the completed output contract; the initial operand row alone is not the final resume contract. Structural usage is checked separately. |
| [Core scope and usage](../../../src/core/validate.rs#L12552) | Bottom-up scope requirements track owner keys and usage counts. Branches must agree; a clause must discharge its own owner exactly once and cannot carry a foreign continuation. Free owners at roots and owner capture across Core barriers are rejected. | Core currently reconstructs structural usage. A certified constituent judgment must supply its usage facts to the new composition instead. The treatment of Core-only barriers and each existing consumer still needs a complete correspondence audit. |
| [Core resume contract](../../../src/core/validate.rs#L17059) | Match handler and owner contract; check the consumed marker, operand type, answer type, exact handler output row and operand-row inclusion. | A typed resume rule needs each premise. A consumed marker by itself is not a proof that all paths use the capability correctly. |

The Core analysis and source traversal use different representations and
operate on different inputs. They establish overlapping structural facts, but
the per-constituent correspondence and the replacement of every Core check are
not yet established. The current [Core validation boundary](../../../spec/elaboration.md#validation-boundary)
remains in force until the governing artifacts change.

## Candidate usage judgments

Write `U(k, e, s, t)` for the judgment that fragment `e`, checked under the
capability identity `k` in usage state `s`, has structural outgoing usage
state `t` for checking subsequent expressions. Here `s` and `t` are
`available` or `consumed`. This state is determined by the structural rules
even if `e` cannot return normally. When it does return normally, the state
must also describe the capability at that return.
The judgment is conditional on its stated input state and other typing and
scope assumptions. It is metanotation, not proposed source syntax or a choice
of certificate representation. Other owners and their facts are accounted for
by their own applicable judgments; this notation does not assert they can
never change while `e` runs. For the same one-shot owner, the rules must never
derive `consumed` to `available`: no construct restores its availability.

The following candidate rules describe the one-owner usage component. Their
premises are established judgments of the constituents, not instructions to
recheck their implementations. They do not replace ordinary typing, effect
checking, or discard safety.

For a construct that makes no use of `k`, its usage judgment preserves the
incoming state, subject to its other applicable rules:

```sequent
U-Preserve :=
  an established applicable judgment says e has no use of k
  ===>
  U(k, e, s, s)
```

For a strict sequence of two constituents, the second receives the first's
structural outgoing state. This premise applies even if the first has a
proved empty normal-return cover. `sequence(e1, e2)` names evaluation order
here; it does not propose a new Ash expression:

```sequent
U-Sequence :=
  U(k, e1, s, m)
  U(k, e2, m, t)
  ===>
  U(k, sequence(e1, e2), s, t)
```

For a match, `scrutinee` is checked first and each arm must have the same
incoming and outgoing state. Exhaustiveness and pattern typing are separate
premises supplied by the applicable match rules:

```sequent
U-Match :=
  U(k, scrutinee, s, m)
  for each arm_i, U(k, arm_i, m, t)
  ===>
  U(k, match(scrutinee, arms), s, t)
```

For `resume value`, its operand must leave `k` available, after which the
resume consumes it. The active matching contract, operand type and effect
constraints remain separate premises of the full resume typing rule:

```sequent
U-Resume :=
  U(k, value, s, available)
  k is the active capability for this resume
  ===>
  U(k, resume value, s, consumed)
```

For an ordinary `discard`, usage alone goes from available to consumed. The
full discard rule additionally requires owned-close safety and the residual
close row; this usage rule does not grant permission to discard:

```sequent
U-Discard :=
  k is the active ordinary capability for this discard
  ===>
  U(k, discard, available, consumed)
```

At the handler boundary, the clause-local capability is introduced as
available and the handler must establish a clause usage judgment ending in
consumed before discharging that local capability. Its operation signature,
answer type, handler row, clause pattern and capture/context obligations are
additional premises. A nested clause introduces its own capability rather than
using its enclosing clause's capability.

An opaque boundary that cannot capture `k` needs an established no-capture
fact under its own applicable rules. It is not enough to omit `k` from the
boundary's ordinary value type. For the first slice, decide how this fact is
expressed and supplied without reopening a certified function, method or
other opaque constituent. This is an outstanding design obligation.

## Consequences for checking and reuse

The source checker may infer usage judgments, but complete Core types must
carry the applicable information. The exact judgment representation and how
the Core type system carries or recovers it from already certified evidence are
open. A constituent's judgment can be conditional on its input usage state;
the enclosing rule establishes that state and composes its result. It must not
revisit the constituent to infer usage again. An unproved input or boundary
premise is not a successful unconditional judgment.

The [completion-site rules](first-slice-close-derivation-rules.md#introduce-references-to-pending-completion)
extend the same structural derivation with a guarded cover of where this
owner's completion can be carried. The cover is needed when an inner discard
captures a pending outer resume. It is produced with the usage judgment and
reused at the new control boundary, not reconstructed by a second inspection.
Its possible sites do not establish that any particular site executes.

Before retiring an existing source or Core check, record which new judgment
establishes its result, which consumer uses it, and how the checked Core
composition establishes the remaining premises without rechecking any
certified fragment. This trace identifies a candidate disposition, not an
implemented replacement. In particular, no-capture evidence, identity and
type/row contract checks, discard safety, and Core-only scope barriers still
need their full mappings.

Existing [usage diagnostics](../../../tests/effect_diagnostics.rs#L461) cover
zero, double, unequal branch and captured uses;
[effect typing](../../../tests/effect_typing.rs#L497) includes branch usage.
These are examples for subsequent validation, not a completeness proof. They
were inspected but not run for this documentation trace.
