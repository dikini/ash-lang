# First Slice: Discard Ownership and Completion

This working trace refines V4 in the
[verification audit](first-slice-verification-audit.md#continuations-and-closing-control).
It follows the [one-shot usage trace](first-slice-continuation-use-trace.md):
consuming a capability is necessary, but does not by itself establish that its
capture can be discarded safely. This trace covers ownership and completion.
It records cleanup interpreter compatibility and the close effect row as
separate premises; their internal rules are not developed here. Current Ash
semantics come from the specification, not these candidate judgments.

## Operational behavior

The [discard transition](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
finds the matching live clause owner and splits its current clause continuation
from the capture it owns. After ownership validation and initial preparation
succeed, it consumes that owner, retains the clause continuation and outer
control, and schedules owned closing before returning `Unit` to the clause.
It does not resume the abandoned expressions or restore captured source
handlers.

The owned close contains the selected capture's owners in structural
innermost-to-outermost order. A live clause inside that capture contributes
its own capture recursively at that position. A consumed clause contributes no
further capture. A non-owning association is not authority to close an outer
owner. An armed cleanup in the owned close may run; a running cleanup or
unfinished close cannot be abandoned. Outside completion obligations must
remain reachable. See the [static discard rules](../../../spec/static-semantics.md#effects)
and [cleanup rules](../../../spec/static-semantics.md#scoped-cleanup-actions).

The current transition is conditional on successful initial preparation. The
specification also describes internal failure before or during close. This
trace does not classify those failures as external events or claim that current
typing already proves the intended narrow no-error guarantee.

## Facts needed by a composition

At a discard point, the type-system account must distinguish:

1. The available ordinary capability and the particular capture it owns,
   including how each possible request and handler selection supplies that
   relationship.
2. The recursively owned completion obligations and their structural close
   order, including the phase of each relevant cleanup or close.
3. Completion obligations outside the owned closure and the surviving control
   needed to reach them. Merely omitting an outside owner from the close list
   does not prove its scheduled completion remains reachable.
4. The obligations of any close actions: their compatible interpreter
   contexts, effects and other applicable resource facts. These are separate
   premises here, not consequences of capability consumption.

The identity and relevant facts of opaque constituents must be available from
their established judgments or as conditional boundary premises. The new
composition establishes the relationship between those facts; it does not
inspect the verified constituents again. A possibility that cannot be proved
safe remains an obligation or causes rejection at an unconditional use.

## Current checks

| Check | Inputs, result and relevance | Candidate disposition |
| --- | --- | --- |
| [Source discard elaboration](../../../src/elaborate.rs#L14049) | Requires an active matching owner, rejects a private Store-associated root, creates a consumed discard node of type `Unit`, and defers the close row. | The full discard rule needs those local premises and result. Structural consumption and a deferred row are not proof of ownership safety. |
| [Request and control discovery](../../../src/core/capture/control.rs#L5768) | Uses known control, callable summaries and context to find possible requests, selected handlers and captured continuation relationships. Relevant unknown behavior can prevent a discard proof. | Constituent judgments must supply the possible requests, control relationships and assumptions; composition must account for every relevant possible selection. The exact sufficient type-level facts are not yet designed. |
| [Completion selection](../../../src/core/capture/control.rs#L7181) | Selects matching clause owners; invalid escaped or consumed owners fail. Strict discard rejects an unknown selected event. The stricter actual-capture authentication mode also requires an unambiguous instance, effect and request port. | Match the selected capability and its capture in the judgment. Do not generalize the authentication mode's extra checks into unconditional source rules. |
| [Owned close traversal](../../../src/core/capture/control.rs#L7032) | Follows the capture, recursively accounts for live clause captures, schedules armed cleanup and rejects running cleanup, unfinished closing and retained private work in strict checking. | State ownership, structural order and completion-phase premises. Frame and graph details describe the current analysis, not required type syntax. |
| [Outside completion](../../../src/core/capture/control.rs#L5689) | In strict analysis, reaching an unconsumed clause after an abandonment reports unsafe discard with a completion owner. | Prove that the new composition preserves outside required completion, including its path through surviving control. The cited check is one traced rejection path, not a claim that every outside-owner path has been audited. |
| [Core reconstruction](../../../src/core/validate.rs#L13803) | Under its capture-analysis gate, the current validator reconstructs relationships from assembled Core and reports unsafe or invalid cases. | A replacement must use the relevant certified judgments and check the composition's new premises. The exact repeated facts and all affected consumers still need mapping; current Core validation remains required. |

The shared graph also serves other resource and control queries. Identifying a
replacement judgment for discard does not authorize removing the graph or its
outside consumers.

## Candidate judgments and discard rule

The following names describe obligations a typing rule must establish; they
are not Ash syntax, a selected representation, or a complete formalization.
Each judgment has a subject, context and assumptions that an eventual rule
must make explicit. The current `T-Discard` rule already states the safety
conditions at a high level; the task is to refine its premises into facts that
can be established compositionally.

- `Owns(k, capture)` relates the available capability to its actual capture.
- `ClosePlan(capture, plan)` accounts for the recursively owned obligations
  and their structural close order. It distinguishes a live nested clause from
  an already consumed one, and ownership from non-owning association.
- `CompletionSafe(plan, outside)` establishes that closing the plan does not
  abandon running or unfinished work and that required outside completion
  remains reachable through the surviving control.
- `Interpretable(plan, context)` and `CloseRow(plan, context, epsilon)` state
  the separately required action-interpreter and residual-effect facts.

Given those facts and the ordinary typing premises, a candidate discard rule
would consume `k`'s availability, establish its consumed state and return
`Unit ! epsilon`, with the close plan scheduled before the remaining clause
continues. The close's owned obligations are scheduled, not all established as
already completed by the typing step. The rule must preserve the stated
outside facts and make any assumptions visible in its conclusion. On
successful runtime close, the owned obligations complete as specified. The
[usage rule](first-slice-continuation-use-trace.md#candidate-usage-judgments)
establishes only the capability-state part of this result.

The candidate names do not themselves solve the problem. The design still
needs rules that derive the ownership and completion facts from certified
constituents, cover all possible relevant selections, and give the checker a
workable way to establish or reject each premise. The operational and typing
rules must be connected by the separately established system-level argument;
tests alone do not establish that connection.

## Cases the rules must distinguish

- A nested live clause inside the capture contributes its owned capture;
  the same nested clause after consumption does not contribute it again.
- An armed cleanup in the owned capture may be scheduled, while an already
  running cleanup or unfinished close must not be abandoned. A running cleanup
  outside the selected capture does not by itself prevent an action-local
  discard if its completion remains reachable.
- An owner can be outside the close plan yet still be endangered if its
  scheduled completion lies in abandoned control. The existing
  [outer-clause case](../../../tests/effect_diagnostics.rs#L210) rejects such
  a discard; [owned nested-clause cases](../../../tests/effect_diagnostics.rs#L163)
  include accepted closes.
- An unknown relevant higher-order request can leave discard safety unproved;
  this uncertainty alone does not reject resource-free resume-only code. See
  the [unknown-call cases](../../../tests/effect_diagnostics.rs#L233).
- An armed and a running cleanup have different outcomes in the existing
  [cleanup cases](../../../tests/cleanup_typing.rs#L95). Interpreter
  compatibility and row agreement still need independent checks even for an
  owned, armed cleanup.

These tests were inspected, not run for this document. They illustrate the
requirements and do not prove completeness. The next audit must trace how the
required ownership and outside-completion facts are established from each
kind of request and opaque boundary before deciding which checks to replace.
