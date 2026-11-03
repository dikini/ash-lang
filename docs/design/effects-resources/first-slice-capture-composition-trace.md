# First Slice: Request and Capture Composition

This working trace covers E10 in the
[rule catalogue](first-slice-catalogue-and-map.md#effect-handler-and-control-rules).
It connects the request and handler rules with the separate
[one-shot usage](first-slice-continuation-use-trace.md) and
[discard ownership](first-slice-discard-ownership-trace.md) traces. It does not
define general function typing, add control syntax, or claim a complete
type-system calculus. The specification remains the authority for current Ash.

## Operational relationship

The [request and completion transitions](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
evaluate the request operand and use its saved lexical instantiation to find
the nearest accepting boundary. A source-handler selection moves the selected
handler and intervening control into a live clause-owned capture; the clause
runs outside that capture. A direct request in the clause therefore bypasses
the moved handler. A builtin cell or native interpreter follows its own
specified branch rather than introducing an ordinary source clause.

Resume consumes its matching live capability and restores the selected capture
in its original order above the clause continuation. The restored computation
continues from the request; it does not repeat the prefix that preceded the
request. Discard consumes the capability and starts closing its owned capture,
subject to separate ownership, completion, interpreter and row requirements.
The two operations do not have the same obligations.

The [static rules](../../../spec/static-semantics.md#effects) require this
relationship to account for requests made by known callees and for the caller's
control. An outward request can encounter live completion owners, including
owners introduced by caller context. A handler installed inside a live clause
does not capture the outer owner for requests confined to its own body. Unknown
relevant higher-order behavior can prevent a discard proof; uncertainty alone
does not reject resource-free resume-only code.

## What current verification does

| Current check | Inputs and result | Judgment requirement |
| --- | --- | --- |
| [Module capture checking](../../../src/elaborate.rs#L5791) | Completed local roots, imported global and method summaries and applicable selected-method routes feed row solving and `check_builder`. Successful checking publishes callable capture summaries. | Reuse the established facts of an imported callable and selected declaration; preserve their subject, assumptions and instantiation. A missing summary is not a fact that the callable is pure or independent. |
| [Shared graph entry points](../../../src/core/capture.rs#L3174) | `check_builder` checks source-built roots with imports and routes; `check_nodes` can analyze Core nodes. Cleanup-row inference is a separate query using the same graph engine. | Record the facts established by each query and its consumers. Sharing an engine does not prove two queries are the same judgment. Existing summaries are not yet the complete typed certificates required by this design. |
| [Boundary matching](../../../src/core/capture/control.rs#L5966) | For an event and active control, specialize relevant request and boundary labels in their own contexts. Track possible matching and possible outward continuation when equality or targets are uncertain. Cell matching also accounts for possible actual target owners. | The selection rule must use exact declaration identity and applicable argument equalities, preserve lexical instantiation, and account for each relevant possible nearest selection. Different type parameters are not proof of inequality after instantiation. |
| [Request continuations](../../../src/core/capture/control.rs#L6156) | Follow each possible selected source handler, resource or native interpreter, as well as possible outward escape. Source selection checks the crossed payload and follows matching operation clauses. | Each handler or boundary composition must establish its own payload and control premises from the request and context judgments. Static possible selections are distinct from the single boundary selected in an actual runtime step. |
| [Clause capture](../../../src/core/capture/control.rs#L6752) | For a source clause, the analysis moves the selected boundary and intervening prefix into a capture and starts the clause outside that boundary. | Introduce the clause-local owner and its capture relationship while preserving outside obligations and the ordered boundaries in the captured segment. No use of a declaration's interface may reopen its body to reconstruct these facts. |
| [Resume restoration](../../../src/core/capture/control.rs#L7458) | Restores the selected captured control above the continuation following resume. | The resume rule must preserve the relationship and its resource/completion facts, consuming only the selected one-shot availability. The details of a graph copy are not the required logical representation. |
| [Strict discard analysis](../../../src/core/capture/control.rs#L7181) | Rejects a selected unknown event when strict safety is required and checks the selected owner and close. The [outside-clause path](../../../src/core/capture/control.rs#L5689) can expose an abandonment that skipped a completion. | Safety must be proved for every relevant possible selected capture; unknown is not a successful proof. Apply the separate discard premises only where discard occurs. |
| [Core capture validation](../../../src/core/validate.rs#L13803) | After ordinary Core checks, a conditional gate invokes capture reconstruction on assembled Core with no imported summary inputs. | The desired checker consumes established typed constituent judgments and checks only the new composition. Exact repeated judgments and all existing Core consumers remain to be accounted for before replacing current validation. |

## Facts introduced, preserved and discharged

The type-system account needs to express the following relationships without
assuming an effect row is a complete control contract:

1. A computation may request a particular operation at a particular exact
   instance, under stated type and row assumptions. Its request can arise in
   a checked opaque callable and must be usable without rechecking that body.
2. The enclosing context establishes which boundaries may be selected and
   which control, resources and completion obligations each selection captures
   or leaves outside. A polymorphic context may have multiple possible
   selections until its equality facts are established.
3. Source-handler selection introduces a local capability and its ownership
   relationship. The selected handler leaves the active clause context while
   its identity and control remain in the capture; outside obligations remain.
4. Resume eliminates that capability's one-shot availability and re-establishes
   the captured control for continuation. Discard instead requires a proof of
   safe owned close and preserves the surviving context. Their separate
   premises are not inferred from the mere occurrence of the effect.

These are candidate judgment requirements, not an assertion that the current
source callable type already contains all of them. A declaration can be
checked under explicit assumptions, and its users must establish those
assumptions for their new compositions. An unproved premise does not become
true because an opaque boundary hides its implementation.

## Correctness and outstanding rule design

The [request and capture judgments](first-slice-request-capture-judgments.md)
develop a candidate boundary, composition and per-check disposition from this
trace, including a comparison of the same computation in two contexts.

The rules need to explain why well-typed composition cannot produce the
in-scope invalid captures, missing or repeated completion, or unsafe discard
described by the operational semantics, under the stated boundary and
environmental premises. This requires more than proving effect-row membership
or structural one-shot use. It also does not establish narrow correctness for a
whole program without the other applicable rules and separately justified
system-level correspondence.

The detailed rule still needs a sufficient account of request and context
facts, equality and possible selection under polymorphism, their composition
through opaque callable interfaces, and how the resulting capture fact is
supplied to resume and discard. Trace each existing graph output and consumer
against that account before retiring a check. The [polymorphic coincidence](../../../tests/effect_typing.rs#L205),
[known callable](../../../tests/effect_typing.rs#L260),
[restored-handler](../../../tests/effect_typing.rs#L326), and
[unknown-call](../../../tests/effect_diagnostics.rs#L233) tests are relevant
evidence to inspect; they were not run for this trace and do not prove
completeness.
