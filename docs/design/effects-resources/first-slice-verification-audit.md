# Effects and Resources: Verification Audit

This working audit belongs to [DN-0061](../DN-0061-effects-and-resources-first-slice.md).
It follows the [rule catalogue and implementation map](first-slice-catalogue-and-map.md)
from checks performed by the compiler to the premises and conclusions a
replacement type system must express. The [judgment requirements](first-slice-judgment-requirements.md)
describe their intended compositional use.

This is a traced starting inventory, not a completed audit or a set of formal
typing rules. Code describes current checks; the specification defines current
language behavior. A discrepancy or unclassified check must remain visible
until resolved. No compiler check can be removed merely because a similar
statement appears in this document.

## Audit method

For each check, record its subject and assumptions, the predicate actually
checked, its result or rejection, the applicable specified rule, and the
candidate judgment or premise that accounts for it. Follow its consumers and
record the proposed replacement before removing it. Distinguish:

- a language obligation from a traversal, data structure, work budget or other
  implementation mechanism used to check it;
- a fact about a constituent from the new premises of a composition;
- an inferred fact from a conditional assumption or an unproved obligation;
- checks that share a graph from checks that establish the same judgment about
  the same subject under the same assumptions.

The new rules must justify the relevant accepted and rejected programs, not
copy the existing algorithms. Where an existing check is conservative, compare
it with the specified obligation before deciding whether its exact behavior is
required. Classify mismatches instead of silently adopting either the code or
the candidate rule. Ordinary data and function checking remain outside this
slice; their established judgments and outstanding assumptions are inputs.

## From operational behavior to type judgments

For each in-scope operational rule or specified transition, trace:

1. Its input configuration and premises, the step or steps it permits, and its
   resulting configuration and observations. Include behavior specified in
   prose, and identify any missing or inconsistent operational rule.
2. The facts needed to justify that behavior: what becomes available, what is
   used or discharged, and what remains true. Identify each fact's subject,
   scope and assumptions. Record facts from outside the slice as established
   premises or outstanding obligations.
3. The existing verification that establishes or checks those facts, with its
   inputs, outputs and consumers. Distinguish a missing check from one not yet
   traced, and distinguish an implementation mechanism from its obligation.
4. The candidate type judgments and rules that express the same requirements:
   their premises, the facts introduced into their conclusions, the facts
   eliminated or discharged, and the facts they preserve. A single rule may
   introduce one kind of fact and eliminate another. Relate the static rule to
   the operational behavior it accounts for; type checking does not execute
   the transition.
5. How the checker obtains or infers the premises and reuses certified
   constituent judgments; which new composition premises it checks; and the
   disposition of each existing check once its consumers are covered.

An introduction establishes a fact under the rule's premises. In this account,
elimination discharges or removes a tracked fact from the applicable judgment
when the construct uses or closes it. The rules must state which facts have
that usage discipline and which are preserved or may be reused: using an
ordinary proposition to derive a consequence does not inherently consume its
proof. Removing a capability from a local judgment also does not remove facts
that remain applicable outside its scope. These distinctions must come from the
semantics and rules, not from the name of a construct.

### Worked trace: request and resume

The following trace illustrates the method; it is not a complete new typing
rule or a proof of correspondence. The current
[request and resume transitions](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
and [effect typing rules](../../../spec/static-semantics.md#effects) are the
authority for present behavior.

| Aspect | Request selects a handler | Resume restores the captured control |
| --- | --- | --- |
| Operational step | `E-Request-Select` finds the nearest accepting handler and moves that boundary and intervening control into `live(captured)`; the selected clause runs outside that segment. | `E-Resume-Restore` consumes the matching live owner, restores the captured segment in its original order and leaves the clause owner marked consumed. |
| Facts to account for | A fresh clause capability is available and owns the selected capture. The moved handler is not an active enclosing handler for direct clause requests; its identity and control remain in the capture. Outside control remains outside. | The capability must still be available after checking the resume operand. Its one-shot availability is discharged, the captured control's restoration obligations become applicable, and the surrounding clause control remains. |
| Current verification | [Handler and clause checks](../../../src/elaborate.rs#L14550), [structural capability usage](../../../src/elaborate.rs#L30759) and the capture analysis check different parts of this relationship. | [Resume elaboration](../../../src/elaborate.rs#L14147), structural usage and the [Core resume contract](../../../src/core/validate.rs#L17059) check the operand and capability contract; control analysis accounts for capture relationships. |
| Required typing account | The handler rule introduces the clause-local capability and its assumptions and accounts for the captured and outside control. It must preserve what the clause needs without exposing the captured implementation. | The resume rule uses the certified operand judgment and available capability, discharges one-shot availability and establishes the answer and effect contract. It must account for restored control without rechecking a certified constituent. |

The existing structural rule calls the resulting capability state `consumed`;
eliminating availability does not mean erasing that state or the facts needed
to finish the clause. Likewise, the handler's static removal of an exact effect
from a body row and the operational movement of a handler into a capture are
related but distinct facts. Their correspondence still needs to be established.

## Trace index

Each catalogue rule has a trace below. These are starting traces through the
specified behavior, current checks and candidate judgments; an entry is not a
claim that every implementation branch has been audited or that its rules are
complete. Follow the unresolved items in each trace before replacing a check.

| Catalogue rule | Trace |
| --- | --- |
| E1–E3: effect declarations, instances and rows | [Effect and handler trace](first-slice-effect-handler-trace.md) |
| E4–E6: request, handler and selection | [Effect and handler trace](first-slice-effect-handler-trace.md); [capture composition](first-slice-capture-composition-trace.md) |
| E7: resume | [One-shot use](first-slice-continuation-use-trace.md); [capture composition](first-slice-capture-composition-trace.md) |
| E8: discard | [One-shot use](first-slice-continuation-use-trace.md); [discard ownership](first-slice-discard-ownership-trace.md); [cleanup trace](first-slice-cleanup-trace.md) |
| E9: structural continuation use | [One-shot use](first-slice-continuation-use-trace.md) |
| E10: capture and handler composition | [Capture composition](first-slice-capture-composition-trace.md); [discard ownership](first-slice-discard-ownership-trace.md) |
| R1–R3: cell scope, acquisition and access | [Resource trace](first-slice-resource-trace.md) |
| R4–R6: dependencies, retention and completion | [Resource trace](first-slice-resource-trace.md); [capture composition](first-slice-capture-composition-trace.md) |
| R7–R10: cleanup, interpretation and close effects | [Cleanup trace](first-slice-cleanup-trace.md); [discard ownership](first-slice-discard-ownership-trace.md) |

## Checks and candidate rules

The rule IDs refer to the [catalogue](first-slice-catalogue-and-map.md#rule-catalogue).
Each proposed rule below names a required premise or conclusion; it is not yet
a complete formal inference rule or an implemented replacement.

### Requests and handlers

**V1 — Request typing (E1–E4).** Source
[checks the request operand and constructs the request](../../../src/elaborate.rs#L13966);
Core [validates effect nodes](../../../src/core/validate.rs#L15211). The
[specified request rule](../../../spec/static-semantics.md#effects) requires
the operation's instantiated input type and combines the operand effects with
the exact requested instance. A candidate request rule must consume the
certified operand judgment and operation contract, establish those type and row
premises, and produce the operation result and computation row. It must also
preserve payload and control facts needed by the later rules below; an effect
row alone is not shown to express those facts.

**V2 — Handler coverage and output (E5–E6).** Source
[checks clauses and constructs the handler](../../../src/elaborate.rs#L14550).
The [Core handler validator](../../../src/core/validate.rs#L16777) checks
operation coverage, clause patterns and answer types, body remainder and
clause effects, and the least handler output row. The candidate handler rule
must establish these premises from the certified body, clause and effect
contracts, with the clause capability local to its clause. Exact matching and
the selected runtime interpreter have distinct roles: static row accounting
does not itself select the runtime boundary. Compare the
[handler rules](../../../spec/static-semantics.md#effects).

### Continuations and closing control

**V3 — Clause capability use (E7–E9).** Source
[walks each clause](../../../src/elaborate.rs#L30759), starting with an
available capability and requiring it to be consumed on every normally
completing path. It checks a resume operand before consuming, requires
matching branch outcomes, rejects a second use and prevents capture across
specified barriers. Core independently computes free scope and continuation
requirements in its [scope traversal](../../../src/core/validate.rs#L12552)
and checks the [resume contract](../../../src/core/validate.rs#L17059).
The [specified rules](../../../spec/static-semantics.md#effects) supply the
language requirement. Candidate sequencing and branch rules need input and
output usage facts; resume needs the operand type, effects and available
capability and then consumes it. The handler discharges its own clause
capability. Counts and tree walks are current checking mechanisms, not a
required type representation. Map every Core capture barrier to its specified
scope before claiming full correspondence.
The [one-shot continuation-use trace](first-slice-continuation-use-trace.md)
follows this check into candidate usage judgments.

#### Structural usage: source and Core before and after

This trace follows only ordinary one-shot source-handler capabilities in the
slice. It separates the source clause, the newly constructed Core and a later
composition: they are not automatically the same verification subject. The
[specified structural judgment](../../../spec/static-semantics.md#effects)
describes `available` and `consumed`, and the
[operational rules](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
move the corresponding live capture on resume or discard. The current
[Core validation boundary](../../../spec/elaboration.md#validation-boundary)
requires independent Core checking; the proposed reuse below is a design
change, not a description of what current Ash already does.

| Current check and subject | Inputs and result | Candidate typed-system disposition |
| --- | --- | --- |
| [Source clause usage](../../../src/elaborate.rs#L14844) calls `check_clause_resume_usage` on each resolved clause body with that clause's `ResumeId` and an initially available state. | The [iterative traversal](../../../src/elaborate.rs#L30759) returns success only for structural output `Consumed`; otherwise it reports `ResumeNotConsumed`, `ResumeAlreadyConsumed`, a capture diagnostic or a resource failure. It does not publish a reusable `U` judgment or site cover. | During that clause's first check, compose the existing [candidate usage rules](first-slice-continuation-use-trace.md#candidate-usage-judgments) and the [site-cover rules](first-slice-close-derivation-rules.md#introduce-references-to-pending-completion) from the same constituent judgments. Carry the result with its owner, subject and assumptions; do not visit the clause again to recover it. |
| [Source resume construction](../../../src/elaborate.rs#L14147) searches the active clause owners, checks the operand against that owner's input and constructs a consumed-marked Core `Resume`. [Discard construction](../../../src/elaborate.rs#L14049) requires an active ordinary owner, constructs a consumed-marked `Unit` node and defers the close row. | This checks owner context and ordinary operation typing. Its initial resume row comes from the operand, with the shared handler output resolved later; the consumed marker is not by itself a structural use proof. Discard's marker does not prove its owned-close safety. | Use the already certified operand's `U` and type/row facts in `J-Resume-Composition`; use `U-Discard` plus the separate owned-discard judgment. The new constructor establishes its own owner/operand/row relationship and retains its case-indexed control obligations. |
| [Effect Core node validation](../../../src/core/validate.rs#L15870) collects handler and clause contracts, then checks every actual Core `Resume` and `Discard` against them. | The [handler check](../../../src/core/validate.rs#L16777) rejects duplicate handler identities and duplicate `(handler, owner)` clause keys. `validate_effect_resume` checks the selected contract, consumed marker, operand and answer types, exact output row and operand-row inclusion; discard checks its consumed marker, `Unit` result and existence of its owner contract. Success is validation of this Core subject, not a published source proof. | A newly constructed Core handler and operation compose the certified clause, owner and operand judgments with their actual identities and complete Core type/row facts. Establish the new relationships once. Existing certified Core constituents retain their proofs; an unverified Core input still needs its first applicable check. |
| [Core scope analysis](../../../src/core/validate.rs#L12552) builds per-node free requirements for the actual Core graph, then [validates roots](../../../src/core/validate.rs#L11901). | Its shared map includes ordinary binders and local nominals as well as `(HandlerId, ResumeId)` requirements. A resume requirement retains an occurrence and a structural count saturated at two. The root must have no unbound requirement. | The `U` projection and an explicit scoped owner/capture-barrier fact replace only the in-slice continuation part. A Core node producer composes certified child facts and checks its own binder and owner relationships. The broader binder, nominal, region and other excluded consumers still need their own dispositions. |
| [Capture/control checking](../../../src/core/capture/control.rs#L7190) follows an actual selected completion and its capture. | It has different inputs and conclusions from the structural count: selected control, live/consumed owner, nested captures, outside completion and, for discard, close safety and interpretation. The analyzer can reject an unknown selected discard. | Reuse the same certified `U` and site cover for structural references, then check the new selected capture and outside relationship through `J-Selected-Source`, the [owned-discard rule](first-slice-close-rules.md#dependencies-and-the-discard-composition), ticket/route and interpreter judgments. A site cover is not by itself a discard permission. |

The source traversal is structural even when its subject has no proved normal
return. It visits a resume's operand first, then consumes the named owner; a
match checks the scrutinee and requires each arm to leave the same outgoing
state. It still inspects syntactic remainders and arms whose reachability is
unknown. These are the current algorithm's facts; they are more precise than
reading “normally completing path” as a separate reachability analysis. An
ordinary call, tuple or binding composes its child order. The resolved cleanup
form visits its body and generated action; the source initializer was lowered
to the preceding callback binding, so the site-cover correspondence must
include that binding and any generated Core adapter. Neither a proved empty
normal-return cover nor an unexecuted branch permits a second structural use.

Source functions, recursive members, supplied local evidence methods and
nested handler clauses are checked as capability-capture barriers. Core
`analyze_free_binders` also checks function and recursive initializers,
`TypeAbstraction`, region-closure code and each handler clause boundary. At a
handler clause it removes that clause's exact `(handler, owner)` requirement,
requires its count to be one, and rejects a remaining foreign continuation.
At a match it compares each arm's continuation-key set and saturated count,
then combines that result with the scrutinee requirements; sequential
combination saturates at two. The map retains one occurrence for reporting,
not an exhaustive guarded list of all completion sites. Consequently a
candidate site cover must be produced alongside the new usage derivation; it
cannot be claimed to be an existing output of this map. Core-only barriers,
generated adapters and evidence methods still require explicit correspondence
to the appropriate source or outside-boundary rule.

The **gate matters**. In
[`run_effect_with_registry`](../../../src/core/validate.rs#L13803), ordinary
effect-node checks and `validate_scopes` run before the capture-analysis gate;
they run even when the program has no discard, generic cell or resource. Only
the later `check_nodes` or `check_nodes_with_release` reconstruction is skipped
when `has_generic`, `has_discard` and `has_resource` are all false. The last
flag also includes cleanup and several excluded owner forms. If retained
control is present, the separate release-check variant is selected. Therefore
the gate cannot be used as evidence that the Core structural usage/owner
checks were skipped, or that all work inside the gated analysis has the same
subject as the source usage traversal.

Source and Core do have related, but distinct, inputs. Source checking starts
with a resolved clause and `ResumeId`; Core checks the actual node graph,
handler/owner pair, complete node types and rows, and Core-only scope and
registry facts. Elaboration may introduce binding, pattern and adapter nodes.
A correspondence must show that each source usage and site certificate is
transported to the exact Core fragments it covers, while each new Core node
establishes only its new local premises. The presence of a source proof does
not by itself authenticate a different Core graph. Once a particular Core
fragment has been successfully typechecked and certified, however, composing
it checks only the new composition and its interface: neither its usage nor
its control/value analysis is verified again.

Before retiring any part of either current path, establish and record:

1. For every in-slice constructor, branch and capability barrier, the same
   structural input/output state and owner scope as the applicable current
   requirement, including syntactic sites with no proved normal return.
   Account separately for generated Core nodes and the excluded `retain` path.
2. A complete, scoped site cover produced with that first usage derivation,
   including same-owner branch alternatives and pending resume operands, and
   its consumption by completion-ticket and outside-preservation rules.
3. Authentication and transport of the exact handler/owner identity,
   operation signature, Core operand and answer types, output row and active
   dynamic owner facts. Static usage is not the proof of nearest runtime owner.
4. The distinct discard capture, close-row, interpreter and dependency
   consumers, including unknown alternatives and their obligations. Showing
   one structural use does not discharge any of them.
5. A disposition for the shared Core scope map's binder, nominal, generated
   and excluded-owner consumers, and evidence that any retained work proves a
   genuinely new composition relation rather than reconstructing a certified
   constituent. Until then no whole traversal or pass is identified as
   removable.

These are correspondence and replacement obligations, not a requirement to
run both implementations on every checked program. Examples of current
diagnostics are in the [one-shot trace](first-slice-continuation-use-trace.md#current-source-and-core-checks);
they are useful evidence but are not a proof of coverage or equivalence.

**V4 — Discard admission and ownership (E8, E10).** Source
[constructs discard](../../../src/elaborate.rs#L14049) for an active ordinary
clause owner and defers its close effects; structural consumption alone does
not establish safety. The capture analysis
[checks the selected completion](../../../src/core/capture/control.rs#L7181)
and [closes the owned segment](../../../src/core/capture/control.rs#L7032),
including recursively owned captures. It rejects unsafe or unknown selected
discard paths and cannot skip an outside owner, running cleanup or unfinished
close. The candidate discard rule needs the certified capability, owned and
outside obligations, and closability under the relevant interpretation
context; its conclusion consumes the capability, gives `Unit` and accounts
for closing effects. The [specified discard rule](../../../spec/static-semantics.md#effects)
is the authority. The control trace has not classified every analysis branch.
The [discard ownership and completion trace](first-slice-discard-ownership-trace.md)
follows this check into candidate judgment requirements.

#### Unknown callable request reaching a discard

This trace resolves one specific unknown-control path, not every unknown
dependency path. The subject is a new handler composition around a call whose
callable behavior is not fully known at that boundary. Its possible request
can reach a source clause that discards. The
[specification](../../../spec/static-semantics.md#effects) requires that the
discard close its owned capture without skipping outside or running
completion. Its [execution](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
moves and closes the selected capture; an effect row alone does not identify
the intervening owned control.

| Current producer or check | Actual fact or result | Proposed disposition |
| --- | --- | --- |
| In [`calls_after`](../../../src/core/capture/value.rs#L4994), strict call arguments must first have available value atoms. A callable `Atom::Closure` yields a known target; `Atom::Unknown` sets an opaque successor flag. The fallback without value-call precision also marks an unknown or empty target set opaque. | The call may take a known target and may also have an opaque alternative. If an argument has no currently known atoms, this query publishes no new call successor and keeps its previous prefix for replay; it does not prove that the argument cannot return. An unknown callable is not, by that fact alone, an actual request or an unsafe discard. | The callable's first checker publishes its applicable guarded behavior, residual and dependencies, or a sound unknown interface. The application instantiates that one interface for the actual argument and state; it does not reopen the callable body to find its requests. |
| [`discover_call`](../../../src/core/capture/control.rs#L4670) adds an opaque normal-return possibility. For an opaque call it also constructs `unknown: true` request events from an applicable request prefix and the instantiated function row's known effects; an unresolved row tail contributes an unknown request alternative. | Even when a row member identifies an effect, its event remains unknown about the opaque request/control behavior. For an event originating at a call, [source-handler selection](../../../src/core/capture/control.rs#L6156) does not filter by a known request operation and visits applicable clause alternatives. This is a conservative graph case, not proof that each request or clause executes. | Preserve all established request, return, non-return and failure alternatives. A complete request/residual contract may be more precise than the row; if unavailable, the unknown case remains an obligation. An unknown row tail cannot be erased, and a known effect label does not supply a captured-control proof. |
| For a selected opaque request, [`requested_clause`](../../../src/core/capture/control.rs#L6760) carries that same event into the new analysis clause frame and adds a synthetic pending position for the call in the captured prefix. | That position supports the analysis of possible opaque resumption; it is not a semantic instruction to rerun the source call. The event retains the call-site source and `unknown` flag when the selected clause is checked. | Compose exact conditional boundary selection and the selected capture from `J-Selected-Source` with the callable's already certified request and delimited residual. The actual captured and outside positions belong to this **new** handler composition. Reuse the residual after an actual reply rather than replaying the operand or callable. |
| In [`completed_selection`](../../../src/core/capture/control.rs#L7231), a selected discard with `event.unknown` returns `unsafe_discard` when row inference is disabled or actual capture authentication is enabled. Strict source and ordinary Core capture checking have `infer_cleanup_rows = false`. | The result is `Failure::Unsafe` with this discard and request/call source; [source diagnostic conversion](../../../src/elaborate.rs#L30714) reports `effect.discard-unsafe`, and the [Core validator](../../../src/core/validate.rs#L13909) reports its unsafe-Core-discard cause. This branch applies to discard, not resume. Row inference alone is not this strict safety result. | `J-Owned-Discard` checks every covered actual capture case, including its exact owner, nested close, outside completion, action interpretation, dependency crossings and residual row. The complete opaque case must supply those facts or retain its obligation; `U(k,discard,available,consumed)` and an effect row are insufficient. A resume uses its own restored-control and reply premises; do not impose discard safety merely because the callee is unknown. |

For a concrete checked fixture, [`unknown_higher_order_and_open_row_calls_block_discard_only`](../../../tests/effect_diagnostics.rs#L233)
defines `relay action = action ()`, once with a known `{B}` effect row and
once with an abstract row. A `B` handler around `relay ask` uses either
`discard` or `resume ()`. The fixture asserts the current source/public
pipeline rejects the discard alternatives and admits the resume
alternatives. It was inspected, not run for this audit. This example shows a
current conservative refusal; it does not prove that every possible runtime
capture in the discard example is unsafe, or that a future complete contract
must preserve the same rejection.

The distinction matters at Core as well as source. Module completion calls
[`check_builder`](../../../src/elaborate.rs#L5818) with its roots, imported
callable summaries and selected method routes. Under the applicable gate,
the linked [Core validator](../../../src/core/validate.rs#L13803) instead
invokes `check_nodes` on the assembled nodes with empty global and imported
summary inputs, rebuilding applicable capture relationships for that Core
subject. This trace does not establish that a rejected source fixture reaches
Core, nor that every resulting Core query repeats an identical earlier fact.
It identifies the concrete candidate boundary: once the exact Core fragment
and its conditional opaque request/capture facts have been typechecked and
certified, its user reuses them. A new handler, actual selection, capture or
outside completion is a new composition and checks its own relationships;
it does not reverify the already certified fragment. Existing validation stays
in force until the full source-to-Core interface, every applicable consumer
and the necessary governing change are established.

The remaining unknown-dependency question is separate. In particular,
[`dependencies`](../../../src/core/capture/value.rs#L7293) discards its
underlying traversal's completeness flag, while other consumers can impose
additional checks. The [focused predecessor correspondence](first-slice-dependency-cover-rules.md#from-the-existing-atom-test-to-a-reusable-judgment)
records the missing actual-dependency coverage and owner-enclosure lemmas. The
opaque-call discard branch above is evidence for one conservative control
rejection, not an explanation of every unknown value, result or payload case.

**V5 — Interpreter at close (E10, R9–R10).** During a close, the current
[interpreter check](../../../src/core/capture/control.rs#L6212) identifies
possible nearest matches in the applicable lexical context. Strict checking
rejects an action request that selects a removed handler. An outer handler for
the same instance does not replace that required interpreter. The rule for
closing an action must therefore preserve its actual interpreter requirements
and establish their compatibility at the closing position. Row membership
alone does not establish this. See
[cleanup safety](../../../spec/static-semantics.md#scoped-cleanup-actions).

### Scoped resources and values

**V6 — Scope identity and result (R2–R4).** Source
[checks and defers resource escape](../../../src/elaborate.rs#L13706), then
revisits unresolved type and row information; Core
[validates the resource node](../../../src/core/validate.rs#L14413). For a
generic cell, the [specified rules](../../../spec/static-semantics.md#generic-cell-foundation)
check the initializer in the preceding scope, introduce a fresh owner and
sealed provider for the body, remove only its exact cell effect, and prohibit
the closing identity from escaping. A candidate scope rule must establish
those relationships, discharge its local owner and retain the initializer's
effects. `T` is polymorphic: resource rules do not depend on a particular
payload type. The separate value-dependency check in V7 remains necessary.

**V7 — Value dependencies and escape (R4–R6).** The
[dependency traversal](../../../src/core/capture/value.rs#L7303) follows
actual resource atoms, captured values and aggregate fields; the
[resource check](../../../src/core/capture/value.rs#L6184) tests dependencies
against the closing owner. A candidate rule must relate a particular value to
its relevant owners and prove it can cross the boundary. Its ordinary payload
type alone is insufficient. Known dependencies are not evidence that an
unknown value is independent. The specification's treatment of relevant
unknown higher-order behavior must be followed, but the path from every
unknown to each current rejection is not yet traced: individual dependency
queries do not simply reject every unknown atom.

#### Unknown value at a resource result

This trace concerns a value dependency, not the opaque callable request in
V4. Consider an already checked function whose symbolic parameter `x` is
returned as the body value of a generic cell scope. The function's ordinary
typing remains outside this slice. The question here is only which facts the
cell-result check obtains for that particular `x` and the fresh cell owner.
This is a conditional analysis trace, not a claim that every such source
program is admitted or that its parameter actually depends on the cell.

| Current producer or consumer | Exact result | Proposed composition |
| --- | --- | --- |
| [`Graph::start`](../../../src/core/capture/value.rs#L2739) creates a symbolic root for every local function body and seeds each parameter slot with `Atom::Unknown`. A [variable expression](../../../src/core/capture/value.rs#L1272) is an alias of its binder; [alias evaluation](../../../src/core/capture/value.rs#L6633) installs its value link. | After propagation, the body value can contain that same unknown atom. This is an analysis value for the symbolic input, not an assertion that a concrete runtime value contains the newly acquired cell. Other origins and contexts can add their own atoms. | The already certified input supplies a dependency cover, with its scope and conditions. The alias transports the same value's cover; the resource composition does not inspect the function body again. |
| [`dependencies_with_completeness`](../../../src/core/capture/value.rs#L7303) traverses the body slot and its referenced values. Encountering `Atom::Unknown` makes `complete = false`; the resource list contains the resource atoms actually found by this traversal. [`dependencies`](../../../src/core/capture/value.rs#L7294) returns only that list, discarding the completeness flag. | For a converged body slot containing only `Atom::Unknown`, the projected list is empty even though completeness is false. An empty projected list is therefore not, by itself, proof that this value has no resource dependency. If known resource atoms accompany the unknown, those known atoms remain in the list. | Use `Cover(v,S,D)` only with an established complete upper-bound contract for the actual value and owner domain. The conservative `J-Cover-Top` includes all of `S`; it cannot by itself discharge independence from an owner in `S`. Preserve unknown obligations rather than treating an empty legacy projection as a cover. |
| After ordinary discovery and the payload and retention checks, [`resource_candidates`](../../../src/core/capture/value.rs#L6238) selects a resource/context only when the projected body dependencies include that exact resource atom; [`check`](../../../src/core/capture/control.rs#L3297) then invokes focused checking for candidates. In the focused query, [`check_resources`](../../../src/core/capture/value.rs#L6184) rejects if the projected body dependencies contain the exact focused resource atom. | In this specific unknown-only state, this candidate query does not select that resource; the unknown atom alone does not cause its focused escape rejection. If the exact known owner is also present, it can select the candidate and the focused query tests its own converged projection. This does not settle other source, payload, retention or control checks, nor prove that the whole program is accepted. | For each actual normal body result, `J-Cover-Body-Exit` consumes its correlated cover and requires the closing owner `a` in `S` and absent from `D`. A separate sound pre-birth or other contract may establish this absence for an opaque input; no such fact follows merely from `Atom::Unknown` or from an ordinary polymorphic type. If it cannot be established, keep the crossing obligation or reject unconditional admission. |

The [specification](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
requires conservative treatment of relevant unknown higher-order behavior.
The trace above does not establish that this isolated projection violates or
satisfies that requirement: other evidence and checks can matter, and the
precise correspondence between legacy atoms and complete runtime dependency
covers remains to be proved. The [dependency-cover record](first-slice-dependency-cover-rules.md#results-payloads-and-replies)
states the candidate interfaces and the separate completeness obligation.
Replacing this legacy query requires that correspondence and all relevant
consumers; this trace alone does not remove any current check.

**V8 — Cell retention and snapshots (R3–R5).** Current
[cell initialization](../../../src/core/capture/control.rs#L6375) records
the actual initializer and the target's enclosing owners; the
[retention check](../../../src/core/capture/value.rs#L5981) tests retained
dependencies against the target's birth enclosure and rejects self or
unproved containment. Reads and writes track actual targets, replacements and
snapshots. The candidate rules must establish strict enclosure for each
possible target of an initializer or builtin write, and associate each read
with the value actually returned. An intercepted write is not a builtin slot
update; an intercepted read takes the handler reply's facts. A snapshot's
facts must not be substituted for a later slot value's facts. See the
[generic-cell rules](../../../spec/static-semantics.md#generic-cell-foundation).

**V9 — Payload crossings (R5–R6).** The current
[payload check](../../../src/core/capture/control.rs#L7587) and
[crossing checks](../../../src/core/capture/control.rs#L7633) account for the
owners crossed by an operation. The candidate request and boundary rules must
establish that each actual payload and reply can cross each relevant owner;
checking slot retention does not establish this separate obligation. Preserve
the specified exception for the owner's trusted interpreter. See
[resource dependency rules](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies).

### Cleanup and rows

**V10 — Cleanup completion (R7–R10).** The current
[close traversal](../../../src/core/capture/control.rs#L7032) distinguishes
armed cleanup, running cleanup and unfinished closing; it schedules eligible
actions in the owned segment. The candidate scope, capture, resume and close
rules must carry the action's completion obligation, preserve its phase and
saved result, and establish that closing does not skip running or outside
work. On successful execution an armed action is invoked once, subject to the
[specified cleanup behavior](../../../spec/static-semantics.md#scoped-cleanup-actions).
This conclusion is conditional on the specified execution and failure
assumptions; it is not a proof of termination.

**V11 — Cleanup effect row (E8, R9–R10).** Source
[infers close requirements and solves row equations](../../../src/elaborate/cleanup_rows.rs#L392).
For each relevant action, [row recording](../../../src/core/capture/control.rs#L6855)
uses its instantiated latent row and retained resource interpreters. The
solver starts pending rows empty and iterates unions and exact removals to a
fixed point. Strict checking separately
[checks row agreement](../../../src/core/capture.rs#L3871). A candidate
discard rule must establish the least residual close row from the action
contracts and retained interpretation, with surviving source handlers
discharging effects at their own boundaries. It must not replace the latent row
with an assumed list of only the requests executed by an action.

**V12 — Inference is not safety.** The
[inference entry point](../../../src/core/capture.rs#L3243) and
[strict check](../../../src/core/capture.rs#L3174) use shared graph machinery,
but inference collects cleanup requirements while strict checking also checks
control safety and row agreement. Their overlap alone does not show that they
prove the same judgment. In the replacement, the type system must establish
both the row and the independent ownership and interpreter premises in V4,
V5 and V10. Surface inference may find a row; typed Core must carry complete
types, and successful Core type checking must establish the applicable rules.

## Existing reuse and the remaining audit

[Module completion](../../../src/elaborate.rs#L5791) consumes imported global
and method summaries, solves cleanup rows, checks local roots and publishes
callable summaries. This is existing reuse; those summaries are not yet the
complete certified type-system judgments required by this design.

The [linked Core validator](../../../src/core/validate.rs#L13803) performs
ordinary validation and conditionally reconstructs capture, resource and
completion relationships from assembled nodes without imported summaries.
The current [elaboration specification](../../../spec/elaboration.md#validation-boundary)
requires this validation. The audit has not yet matched each reconstructed
fact to its earlier subject and assumptions, so it cannot state which exact
checks are repeated or propose their removal. The intended replacement checks a
new composition using certified constituent judgments and the new premises;
it never verifies the certified constituents again. Resolve the present
validation requirement through the appropriate specification and decision
process before changing it.

Complete the audit by tracing every in-slice rejection and successful output of
the shared analyses, including imported and selected-method paths, to a
specified rule and candidate judgment. Record each consumer and its
before/after disposition, retaining shared analysis while an outside consumer
still needs it. Investigate the unknown-dependency path and any Core-only
scope checks identified above. The catalogue also records the existing
generic-cell versus `Int` specification wording discrepancy. These are open
items, not evidence that the implementation is correct or incorrect overall.

## Establishing that type checking works

Successful checking must establish enough to justify the narrow program
correctness guarantee in
[DN-0060](../DN-0060-typed-data-and-control-roadmap.md#program-checking-and-correctness):
under its stated assumptions and barring external events, an accepted program
can run without raising an error. For this slice, identify each relevant
execution error and the judgment premises that rule it out. Where the slice
depends on a boundary premise, the enclosing program must establish it or
meet an explicitly stated environmental assumption. Passing the existing
checks or preserving facts alone does not establish sufficiency.

For each candidate rule, define its premises, conclusion, type-level
representation and any conditional obligations. Show which established
judgments it consumes and how source elaboration produces complete Core types.
Then implement and check the rules as one source-to-typed-Core path, replacing
the corresponding legacy verification only when all its relevant consumers
are accounted for. This is the planned development work, not authorization to
implement it from this audit.

The validation evidence must cover specified accepted and rejected cases,
including branches and capability consumption, polymorphic exact instances,
unknown dependencies, cell retention and snapshots, close rows and removed
interpreters. It must also show a composition using certified constituents
without verifying them again, and a conditional judgment whose missing
premise is not treated as proved. Trace the actual type-checking procedure so
that inference, obligation discharge and termination or resource limits are
understood; the existence of a declarative rule alone does not establish a
working checker. Representative existing tests include
[effect diagnostics](../../../tests/effect_diagnostics.rs),
[resource scope typing](../../../tests/resource_scope_typing.rs), and
[cleanup interactions](../../../tests/cleanup_interactions.rs). These are
evidence to review, not a completeness proof, and were not run for this audit.

The checker establishes that the particular program satisfies the rules;
separately established system-level soundness and correctness proofs justify
the narrow execution consequence. The compiler does not repeat those system
proofs for each program. The current
[failure semantics](../../../spec/dynamic-semantics.md#scoped-cleanup-actions)
also admit internal failures during cleanup. The agreed
[failure admission rule](first-slice-failure-judgments.md#agreed-admission-rule-for-the-first-slice)
requires those failures to be ruled out for an unconditional no-error
conclusion. Establishing the individual failure covers and their discharge
remains work for the slice. This audit does not change current semantics.
