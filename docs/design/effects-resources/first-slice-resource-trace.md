# First Slice: Cell Resources and Dependencies

This trace belongs to [DN-0061](../DN-0061-effects-and-resources-first-slice.md)
and follows R1–R6 of the [catalogue](first-slice-catalogue-and-map.md#resource-and-cleanup-rules).
It records current behavior and candidate judgment requirements; it is not a
new calculus, a change to the specification, or a proof that the implementation
is complete. The separate [discard trace](first-slice-discard-ownership-trace.md)
covers the full ownership and completion composition. Tests linked below were
not run for this documentation trace.

A judgment below means an established fact about a particular subject under
stated assumptions, not a selected syntax or certificate format. A new scope,
request or close must check its own premises using certified judgments of its
opaque constituents; it must not recheck their bodies. Missing premises remain
obligations and dependent conclusions remain conditional. Ordinary values,
function application, calls and excluded resources supply facts at the
boundary, rather than being recursively analyzed by these rules. The existing
summaries and Core validation do not yet constitute the complete reusable
certification required by DN-0061.

## R1 — Legacy scope

**Specification and execution.** The [static rule](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
checks an `Int` initializer in the preceding scope; the body receives fresh
rigid `R`, `Handle<R>`, sealed `Provider<R>` and an interpreter for exact
`Ops<R>`. The result has the body type and the outward row is the initializer
row union the body row with exactly `Ops<R>` removed. The result type, outward
row, schemes and evidence may not expose `R`. Other instances remain outward.
The [initialize, acquire and return transitions](../../../spec/dynamic-semantics.md#scoped-cell-execution)
evaluate the initializer first, acquire only after successful preparation,
create a fresh activation and release it on normal return. `R` is lexical;
the activation distinguishes executions, including repeated executions of one
site. A copied handle is access to the same owner, not another owner.

**Current checks.** [Resolution](../../../src/resolve.rs#L10896) takes the
already resolved initializer before allocating the body identity and handle.
[Scheduling](../../../src/elaborate.rs#L16632) checks the initializer as `Int` before the body; [body entry and finish](../../../src/elaborate.rs#L14218) create the handle
binding, remove the exact instance from the body row, union initializer effects,
and reject the owner in outward type, row or enclosing binding. If the exact
cell effect is explicitly present, source removes it; if known absent, it
preserves the row; an unconstrained open tail makes removal ambiguous and
rejects. [Core computes the same cases](../../../src/core/validate.rs#L14133).
The specification's phrase “after removing” does not explicitly state these
absent and ambiguous cases; its precise intended resource-scope rule needs
clarification before translating it. Ordinary handler admission separately
requires its target present. Unsolved type
and row variables are [revisited after solving](../../../src/elaborate.rs#L13706).
The [Core resource validator](../../../src/core/validate.rs#L14413) checks the
legacy initializer against `Int`, body/result equality, exact outward row and
resource authority and provider method provenance; invalid facts fail
validation. The [machine acquisition](../../../src/eval/machine.rs#L4210)
checks the legacy integer and live capacity before publishing the owner;
[access](../../../src/eval/machine.rs#L4836) authenticates operation and
activation. Ordinary resolution, type, row and continuation errors precede
resource dependency admission. These checks do not by themselves prove R4–R6.

**Candidate composition.** Use certified initializer and body judgments plus
the sealed API contract. Introduce a fresh local identity, access and provider
for the body; check initializer type, exact row subtraction, owner non-escape,
and the separate value and completion obligations below. Discharge the local
identity and interpreter at scope exit, preserve the initializer effects and
body result facts that can cross, and preserve unrelated effects and enclosing
owners. Freshness, evidence authenticity and initialization-before-owner are
premises, not consequences of an `Int` result. [CP-0031](../../proposals/CP-0031-remove-legacy-integer-cell.md)
proposes removal of this facility; it remains current until that transition is
retained. It is not evidence that R1 is already removed.

## R2 — Generic scope

**Specification and execution.** The [generic rule](../../../spec/static-semantics.md#generic-cell-foundation)
checks the initializer against fixed monomorphic `T` before introducing fresh
`R`, `Cell<R,T>`, sealed `Provider<R,T>` and exact `Ops<R,T>`. It retains the
body result, unions initializer effects with the body row minus only that exact
instance, and does not generalize reads. `T` may be abstract in the surrounding
context. `read` and `write` are ordinary applications of provider methods;
their contracts and selected evidence are inputs to this slice. The generic
[acquire and return rules](../../../spec/dynamic-semantics.md#scoped-cell-execution)
create and release a `GCELL` holding the ordinary checked value. Preparation
failure publishes no owner.

**Current checks.** The same [resolution and elaboration path](../../../src/elaborate.rs#L14218)
builds the two-argument handle and exact effect instance, with the same
present, known-absent and ambiguous-tail row behavior as R1; the
[Core validator](../../../src/core/validate.rs#L14413) selects the payload
argument instead of `Int`, compares it with the initializer type, and checks
body, row, authority and provider methods. The
[generic initializer and monomorphic-read tests](../../../tests/resource_scope_typing.rs#L1416)
are representative evidence. The [Core validation specification](../../../spec/elaboration.md#validation-boundary)
still says each resource initializer is `Int`, while generic static semantics
and this validator use `T`; that discrepancy remains open.

**Candidate composition.** As in R1, instantiate the certified scope and API
contracts at the exact `R,T`, supply the fresh local facts, and discharge the
local interpreter and owner on exit. Preserve all constraints on abstract `T`
and do not assume that a value of `T` is resource-independent: actual stored
dependencies are a separate premise. General application typing is outside the
slice. A source handler may interpret the very same method request before the
builtin boundary, so the method contract must preserve request and reply facts
as well as its ordinary type and row.

## R3 — Acquisition and access

**Specification and execution.** The [cell steps](../../../spec/dynamic-semantics.md#scoped-cell-execution)
evaluate an initializer once, prepare and publish a fresh activation with a
non-owning handle and lexical instantiation. Requests select the nearest
accepting boundary by its applicable identity and context. A source handler
can intercept the exact effect before the builtin is selected; it is not
selected by authenticating the builtin handle. When the builtin cell is
selected, it authenticates the operation and actual handle for a live owner.
The generic builtin additionally authenticates complete `R,T`. Read returns
the current root; write replaces only that root and returns `Unit`. Selection is innermost
first: a nearer exact source handler intercepts, and an intercepted write is
not a builtin replacement. Intercepted reads have the actual reply's facts.
Copies preserve access, not ownership. Generic write preparation failure leaves
the old root intact, although operand effects already occurred; terminal disposal
failure can occur after replacement. Capacity and preparation failures are
internal failures, not source branches.

**Current checks.** [Runtime selection](../../../src/eval/machine.rs#L4480)
compares instantiated effects while searching boundaries, and checks the
activation when considering a builtin resource boundary;
[legacy and generic interpreters](../../../src/eval/machine.rs#L4836)
check operation and handle, with generic reply/trace preparation before root
replacement. [Acquisition](../../../src/eval/machine.rs#L4210) checks capacity
and allocates a fresh key. The [generic access analysis](../../../src/core/capture/control.rs#L6551)
uses the selected resource occurrence, original request operation and possible
handle targets, then reads recorded roots or records a replacement only for a
selected builtin cell. [Execution tests](../../../tests/resource_scope_runtime.rs#L569)
cover interception and [machine tests](../../../src/eval/machine.rs#L11191)
exercise wrong type, donor, stale and family cases; they are not a proof.

**Candidate composition.** Certified initializer and API judgments introduce
one owner and access fact only after acquisition's premises; handle duplication
preserves the same owner and does not create another release obligation. An
request rule accounts for exact operation and lexical instantiation when
selecting the interpreter. A selected builtin access checks its actual target
and live activation. It preserves the owner
and current root on a read; a builtin write establishes a new root only after
its separate retention and crossing premises. Handler selection is a control
fact, not inferred from effect-row membership. Preserve operand effects and
actual handler reply facts on interception. How static judgments justify all
runtime authentication and preparation assumptions remains to be proved.

## R4 — Dependencies and crossing

**Specification and execution.** [Resource dependency rules](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
reject a normally returned value dependent on its closing owner, and an
operation operand dependent on an owner it crosses to an outside handler.
An outer-dependent value may cross an unrelated inner owner while staying
inside its own. The owner's trusted interpreter is an admitted recipient.
Dependencies include actual captures, selected evidence and indexed operation
metadata, surviving aliases, imports and instantiation; matching types or
unused environment entries alone do not establish one. Strict children must
complete before a result exists. Unknown relevant behavior that prevents proof
of independence is conservatively rejected; ordinary errors retain precedence.

**Current checks.** [Dependency traversal](../../../src/core/capture/value.rs#L7303)
walks resource atoms and actual aggregate and closure paths while tracking
completeness. [Result checking](../../../src/core/capture/value.rs#L6184)
rejects a body result containing the focused resource atom;
[crossing collection and checking](../../../src/core/capture/control.rs#L7587)
record each crossed resource and query the actual payload. The source's
[type and row escape checks](../../../src/elaborate.rs#L13706) are distinct
from this value analysis. [Imported and hidden-capture tests](../../../tests/resource_scope_typing.rs#L299)
and [payload tests](../../../tests/resource_scope_typing.rs#L625) provide
examples. Individual queries must not be described as rejecting every unknown
atom: the complete unknown-to-rejection path is not yet classified.

**Candidate composition.** An opaque value judgment must identify the actual
subject, dependencies, completeness, owner scopes and assumptions; a call or
selected method supplies its established result and request relationships.
At each result or payload crossing, check independence from each crossed owner,
except the specified trusted recipient; preserve dependencies on owners that
remain live. An absent dependency in an incomplete judgment is not proof of
independence. Discharge the closing owner's local access and completion only
after crossing and close premises hold; do not erase independent outer facts.
Backing-region facts, including possible dependencies of an `Int`, are outside
this slice but must be established or explicitly assumed when relevant.

## R5 — Retention and snapshots

**Specification and execution.** For [generic contents](../../../spec/static-semantics.md#generic-cell-foundation),
each initializer and actual builtin replacement must retain only resource
owners that strictly enclose the target activation at its acquisition. Self,
younger, incomparable and cyclic retention reject at that operation; a later
clear cannot repair it. Every possible target and payload matters. Recursive
activations at one lexical site differ, and an enclosing activation can supply
a child. Capture and restore do not retroactively alter the birth relation.
A read snapshot has the actual returned value's dependencies; replacement
changes the current root, not earlier snapshots. An intercepted write does not
replace the builtin slot, and an intercepted read uses its handler reply.

**Current checks.** [Initialization](../../../src/core/capture/control.rs#L6470)
records initializer roots, enclosure and predecessor inputs at birth.
[Request processing](../../../src/core/capture/control.rs#L6551) iterates
possible targets and replacement roots, or links a read to current roots;
[focused retention checking](../../../src/core/capture/control.rs#L6644)
checks recorded sites. The [retention predicate](../../../src/core/capture/value.rs#L5981)
accepts a resource atom in the recorded enclosure or a qualifying immutable
predecessor proof, excluding the focus itself; otherwise it reports a dependency
failure. Its predecessor case is conditional on separate validity and structural
birth premises, not a general inference that older unequal owners enclose the
target. [Typing cases](../../../tests/resource_scope_typing.rs#L1614) distinguish
snapshots and [self/younger rejection](../../../tests/resource_scope_typing.rs#L1761);
[execution cases](../../../tests/resource_scope_runtime.rs#L710) distinguish
handler reply and later stored roots.

**Candidate composition.** Acquisition introduces a target activation and its
birth-enclosure relation, checks each possible initializer's actual dependencies,
and records its current root. A selected builtin write checks the replacement
against that same birth relation before establishing a new current root. A
read establishes a separate snapshot judgment from the actual selected root;
later writes preserve prior snapshot facts. Source-handler interception instead
uses the clause's certified behavior, including any distinct writes it performs.
Use certified values and control paths without reopening them. All-target
coverage, joins, recursive activations, symbolic predecessors and completeness
remain proof obligations for a full rule and its correspondence to the current
analysis.

## R6 — Capture and completion

**Specification and execution.** [Capture and release](../../../spec/dynamic-semantics.md#scoped-cell-execution)
move the same owner, activation and current contents into captured control and
restore them on resume, in order. Live capacity remains charged throughout.
Normal return releases the cell. Checked discard closes cells inside its
recursively owned abandoned segment in structural order; it cannot skip
required completion outside that segment. Inner release precedes outer release,
so enclosing cells remain available to inner cleanup. Divergence need not
release; internal failure disposal is not source completion.

**Current checks.** [Capture and resume machinery](../../../src/eval/machine.rs#L4980)
moves frames, while [acquisition](../../../src/eval/machine.rs#L4210) tracks
live resources; [normal release](../../../src/eval/machine.rs#L3469) removes
the boundary. The [control close traversal](../../../src/core/capture/control.rs#L7032)
and [discard check](../../../src/core/capture/control.rs#L7181) analyze owned
versus outside completion, in addition to dependency checks. The
[resource typing cases](../../../tests/resource_scope_typing.rs#L641) include
owned and outside owners, and [runtime cases](../../../tests/resource_scope_runtime.rs#L735)
cover capture and owned discard. These examples do not establish all paths.

**Candidate composition.** Acquisition introduces exactly one completion
obligation tied to the activation. Capture transfers, rather than duplicates
or discharges, the owner and contents into the selected segment; resume
restores them and preserves outside obligations. Normal completion discharges
the owner after result crossing succeeds. Discard needs a certified owned
segment, its closability and outside-obligation preservation; it discharges
only the owned cells actually closed and preserves outside control. Closing
effects and cleanup interpreter requirements are separate premises in the
[discard trace](first-slice-discard-ownership-trace.md). No rule here proves
termination or treats a captured cell as released merely because it is inactive.

## Correctness and remaining evidence

R1–R6 need to rule out the slice's contribution to stale or mismatched access,
invalid identity or authority, dependency escape, invalid retention and skipped
completion under their stated premises. Capacity, allocation and preparation
failures also occur in current execution. The agreed
[failure admission rule](first-slice-failure-judgments.md#agreed-admission-rule-for-the-first-slice)
requires their applicable internal cases to be ruled out for an unconditional
no-error conclusion. Individual covers and evidence still need to be derived;
an internal capacity limit is not an external event by declaration.
Successful observation and internal failure disposal are distinct, and the
specification does not prove termination.

The mapping above is representative, not an exhaustive classification of every
source, import, evidence, linked-Core, unknown-dependency or runtime branch.
Existing module summaries and independent Core validation have different
subjects and assumptions in places; their exact reuse and replacement must be
mapped before retiring any check. Shared analysis also serves excluded scopes.
The prospective judgment language, certificate transport, source inference,
Core completeness and reconciliation with AD-0007 remain open; a system-level
soundness and execution correspondence proof is separate from checking an
individual composition. No tests or builds were run for this trace.
