# C3 drain analysis correspondence and limits

This map relates the [bounded proof](DrainSafety.lean) to the reviewed
implementation of one focused Store query. The independently reviewed source
completed the frozen [AD-0012 gate](../../tasks/evidence/local-retained-control/c3-model/README.md).
The linked validator runs this analysis for retained carriers. The connected
C2/C3 checkpoint was independently verified at milestone commit
`d256bef288ac6b828e475c9dcaaf710812405b7a`; C2 and C3 are accepted. This map
is not a mechanized proof of the Rust compiler.

## Focused analysis and closure

The ordinary discovery records each reached Store acquisition as a candidate
and saves its entry state (`discover_boundary`). `check_focused_entries`
requires every candidate to have an entry, reconstructs each occurrence with
`restore_entry`, and starts the new focused Store with `DrainWork::Empty`.
This seed describes a freshly acquired Store, not an arbitrary old summary.
The focused query calls `discover` and tests `release_unsafe` only after that
query has returned successfully. Each focused Resource return inspects the
work on that actual predecessor; any value except Empty latches refusal.

The linked validator authenticates the registry, carrier ports, types and
scopes before reconstructing capture control. Its census selects
`check_nodes_with_release` when the actual Core contains Store, RetainedRoot or
Retain; other programs keep the ordinary capture check. Both paths charge the
remaining shared Core work budget, including failed work. The capture graph's
own fast path also recognizes RetainedRoot and Retain, including a generic
root without a local Store. Subsequent checks must still succeed for admission.

`discover` retains normalized complete control States in `visited` and
processes its pending queue. After the queue empties, it closes the value graph.
If the graph revision grew, it directly requeues recorded call States and
explicit-owner/retained request States, bypassing `visited` suppression. A
call's delivered prefix is published only after its new successor and value
work succeeds. A call waits for a value alternative at every strict argument
port before delivering any callee or opaque-return successor, as the value
transfer already does. An absent argument keeps the earlier prefix for replay;
an unknown argument remains an alternative. New Store/key operands remain
unresolved until their replay succeeds; any still unresolved after both
queues stabilize fails. A work or allocation refusal returns failure, not a
partial release result.

This replay list does not omit a value-dependent Change to a prior Choice or
Bind: `case_of` reads the borrowed immutable graph and a path-local facts map,
not growing atoms or edges. A slot's `(expression, context)` identity is
append-only, and facts are part of the complete State's equality and hash.
Thus the same State has the same case read after a value revision. A different
fact is a different State. Calls and owner/Store/key selection do read growing
atoms and are the explicitly replayed cases. This stability argument does not
by itself establish that a reused aggregate origin denotes the right dynamic
value; that separate condition appears below.

## Local transfer and physical completion

| Event | Rust control/evaluator | Lean evidence and condition |
| --- | --- | --- |
| Actual Probe | `requested` checks the driver before source-handler selection. `requested_native` requires the actual recent focused Store, exact canonical Probe and instance. It splits the current work and writes that answer to its result port immediately. | `selected_probe_sound` and `selected_probe_forget_origins_sound` require actual selected-provider and driver premises. A source handler's Bool is not an authentic Probe. |
| Reads and results | `case_of` follows only path-local facts and the transparent expressions, with exact constructor and payload checks. Every `DrainProjection::assign` first drops all older aggregate origins, even if the assigned result is unknown. It retains earlier scalar cases. Executed Bind/arm and CaseReturn copy the read; CallReturn, Handler, Clause and Root return clear the map and omit returned aggregate origin. | `DrainSafety-v4.lean` proves global origin forgetting, read-to-assignment and read-to-return cases using `read_sound`. Resume uses the same `read_return_sound` rule: it retains the case and freshness, but clears the map and drops the incoming origin before assigning the captured request port. Calls snapshot every actual read before clearing facts, then assign each formal from that snapshot; the pointwise formal lemma retains earlier scalar formal cases. |
| Reused contexts | Calls, source-clause entry, Continue and focused acquisition discard caller facts; call arguments and returned cases omit aggregate origins. An unfactored binder is an `Expr::Slot`, where `case_of` stops rather than following global joined value edges. Every case assignment now forgets all origins already stored in the current facts, before it publishes the newly read case. | The shared-Core fixture confirms that one aggregate and one Match can execute twice in one value context: the old false payload became the new true fact, and the old implementation allowed a Pending close. The current guard refuses that graph. For an ordinary Bind or arm, the introduced binder is out of scope in the initializer or scrutinee; a Match result cannot occur in its own descendant arm construction without a Core cycle. These are local conditions on a just-read incoming origin, not a claim that a static port is an occurrence. Resume's captured request port need not satisfy those syntactic conditions, so Resume drops its incoming origin. Static port equality and source-only call resets are not sufficient authority. |
| Fresh root and finish | Analysis pushes RetainedRoot outside the private Handler. Runtime installs the counted completion marker below the Handler; a restored cut likewise sits above a fresh marker, and its consumer's Some adapter sits below. | `enter_root_sound` applies on actual root admission. `finish_root_sound` and C1 `Step.finish` apply at the matching marker's real return after the clause suffix and owned cleanup, with `ReadyToFinish`, not when the Handler disappears. |
| Retain and continued work | Retain publishes a slot while the current private clause suffix still runs. The root marker remains counted. Continue uses a fresh marker and changes the analysis work to Unknown on both miss and live paths. Old retained entries are possible work, not exact slot counts. | Retain changes the work view to Pending. C1 `Step.retain` is a macro through the actual administrative return; its `adminSuffixClear` premise is not asserted at the Retain instruction. Pending covers the intermediate saved slot and unfinished suffix. |
| Closing | `close_segment` preserves armed cleanup before the focused Store and rejects abandonment of unfinished RetainedRoot or running cleanup. The focused Store's real return checks its predecessor. Runtime decrements the root only at `RetainedRootCompletion` pop and tests both active roots and live slots at Probe and release. | C1 `finishOuterClose` requires actual empty work after normal cleanup; it is not justified by discarding the marker or by constructing a result. The outer-discard focused tests witness cleanup return before the same Store close, and reject missing drain or later Retain. |

The root/Continue, interpreter and support checks must have already succeeded
for the same actual Store before these work facts are used. A partial failure
teardown is separate from normal release. These facts do not prove that any
particular source program passes linked validation.

## Full-State relation and implementation correspondence

The proof domain is the finite collection of normalized *analysis* States
in one successfully completed focused query. It is not the set of all
runtime stacks, generations or recursive executions. A State includes the
control position and context, active and captured edges, Store associations,
retained records, and its work and case projection. Equal ports alone never
identify two States. The normal-return relation pairs an actual full call
entry with its matching returned full State, using the existing CallReturn,
handler and clause continuation frames. Only after identifying both endpoints
may their work and cases be projected. No projected-only relation is composed
across different owners or stacks.

For the correspondence, define `Step` from the existing control successor
rules at the query's final value closure, before testing membership in the
visited set. It includes both ordinary enqueue successors and successors of
replayed call and owner requests. It does not mean "an edge already in
visited." The finite universe used by Lean can include the observed States
and all their one-step possible successors at that final closure; checking
closure establishes that those successors are visited. Successful budgeted
execution supplies a finite actual graph. It does not establish global
termination of source execution or of an unbounded analysis.

The worklist argument is:

1. `restore_entry` constructs the fresh focused Store seed and `discover`
   enqueues it through the same normalization and visited insertion as every
   other State. The seed is in the successful query's visited set.
2. Each dequeued State expands every syntactic and control successor for its
   fixed full State. Queue exhaustion followed by successful `data.close`
   and unchanged `revision` means no newly propagated call target or
   Store/owner/key operand remains undelivered. On any revision change, every
   recorded value-dependent call and owner request is requeued directly, even
   if its State was already visited. A changed case fact creates a different
   State; a fixed State's case read is stable as explained above. Any
   unresolved retained operand causes failure after the loop. Therefore each
   final-closure `Step` from a visited State has its successor in visited,
   subject to the code-by-code successor audit below.
3. `Path` retains those whole-State edges; `path_is_visited` inducts from the
   actual seed using the successor-closure property. `Reach` has
   `R0 = {seed}` and `R(n+1) = Rn ∪ post(Rn)`. The existing finite-union lemma
   gives a finite bound. `finite_return_bound` similarly bounds the pairs of
   actual matching call entry and return States, including mutual and imported
   calls. It does not infer termination or pair an entry with an unmatched
   continuation.
4. Every focused Store-close predecessor on such a path is visited. At that
   predecessor `returned` latches `release_unsafe` unless the work is Empty.
   A successful focused `discover` therefore provides the checked premise of
   `checked_close_is_quiet`; C1 `NoWork` follows only for the same represented
   Store close. The later retention, payload, support, resource and linked
   Core checks must still succeed before admission.

The representation induction begins with the actual fresh Store's zero roots
and live slots. At each actual selected transition, the local work lemmas keep
its work represented: root admission uses `enter_root_sound`; actual Retain
creates a live slot and uses `retain_sound`; Continue, stale/missing keys and
unknown control widen to Unknown; only actual marker return may use
`finish_root_sound`; the selected native Probe uses the real driver premise and
splits on the provider's actual predicate. Old abstract retained records are
may-work and are not counted as exact owners. An interrupted or failed move is
not a normal successor. At actual case transfers, the Read lemmas preserve the
value/work relation, and unknown cases explore all applicable arms. Work
mutation expires old Probe freshness. These steps establish representation
through the path; it is not assumed for the first time at an Empty close.

The independent bounded review found no further missing worklist, completion
or control transition in the v2 mapping. Its incoming-origin review identified
Resume as the transfer without a syntactic destination condition; the current
candidate drops that origin. The local forgetting lemma does not itself prove
payload stability: the ordinary scope and graph conditions above are part of the
concrete correspondence independently reviewed at `0f73745e`. The linked
admission routing above is retained product behavior. The later C4 strict-call
readiness repair preserves the recorded revision replay and was independently
reviewed with its affected tests. This is not a Rust mechanization.

## Evidence and remaining gates

The [independent review](../../tasks/evidence/local-retained-control/c3-model/review.md)
pins product checkpoint `0f73745eeb897c9018638a210aa34c26ca53de9c`, the
[model source](DrainSafety.lean), its correspondence and the focused Rust
receipts. The shared-Core regression reached the existing linked release gate
after 23,857 work units; the focused query then refused the unsafe close.
The retained regression family passed 94 tests at that checkpoint.

The linked validator now admits the checked recursive and cleanup drains and
refuses the corresponding undrained paths. Public source and image execution
exercise both drains. The recursive drain also runs after linked identity and
folding transforms. Fresh allocation under an allocator handler owned by the
capture passes; the distinct external cleanup forwarder is rejected under the
accepted interpreter-identity contract. Full C2/C3 acceptance and the connected
checkpoint are recorded in [PR #162](https://github.com/dikini/ash-lang/pull/162).
The later [C4 library delivery](https://github.com/dikini/ash-lang/pull/163)
was retained at `73f6304a69183682a94d85aa81f9b1a88c21ef5e` after its own
fresh workspace checkpoint. C5 specification and final integration remain
separate.

The standalone Core validation allowance remains 983,040 units. In the public
source driver, the outer-discard fixture used 1,309,582 of 78,225,000 units; its
image startup used 1,355,242 of 1,753,834 units. Those allowances are computed
from their inputs, and these measurements do not establish a bound for every
program.
