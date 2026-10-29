# One-way completion: candidate proof slice

[OneWayCompletion.lean](OneWayCompletion.lean) is the retained model for the
[assignment](one-way-completion-proof-assignment.md). Its frozen, independently
reviewed gate and 130 ordered reports for 129 unique names are recorded in the
[proof evidence](../../tasks/evidence/pinned-one-way-proof/README.md). The
retained source is `870b4f0f4b134e49a2d97a1039d8f362700cb2ff1f7d667877d6cb9816e1573c`.
The subsequent helper-routing draft is not part of that source or gate. The
model's scope and the trusted mapping to actual Core and runtime behavior are
separate; the model alone grants no product completion authority.

## Modeled result

The modeled control state carries its Network, activation key, actual control
node, frame stack, external-work bits and taint. Its receive transitions use the
selected Network channel and operation: Message commits the exact queue head to
held work, Empty requires an unsealed empty channel, and End requires a healthy,
sealed, empty channel. End first records a pending observation for the same
activation, lane and side. Only the modeled successful reply edge creates an
End fact; a source value or helper return cannot create it.
`control_step_network`, `execution_step_network` and `execution_network` map
the modeled control and processing steps to `WorkerChannel.NetworkTrace`.

The authenticated End return requires a fact and frame for the same key.
An ordinary normal return can carry no End fact. The oldest outer driver has
an exact result destination and a checked End match leading to finish or stop;
inner recursive frames have the separately checked inert suffixes.
`trace_preserves_frames` derives the modeled live frames from their exact call
nodes, with no bound on finite dynamic stack depth. The bounded suffix checker
admits allocation-free alias, construction, projection, branches and returns;
it checks all listed operands and both branch successors. It translates those
nodes into the same modeled control machine. `trace_fact_origin` shows that
such a suffix execution cannot mint an End fact. Unsupported nodes and
message-derived operands fail that check.

The restricted processing graph represents no-output stutters, forwarding with
explicit finite operand and destination ports, and selected native bindings whose
synchronous return and preservation of modeled network, Store and dependencies
are explicit conditional premises. Their association with actual native calls
and the ordinary host assumptions remains to be established. Forwarding unions message-derived value
and capture dependencies into the destination; branch enumeration covers both
successors. It orders cleanup start and return before the marker. Retain,
callbacks, escape and unknown nodes fail. `checked_region_marker_finishes` maps every
modeled region walk reaching its marker to C1 cleanup and the same-entry
`WorkerChannel.NetworkStep.finishProcessing`. It checks all supplied older
frame continuations. The same-Store work projection includes the active
capture, clause, live slots and explicit external callback, cleanup, capture and
other-work bits. The relation of those bits and the selected C3 query to actual
runtime work remains unproved.

The finite analysis join refuses different full contexts, loses unequal facts
and work, unions dependencies and escape, and proves that an End fact at a join
came from every listed normal predecessor. The separate `Summary` relation
starts empty; `no_base_no_returns` excludes a bare recursive cycle, `least`
proves leastness, and its pair-universe theorem proves finite convergence.
The finite projection keeps a pending End distinct from a successful reply,
and keeps taint, terminal failure, compatibility and pending state separate.
It retains symbolic receive sites rather than dynamic delivery identifiers,
with fixed-width dependency and frame-site bits. A draft bounded solver records
full entry/current configurations, starts its return-pair set empty and
replays configurations after each revision. The solver proves a least fixed
point for its enumerated rules. From reached configurations,
`certified_call_enters` and `certified_matched_return_replayed` connect an
actual modeled call and its matching return to solver replay. `SolverFrames`
records each dynamic frame with the reached caller that created it. From that
witness, `certified_stack_call_enters` and `certified_stack_return_replayed`
connect the actual push and matched return to solver configurations, and
`certified_stack_return_matches` excludes a wrong return port by replaying the
tainted result and checking admission. `certified_execution_reached` derives
that witness and solver reachability for every finite, healthy modeled
execution from the normalized initial seed and an empty initial frame stack.
`certified_dispatch_successor` derives the checked selected-root successor.
`certified_receive_message`, `certified_receive_empty` and
`certified_receive_end_pending` cover those concrete receive outcomes from a
reached configuration. The Message case derives the empty held list and active
root exclusion from admission. `execution_preserves_reply_consistency` keeps a
pending End separate from a returned fact throughout modeled execution.
`certified_end_reply` connects a successful reply of that pending fact to the
solver. `certified_branch_successor` covers either branch, and
`certified_forward_successor` propagates the listed operand dependencies.
`certified_processing_successor` derives the selected delivery, root and work
checks from admission and covers the actual modeled processing path.
`certified_execution_finish` combines that induction with the finish check.
From an accepted normalized seed, empty initial fact, pending reply and event
list, and an empty initial frame stack, every healthy modeled finish has a
genuine End event, no current or held delivery, empty projected same-Store
work, checked saved-frame suffixes and a Network trace. It does not assume the
finish cut or solver reachability as premises.

The revised model preserves normal returns without End and the driver's
non-End stop. Both receive-failure forms, before and after operation-token
acquisition, retain their control successors. Result constructor cases remain
separate from authenticated End provenance: an unknown or unauthenticated
End-shaped success takes a tainted alternative that healthy admission refuses.
`certified_execution_coverage` covers unfiltered modeled Execution: a healthy
endpoint is solver-reached, while a failed endpoint cannot satisfy the finish
predicate. Network failure is permanent; failed paths need no exact solver
projection to establish this accepted-finish safety result.

A separate restricted `Loop.Run` combines modeled Message, Empty and End paths.
`normal_run_end_witness` identifies the exact modeled sealed End channel and
Network transitions. `normal_run_observes_end` derives a quiet held list and
Store from a safe, quiet entry for every finite `Run`. Its Message constructor
requires a checked region path, exact held entry and matching selected C1 root.

## Model limits and implementation evidence

These modeled results do not constitute a mechanized proof of the implementation. `Loop.Run` is already
filtered by acceptance premises and is not derived from `Execution`. Its frame
fields are not connected to the actual control steps that created and returned
those frames. The unified execution includes a dispatch transition linking the current
Message entry to a capture constructed from a finite root graph and to the
selected root consumer. A rejected capture graph and a mismatched actual root
have explicit tainted successors. The selected-root projection checks the
concrete branch, held entry, owner, cleanup shape and consumer. The relation
between this graph and actual linked Core is a trusted, independently reviewed
implementation mapping rather than a mechanized Rust refinement proof. Unsupported control nodes
and paths reaching an unverified
processing operation invalidate the fact and taint the state. The unified
execution retains control continuations after Network failure. Permanent
failure prevents the concrete finish predicate from succeeding. Solver admission
rejects the modeled unsupported processing, rejected capture and mismatched
capture alternatives. Their coverage of actual linked Core and runtime
successors is checked through the implementation mapping and connected tests
below. The modeled finish theorem alone grants no actual `finish_receive` or
release authority. The implemented validator and runtime enforce their own
authenticated routes, cuts, observations and settlement checks.

The modeled call transfer uses simultaneous reads of finite argument and
capture ports, a saved caller dependency vector, and a
return assignment that replaces the caller destination. Successful End reply
replaces its destination; pending observation and failure do not. Return nodes
name their value operand. Authenticated End and inert-suffix returns reject
a derived operand; ordinary returns without an End fact may retain dependencies. Its finite
projection records saved-frame return maps and computes a conservative
dependency closure. A solver replay of a return-source mismatch produces a
tainted successor, which the checker rejects. The execution induction connects
this replay to mismatched returns and saved frames in the modeled machine.
The preflight budget must cover this computation and the remaining solver
work; its cost coverage is not proved.

The accepted [C3 correspondence](drain-correspondence.md) already covers the
focused full-state closure, matched call and return, fresh root and marker
completion. The implementation mapping relates worker, delivery, End and native
evidence to that same focused query; it does not require a second general
evaluator proof. C3's ordinary Unknown native result remains conservative.

| Boundary | Reused C3 result | Additional one-way obligation |
| --- | --- | --- |
| Helper call and return | Final-closure replay, simultaneous input reads and matched full-state returns | Rebind every selected closure alternative and return in the same focus; reverse the actual port pairs and preserve their contexts. |
| Native return | Unknown work is conservative for an unresolved request | Authenticate the actual selected binding and successful return, check the ignored Unit use, and apply the conditional host-preservation premise only on that edge. |
| Message completion | C3 tracks the selected root's completion at the same Store's matching marker | Associate the committed dynamic delivery with that root, consumer and completed cleanup before discharging it; unrelated work must remain represented. |
| End and driver | C3's normal return and suffix evidence | Bind the genuine End reply to the correct activation, outer return destination and `finish_receive` predecessor. |
| Budget | The focused analysis charges its work to the existing Core budget | Charge the added collector, identity checks and replay; establish the actual linked positive within its applicable source-derived allowance. |

The narrow `requested_interpreter` extension is implemented in the
private scoped worker query. Its bounded source mapping has independent review
and focused evidence; final assembled workspace verification and delivery
acceptance remain separate gates.
It retains boundary selection, the payload check, external-result handling and
the return edge. The conditional transfer applies to the current request at
the selected native boundary and focused Store, with the instantiated effect,
authenticated symbol and checked ignored-Unit continuation. Under the ordinary
host-preservation assumptions, the successful return preserves **any incoming
C3 work**, including Pending and Unknown, while expiring stale case and Probe
facts. Unknown, escaping, intercepted, failed and nonreturning paths supply no
such transfer. Identity collection by itself neither establishes closure nor
clears work. The query must replay all alternatives to final closure and charge
this work before it publishes a result.

A focused fixture diagnostic reached eligible native returns for one worker
side under this conditional query. The ordinary unscoped, ineligible and
resource-exhaustion paths still need their guard checks. This diagnostic does
not issue a completion fact or establish the runtime binding and host premises.

This pointwise work-preservation rule does not require a particular helper
history or a matched helper frame. Existing C3 closure covers its callers and
frames. Delivery retirement is a separate obligation: it must bind the actual
committed delivery to the selected dynamic root, consumer and completed cleanup
at the same Store, with the required caller and result evidence. A native
identity or work-preserving return alone grants no retirement permission.

The runtime association uses the existing
[`check_network_native_support`](../../../src/eval/machine.rs): it instantiates
the admitted worker's native effects for the fresh Network activation, checks
the registered symbol and selected root interpretation, and checks the installed
binding. [`try_copy_for_worker`](../../../src/foreign/source_bindings.rs)
retains that symbol identity and callback in each worker copy; invocation checks
the identity again. These checks associate the selected binding. They do not
prove its synchrony, nonreentry, visibility or Store, Network and dependency
preservation, which remain conditional host assumptions. Callback failure is
not a successful native return.

The retained model's `callInputs` relation reads `(source, destination)` pairs;
the Core collector's `existing_call_ports` gives `(callee destination, caller
or creation source)`. The implementation-to-model mapping reverses these pairs
in the same focus, preserving their contexts and charging the construction.
Every actual closure and return alternative remains subject to the existing C3
checks. This mapping is a trusted review boundary, not a theorem about Rust.

The current linked checker also recognizes a narrow pure Unit helper and an
ordered `(Worker<N>, Bytes)` receive-loop argument. It authenticates the actual
helper and recursive target, the byte comparison, each argument and projection,
and the matched top-level return. A recursive cycle alone supplies no return.
For a restored call, the checker examines every aggregate at its actual
creation context and authenticates the paired restored call and capture ports
before reading the original callee's projections. The recursive carry must be
the original expected-byte field. Generated tuple allocation preserves the
focused work state only for the authenticated entry Region and its checked
default return. Other Region routes remain conservative. These are bounded
implementation checks; the retained model does not prove their Rust mapping.

The modeled region checker uses bounded fuel and refuses cycles within its
processing graph. The correspondence of linked definitions, selected evidence,
transformed or imported control, message-derived value and capture propagation,
failure edges, older frame suffix coverage and dynamic activation instantiation
remains a review and testing obligation. The summary algebra uses abstract base
and wrapping relations rather than exact linked call/return rules. The model's
budget is not a measurement or proof of the cumulative Core budget.

The structural evaluator checks the builtin receive operation and activation
before reserving a receive. On Message, the guarded envelope survives through
reply construction; `Frame::NetworkReceiveCommit` reserves receiver-held
responsibility before committing the guard and rolls it back if commit fails.
The current structural path can invoke the selected provider for byte storage,
kind, tuple and Message construction, then invoke it again for a failure and
result if commitment or held-obligation reservation fails. Failure replies must
retain that selected context. The host End outcome also passes through reply
construction: the modeled fact is created at its successful reply edge. The
product still needs a proof relating that edge and allocation or reply failures
to the actual evaluator.
`Frame::RetainedRootCompletion` decrements the selected Store's active root at
its actual pop. These observations are a mapping target, not a proof that Rust
or native behavior refines the model.

The retained `WorkerChannel` model has one active C1 capture per Store; actual
runtime concurrency must be reconciled with that restriction. Actual native
synchrony, copied-byte commit and wake behavior, linked-Core reconstruction,
implementation tests, independent proof review and frozen gates remain
separate requirements.
