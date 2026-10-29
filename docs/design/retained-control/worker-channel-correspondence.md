# Bounded worker and channel model: correspondence obligations

`WorkerChannel.lean` is a candidate for independent review and the frozen
AD-0012 gate. Local language-server diagnostics do not establish a retained
proof result. This model is conditional evidence for CP-0027 and AD-0017, not a
proof of the Rust implementation, operating system or Ash evaluator.

## State and inductive claims

There are exactly two worker identities. `DistinctStores` requires different
C1 store and owner identities, and each worker's C1 `Unique`, `ContextSafe`,
`SlotIdsUnique` and `GenerationBounded` properties are preserved by actual C1
steps. The initial theorem requires those properties for both supplied stores.
The actor for a local store step must equal its owner. A single commit requires
both workers prepared; every execution, operation, registration and dispatch
step requires that joint commit. Preparation can be aborted only before commit.

Each direction retains ordered accepted, received and queued entries. Each
entry contains an identity and its immutable byte snapshot. `Channel.Safe`
requires distinct accepted identities, the FIFO equation and capacity bound,
and a permutation from received entries to completed plus held entries. A
send may introduce only an unused identity; receive transfers the exact head to
held work. Failed preparation or copying is represented by a no-change step.
Completion selects an exact whole held entry, and the invariant proves that a
completed identity cannot also be live. Completions may occur out of order.

Dispatch binds a held entry to the receiver's actual C1 `Step.launch`; its
capture has the entry identity as both branch and owned identity. A dispatched
fact remains linked to an actual held entry under every modeled transition.
Finishing the selected entry requires the same identity and a matching active
capture with C1 `ReadyToFinish`; it performs that capture's actual C1
`Step.finish`, removes the selected entry and clears its dispatch fact. Generic
local C1 steps cannot finish a dispatched capture outside this transition.
Worker return requires C1 `NoWork`, a valid close phase and actual C1
`Step.release`. The imported C1 theorem establishes the modeled cleanup and
nested-control premises. The C3 correspondence must still establish that the
actual source, handler suffixes and cleanup reach this specific C1 completion
boundary; a name or fabricated status is not evidence.

Each lane and interest has a finite keyed set of active registrations. Each
registration has its own pending bit. Registration chooses a fresh generation
without replacing other registrations. Readiness refresh sets the pending bit
of every matching active registration, and repeated refreshes coalesce. Poll
refreshes all interests, selects a pending registration and clears only that
bit; other pending registrations remain accounted for. The model records an
in-flight wake under a separate fresh callback identity until completion.
Cancellation removes only its selected registration and pending bit; it does
not erase an in-flight wake. The validity invariant bounds issued generations
and callback identities, so old identities cannot become fresh. The two-watch
lemmas cover repeated registration, simultaneous readiness, polling one and
cancelling one without losing the other. Operations likewise occupy distinct,
monotone identities and a channel step consumes the exact current operation
for its owning polarity. The model uses unbounded naturals; native exhaustion
must refuse rather than wrap.

Send sealing and genuine receive End are distinct steps. End requires the send
side sealed, the queue empty and the channel healthy; the inductive invariant
then gives equality of accepted and received histories. End alone does not
complete held receiver work. Each worker can return only after its own sender
is sealed, its receiver has observed End, its receiver-held entries are
finished and its C1 store actually closes. Normal backing release requires both
workers returned, both directions sealed and End observed, queues and held
entries empty, and all operations, active registrations, callback identities and
dispatched facts absent. A released network has no further modeled transition.
The release conditions inspect concrete state; no step assumes an arbitrary
successor satisfies the global invariant.

Terminal failure atomically marks both directions failed and rechecks all
active watches. The failure invariant proves that no later step or finite
trace accepts another send. Registration after failure observes terminal
readiness and creates its wake even if no subsequent channel change occurs.
Existing operations can be refused, watches cancelled, callbacks completed,
and already-ready processing can finish. Normal release cannot occur after
failure; support stays retained until a separately specified failure-disposal
contract permits release. This model makes no successful-drain claim for that
case.

## Implementation correspondence still required

The frozen model and actual implementation need independent comparison. Map
every actual entry, operation, callback and failure transition to a matching
model step or documented stutter; prove the initial C1 and distinct-store
premises. In particular:

- Actual copied bytes must come from protected live source storage, preserve
  every byte, and be independently owned and visible before atomic acceptance.
  Receive must commit its local copy before moving the exact queue head into
  receiver responsibility. Failure before that commit keeps the original entry
  and obligation. This model does not prove native memory safety or visibility.
- Actual send and receive authorities must map to the fixed owner and polarity
  in the model; their operations and message identities cannot be duplicated or
  reused. FIFO and capacity changes must linearize to the modeled synchronized
  steps. The model selects atomic acceptance/publication; an uncertain native
  outcome is not a normal refusal and needs the accepted contract's retained
  reservation and resolution treatment.
- Associate each accepted message with the actual unique C1 root capture at
  dispatch. Verify that later resume, handler suffix and cleanup transitions
  preserve that identity, and that only the corresponding C3 actual-completion
  boundary uses `finishProcessing`. The `noDispatchedFinish` restriction on
  generic local steps must be checked against all real control successors. C1
  proof and source correspondence do not themselves prove Rust execution.
- Actual watch state, registration, poll, cancellation and callback lifetimes
  must match the finite keyed registrations, pending bits, in-flight wake
  identities and atomic level rechecks. A live native callback, registered wait,
  or operation may not disappear from the model before actual completion. Prove
  no future callback or access after settlement, including cancellation and
  stale-notification races.
- Show actual seal, End, worker return and backing destruction satisfy the
  modeled preconditions. Return requires actual worker and cleanup completion;
  a queue-empty observation, copied bytes or callback name cannot supply it.
  Partial entry and postcommit failure retain every owner and support obligation.
- Entry admission and private control-envelope origin, OS pinning, native join,
  synchronization, overflow refusal and byte visibility are separate checks or
  explicit host assumptions. Distinct abstract Store identities do not by
  themselves prove physical resource non-aliasing. Liveness, scheduling fairness,
  deadlock freedom, native memory safety and the N3 bidirectional ledger are
  outside this finite safety model.

## Transport correspondence at `f5ae9b6`

The private candidate transport (`src/eval/network_transport.rs`)
at `f5ae9b692b07dbd1396dbddb946a3fc2c8fbbf1d` is evidence for the following
mapping. That implementation is outside this proof-only delivery.
These observations do not prove that every Rust transition
refines the model or that higher-level worker completion exists.

- The host allocates `Shared` with fallible `triomphe::Arc::try_new`, assigns a
  checked activation identity and keeps a mutex around both directions and their
  watches. Admission, worker pinning and a C1 store are outside this transport.
- `try_send` holds a per-direction `SendGuard`, makes a fallible byte copy,
  rechecks state under the mutex, then pushes the envelope and refreshes watches.
  The push is the candidate atomic acceptance/publication step. Full, closed,
  allocation failure and failed-state outcomes publish no envelope.
- `reserve_receive` removes the head into an owned `ReceiveGuard` and marks a
  reservation. For the abstract FIFO, that guard-held original remains the
  queue head until `ReceiveGuard::commit`; capacity and readability include the
  reservation. `snapshot` is fallible, and dropping an uncommitted guard
  restores the original head. The guard retains an `Arc` to backing. Map the
  real operation and guard lifetime to the model's live operation identity;
  establish that a successful receiver-owned copy and `commit` correspond to
  receipt before discharging that operation.
- The host maintains one bounded vector of up to 64 watches across both sides
  and interests. Each has an activation, side, globally issued checked
  generation, interest and pending bit. The model permits any finite number of
  registrations, so it overapproximates this host limit; host refusal for the
  limit, allocation or exhaustion maps to `refuseWatch`, which publishes no
  registration. A refinement must assign each concrete registration to its
  lane and interest, preserve its stable identity across cancellation and poll,
  and account for the concrete global generation sequence versus the model's
  per-group sequence. Do not equate generation numbers without that mapping.
- `refresh` scans all watches and sets each ready watch's pending bit; setting
  it repeatedly coalesces. `poll_wake` refreshes first, then selects and clears
  one pending watch for the requested side. `Network.advance`, `pollWake` and
  `pollEmpty` perform the matching global refresh and single-selection cases;
  the model does not impose the host cursor's selection order. The returned
  registration is a value: if its consumer retains or can access backing,
  represent that activity by the model's distinct in-flight wake until it has
  actually finished. If no such activity survives the return, it may discharge
  that conservative model obligation immediately.
- `finish_send` seals a direction and refreshes readiness. `fail` marks terminal
  failure and refreshes watches when it obtains the lock. The host transport
  `settle` checks both seals, queue/reservation/send users and watch emptiness;
  it explicitly does not establish worker completion or receiver processing.
  The modeled release additionally requires genuine End and C1/C3 completion.
  The caller must compose these checks; transport settlement alone is not the
  network release proof. Lock poisoning and unsuccessful failure reporting
  require an explicit implementation correspondence, not an assumed wake.

## Proposed frozen closure

The new `WorkerChannel` module imports `Std` and the retained C1 `Ownership`
module. Use the frozen C3 evidence as parent and retain its registered
`Ownership`, `OwnershipExamples` and `DrainSafety` modules. A fresh runner
configuration must pin the new source and review, the existing direct import,
compiler/library and report list. The exact expected theorem names are the
`#print axioms` declarations at the end of the model; the runner checks each
and accepts only its standard axiom set. Source review precedes the frozen
gate. An LSP workspace and its locally compiled import are development aids,
not a gate receipt. Rust/native correspondence and the connected N-core gate
remain separate.
