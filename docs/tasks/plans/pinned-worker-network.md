# Pinned worker network execution plan

> Historical plan: the 2026-10-31 ordinary Ash direction supersedes its
> protocol-checker and one-way completion requirements. See the
> [active plan](pinned-worker-ordinary-protocol.md).

Owned by [TASK-0058](../TASK-0058-pinned-worker-network.md). This plan orders
work and does not define semantics or authorize implementation. Original issue
acceptance remains authoritative for scope; no criterion is complete here.

## Deliveries and acceptance

1. **N1 — [#76](https://github.com/dikini/ash-lang/issues/76).** Reviewed at
   `b296e17ce9e4f1760ce73df4f4716ef0c0fb2093`: CP-0027 and DN-0058 cover entry and capture admission, endpoint authority,
   resource-free copies, FIFO, commit/failure ownership, visibility, wait races,
   stale notifications, genuine End and backing settlement. Specify actual
   source/Core admission and control-envelope provenance. CP-0027 and AD-0017
   record the accepted transition and host/channel decision. Review and verify
   this adoption on its retaining branch before N2 implementation.
   Preserve assumptions and terminal failure limits. No worker recovery,
   silent transfer or native-stack suspension. Record retained verification and
   acceptance readback before closing N1.
2. **N2 — [#77](https://github.com/dikini/ash-lang/issues/77).** With accepted
   N1, build admitted pinned workers, copied channels, notifications and
   one-way completion. Construct local resources on their owner; only it drives
   its Store. Preserve accepted unpublished, queued and receiver-held work;
   keep receiving while bounded sends finish; release only after endpoints,
   cleanup, registrations and backing users settle. Discharge the bounded
   worker/channel preservation assignment before using it for release.
   The [bounded source proof gate](../evidence/pinned-worker-channel-proof/README.md)
   passed for the reviewed four-module closure. Actual C3 completion and
   runtime/native correspondence, refinement and N-core remain pending.
3. **N3 — [#78](https://github.com/dikini/ash-lang/issues/78).** In parallel
   with N2 only when assigned, freeze the finite-list model and prove
   registration, retirement, acknowledgement, whole-entry and order-preserving
   RemoveById, freshness and successor state, and restricted checking-rule
   soundness. [CP-0028](https://github.com/dikini/ash-lang/blob/b3e16b7c31d55850ab6f879286a594b4f6cb2540/docs/proposals/CP-0028-checked-functional-network-ledger.md)
   and its bounded proof assignment were independently reviewed at
   `94c0be0375d19f8e60900d5d77be2f5caa746eb0`; the transition is accepted,
   without proof or product acceptance. Adopt any required verifier decision
   before product work. Bind untrusted plans to actual linked definitions;
   check induction, dependencies and all reachable branches. Unsupported transforms preserve a
   checkable form or reject; exhaustion grants no permission. Test mutations,
   imports and transformed Core. No general source proof language.
4. **N4 — [#79](https://github.com/dikini/ash-lang/issues/79).** After reviewed
   N2 and the N3 proof/checker gate, compose verified ledger transitions,
   actual local completion and transport premises into recursive drain
   summaries. Register children before publication; cover parents until
   authentic acknowledgement. Reject stale emptiness, forged completion,
   obsolete state, raw publication and envelope confusion; revalidate after
   transformations and through imports. A separately accepted codec extension
   and its actual-definition soundness are required before any codec-dependent
   completion or release permission. Exercise adversarial and budget cases.
5. **N5 — [#80](https://github.com/dikini/ash-lang/issues/80).** With connected
   N2–N4 and adopted normal/abandonment obligations, seal new roots but allow
   covered descendants; keep both workers and notifications serviceable for
   feedback. After stable application quiescence, close application sends,
   observe genuine End, finish service and cleanup, and settle endpoints,
   workers and backing. AppQuiet alone does not release support. Test bounded
   feedback and producing cleanup.
6. **N6 — [#81](https://github.com/dikini/ash-lang/issues/81).** Demonstrate
   request/reply using local regions/cells, retained computations, copied
   messages and an ordinary Ash binding over supported bytes/pointers. Exercise
   SQLite to the extent supported and report remaining gaps; a small fixture
   complements but does not replace that canary. Do not require obsolete
   checked/isolated FFI or process containment. Verify shutdown and failure
   limits without claims of deadlock freedom, termination or native correctness.
   Complete specification, proof/full gates, independent review, retained
   verification, acceptance updates and separately authorized Main delivery.

### Native completion sequence for the current N2 candidate

This sequence closes the native part of N2 under accepted
[CP-0027](https://github.com/dikini/ash-lang/blob/b3e16b7c31d55850ab6f879286a594b4f6cb2540/docs/proposals/CP-0027-pinned-workers-and-copied-channels.md),
[AD-0017](../../decisions/AD-0017-pinned-worker-host-and-transport.md) and the
[one-way assignment](../../design/retained-control/one-way-completion-proof-assignment.md).
It does not close N3–N6 or change C3. The local source baseline is
`8c6e23efe0d798c5949ebac79706a34972e642fd`; current Rust and Lean changes are
unretained candidates whose final pins and receipts must replace that baseline
before a delivery claim.

The actual startup path includes root native interpretation, the entry Region,
linked initializers, copied input, eager metadata and the worker call. Discovery
must follow that path rather than seed a same-typed worker directly. The current
native trace records the full request event, selected boundary and returned
edge. The borrowed `NetworkNativeIdentityScope` now feeds a production
provisional route/cut query; its supported cut issuer and runtime consumer have
passed independent review. Ordinary native handling remains conservative.
The all-owner release handoff for authenticated sealed-Worker symbolic roots
has a clear code review and its real positive reaches the lifecycle refusal;
its corrected complete harness still needs a frozen rerun. The next delivery
checkpoint is actual admitted one-way execution: qualify the canonical finish
wrapper's selected context-query clause, connect authentic End to runtime
finish, and settle worker/endpoint/backing state. These provisional facts do
not establish public completion, the full frozen N2 gate or N3 currentness.

**Mechanical checks and assumptions.** Reuse `AuthenticatedNativeRegistry`,
the actual network owner/spine and `NetworkBodyFacts`, and
`SourceNativeBindings`. The validator authenticates original symbol identity
and complete effect instances; `check_network_native_support` checks the worker
instance under the fresh runtime activation and root interpretation; invocation
checks the same symbol Arc and calls its associated callback. These checks do
not establish synchrony, nonreentry, retention behavior, thread safety,
visibility or preservation of modeled Store/network/dependencies. State those
ordinary binding/module assumptions explicitly in the conditional transfer and
its evidence. Do not add a second binding registry or generic native certificate.
An actual successful native return completes that invocation locally. It does
not settle shared foreign state or backing needed by later native uses; those
obligations remain live under CP-0027 until their ordinary contract permits
settlement.

1. **Stabilize the private discovery handoff — checker owner.** Finish focused
   discovery from the actual startup and same Store, including failed-focus
   convergence. Borrow the validator identity scope before moving entry facts
   into admission metadata. Use the existing original-node mapping to associate
   Core occurrences with control/value ports. A private collector must retain
   the final converged values, trace, exact owner/side, selected Store/root and
   call/return witnesses; it must not make a failed C3 query successful or export
   partial completion authority. The N3 owner can use a separate discovery view
   for actual provider/dispatch identity without requiring C3 Empty. That view
   grants no completion or release. Evidence: the real linked startup reaches
   the native helper and actual provider/dispatch; failed or unresolved focus
   publishes no accepted completion result.
2. **Establish coverage and the cost boundary — checker owner, with proof
   owner checking the relation.** Enumerate every final-closure request route,
   selected source/native boundary, branch, call alternative, actual matched
   return, capture and failure continuation from those reached states. Replay
   after value or target growth; begin normal-return summaries empty. Associate
   each result with its actual operand and destination, preserving simultaneous
   call reads and saved caller state. Unknown targets, missing alternatives,
   changed evidence, stale contexts and exhausted work refuse permission.
   Charge collector construction, table capacity scans, replay and retained
   witnesses to the existing cumulative budget. The current diagnostic cost of
   roughly 26–38 million units is not a public-path cost measurement. The
   standalone Core allowance is 983040 units; modular source validation instead
   receives the remaining input-derived IndependentCore ledger. Measure the
   required fixture through its intended public entry point before assigning
   optimization work. Reuse final analysis state where needed. Any proposed
   limit calibration requires explicit justification and acceptance; do not
   silently raise the limit. Keep new worker work boxed
   or outlined outside ordinary discovery frames and preserve the required
   64 KiB stack check. Evidence: complete successor accounting on the linked
   positive and required negative controls, a production-budget positive, and
   exact/short budget refusal with no partial permission.
3. **Connect the native return condition — checker and proof owners.** Match
   the trace's full Event, selected native boundary and actual returned edge
   to the scope's original registered symbol, instantiated effect and admitted
   worker side. A conditional transfer may preserve the pre-call work only at
   that successful return and under the stated binding assumptions. It must
   preserve prior pending/unknown work, operand dependencies and all saved
   suffix/cleanup obligations; issuance and binding admission clear nothing.
   A nearer source handler follows its real clause and completion path. Missing
   binding, wrong instance, callback/interface failure or nonreturn supplies no
   successful native edge. Keep ordinary C3 conservative; only the private
   network query may consume the proved transfer for this exact route.
   `Region.native` currently has no result ports: support the required actual
   synchronous native positive with an ignored Unit result, documenting that
   exact use. Refuse Address results and consumed results in this completion
   fragment unless their dependency/result-use correspondence is established.
   CP-0027 permits this sufficient narrow N2 fragment; arbitrary native result
   support is not an additional closure requirement. The ignored-result case
   still needs the actual imported/native positive and all other cut evidence.
   Evidence: actual source-native and imported-helper positives, intercepted
   and substituted helpers, changed symbol/instance, result escape and native
   failure controls, with the actual linked occurrence identified in each case.
4. **Finish acceptance-to-completion — proof owner, then independent review.**
   Compile the repaired full one-way development and audit its axioms. Keep the
   oldest outer driver separate from inert recursive suffixes, represent real
   normal returns without End, preserve failure successors and exclude unknown
   End-success returns. Derive coverage from unfiltered modeled Execution;
   acceptance-filtered `Loop.Run` is insufficient. Prove the conditional native
   transfer and connect collected linked Core and runtime successors to the
   model, including result use, actual root/marker, same-Store C3, older frames
   and cleanup. Derive the matching held delivery's finish and genuine End;
   do not assume the desired cut or that successful return settled foreign
   backing. Evidence: a successful frozen Lean source/axiom gate plus reviewed
   rule-by-rule Core/runtime correspondence and the assignment's positive,
   negative, import, transform, failure and budget evidence. Source compilation
   alone does not establish Rust or native refinement.
5. **Enable only the connected runtime permission — assigned product writer.**
   After steps 1–4 are reviewed, connect the validator result to the actual
   admission and fresh runtime activation. Tie Message responsibility to the
   actual committed delivery and release it only at that delivery's completed
   selected root, suffixes and cleanup. Tie finish_receive to genuine End and
   completion of every earlier held delivery. Normal joins and backing release
   additionally require worker scopes, endpoint operations, registrations,
   callbacks and native backing users to settle. Keep terminal failure and
   incomplete teardown failclosed; the present failure parking/retention cannot
   become ordinary release merely because a native call returned. Evidence:
   multiple real messages and Empty retries through recursive/imported/native
   processing, clean completion and settlement, plus failure and outstanding
   user/callback cases that retain protection. Obtain the focused native gate,
   independent review, retained verification and N-core full gate before N2
   dependents rely on the result.

Steps 1–3 are the checker bottleneck. The proof owner can repair and compile
the modeled control relation while the checker completes discovery; agree the
collector-to-model fields before either owner extends its interface. The N3
owner can complete ledger/Core proofs and actual provider/dispatch discovery in
parallel, consuming no native completion claim. Serialize shared Rust writes
and every Cargo/proof gate through the assigned operator. Do not spend another
full gate on a diagnostic-only path; establish the actual public-path budget
before claiming a production cost failure.

No semantic change is authorized here. Return to the governing proposal if a
required binding behavior cannot be stated as the accepted ordinary foreign
assumption, a required result cannot be represented by the checked fragment, or
runtime concurrency cannot be related to the model's one active C1 capture.
Report such a gap explicitly rather than weakening C3, omitting a successor or
marking the native obligation complete. After N2, retain the existing N3 proof
and actual-Core gate, separately accepted N4 codec and driver composition, N5
shutdown and N6 SQLite/example/specification work in the order above. A native
positive is necessary evidence, not the M4 completion gate.

## Reuse boundary and next delivery

M1–M3 already supply owner and interpreter compatibility, actual root/cleanup
completion, full-state call/return matching, final value-closure replay and
conservative C3 joins. Extend those judgments for M4; do not build a second
general execution engine or require formal verification of Rust. Required
bounded proofs and independent review must cover the actual new implementation
and its correspondence to the retained foundations.

For N2, static integration now supplies both actual worker End descriptors and
the reviewed Message processing cut. The integrated validator and required
same-binary End negatives pass at `/tmp/ash-end27/`; the valid case uses
120,488,904 cumulative work units within its unchanged source-derived allowance.
The lifecycle Registry gate remains enforced.

The next delivery is working native shutdown: consume the exact End descriptor
and current host observation at finish, require genuinely retired held
deliveries, complete both receive endpoints, dispose successful workers, join
carriers and settle drained transport registrations and backing users. Keep
runtime code moving in parallel with N3 model proofs; review their actual
implementation-to-model mapping without formally verifying Rust. Replace the
Registry gate only for the authenticated supported case after the connected
lifecycle is ready. Unsupported cases keep their existing refusal behavior.

Native preservation is pointwise in the existing work projection: it neither
identifies a delivery nor retires a root. It needs no separate dynamic helper
ancestry proof. Actual delivery/activation lineage remains required when
retiring a specific obligation. Reuse C3 selected-clause and restoration
semantics for recursive caller stacks; do not duplicate them with a new stack
engine or require unique abstract addresses.
For N3, connect the actual insertion definition to its existing checked model
and publish a conditional definition law. Its premises may include finite
represented inputs and a faithfully selected default provider; actual live
initialization, provider selection and currentness belong at the consuming
call. They do not block the definition law. The arena mapping must still cover
exact query/allocation operations, arguments, captures and returned values.
Reuse that connection for the remaining original schemas, then establish
freshness and conservative successor/currentness transfer before publishing
usable ledger or release facts. No conditional helper summary supplies those
premises merely by being accepted.

The previous N2/N3 hour ranges were withdrawn as unsupported. Re-estimate from
connected native completion and actual-arena conditional Insert acceptance,
separating inherited work from the remaining M4 changes.

## Checkpoints and ownership

The orchestrator schedules gates; the assigned developer is the sole product
writer and heavy-build operator. Reviewers inspect immutable pins and receipts.

- **N-core:** connected worker/channel and bounded preservation ready for
  dependents. Fresh full workspace gate on the pinned integrated candidate;
  owner: assigned developer. Independent review and actual retained verification
  remain required for every slice.
- **N-proof:** frozen ledger, checked soundness and actual linked Core
  reconstruction ready for N4/N5 release reasoning. Fresh proof and full
  workspace gate on pinned integrated inputs; owner: assigned developer.
- **N-final:** integrated bidirectional shutdown, examples and specification.
  Fresh proof, native and full workspace gate; independent final review,
  retained verification and acceptance readback. Owner: assigned developer.
  This gate may serve as pre-Main only when inputs remain equal. Main is a
  separate human gate and remains outside milestone-branch integration.

Each delivery records exact source and configuration pins, focused commands and
results, review, retained ref and commit, original acceptance subset, remaining
scope and next owner. Do not mark a criterion complete while any original
obligation or required checkpoint remains. Preserve M1–M3 evidence and the
compatible shared cache; no fresh cold build is implied.
