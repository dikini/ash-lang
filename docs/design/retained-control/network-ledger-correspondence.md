# N3 modeled closure: correspondence for independent review

Status: provisional. This note maps a frozen source candidate to modeled rules;
it is not a proof of Rust, the production evaluator, N4 premises, or a
published network-completion permission. The N3 proof and this correspondence
require independent review together on the final integrated source pin.

The current source candidate is `target/ash-m4-evidence/n3-pr-checkout`.
Its source manifest `target/ash-m4-evidence/n3-arena-candidate-before.sha256`
has SHA-256 `6b5b2d6c01616dc0be7a4b96e73721a4871e9aeb01e55240d7906ded1d151dc3`.
The earlier focused import and transformation tests used manifest
`n3-import-transform-before.sha256`, SHA-256
`5e118d3663d939b5a2ca2dd364c2932915f4e3df27b0926ce41f5331e60f2992`.
The final integrated gate must pin the resulting full tree. Selected current
source files are:

| Relative source path | SHA-256 |
| --- | --- |
| `src/core/ledger_checker.rs` | `495c9f121f1cba5520a487340e41e032e9aac9b481f2678a3413175522314e03` |
| `src/core/closure.rs` | `2e6e21603a608ba01f1ff907c0d3a6317585b3a64d63b6f56f0e1b2f230e7571` |
| `src/core/retirement.rs` | `cadee03bb9724ee3f169a321caf1fdcdad94ce6253a1650465ebe68a78dc2c43` |
| `src/core/acknowledgement.rs` | `7f89795487e0a79c5dbcce31d31ad8dc6050b5e177490222d7c75a59b6b115db` |
| `src/core/capture/network_ledger.rs` | `46eb6d644eeb1660ecf8ceba70cbee116e29f3fd9bcc3047a7b9c25838e2de0d` |
| `src/core/capture/transition_observation.rs` | `23fac1c47a4d1b13e6b93ce5841448e8ee219d144ce1d1d09f8aa29636437b0f` |
| `src/core/capture/network_end.rs` | `312f545d63faf96b9e939685494f684d98361ce1fed63b8890af9779cd580341` |
| `src/core/capture/network_completion.rs` | `5ca27be5de34e319ff5372dd7686d63b045e8a59674642116f1dc01e14b811e6` |
| `src/core/driver.rs` | `3cf01d7b9f805d0cc199673f21293d911bad17ab92805d543e664b3b9da0cad1` |
| `src/core/validate.rs` | `360a5b6eee116f9d2bb61fe9666397ade406b21735c35f5aa95ef27fbed0debf` |
| `tests/fixtures/n3-ledger-transitions.ash` | `984ac68351cc955845344acb298933686277861c196a65492a7636629c02018f` |

## Data and evaluation boundary

A nominated plan is untrusted. `linked_initializer`, candidate uniqueness,
nominal checks and `stage` in the transition checkers bind actual linked
stored closures, their captures and arguments. Helper checks bind the same
comparison and projection dependencies; `require_distinct` and exact captures
exclude ordinary dependency cycles in these shapes. The reviewer must check
that each actual selected closure and all transitive helper captures are those
bound values. The modeled `Checker.checkLinkedSchema` resolves one definition
and its actual modeled body; its rank-checked dependency rules are separate
from Rust and require the correspondence just described.

The relation to a modeled ledger must decode finite acyclic whole record,
child and output sequences, preserving their values and order. It must prove
unique keys, nonnegative serial and fixed unique allocator identities from
checked initialization and every current successor. Model `Nat` worker and peer
values correspond only to nonnegative representable source integers with
equality preserved; the model's serial is a mathematical `Int`. Nominal IDs,
phases, result and list constructors correspond by linked identity, not name.
An arbitrary source copy or matching type does not establish this relation.
Linked checker witnesses compare the address of their borrowed Core arena;
trait-object vtable identity is not used as arena identity. Separate checks
still bind the linked program and each arena-local node.
`observe_ledger_plan` checks a fixed, nonnegative literal allocator across the
nominated registrations (`network_ledger.rs:3780`); `validate.rs:3242`
compares the fixed values and Root/Worker roles when both sides of the same
owner are present. A one-sided observation retains the peer-allocator and
history premise. These source checks do not establish the finite issued
history or authorization in a different activation.
Registration and root initialization have existing `CoreRecordRegistration`
and `CoreRootInitialization` derivations for their admitted Core shapes.

The correspondence must establish actual left-to-right call-by-value
execution, complete reached nominal/equality arms, exact substitutions and
normal return. It must establish the same captured default Region allocator for
all allocating operations: successful allocation preserves existing values,
creates fresh initialized storage and resumes once; refusal or failure has no
normal return. Unknown or intercepted provider, local handler, unproved callback
or unsupported operand must reject, not be treated as pure by an empty effect
row. `CoreEval` and `CoreRegion` give the modeled allocation and stored-value
laws, but do not prove their Rust implementation. Linked finite lookup,
update, removal and insertion must use the actual nominated bodies and exact
arguments; finite/unique inputs and projected-key equality must be established
at each helper call. A helper call's normal return, not a producer annotation,
supplies its modeled result. Sufficient modeled fuel says nothing about actual
termination or allocation success.

`ClosureCheck`, `RetirementCheck` and `AcknowledgementCheck` each resolve a
modeled linked body, check the relevant helper bodies, evaluate its reachable
branches, and prove every normal returned model value equals `close`, `retire`
or `acknowledge`, respectively. These are schema-specific modeled evaluators.
Mapping an actual return to a modeled evaluation is a substantive review
obligation; assuming the desired ideal transition is not a substitute.

## Exact transition correspondence

- **Close**: `check_nominated_closure_call` checks `(ledger, wanted)` and the
  entry and finish closures. `check_conditional_closure` checks Record lookup
  and update, actual constructor tags, binding identities and arguments.
  Missing lookup and already-Closed return the original input. For Open, the
  replacement contains the actual record ID, parent, Closed tag and original
  children; the Ledger contains original counter, updated records and original
  outputs. The selected update uses the actual key and whole record list.
- **Retire**: `check_nominated_retirement_call` checks `(ledger, wanted)` and
  the entry, work, found, parent, phase, children and commit stages, plus
  Record lookup/removal and output append. Root, absent record, absent parent,
  Open record and nonempty children return the original input. Closed,
  childless Work with a parent returns original counter, the exact removal
  result and original outputs appended with `Ack(actual parent, wanted)`.
  Rust's Root fast path corresponds to a model-only lookup stutter: model
  lookup followed by the root guard also returns the original input. No actual
  lookup is assumed on the fast path.
- **Ack**: `check_nominated_acknowledgement_call` checks ordered
  `(ledger, parent, child, peer)` plus record/child lookup, child removal and
  record update. Missing parent, missing child and destination/peer mismatch
  return the original input; duplicate acknowledgement is missing-child only
  when the actual current successor is used. On a match, removal receives the
  requested child and the selected record's actual children. The replacement
  retains the whole selected record's ID, parent and phase, and uses the exact
  removal result; the returned Ledger retains its actual counter and outputs.
  Authentication of the exact peer and envelope is a separate N4 premise.

Each successful helper result is the actual evaluated value in the same
checked call; the representation and helper laws derive the model's branch,
fields and frame, including all no-op outcomes. The matched return and checked
constructor operands must be independently audited at this pin. The
`successor_fields`, `replacement_fields` and `returns` node coordinates are
witnesses to check, not semantic facts on their own.

## Control and history boundary

`NetworkLedgerHistoryControl` composes the four linked modeled checker
soundness theorems with `Tracked.run` and `Tracked.runAll`. Its `State` fixes
activation and owner, stores the modeled Core environment and current value,
and requires the role's actual environment lookup to return that same value.
The represented value is related to the tracked ledger by `rep`; the linked
`Program` is a parameter of the whole trace and cannot change between steps.

`returned` checks actual Core normal evaluation and a linked modeled return,
updates tracked history, and places the actual result and projected ledger in
a pending state. It removes the current port. A direct Core `bind`, or the
reached `Selected` two-field result match, must bind that exact pending value
before it becomes current. The result-match rule requires the first nominated
ledger binder to occur in the new arm bindings, with distinct ledger and
status binders; lookup cannot fall through to an inherited caller binding.
`bindAlias` requires an actual variable read from the prior current role.
`enterCall` checks the actual Apply node, function and argument evaluation,
stored `CallTarget`, the resolved stored tuple, its ordinary field view, and a
selected formal tuple match. The same in-range index selects the actual
current value and the newly bound ledger formal for an arbitrary positive
arity and ledger position. It does not require distinct runtime values for
distinct source ports. Exact linked-call argument association remains
`inputAt`, an explicit
trusted correspondence premise. The model does not prove the C3-to-event
relation, and a pending result cannot publish a current fact before binding.

`source_position`, `entered_call`, `matched_source_return`,
`returned_ledger_port`, `entered_driver` and `advance_successor` are the source
operations to audit against these steps. Registration uses the actual returned
pair's reached match arm; the other transitions return a Ledger. Binder
matching must use the actual result from the same call, not an old input or
copied coordinate. Recursive entry binds the actual current successor through
the checked call, evaluated argument tuple and selected formal projection.
`observe` requires the exact current value; a returned successor invalidates
the old observation. Reuse of an old value after a no-op requires actual
returned value equality or a separately established equality.

`driver.rs:30` accepts any positive arity and in-range ledger field;
`driver_formal_projection` (`network_ledger.rs:1394`) checks each field.
The reviewed V5 rule covers those modeled choices by the same actual/formal
index. Its concrete stored tuple, matching and binding must be independently
compared with C3 port identity. The Rust checks on extra source ports and
captures remain additional conservative source restrictions; they do not imply
that different ports or binders have unequal runtime values. The actual Rust
and C3 mapping remains a trusted correspondence; the modeled rule alone does
not prove it.

The candidate's `network_end.rs:53` allows an ordinary checked processing
prefix before a tail-recursive non-End path. At `:111` the prefix must be a
single Match arm whose pattern is either a wildcard or a nonempty flat tuple
of binders and wildcards. The tuple field scan is charged to the same budget;
nested, refutable or multiple arms reject. The checker still requires the
actual End arm to return true, non-End arms to return false or reach the
nominated recursive binder, and the existing worker/owner, finish and matched
return checks. This shape change permits evaluating the processing expression
before the recursive call; it is not evidence that processing or retained
control has completed. `CoreEval` uses left-to-right evaluation, `Attempt` and
`Selected` for reached matches, and the generalized `enterCall` checks the
actual recursive tuple and selected ledger field. The Rust-to-model mapping
must connect those checked source nodes, environments and normal returns. The
N2 End, worker and finish checks retain their own evidence obligations.

The `callReturn` rule restores the caller only after an actual Core call
normal return, an exact caller Bind, the same tracked state and current value,
a surviving caller binding and a matched C3 return witness. The trusted
`returnMatch` relation must mean the very same entered call, frame, caller and
callee contexts and return, not merely matching numbers. Unsupported or
mutating calls must invalidate the old current fact.

`joinKeep` requires both paths to agree on activation, owner, tracked state,
current value, point, context and role, plus a correspondence to the actual
join. Unknown capture, reentry and joins map to `invalidate`, which clears
current and pending values. `receive` requires exclusive control and a modeled
ordered flow: observed Message, commit, reply and matched return; observed
non-Message, matching reply and return; or observed Message followed by
Failure, failure reply and return. `receiveActual` connects the witness, call,
ordered events and the exact before/after modeled state to C3; it must prove
the actual outcome, checked operation/owner/side, message commit, reply and
matching frame restoration. The model does not derive this relation from
coordinates. The concrete source mapping starts with `entered_call` (`network_ledger.rs:1088`)
and `checked_context_capture` (`:523`) for the nominated closure, caller and
selected Region origin. The source must select the expected receive operation
and worker owner/side (`:2523`), then check the exact stage sequence
(`:2528`), and `matched_source_return` (`:1133`) must restore the saved
caller context, role and current port under the same call witness. A received
message may allocate buffers or other storage. V5's receive rule holds its
modeled `Store` fixed; the correspondence must interpret that store as the
ledger-reachable projection, or provide a retained-representation relation,
so that those fresh allocations preserve every reachable ledger value and
subsequent modeled allocation remains fresh under a consistent location
mapping. It must not assert that the complete concrete runtime heap or its
allocator counter is unchanged. This projection, selected provider behavior,
nonreentry and actual matched restoration are explicit premises, not proved by
the presence of coordinates. N4 must establish exclusive ownership through
suspension and restoration and exclude reentry, mutation and unknown joins.

Budget exhaustion must reject before publication, with no partial fact. The
existing abstract `NetworkLedgerBudget` models atomic publication only; the
actual cumulative charges, retries, and N3 publication boundary require
source-level evidence. `PendingLedgerObservation` (`network_ledger.rs:3558`) remains provisional,
stores source coordinates for revalidation in the same worker focus and
carries requirements for issued history, peer allocator, exclusive update and
peer authentication. The production worklist checks call returns, successor
bindings and joins in `network_ledger.rs`. The test-only observer in
`transition_observation.rs:174` separately follows a checked successor;
at `:915` it matches the normal return, and at `:934` it checks incoming
edges for the same witness, result and caller context. These observations do
not publish a dynamic current ledger by themselves.

`with_observed_ledger_plan` (`network_ledger.rs:3724`) also provides a scoped
`SameFocusLedger` query (`:3578`). `checked_input` (`:3613`) ties a nominated
source site and variable binder to the same reached state, caller context and
must-joined current port, without exporting the port. A caller must separately
bind that variable to its actual call or field. The callback result remains
conditional and must be discarded if any subsequent full validation fails;
its source coordinates and recorded closure targets are requests for
revalidation, not a return-value, output-envelope or network permission. The
actual activation is the live worker focus, not a runtime activation ID. N4
must independently establish exclusive update, peer and output relationships.

## Linked fixture and budget evidence

The source candidate includes `retirement_successor_is_acknowledgement_input_and_old_alias_is_stale`
(`network_ledger.rs:4131`), whose linked production path nominates actual
registration, Close, Retire and Ack calls and checks their observation
identities. In the fixture's modeled execution, Close and Retire target a missing Work
record and are no-ops, while Ack removes a matching Root child. The linked
validation test checks the call and result identities; it is not a native
execution receipt. The fixture does not exercise successful retirement or
Ack output emission. The stale variant tests rejection of an
old successor input. `requested_ledger_plan_runs_inside_full_linked_validation`
(`:4147`) adds a renamed-binder case. The shared-budget test (`:4248`)
measures the observer on one settled linked focus, then checks the exact
allowance, one unit short, a pre-spent allowance and retries without resetting
the exhausted budgets. A separate full-validator query with a pre-spent
allowance expects Resource and returns no observation. The focused r2 batch
passed seven of eight cases, including the mixed and budget cases; its sole
failure was the receive negative test harness. The r3 test-only repair passed
the canonical receive case, including that negative. The r2 raw log SHA-256
is `490a6c574113b79894f6a5a2cc7b6186777ee652b5cb13a37bfe967ab89a6d53`;
the r3 raw log SHA-256 is
`c7e97c23f5aacd5801663ae699f00d6c1689a124b9099bb8f051f0172847078f`.
The `imported_ledger_and_transformed_core_are_rechecked` case (`:4186`)
passed with a separately imported ledger module on the full linked-validator
path and rejected a same-typed changed helper before publication. The existing
Network transform returns `InvalidValidatedInput`, which the test expects before
any observation. The ledger-only `linked_registration_counter_uses_the_returned_successor_field`
case (`ledger_checker.rs:5163`) passed after a supported identity traversal:
the rebuilt Core has a fresh arena, rejects the old nomination, independently
validates with linked evidence, and reconstructs the call, result and helper
relationships. These two focused cases passed in the raw log SHA-256
`585ed648a112e698dcdd2e97da493fe7bf81911febca976abddd6074977328bb`.
The complete integrated gate remains pending. Full coverage of successful retirement emission, wrong-peer and duplicate
acknowledgements, linked mutations, transforms, failed retries and the governing
assignment's other cases remains subject to the combined evidence and review.

## Network boundary

The reused `NetworkLedgerProtocol` models initialized workers, actual modeled
ledger actions, pending outputs, work/ack flights and replacement of one
tracked ledger. `initialized_protocol_graph_rooted` proves rooted graph
coverage, `initialized_protocol_token_invariants` token uniqueness and
coverage, and `initialized_protocol_quiet_trace_stable` stable quiet for
finite model traces. `NetworkLedgerCoverageClosure.stable_app_quiet` adds an
explicit conditional correspondence from each real step to a protocol trace,
a current-root probe relation, and coverage of each active real item by a
modeled token. It requires distinct owners and names actual completion, honest
codec, authenticated peer, faithful transport, disciplined emission,
at-most-once dispatch, closed admission and absence of unaccounted producers.

These are not discharged by the ledger. The correspondence must justify
reservation before publication; exact codec and peer on receipt; installation
before dispatch; retained control and actual local completion before close;
retirement and ack emission; and matching removal only after authentic
receipt. Protocol close itself does not establish local completion; that is a
real-step mapping premise. Any uncontrolled raw endpoint, unregistered
producer, forged or duplicate dispatch, lost/misdecoded message or stale root
observation invalidates the mapping. AppQuiet is not backing or endpoint
settlement. No N4 or N5 permission is established here.

## Open gates

Independent review must audit this mapping against the final retained source,
actual linked tests and frozen proof/toolchain. The V5 Lean closure receipt is
`n3-proof-closure-v5/lean/verification-v5.log`, SHA-256
`8d8f2430587fcb1dda0629065105b8fc48a3f01d5c141b8a76f7887437055e68`;
its before/after source manifests both hash to
`8ea99806d97ad6a0dd6827c8f0514ed6e70548773db59639a2e72870363dd643`, and
its tool pins match. The named theorem axiom inventory contains only
`propext`, `Classical.choice` and `Quot.sound`. Independent review cleared the
modeled V5 delta and its receipt; that review does not discharge the trusted
actual-source correspondence. Independent review and the fresh integrated
proof and workspace gates remain required on the final source.

The conditional currentness and network premises remain undischarged until N4.
Runtime/evaluator/Rust correctness, resource-failure and codec/transport
correspondence remain trusted or separately verified according to their owning
tasks. This note is not a source integration receipt or Main gate.
