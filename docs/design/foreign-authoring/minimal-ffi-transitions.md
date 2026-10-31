# Canonical transitions for the minimal FFI cases

> Status: superseded checked-host design. These contracts are not implemented
> by current ffi-ash. [DN-0057](../DN-0057-checked-ffi-module-boundaries.md)
> records their disposition; [DN-0037](../DN-0037-ash-authored-foreign-library-interfaces.md)
> records the accepted current foreign-call boundary.

This document belongs to
[DN-0057](../DN-0057-checked-ffi-module-boundaries.md). It owns the proposed
transition rules for the [worked cases](minimal-ffi-contract-cases.md).
Sections explicitly distinguish common FFI rules from the SQLite instance.
Neither section depends on an OS, executable format or source syntax.
These are design choices pending semantic adoption and implementation evidence.

The [SQLite policy](minimal-ffi-sqlite-policy.md) owns operation signatures,
inputs, constants and native assumptions. The
[ABI profile](minimal-ffi-abi-profile.md) maps native roles to one target;
the [launch profile](minimal-ffi-launch-and-artifacts.md) supplies platform
execution mechanisms. Other documents summarize or reference these tables;
they do not define competing transitions.

## Common state coordinates

| Coordinate | States and meaning |
| --- | --- |
| Call observation | Not entered; entered/unresolved; admitted outcome with exact recorded status/disposition. |
| Source delivery | Pending; failure selected; published value/ordinary failure; failed delivery. Native outcome admission is not source delivery. Each call publishes at most one result. |
| Native disposition | No owner; owned; consumed; uncertain. Quarantine does not assert consumption. |
| Source access | Unpublished; usable; quarantined; retired. Only usable access admits ordinary resource operations. |
| Local completion K | Absent before source-scope publication; Pending; Closing; Discharged with one reserved completion record; TransferredToHost after terminal evaluation. Native disposition is separate. |
| Executor/session | Live; lost/stopping; terminated and observed. In-process host death gives no subsequent-report guarantee. |
| Evaluator | Running; terminal runtime failure. Worker resource state is not this parent/evaluator state. |

Native disposition records the last established observation, with a separate
marker for any later unresolved transition. After session loss or process
reclamation it is not a claim that the native object still exists. Physical
reclamation and successful native completion remain different facts.

Call-entry preconditions are conjunctive. They cannot override quarantine,
consumption, wrong identity, dead session or terminal evaluation. They are not
invariants required to process a failure or close an already existing owner.
The unique local completion owner is separate from reusable access. An
unpublished guard admits only its disposal path and has no source completion
obligation. Contradictory source identities/Core authority are internal failures;
valid access whose session was lost receives a boundary failure. Neither enters
native code. Known identities and admitted outcomes are never reused or erased.

## Phases and event guards

| Phase | Guard and authority |
| --- | --- |
| Admission | Check current operation permissions, exact identities/lineage, live executor, state and reservations before native entry or dispatch. Completion entry uses the Closing owner's authority, not ordinary reusable access. |
| Entry | Record the pending operation and its admitted entry-state snapshot. Invalidate row access when the admitted invalidating call actually enters. |
| Observation | Match a direct return or candidate control frame to that pending operation. Validate it against its saved entry state; do not rerun ordinary source-access admission. Conforming outcomes commit O4; contradictions take the violation/failure path without fabricated O4. |
| Delivery | Use admitted control and its reserved result record. Source success additionally requires complete valid value admission; error delivery may require prior unpublished-owner disposal. |
| Failure | Process loss, timeout, protocol violation or evaluator exhaustion using pending/session/owner records. Live executor and usable source access are not prerequisites. |
| Local close | Use the unique local completion record and structural closing position. Loss/quarantine may require local discharge without native entry; see K1–K9. |
| Reclamation | Use supervisor/physical-owner records after termination or safe disposal is actually observed; local completion need not still be pending. |

Transitions are serialized per resource group. Once session loss or isolated
terminal failure is committed, no later frame from that session is admitted
as new control authority or used to reopen it. Preserve control committed
before the failure; later bytes cannot reverse the cutoff. This chooses an
ordering for races without claiming when the native operation actually ran.

## Common outcome precedence

An admitted outcome is a conforming direct return recorded by the intact
in-process bridge, or a complete isolated outcome frame validated against the
pending request. A partial/unvalidated frame establishes no completion. Native
reports remain conditional on explicit foreign assumptions in either mode.

| ID | Phase | Event/guard | Native observation and ownership | Source/evaluation and continuation |
| --- | --- | --- | --- | --- |
| O1 | Admission | Input/state/configured-limit refusal before entry or any dispatch bytes | Not entered; no new owner; existing facts unchanged. | Ordinary refusal only if its result was admitted. No implicit retry; earlier operand effects remain. |
| O2 | Admission | Mandatory evaluator reservation fails before entry | Not entered; existing owners retained for terminal disposal. | Terminal evaluator failure; no native call. |
| O3 | Entry | Native entry or any request bytes sent, no admitted outcome yet | Entered/unresolved; previous known dispositions remain; this call's transition is unestablished. | No result publication. After isolated loss use O7. |
| O4 | Observation | Complete conforming outcome admitted | Commit exact status and operation-specific state/disposition in reserved storage. | Delivery remains pending until required value admission finishes. |
| O5 | Delivery | Selected value/error fully admitted; evaluator running, result not already published. Success additionally requires O4. | Preserve any O4; copied value carries no native dependence. | Publish the selected result once. After failure selection no late payload can change it into success. |
| O6 | Delivery | Local conversion/size/encoding refusal after O4, evaluator healthy | Preserve O4 and any acquired guard. Ordinary refusal does not imply rollback. | Dispose of an unpublished owner, or retain it safely under the admitted policy, before returning the refusal. State determines continued use. |
| O7 | Failure | Isolated timeout/death/transport loss/protocol failure | Keep every prior admitted outcome. Only an unresolved call transition stays unknown. No assumption that a missing acquisition reply means no owner. | Lose session; retire access; select boundary failure for pending delivery. Keep Pending obligations for closing positions; settle Closing through K4. Preserve already published results; healthy parent may handle failure. |
| O8 | Failure | Evaluator work/allocator/mandatory capacity fails at any point | Preserve O4 if already admitted; otherwise retain unresolved observation where entry occurred. Preserve guards/dependencies. | Terminal evaluator failure; transfer unfinished local obligations through K8. In isolation commit session loss and use reserved supervisor disposal; no late-frame admission. |
| O9 | Delivery | Optional diagnostic allowance refused | No change to outcome or disposition. | Mark diagnostic unavailable. Continue only if mandatory delivery succeeds; no global budget refill. |
| O10 | Reclamation | Isolated process termination actually observed | Record process reclamation separately; prior unknown native completion stays unknown. | Retire process reservations only when safely reclaimed; no source/native-cleanup success is inferred. |

O7/O8 may occur after O4: they cannot overwrite an admitted consumed or retained
outcome with unknown. After valid control but missing required payload, source
delivery fails even though ownership can be known. A malformed later frame
loses the session without undoing previously admitted control. Unexpected
status/disposition combinations fail validation before outcome admission.

Failure selection is irrevocable for that call: later bytes or cached payloads
cannot publish a competing success. An already published independent value is
not revoked by later session loss; that loss affects subsequent access and
completion reports. Mandatory failure-delivery exhaustion still takes O8.

There is no single error value that overwrites these coordinates. Terminal
evaluator failure prevents source continuation and is the runtime primary;
already observed native status and body/completion outcomes remain separate
evidence. Without terminal evaluator failure, body and ordered completion
failures retain their existing independent reporting roles. Diagnostic loss
never becomes the primary ownership fact. No row promises rollback, durable
database effects or successful eventual teardown.

## Common exhaustion domains

| ID | Failing domain | In-process interpretation | Isolated parent interpretation |
| --- | --- | --- | --- |
| X1 | Source evaluator or its mandatory codec/control allocator/work | O2/O8: terminal evaluation. | O2/O8: terminal parent evaluation, including parent decode/allocation failure. |
| X2 | Native library returns an ordinary allocation/error status | Admit native outcome and its lifecycle effects; deliver if evaluator capacity permits. | Admit validated native outcome; no inference that the parent's budget exhausted. |
| X3 | Configured operation/result/optional diagnostic allowance | Admitted ordinary refusal or O9. An actual evaluator allocation failure is X1. | Same for parent-owned limits; worker claims about its own limits are foreign data. |
| X4 | Isolated worker runtime, memory/work limit, failed control preparation or missing acknowledgement | Not a distinct process domain; classify actual evaluator failure as X1 or returned native failure as X2. | Session failure O7. Preserve any prior admitted outcome; stop worker and invalidate proxies. Never terminate parent evaluation solely because the worker claims global exhaustion. |
| X5 | Supervisor cannot finish termination/reaping promptly | No per-library process-reaping promise. | Keep stopping state and charged reservations; no fresh session/proxy reuse and no false reclaimed report. Actual supervisor control-capacity failure must have been prevented by admission or reported as host failure. |

An isolated worker's ordinary, bounded library refusal can be returned as X2
without losing a live session. Worker-runtime exhaustion X4 loses the session
even if it managed to send a failure reason. The parent trusts neither its
counters nor an asserted parent failure. Which allocator/domain failed is part
of the fixed failure classification, not inferred from diagnostic wording.

## SQLite state and admission

The following is library policy for both executors, not a platform profile.

| Coordinate | Statement/connection instance |
| --- | --- |
| Execution E | Prepared; Row(g); Done; ExecutionError. A conforming reset establishes Prepared. |
| Bindings B | Known; Uncertain. New prepared statements start Known, with null unbound parameters. |
| Row generation g | Fresh per admitted native ROW transition; original-kind cache scoped to that generation. Invalidated on step/reset/finalize entry or access/session loss. |
| Access A and disposition D | Common coordinates above; normal operations require usable A and owned D. |
| Session L | Live for ordinary operations. A lost session never becomes live by reset or clear. |
| Dependencies | S retains C and executor backing H until known native consumption or process reclamation permits physical retirement. |

Admission of native calls requires exact identity/lineage, serialized group
access and the admitted executor/operation. Processing pending observations,
loss and local completion uses their phase-specific records instead.
State/input refusal before entry leaves native/protocol coordinates unchanged;
a closing scope can still discharge locally with that refusal report.
Native contract contradiction quarantines the group,
invalidates row access and blocks ordinary calls. Keep already known consumed
facts. A native address whose ownership was not established is never used as
a destructor operand. Completion/disposal requires its separate owner authority.
Lifecycle rows do not grant native entry through a quarantined group or a
lost session. An eligible unpublished guard uses its admitted disposal path;
quarantined state needs a separately justified host-disposal path. A refusal
already returned by native finish is never silently retried by these rows.

Unlisted native statuses are preserved as numeric native errors only where
the operation permits an error outcome. A status impossible for that operation,
or detected misuse, is a contract violation rather than invented protocol state.
Tables assume a conforming return unless a contradiction row says otherwise.

## SQLite acquisition and lifecycle table

The phase column determines when a row applies. Operation predicates are checked
at Admission and retained in the pending record. Observation rows commit O4
only for conforming direct returns or validated control; contradiction rows
reject control instead. L9 is a Delivery event, L19 is a pre-entry completion
block, and L23 is a Failure event. They require no fabricated native outcome.

Finish authority is either the published scope's K=Closing authority or the
separately admitted executor-guard disposal authority. An unpublished guard
has no source K; a worker's physical guard likewise does not mint a second
source obligation beside the parent's K. Its finish executes only the admitted
request/disposal role and uses its own exact-once native-attempt ledger.
K3/K5/K6 in the rows apply only when a published scope's K is Closing;
executor-only disposal updates physical facts without creating a source report.

| ID | Phase | Operation/entry precondition | Event/native observation | State, owner and dependency transition |
| --- | --- | --- | --- | --- |
| L1 | Observation | Open; admitted host, no published C | OK and non-null C | Guard unpublished C with H backing; publish only at O5, installing K=Pending. |
| L2 | Observation | Open | Error and non-null partial C | Guard partial C; no client publication; capture status then dispose once through close policy. |
| L3 | Observation | Open | NOMEM and null C | No C owner; ordinary native failure; no query/close through null. |
| L4 | Observation | Open | OK/null or other error/null | Contract violation; no client C; do not invent a destroyable address. |
| L5 | Observation | Prepare; usable C | OK and non-null S | Guard S retaining C/H; E=Prepared, B=Known; publish after tail/result admission, installing K=Pending. |
| L6 | Observation | Prepare; usable C | OK and null S | No executable statement; no S owner/dependency. Apply successful-input/tail policy before returning that outcome. |
| L7 | Observation | Prepare; usable C | Error and null S | Native failure; no S; ignore tail. |
| L8 | Observation | Prepare; usable C | Error and non-null S | Contradiction: quarantine group, retain C/H protection, never finalize the suspect pointer. |
| L9 | Delivery | L1/L5 result publication refused after conforming acquisition | Guard remains unpublished | Dispose via admitted close/finalize, retaining dependency until disposition known. Isolated parent admission failure loses session and terminates worker instead. |
| L10 | Observation | Bind text/null; E=Prepared, B=Known | OK | B stays Known; E unchanged. |
| L11 | Observation | Bind text/null; E=Prepared, B=Known | Native error | B=Uncertain; E unchanged; no execution/rebinding until successful clear or disposal. |
| L12 | Observation | Clear; E=Prepared, any B | OK | B=Known with all null bindings; E unchanged. |
| L13 | Observation | Clear; E=Prepared, any B | Native error | B=Uncertain; E unchanged. |
| L14 | Observation | Step; E=Prepared or Row(g), B=Known | ROW | Invalidate preceding row on entry; E=Row(fresh g), original-kind cache empty; S/C remain owned. |
| L15 | Observation | Same step precondition | DONE | Old row invalidated; E=Done, B unchanged; S/C remain owned. |
| L16 | Observation | Same step precondition | Permitted native error, including BUSY | Old row invalidated; E=ExecutionError, B unchanged. Reset required; no implicit step retry. |
| L17 | Observation | Reset; E=Prepared/Row/Done/ExecutionError, any B | OK or permitted native error | Invalidate row; E=Prepared, preserve B exactly; record any reset error independently. |
| L18 | Observation | Finalize; conformingly owned S, any E/B, admitted finish authority | OK or permitted native error | D=Consumed, A=Retired; invalidate row/cache, remove S's native edge once; K3 discharges local completion before diagnostic/value delivery. No repeated finalize. |
| L19 | Admission/local close | Close C; admitted finish authority but live/unresolved dependent | Blocked before entry | C remains owned; withhold source access at scope completion; retain backing; K5 records blocked local completion without native entry. |
| L20 | Observation | Close C; admitted finish authority, no known live dependent | OK | C consumed; retire access and remove its edge once; K3 records local completion. |
| L21 | Observation | Same close precondition | BUSY | C still owned, A=Quarantined; preserve H/backing; K3 records retained completion, with no automatic close retry. |
| L22 | Observation | Same close precondition | Other error or contradiction | No established consumption: quarantine C/group and retain required backing; preserve numeric status; K3/K6 settle local completion according to admitted outcome versus violation. |
| L23 | Failure | Existing session/proxy records; loss event, no live-access predicate | No outcome or previously admitted outcome | Retire access; invalidate row/cache; preserve observed disposition and mark only unresolved transition unknown. No native finish through stale proxy; Pending/Closing local completion follows K4. |

L11 followed by L17 leaves B=Uncertain: step and rebind are rejected until L12
or disposal. L17 may reset execution while reporting an error; it does not
certify successful database completion. A copy failure does not itself change
E/B. Unknown native disposition never proves dependency removal.

Physical quarantine records retain C/H and the executor configuration even
after their source scopes end. Source-scope discharge grants no further access
and does not free that backing. Only established consumption, safe admitted
disposal, or observed isolated process reclamation permits physical retirement.
In-process refusal may retain records until host termination, without a release
guarantee. Process reclamation never rewrites unknown native completion as
successful finalization.

## Common exact-once local completion

K tracks the source scope's unique obligation, not native lifetime or whether
report text reached source code. Its fixed record is reserved before publishing
the source scope. Ordinary access and report constructors cannot mint K.
An unpublished partial-acquisition guard has K=Absent and only host disposal;
it never enters this table as a published scope.

Select local-close handling in this order, using the current serialized
state rather than table row order:

1. Discharged or TransferredToHost takes K7 unchanged.
2. Terminal evaluator failure transfers unfinished Pending/Closing obligations
   through K8, before considering session loss or any ordinary discharge.
3. A healthy Pending owner waits for its admitted structural closing position;
   only there does K2 claim Closing. Loss does not close a Pending scope early.
4. For a healthy Closing owner, select session loss K4 first, otherwise
   quarantine/contract violation K6, otherwise a blocking dependent K5.
5. Only if none applies may the admitted native finish enter. Its conforming
   outcome commits O4/K3 together; a later event cannot replace that record.

This selects one primary completion reason and at most one record. Preserve
other applicable conditions as secondary facts, including dependencies and
unknown native completion; they cause no second discharge or native call.
K1 publication and K9 physical reclamation are separate events, not competing
local-close reasons. A contradictory candidate return follows K6 after
observation rejects it, without inventing an admitted native outcome.

| ID | Phase and guard | K/access transition | Native facts and report |
| --- | --- | --- | --- |
| K1 | Delivery: guarded acquisition and source-scope publication commit | Absent to Pending once, together with access publication. | Retain native owner and its dependencies; no completion report yet. |
| K2 | Local close: evaluator healthy, normal structural exit or admitted owned abandonment, K=Pending | Pending to Closing; revoke ordinary access and claim the one closing attempt. Existing source/control obligations still govern the closing position. | Select K4, then K6, then K5 in that order; only otherwise begin the one safely admitted native finish using completion authority. |
| K3 | Observation: admitted native finish outcome for this Closing owner | Closing to Discharged with one reserved completion record before any fallible report delivery. | Record native-consumed or native-retained reason with exact status/disposition, even on error. No second native finish or local report from later scope exit. |
| K4 | Failure/local close: evaluator healthy, session lost, K=Closing; or healthy Pending owner reaching its structural exit after loss | Pending first takes K2; Closing to Discharged locally. | Record session-loss reason with last admitted facts and any unresolved finish marker; no dispatch, native consumption inference or wait for reaping. Pending scopes not yet exiting stay Pending. |
| K5 | Admission/local close: evaluator healthy, session live, no group quarantine/contract violation, known dependent blocks finish before entry, K=Closing | Closing to Discharged locally with dependency-blocked reason; retain physical quarantine. | Record no native entry; required backing remains. No source closing retry; separately justified host disposal is distinct. |
| K6 | Failure/local close: evaluator healthy, session live, group quarantined or candidate finish outcome contradictory, K=Closing | Closing to Discharged locally with quarantined/contract-violation reason. | Preserve established disposition and raw status without inventing control admission or calling a suspect pointer. Retain physical protection. |
| K7 | Local close/failure: K already Discharged or TransferredToHost | No second transition, source finish, completion-report insertion or resource authority. | Existing record remains; later diagnostic/transport failure is separate. If native consumption was already admitted, loss never adds another session-loss completion for that owner. |
| K8 | Failure: evaluator terminal X1/O8, K=Pending or Closing | Transfer to TransferredToHost once, preserving whether finish was unstarted, unresolved or already observed. | Host/supervisor disposal owns physical records; source completion/cleanup is not claimed. Discharged obligations remain Discharged. |
| K9 | Reclamation: safe physical retirement observed, any K | No completion-state change. | Reclaim permitted physical records; retain any local record still needed at source closing/reporting. Native unknown does not become successful consumption. |

For a scope finish, O4's native disposition and K3's local discharge commit
in the same reserved bookkeeping transition. No reporting allocation or
failure event intervenes between them. K1 likewise commits local obligation
and source access publication together. Executor-only guards update their
native-attempt ledger without manufacturing a source K.

The common completion record contains the closing reason, last native
status/disposition, any unresolved transition and diagnostic availability.
Names above are semantic report categories, not syntax. It is inserted once
at the owner's structural closing position, with S before C. Body outcome
remains separate from these ordered records. Failed report construction or
output does not recreate K; rendering may inspect the retained record without
running completion again. Source abandonment retains its existing report/output
policy and does not fabricate an abandoned body's return value.

Capture/resume transfers the same Pending/Closing state and record; copying
access transfers neither. Bookkeeping discharge does not authorize skipping
an executing source action, report continuation or other required control
completion. Existing resume/discard/cleanup admission remains in force.
Exact-once local discharge applies to closing paths that reach these events;
a hung native call can remain Closing, and termination can prevent reporting.
No unconditional source-cleanup or eventual-native-release promise is added.

## SQLite copied-text table

Copy Admission requires usable owned S/C, live executor, E=Row(g), a valid
index, serialized group access and reserved control reporting. Later rows use
the admitted interaction or pending-request record and their explicit phase,
not a repeated live-access test. In particular Failure rows apply after loss.
Native conversion is the bounded interaction's internal Entry/Observation/
Delivery sequence inside the host or worker, not repeated source admission.
Parent delivery occurs only in the isolated parent. A reader over S reads
its current admitted row, not a saved-row view; no cache or reader grants a
native pointer.

| ID | Phase/location | Event/guard | Action and result | E/B and dependencies |
| --- | --- | --- | --- | --- |
| T1 | Native conversion | No original-kind record for (g,column) | Admit bounded cache slot before conversion; query and retain original kind once. Unknown tag is a violation. | Row unchanged; no native representation conversion precedes retained classification. |
| T2 | Native conversion | Classification already retained | Use cached original kind; never reclassify that converted column in g. | Row unchanged. |
| T3 | Native conversion | Kind NULL | Admit SQL null; no text-pointer call. | No retained native dependency in result. |
| T4 | Native conversion | Known kind other than TEXT/NULL | Ordinary kind refusal, no implicit numeric conversion. | Row/B unchanged. |
| T5 | Native conversion | TEXT pointer null | Immediate errcode probe: NOMEM is native failure, otherwise violation. No length/copy first. | Native failure preserves row; violation quarantines group. |
| T6 | Native conversion | Non-null pointer, matching byte count zero | Immediate errcode probe: NOMEM is failure, otherwise empty text. | Preserve row/classification. |
| T7 | Native conversion/failure | Negative byte count or contradictory return | Quarantine group; no unsigned cast, copy or published result. | Block access; retain backing and existing known dispositions. |
| T8 | Admission or native conversion | Configured classification capacity, or a valid payload length, exceeds its operation allowance | Ordinary refusal if small error delivery admitted; no partial value. | Row and retained kind stay; no retry. |
| T9 | Failure/evaluator | Evaluator metadata/copy/UTF-8 work or allocation fails | X1 terminal; close temporary interval, retain control/ownership facts. | No published string; no source continuation. |
| T10 | Native conversion | Native host/worker copy has invalid UTF-8 | Host returns ordinary conversion refusal; worker sends the declared conversion-refusal alternative, not a success-string payload. No replacement or partial string. | Row/classification unchanged. |
| T11 | Native value admission | Native host/worker copy is valid UTF-8 | In-process publishes after value admission. Worker prepares success control and exact payload; only the parent can publish its source result through T16. Preserve embedded zero, omit native terminator. | No native dependency in published result. |
| T12 | Failure/session | Worker loss/runtime exhaustion before parent payload admission | O7/X4: no partial string; parent may handle failure. | Session access retired; earlier copied values survive. |
| T13 | Failure/parent | Parent payload allocation/validation work exhausts | O8/X1: terminal parent; preserve any admitted control. | Same ownership preservation, no source continuation. |
| T14 | Parent delivery | Complete valid worker conversion-refusal alternative with matching pending control | Deliver ordinary conversion refusal if parent capacity permits; no success text is expected and no session loss follows from this refusal alone. | Preserve admitted Row(g)/B and native disposition; K unchanged. |
| T15 | Parent validation/failure | Worker declares string success, but its payload violates UTF-8 or another required shape/length condition | Protocol violation O7, no source value or ordinary native-conversion refusal. Keep any earlier admitted control; lose session. | Retire session access; Pending/Closing completion follows K4. |
| T16 | Parent delivery | Valid text/null success alternative, matching admitted control and all required payload checks pass | Publish independent source text/null. If evaluator validation work/allocation fails, T13 wins instead; never guess a conversion result. | No native dependency in result; parent validation does not prove database truth. |

The parent first admits bounded framing/control and required decode capacity,
then checks a purported success payload and publishes only after complete
validation. Insufficient evaluator work/storage is T13, not evidence about
encoding. Complete valid failure alternatives take T14; invalid success data
takes T15. Missing/truncated payload takes O7/T12, preserving prior control.
A worker failure label cannot establish parent exhaustion. These choices need
no source syntax, wire layout or Linux-specific mechanism.

The cache is lazy per column, bounded by current column count and configured
metadata capacity. It survives failed copies and rereads in the same g.
Step/reset/finalize entry invalidates it, even if the native call reports an
error; rejection before entry does not. Generation exhaustion refuses before
entry rather than reusing an old key. Classification-cache refusal is T8 or T9
according to the actual failing domain. Returned-value admission in the parent
repeats bounds/encoding checks and needs no native classification authority.

## Distinguishing traces and evidence

| Trace | Required outcome |
| --- | --- |
| Bind error; reset OK; step | L11, L17, then reject step because B is still Uncertain; clear OK admits a later explicit step. |
| Finalize error admitted; diagnostic lost | L18 consumed remains; O7 retires session access without another finalize or unknown rewrite. |
| Worker allocation fails; parent capacity healthy | X4/O7 boundary failure, not terminal parent exhaustion; S/C close through K4 in structural order. |
| Same row/column read twice, first copy refused | T1 then T2 with same original kind; no reclassification after representation conversion. |
| Close BUSY; source host scope ends | L21/K3 discharges locally with retained-native report; physical H/backing stays quarantined; K7 prevents retry or duplicate report. |
| Prepare succeeds; source-result allocation fails | L9 guard survives; in-process admitted disposal, isolated session termination; no owner disappears. |
| Reset returns error after ROW | L17 invalidates row, E=Prepared, preserves B and error; no claim that earlier write committed. |
| Copy pending; worker dies before control | Failure T12/O7 uses the pending record despite dead executor; no O4 is fabricated. |
| Native invalid text; valid worker refusal; invalid worker success | T10, T14 and T15 remain distinct: ordinary refusal, ordinary refusal, session loss. |
| Session loss handled inside S; body returns through S and C | K2/K4 discharges each local owner once with loss reports, without stale native calls or waiting for process reclamation. |
| Finalize outcome admitted; then loss; then scope exit | L18/K3 already discharged the owner; K7 prevents a second completion/report; native disposition remains admitted. |
| Closing owner: lost session and retained dependent | K4 selects one loss report; retain the dependency as a secondary fact, with no K5 report or native finish. |
| Closing owner: live session, quarantine and unresolved child | K6 selects one quarantine report; keep child/backing protection without an additional K5 report. |
| Terminal parent failure and session loss while Closing | K8 transfers once; no K4 source discharge or cleanup claim. |
| Discharged consumed owner followed by terminal failure/loss | K7 leaves its record unchanged; no transfer, second report or native retry for that obligation. |

These are acceptance obligations, not executed test results. The common rows
must agree across module summaries, Core validation, runtime and parent protocol
admission. The SQLite rows instantiate those rules; target profiles must not
replace them. Linux credential/syscall/storage acceptance remains separate.
