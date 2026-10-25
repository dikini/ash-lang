# Checked FFI required evidence map

This map belongs to [CP-0024](https://github.com/dikini/ash-lang/blob/a54e9215860cd9693d1a2dc9ff79e8f0f4a57e23/docs/proposals/CP-0024-checked-foreign-host-profile.md)
and [TASK-0050](https://github.com/dikini/ash-lang/blob/a54e9215860cd9693d1a2dc9ff79e8f0f4a57e23/docs/tasks/TASK-0050-checked-ffi-regions-control-program.md).
It translates every [canonical transition](minimal-ffi-transitions.md) into required
future evidence. All rows are **pending**. No entry is an executed product result.

For O/X/K common rows, test both modes where the event exists; isolated-only events
need a corresponding explicit in-process limit statement, not a fabricated process
domain. Test every L/T library row against the actual generated SQLite bridge in
both modes where feasible; impossible native combinations use labeled injected
faults. Pair real native behavior with protocol/bridge fault injection rather than
pretending SQLite naturally emitted contradictions. Observe entry count, exact
pending/control state, value publication, K, required source continuation and
protected dependency edges separately. Check receipts against frozen source,
contract, Core/image, native inputs and policy before transferring evidence.

F3 owns summary/link/Core rejection and transformed-contract tests; F4 owns common
runtime/ownership/completion; F5 owns ordinary source-library realization; F6 owns
build/image/receipt admission; F7 owns isolated transport/executor realization.
F8 audits the complete map and F-core/F-final gates. These issue keys refer to the
[task plan](https://github.com/dikini/ash-lang/blob/a54e9215860cd9693d1a2dc9ff79e8f0f4a57e23/docs/tasks/plans/checked-ffi-regions-control.md), not launched product tasks.

| Row | Required observation | Primary delivery |
| --- | --- | --- |
| O1 | Input/state/operation limit refusal; entry counter stays zero and earlier operand effects remain. | F4/F7 |
| O2 | Mandatory reservation one-short; terminal evaluator with zero dispatch and retained owners. | F4/F7 |
| O3 | Interrupt after first dispatch byte, before control admission; unresolved transition and no source value. | F4/F7 |
| O4 | Admit valid exact control; fail later payload allocation and retain exact status/disposition. | F4/F7 |
| O5 | Deliver once; then send duplicate or late success after selected failure and reject second publication. | F4/F7 |
| O6 | Refuse conversion after acquisition; observe unpublished guard disposal or protected retention before refusal. | F4/F7 |
| O7 | Lose transport before and after admitted control; retire session and preserve earlier facts without replay. | F4/F7 |
| O8 | Exhaust parent before/after native outcome; terminal parent and preserved guard/dependencies. | F4/F7 |
| O9 | Exhaust only optional diagnostic allowance; retain mandatory result and mark diagnostic unavailable. | F4/F7 |
| O10 | Delay termination then observe reaping; keep charged reservations until actual reclamation, never infer native completion. | F4/F7 |
| X1 | Exhaust evaluator codec/control work separately from native allocation; terminal evaluator classification. | F4/F7 |
| X2 | Inject native NOMEM with healthy evaluator; native error may return without parent terminal failure. | F4/F7 |
| X3 | Refuse configured result allowance with healthy evaluator; ordinary refusal differs from real allocator failure. | F4/F7 |
| X4 | Kill/exhaust worker with healthy parent; handled session failure, not asserted parent exhaustion. | F4/F7 |
| X5 | Delay supervisor reaping; stopping domain and reservations remain, no proxy reuse or reclaimed report. | F4/F7 |
| L1 | Open OK/non-null; guard precedes publication and fresh C retains H. | F5/F4/F7 |
| L2 | Open error/non-null; no C publication, capture exact status and one partial-owner disposal. | F5/F4/F7 |
| L3 | Open NOMEM/null; ordinary native failure without query or close through null. | F5/F4/F7 |
| L4 | Open OK/null and non-NOMEM error/null; violation without fabricated owner/destructor. | F5/F4/F7 |
| L5 | Prepare OK/non-null; guard retains C/H, Prepared/Known state before source publication. | F5/F4/F7 |
| L6 | Prepare OK/null with empty/comment-only SQL; no S owner and successful tail/input policy checked. | F5/F4/F7 |
| L7 | Prepare error/null; native error and tail ignored, no S dependency. | F5/F4/F7 |
| L8 | Prepare error/non-null; quarantine and protect C/H without finalizing suspect pointer. | F5/F4/F7 |
| L9 | Fail result/tail publication after acquisition; guard never disappears, dispose or retain safely; no source K. | F5/F4/F7 |
| L10 | Bind OK while Prepared/Known; retain Known and permit a subsequent explicit step. | F5/F4/F7 |
| L11 | Bind error; B becomes Uncertain; reject rebind and step even after reset. | F5/F4/F7 |
| L12 | Clear OK from Prepared/Uncertain; B becomes Known, later explicit step admitted. | F5/F4/F7 |
| L13 | Clear error; B Uncertain and E unchanged, no inferred recovery. | F5/F4/F7 |
| L14 | Step ROW; invalidate old row on entry and establish fresh generation/cache. | F5/F4/F7 |
| L15 | Step DONE; invalidate old row and set Done without changing bindings. | F5/F4/F7 |
| L16 | Step BUSY/error; ExecutionError requires reset and no implicit retry occurs. | F5/F4/F7 |
| L17 | Reset OK/error after ROW; Prepared, row/cache invalidated, bindings unchanged, numeric error preserved. | F5/F4/F7 |
| L18 | Finalize error; consumed S, edge removed once and K recorded before diagnostic loss; no repeat finalize. | F5/F4/F7 |
| L19 | Close with live/unresolved child; zero native entry and protected C/H with blocked local reason. | F5/F4/F7 |
| L20 | Close OK; exact C consumed, edge removed once and local completion recorded. | F5/F4/F7 |
| L21 | Close BUSY; retained C quarantined with H after source host exit; no automatic close retry. | F5/F4/F7 |
| L22 | Close other error/contradiction; distinguish admitted retained outcome from rejected control; no invented consumption. | F5/F4/F7 |
| L23 | Session loss before/after outcome; invalidate access/cache and preserve admitted disposition, never use stale proxy. | F5/F4/F7 |
| K1 | Publish owner/access together; exactly one Pending obligation, no source obligation for unpublished guard. | F4/F3/F7 |
| K2 | Healthy structural exit claims Closing once and revokes access; preserve authored finish effects/continuation. | F4/F3/F7 |
| K3 | Admit native finish error then lose diagnostics; one Discharged record and separate required source continuation. | F4/F3/F7 |
| K4 | Lose session inside nested S/C bodies; close each once in structural order without stale dispatch or reaping wait. | F4/F3/F7 |
| K5 | Live nonquarantined session plus blocking child; one blocked local record and retained physical backing. | F4/F3/F7 |
| K6 | Quarantined/contradictory finish plus child; one quarantine reason outranks dependency block, no suspect-pointer call. | F4/F3/F7 |
| K7 | Discharged/transferred owner followed by exit/loss/terminal failure; no second transition, report or native finish. | F4/F3/F7 |
| K8 | Terminal parent and session loss while Closing; transfer once rather than claim source cleanup/discharge. | F4/F3/F7 |
| K9 | Reap before Pending source exit; physical retirement changes no K, later local report remains available. | F4/F3/F7 |
| T1 | First column read; reserve classification slot and query original kind before representation conversion. | F5/F4/F7 |
| T2 | Read same row/column after refused copy; reuse original classification, never query converted kind again. | F5/F4/F7 |
| T3 | Original NULL; publish null without text-pointer call or native result dependency. | F5/F4/F7 |
| T4 | Original INTEGER/FLOAT/BLOB; ordinary kind refusal with unchanged row/bindings. | F5/F4/F7 |
| T5 | TEXT/null pointer; immediate errcode distinguishes NOMEM/violation before any length/copy. | F5/F4/F7 |
| T6 | Non-null text/zero bytes; immediate errcode distinguishes NOMEM from valid empty text. | F5/F4/F7 |
| T7 | Negative byte count/contradictory native return; quarantine without unsigned cast/copy/publication. | F5/F4/F7 |
| T8 | One-short configured cache/payload allowance; ordinary refusal preserves row/kind; compare actual allocator failure. | F5/F4/F7 |
| T9 | Exhaust evaluator metadata/copy/UTF8 work; terminal evaluator and closed interval, no partial value. | F5/F4/F7 |
| T10 | Invalid native UTF8; ordinary conversion refusal, worker emits refusal alternative rather than malformed success. | F5/F4/F7 |
| T11 | Valid native UTF8 including embedded zero; omit terminator and preserve independent admitted bytes. | F5/F4/F7 |
| T12 | Worker dies before parent payload admission; session failure, no partial string, earlier copies survive. | F5/F4/F7 |
| T13 | Exhaust parent payload allocation/validation; terminal parent independent of whether payload encoding is valid. | F5/F4/F7 |
| T14 | Valid worker conversion refusal and matching control; ordinary refusal without session loss. | F5/F4/F7 |
| T15 | Invalid UTF8/shape in worker success; protocol loss, retain prior control, never relabel native conversion refusal. | F5/F4/F7 |
| T16 | Valid text/null success with matching control; publish independent parent result only after all checks; no truth claim. | F5/F4/F7 |

## Coverage beyond individual rows

Run every distinguishing trace in the canonical table, including overlapping
K reasons, terminal failure versus healthy loss, original-kind caching after
refusal, binding uncertainty across reset, and consumption before reporting loss.
One test may cover multiple rows only with observations for each obligation.

F3 must additionally reject same-spelled origins, wrong full Type/Row substitutions,
opaque alias substitution, forged independence, hidden captured S/C/H, host-row
erasure, stale summaries and transformed copy-window order. Validate imported
wrappers without reinferring their bodies. Preserve nearest ordinary-handler
precedence and source finish control through capture/resume/discard/cleanup.

F6/F7 need approved exact bytes/receipt closure, changed-image races, wrong ABI,
unavailable-control refusal, fresh session identity, malformed versus plausible
false replies, actual launch/resource enforcement and delayed reaping. See the
[experiment contract](linux-profile-experiment.md). Stage A environmental probes
do not satisfy any product row. Missing observation, integrated correspondence,
independent review or required checkpoint keeps the original criterion pending.
