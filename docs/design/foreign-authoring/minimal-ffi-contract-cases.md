# Minimal FFI contract: copied text and scoped statements

This worked design belongs to
[DN-0057](../DN-0057-checked-ffi-module-boundaries.md). The choices below are
candidates for review, not current Ash semantics, an accepted architecture or
implementation authorization. They refine
[DN-0037's readiness brief](dn-0036-readiness.md) before choosing source syntax.

## Bounded profile

Keep the common FFI contract separate from platform realizations. Checked
operation identity, effects, dependencies, result publication, disposition,
reporting and session-loss rules are common. Native layouts, artifact packaging,
launch restrictions and enforcement APIs belong to an explicit target/executor
profile. The Linux choices below are one proposed realization, not requirements
that every Ash platform implement ELF, namespaces, memfd or cgroups.

| Layer | Owning design |
| --- | --- |
| Common outcome precedence and exhaustion domains, then SQLite transition instance | [Canonical transitions](minimal-ffi-transitions.md). |
| Common semantic contracts, effects, dependencies and activations | [Checked representation](minimal-ffi-checked-representation.md). |
| Common exhaustion, reporting and ownership guarantees | [Exhaustion and ownership](minimal-ffi-exhaustion-and-ownership.md). |
| Portable SQLite inputs, constants, signatures and native assumptions | [SQLite policy](minimal-ffi-sqlite-policy.md). |
| Concrete C representations for the selected target | [Linux x86-64 ABI profile](minimal-ffi-abi-profile.md). |
| Common artifact-admission obligations and selected Linux realization | [Launch and artifact design](minimal-ffi-launch-and-artifacts.md). |

Use a SQLite connection with scoped prepared statements. The copied result is
one nullable text column from a current row. A statement depends on its
connection; neither native owner nor temporary view escapes its scope.

For a concrete first target, propose Linux x86-64, the System V C ABI and
fixed-signature generated bridges. Admit checked signed/unsigned integer
widths, opaque native handles, explicit-length temporary buffers, initialized
output slots and required declared sentinels. Enumerate each operation's exact
representation in its checked contract. Reject unsupported aggregates,
variadic calls, callbacks, retained input borrows and general native views.
This profile is a proposed restriction, not a claim of existing target support.

Serialize calls within one connection and its statements. The binding admits
no concurrent or reentrant operation on that group. Input buffers remain valid
for their declared synchronous call, and non-retention remains an explicit
native assumption. Ordinary Ash definitions express SQLite-specific policy;
the common bridge and ownership machinery must also serve the minimal native
arena lifecycle required by DN-0037.

## Common boundary contract

Describe each foreign operation with one authenticated checked contract:

- Defining operation, library requirement, ABI signature and target profile.
- Required resource identities, states and dependencies.
- Each input's representation, access interval and retention assumption.
- Output initialization and interpretation for every native outcome.
- Ownership disposition and protocol transition, independently of error status.
- Conversion, bounds, publication conditions and declared external effects.
- Remaining native assumptions and evidence applicable to each obligation.

Public module summaries preserve client-relevant obligations and transitive
assumptions. Keep the assumption identities and dependencies in checked
metadata; explanatory text supplies their meaning. Do not require clients to
restate assumptions. Core independently validates the relationships rather
than trusting a copied success flag. Native behavior remains assumed where
the boundary cannot enforce it.

Report operation outcome and resource disposition separately. Distinguish
rejection before dispatch, received native outcome, boundary/conversion
failure, and unknown completion after dispatch. A received outcome is an
observation under the binding assumptions, not proof of database correctness
or durable effects. Distinguish live, consumed, quarantined and inaccessible
resource states; unknown native disposition must not authorize access.

Preserve the body outcome and ordered completion reports. Local completion K
is separate from native disposition: loss/quarantine can discharge a scope
locally at its closing position without dispatching a finish or claiming
consumption. K1–K9 make that bookkeeping exact-once. Reporting an error
must not overwrite a known consumption transition. Failure after dispatch
does not promise rollback. Check elimination later needs evidence for the
same obligation and applicable native artifact.

## Copied result: nullable text column

The public operation takes scoped statement access and a column index. It
returns SQL null, an independent valid UTF-8 string, or an explicit failure.
SQL null and the empty string are different outcomes. Preserve embedded zero
bytes when valid UTF-8; do not scan for a terminator or replace invalid text.
Reject other column kinds rather than introducing implicit numeric conversion.

### In-process copied result

1. Before native entry, authenticate the live statement and connection,
   require a current row, and check the column index. Hold exclusive operation
   access for the whole copy sequence.
2. Establish the original column kind once for this row generation and retain
   it across rereads and failed copies. Use that cached classification before
   conversions; return null, reject another kind or enter the text sequence.
3. Obtain the UTF-8 text pointer, then its byte length in the compatible query
   order. Distinguish native allocation failure from null and empty text.
   Check length arithmetic and configured result/allocation limits.
4. Copy the exact bytes while the declared validity window remains open.
   No stepping, resetting, finalizing or incompatible representation query
   may intervene. Validate the independent bytes as UTF-8 before publication.
5. Publish only the completed Ash value. Release temporary access on success
   or failure; no native pointer is present in the result. Later stepping or
   finalization cannot invalidate a successfully published copy.

SQLite documents the relevant preconditions and pointer/length query order in
[column access](https://www.sqlite.org/c3ref/column_blob.html). These remain
foreign assumptions even when the binding enforces its side of the interval.
Null and bounds checks cannot establish that native memory is readable.

Wrong kind, invalid UTF-8 and a configured size refusal leave the statement
in its known row state, provided the native interaction remained conforming.
A detectable contradiction in the native contract quarantines the affected
resource group. A native fault or host exhaustion may terminate execution;
this path adds no recovery or source-cleanup guarantee for those events.

### Isolated copied result

Use one worker process per connection group initially. Native pointers,
temporary buffers and ownership records stay in that worker. It performs the
same copy sequence as one serialized operation and sends a null tag or an
explicit-length byte payload. The client receives no native address.

The parent treats the entire worker as untrusted, including its validators.
Before allocation and publication, it independently checks bounded framing,
protocol/contract version, session, request and resource identities, expected
reply shape, payload length and UTF-8. Worker validation does not substitute
for parent validation. A well-formed reply establishes a valid Ash string,
not that the worker returned the database's true contents.

A declared, valid worker conversion-refusal outcome is an ordinary failure.
Invalid UTF-8 under a worker success-string alternative instead violates its
reply contract. A malformed or mismatched reply loses the session and
invalidates its handles.
Worker death or timeout publishes no partial result. Preserve any admitted
outcome; only an unacknowledged transition remains unknown, as specified by
the [canonical precedence table](minimal-ffi-transitions.md#common-outcome-precedence).
Earlier independent copies remain valid after session loss.

## Stateful resource: connection and statement

Scope ownership controls completion; copying access does not copy release
authority. The [canonical lifecycle table](minimal-ffi-transitions.md#sqlite-acquisition-and-lifecycle-table)
separates execution state, binding validity, access permission, disposition
and session state. Reset changes execution state while preserving bindings
and uncertainty. Consumption and loss of source access are distinct facts.
All guards retain required dependencies until physical retirement is safe.

### In-process resource lifecycle

1. Resolve and preflight native bindings before acquisition. Initialize
   output slots before calls. Guard any partially returned connection or
   statement immediately, including failure outcomes that still return one.
2. Publish scoped access only after native outcome classification, dependency
   registration and result admission succeed. A post-call conversion failure
   disposes of unpublished state under the acquisition contract; it cannot
   silently drop the native owner.
3. Check operation permissions and record each native transition before any
   later fallible reporting conversion. Reject use after consumption or
   quarantine before entering native code.
4. Complete dependent statements before their connection. Statement
   finalization consumes the statement even when reporting an error. Remove
   its dependency once; never retry through the consumed address.
5. Connection close can refuse and retain the owner. A known live dependency
   blocks close before native entry. Unexpected retained state after an actual
   close attempt is reported and quarantined; it cannot be called successful
   release or permit scoped access to escape.

The difference between error and consumption follows SQLite's
[finalization](https://www.sqlite.org/c3ref/finalize.html) and
[close](https://www.sqlite.org/c3ref/close.html) contracts. Use ordinary close,
without silently substituting deferred close. Exact release and retention
behavior remains an explicit assumption about the native implementation.

### Isolated resource lifecycle

The parent owns scoped proxies. Native ownership stays in the worker. Each
proxy is bound to an authenticated parent-side record and a fresh worker
session; wire IDs alone cannot create source access or release authority.
Do not reuse session identities after restart. The parent mirrors only the
states needed to reject invalid requests and replies; the worker checks the
same native operation preconditions.

Acquisition replies publish proxies only after parent admission. If a reply
cannot be admitted, terminate the session and reap the worker rather than
leave an untracked remote acquisition. This bounds abandoned native process
state but makes no claim that foreign destructors ran.

After an acknowledged finalization, consume the proxy even if its report
contains a native error. Local K is discharged before fallible reporting.
After session loss, proxies become inaccessible; Pending scopes remain until
closing and then discharge locally once with loss reports in S-before-C order.
Do not send stale finishes or infer that unacknowledged native operations
completed. Physical process records can outlive local source completion.
Reaping the worker establishes process termination and operating-system
reclamation within the selected profile, not successful library completion.
Previously reported consumed states remain consumed; any in-flight native
disposition can remain unknown.

## Isolation and failure choices

For the first isolated profile, use a local child process, bounded framed
messages over private pipes, one request in flight, and no shared native
memory or transferable native pointers. Include fresh session and monotonic
request identities. Fix protocol and checked-contract compatibility before
acquisition. Apply frame, result, handle-count and allocation limits; reject
an oversized frame before allocating its declared size.

The supervisor owns deadlines, worker termination and reaping. Reject a request
locally when limits or state fail before dispatch. After any dispatch bytes,
loss leaves only unacknowledged transitions unknown; admitted outcomes survive
later payload or diagnostic loss. On timeout,
protocol violation or lost connection, stop dispatch, invalidate the session,
terminate and reap the worker. Do not continue a timed-out session or
automatically restart and replay an operation. This supplies no exactly-once
claim for external effects. OS resource enforcement and a concrete launch
policy must bound workers that ignore protocol limits or deadlines.

Isolation contains native memory faults in the parent under the OS/process
assumptions. Native code may corrupt its worker-side monitor and emit a
plausible false reply. The parent's checks still protect Ash representation
and local authority; database behavior and native lifecycle reports remain
assumed. Restrict filesystem, network, inherited descriptors and process
authority explicitly. A child process alone does not establish those
restrictions. The [launch and artifact design](minimal-ffi-launch-and-artifacts.md)
refines the concrete Linux policy and its evidence requirements.

Use the same value and resource contracts in both modes. Include boundary
failure and unknown-completion outcomes in the shared public model; do not
promise transparent native-fault recovery in-process. Execution mode and its
assumptions remain inspectable. No claim that both modes admit identical
failures, timing or containment follows from sharing the success contract.

## Closure and remaining blockers

The [canonical transitions](minimal-ffi-transitions.md) address the common and
SQLite findings, including R1–R3's phase guards, local completion and encoding
failure distinctions, in the [consistency review](minimal-ffi-consistency-review.md).
The Linux profile's credential/syscall/storage acceptance still requires
separate policy detail and deployment evidence. Transition closure is proposed
design, not acceptance of the platform realization.

The [exhaustion and ownership design](minimal-ffi-exhaustion-and-ownership.md)
resolves the final blocker's pre-admission, minimal reporting, disposition
preservation and terminal-disposal rules in both modes. These are common
executor obligations; platform mechanisms remain in their profiles.

The [launch and artifact design](minimal-ffi-launch-and-artifacts.md) resolves
the third blocker's containment, pre-execution setup, resource enforcement,
storage grants and authorized immutable execution images at design level.
The policy still requires architecture acceptance and deployment evidence;
it does not prove native correctness.

The [ABI profile](minimal-ffi-abi-profile.md) maps native roles to Linux x86-64.
The [SQLite policy](minimal-ffi-sqlite-policy.md) separately owns signatures,
constants and input/output roles. Acquisition, conversion and disposition
transitions have one owner in the canonical tables. These remain proposed
contracts pending semantic adoption and implementation evidence.

The [checked representation](minimal-ffi-checked-representation.md) resolves
the second blocker's canonical contract, module-summary projection, exact
effects, static dependencies, Core validation and runtime activation roles.
It includes a proposed authenticated native-host boundary and preserves the
distinction between copied data, native effects and completion authority.

These cases select candidate rules for independent publication, finite access
windows, serialized resource groups, consumption separate from errors,
session-bound proxies, parent validation and conservative lost-reply handling.
They require no general dynamic type, proof language or source typestate syntax.

The four identified blockers now have proposed design-level resolutions for
these cases. This does not establish implementation or production readiness.
Review the common semantic delta for a change proposal and the concrete
platform/runtime choices for architectural decisions before authorized delivery.
Additional platform profiles must satisfy the same common obligations or
explicitly refuse unsupported execution modes; they need not use Linux APIs.

Required comparisons include null/empty/invalid UTF-8, exact and oversized
lengths, forbidden copy-window invalidation, stale identities, finalize error
with consumption, close refusal, publication failure after acquisition,
malformed and plausible false replies, worker death before and after a native
effect, and restart with old handles. Run native fault injection in contained
processes. Compare the same successful values and scoped dependencies in both
modes; retain their different failure guarantees. A later prototype needs its
own bounded question and disposal conditions under DN-0057.
