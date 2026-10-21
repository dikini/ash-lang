# Checked representation for the minimal FFI cases

This design refinement belongs to
[DN-0057](../DN-0057-checked-ffi-module-boundaries.md). It specifies candidate
checked contracts, effects and dependencies for the
[copied-text and connection/statement cases](minimal-ffi-contract-cases.md),
using their [ABI profile](minimal-ffi-abi-profile.md). It selects no source
syntax or Rust encoding, defines no current Ash semantics and authorizes no
implementation.

## Existing boundaries and representation choice

The [canonical transition tables](minimal-ffi-transitions.md) own outcome,
exhaustion-domain and lifecycle rules. Records below carry all those state
coordinates, pending-operation phases and K; no single protocol tag replaces
binding validity, access, native disposition or session state. Admission checks
live source permissions; failure processing uses pending/owner records without
requiring them to remain live. SQLite signatures and native assumptions belong
to the
[SQLite policy](minimal-ffi-sqlite-policy.md), not a target profile.

The current [elaboration contract](../../../spec/elaboration.md) authenticates
module identities, retains exact computation rows, checks capture summaries
and lowers builtin resource scopes. It adds no general FFI. The
[scoped runtime contract](../../../spec/dynamic-semantics.md#scoped-cell-execution)
distinguishes scope-owned completion from reusable access and fresh dynamic
activations from static identities.
[AD-0007](../../decisions/AD-0007-typed-core-dialects.md) requires structural
types, causal provenance and independent dialect validation.

The experimental [foreign facts](../../../src/foreign.rs) and
[runtime](../../../src/foreign/runtime.rs) already separate defining operation,
state lineage, independent results, acquisition and consumption/retention.
This transfers as evidence for those distinctions, not as adopted source
semantics. The existing manifest or its in-memory allocation identity is not
the selected public contract or a persistent artifact-authentication scheme.

Choose one canonical checked semantic contract with phase-specific projections.
Keep operation semantics and module summaries target-independent. Declared
foreign representation roles and required executor capabilities are common
facts; concrete sizes, layouts, native entries and deployment mechanisms belong
to a separately checked target realization. It refers back to the same
original semantic identities and cannot redefine their obligations. No
Linux-specific syscall or executable format enters ordinary effect rows or
dependency summaries.

Do not maintain independently authored module, Core, ABI and runtime contracts.
An ABI-only descriptor lacks access and ownership facts; ordinary function
types alone cannot express hidden captures, native validity or completion.
Runtime monitoring alone cannot prevent static scope escape. Each stage must
check the obligations for which it has evidence.

## Canonical checked records

Names below describe compiler data roles, not source forms or concrete structs.
Each reference resolves to an admitted original declaration, not a matching
spelling, symbol address, constructor shape or digest alone.

| Record | Required semantic information |
| --- | --- |
| Foreign contract | Defining module/declaration identities, causal origin, revision, native library requirement and ABI-profile reference. |
| Resource family | Defining nominal/effect identities; ordered kinded parameters; which parameter is the owned identity; dependency coordinates; acquisition and finish relations. |
| Operation | Exact defining operation identity and full value scheme; ordered type/row binders; exact computation row; operand paths and identity substitutions; required state checks; transitions by outcome. |
| ABI relation | Reference to the admitted operation's exact native signature, representations, sentinel roles, input intervals and initialized-output alternatives. |
| Result relation | Ordinary copied value, fresh guarded acquisition, or completion of the exact owner; dependency paths and publication requirements per alternative. |
| Temporary access | Source owner/activation coordinates, permitted native query sequence, invalidating operations, bounds/conversion checks and the point where independent publication ends native dependence. |
| Assumption | Defining identity, precise stated obligation, affected operations, target/configuration applicability and any separately admitted evidence. |
| Wrapper summary | Defining function and scheme, exact effect behavior, argument/result/capture dependency relations, required completion/control facts and transitive foreign assumptions. |

An operation's borrowed operands name exact tuple/field paths and their owner
coordinates. A result relation distinguishes retained access from copied
contents. State checks and transitions are a finite, operation-specific table;
the first profile does not admit arbitrary user-supplied predicates as proofs
of native state. Result constructors carry reports, not authority.

Contract revisions distinguish incompatible facts. A content fingerprint may
detect staleness but cannot authenticate a malicious replacement. Checking
must establish identity, structural agreement and availability through the
actual module route. Binding the resulting contract to a native executable
artifact follows the [artifact-admission policy](minimal-ffi-launch-and-artifacts.md#common-artifact-admission-obligations).

## Effects and execution authority

Retain three distinct judgments: which computation occurs, which owners a
value depends on, and which scope owns completion. None implies either of the
others. In particular, an independent copied result does not make its call
pure, and an ordinary handler cannot manufacture native execution authority.

Introduce one compiler-authenticated native-host effect family for this
profile. Its exact instance is indexed by a lexical host identity H. This is
a proposed addition, not a current builtin or a new kind of effect row.
Ordinary operations use Ash's existing exact-instance rows. The trusted host
boundary owns H, its execution mode and native execution authority; it
outlives the connection group. The first profile uses one coarse native-host
effect rather than claiming inferred filesystem or database-effect precision.

| Operation in these cases | Required computation effects |
| --- | --- |
| Open connection | Native-host instance H, plus actual operand-evaluation effects. |
| Acquire statement under C | Exact connection-operation instance C and native-host H. |
| Step, bind, reset, clear, copied column under S | Exact statement-operation instance S and native-host H. |
| Finalize S or close C | Exact owner-operation instance and native-host H, with the scope's authenticated completion authority. |
| Pure UTF-8 check over already copied bytes | Only its actual Ash computation effects; no native effect is introduced by historical origin of bytes. |

Resource handling may discharge its exact connection or statement instance.
It must retain the native-host effect of actual foreign calls and required
completion. An ordinary handler may simulate an operation without native
execution; if its clause invokes native primitives it needs H and their
authenticated contract. Neither simulation nor a same-shaped result can
establish a native acquisition or consumed disposition.

The explicit trusted execution boundary discharges H only for its configured
host implementation. It accounts for initialization, native entry, native
cleanup and isolated dispatch. Imports are passive and supply no host scope.
The executable entry retains an empty outward row only after this boundary
is validated. A semantic proposal must specify this addition to the current
entry contract; it cannot silently waive the empty-row requirement.

In-process and isolated implementations share the operation contracts and
logical effect family. A host identity has one fixed execution mode and
configuration during its lifetime. No automatic fallback or cross-host
resource use is admitted. Mode-specific assumptions and failure outcomes
remain inspectable; their containment guarantees are not equated by sharing
an effect family.

## Dependency representation

Static dependencies refer to lexical owner identities and parameter positions.
They never contain native pointers or dynamic session IDs. Retain these facts
through generic instantiation, tuples, nominal payloads, closure captures,
selected evidence and existing control summaries. A plain return type is
insufficient when a closure or hidden field retains access.

| Entity | Required retained dependencies |
| --- | --- |
| Connection access C | Its scoped owner C and host H. |
| Statement access S | Its owner S, connection C and transitively host H. |
| Closure using S | All dependencies of its captured access and selected operations, even if its ordinary result is a string. |
| Temporary text interval | Exact statement/current-row window and group access; never a source-visible escaping value. |
| Successfully copied string/null | No native resource dependency contributed by this operation. |
| Copied diagnostic/report | No native dependency unless another actual payload field retains access. A report grants no finish permission. |

Dependencies of unrelated retained payloads are still preserved. Marking one
field as copied cannot erase other captured owners. A value may cross a scope
boundary only when all its retained dependencies outlive its admitted use.
The scope's completion obligation is unique and is not a dependency that
copying a handle can duplicate.

Summaries express relations from actual arguments and captures to possible
result positions, including closures and branch alternatives. Joins retain
all possible dependencies; recursive summaries require a bounded fixed point.
Specialization substitutes complete identity/type/row arguments, including
those hidden by opacity. No caller needs the dependency's source body.
Exhaustion admits no partial summary or permission. Work/storage reporting
is refined by the [exhaustion design](minimal-ffi-exhaustion-and-ownership.md).

Protocol state is checked at runtime in this first profile. Successful state
checks authorize only the current interaction; no general source typestate
or first-class proof token is introduced. A failed operation cannot leave
behind reusable evidence that the resource is still in its preceding state.

## Across modules

A checked module publishes its ordinary schemes and a body-free semantic
projection containing the resource/operation/result relations needed by its
exports, wrapper summaries, and transitive assumption references. Public
inspection shows assumptions in terms of affected operations and guarantees;
it does not expose private native layouts or constructors as source access.

Opaque hidden identities remain available to compiler validation without
becoming nameable or constructible by clients. Imports and re-exports preserve
their exact defining origins and authorization routes. Aliasing does not
mint a fresh resource family or operation. A dependency may expose only a safe
wrapper while keeping raw primitives private; the wrapper's effects,
dependencies and assumptions still compose into its clients' summaries.

Summary admission checks the defining identities, schemes, substitutions and
contract projection against authenticated dependency facts. Linking checks
that all references resolve to the same admitted declarations and revisions.
Do not trust a serialized checked flag, an imported report constructor or a
copied identifier. Persistent module formats remain outside this decision;
any later deserialization must re-establish these admission obligations.

## Through Core

Keep native primitives in an authenticated operation family of Effect Core.
Do not encode them as ordinary pure function applications or introduce an
inhabited native operation into Pure Core. Candidate Core roles are native
invocation, guarded acquisition, owner completion and bounded native copy.
They may share the existing operation-family infrastructure; concrete node
variants remain an architecture choice.

Every retained occurrence references its canonical contract, full instantiated
operand/result types and row, exact owner binders, operand paths and causal
origin. Acquisition binds a fresh scoped identity and one completion owner;
finish must reference that owner. A reusable access operand cannot substitute
for it. Explicit scopes retain required completion/control behavior through
capture, resume, discard and cleanup under the existing ownership discipline.

Represent the text copy sequence as one bounded, non-suspending native
interaction whose checked plan contains kind check, pointer query, immediate
error probes, matching length query, bounds, copy and result admission.
No source handler, callback or other native operation runs inside that open
window. No temporary pointer value is exposed as an ordinary Core operand
that can be stored or captured. This avoids a general borrow-token mechanism
for the two selected cases while retaining independently checkable steps.

Core validation reconstructs structural typing, exact rows, identity
substitution, resource lineage, allowed operation roles, publication and
completion relations, temporary-window order, and scope/capture dependencies
from admitted facts. Source annotations and constructor APIs are not evidence
that these checks passed. A target bridge plan is derived only from validated
contracts/occurrences, not from a second authored signature inventory.

Transforms must preserve effects, dependency and completion behavior. They
cannot remove, duplicate or reorder a native interaction merely because its
result is unused, independent, or represented by a pure value. Any changed
occurrence or projection is revalidated; native windows cannot be split across
suspension or reordered with step/reset/finalize. Share immutable contracts
where identity is preserved, without caching per-activation ownership.

## At runtime

Static binders map to fresh runtime activations on every acquisition. A host
activation selects the configured executor. A connection record retains its
host activation; a statement record retains the exact connection activation.
The unique guard holds native ownership separately from aliases of access.
The record stores live protocol state, dependencies, native disposition,
source-access permission and the separate K state from the canonical
[local completion table](minimal-ffi-transitions.md#common-exact-once-local-completion).
Core retains the same unique owner through capture/resume, including whether
closure has started or local completion has already been recorded. Pointer
reuse never reactivates old access.

At call admission, authenticate the binding and actual activations, check
liveness/state and serialized group access, then retain the entry snapshot
and run the admitted plan. Observations, failures and local closure use their
own pending/owner records and phase guards.
Install known state/disposition transitions before fallible result decoding.
Publish ordinary values only after their result relation is satisfied.
Finalization error still consumes S; a retained owner protects its backing
dependencies but grants no source lifetime extension. Quarantine records keep
executor configuration and physical backing alive after source H/C scopes
close; source discharge never substitutes for physical retirement. Follow
the canonical dependency-retirement rules for consumption or process reclamation.

In-process records contain private native handles. Isolated parent records
contain session-bound remote references, while worker records contain native
handles. Both use the same static owner lineage. The parent checks replies
against its pending request and allowed transition table; worker-supplied IDs
or consumed tags cannot create arbitrary local authority. Plausible false
reports remain part of the declared native-behavior assumptions.

Session loss marks the whole group inaccessible and preserves unknown native
completion where applicable. Pending source obligations remain until their
structural closing positions; Closing obligations settle locally on loss.
K4 records one session-loss completion without dispatch or claiming native
finalization. K7 prevents another local report when admitted finalize already
discharged the owner. Physical records survive until safe reclamation; no
old proxy becomes access to a replacement worker.

## The two cases end to end

For copied text, a client's imported wrapper summary requires S and H during
the call and retains the actual statement dependencies in any returned reader
closure. Specialization maps those identities to the caller's exact owners.
Core validates the bounded copy plan; runtime checks the current row and
activation. Successful string/null publication removes only the temporary
native dependence of the copied contents. The call's effect remains recorded.
In isolation, the parent repeats payload checks before publishing the same
ordinary result, with no remote reference embedded in it.

For statement acquisition, the imported contract relates a fresh S to the
actual enclosing C and H. Core validates guard/publication and completion
ownership; runtime installs that dependency before publishing access. Imported
helpers cannot return access or a captured reader beyond S. On finalize, only
the scope's completion owner authorizes consumption; the result report cannot
invoke another finish. Known consumption removes S's native dependency edge
once. Close refusal or quarantine preserves the necessary edges. In isolation,
the same relations apply to parent proxies and worker owners, with session
failure distinguished from acknowledged native consumption.

## Closure evidence and remaining limits

Compare rejection at summary admission, linked/Core validation and runtime
where applicable: same-spelled foreign declarations; re-exported or opaque
identity substitution; forged independent-result facts; reader closures whose
return type hides captured S; branch/recursive dependency loss; host-effect
erasure; wrong-host use; copied access used as completion authority; transformed
copy windows; duplicate finalize; and stale proxies after restart.

Positive evidence must include independent checking of an imported copied-text
helper without its source body, copied results surviving both resource scopes,
captured readers remaining scoped, exact identity preservation through generic
helpers and re-exports, and ownership/effect preservation through a retained
Core transform in both execution modes. Reuse current capture/control checks
and experimental lineage tests only within their demonstrated scope.

This closes the representation choices for the two worked cases at design
level, subject to review and later semantic adoption. A proposal must make
the new host boundary and generic foreign-resource authority explicit. Exact
Rust data structures, persistent formats and source syntax remain unselected.
The [launch and artifact design](minimal-ffi-launch-and-artifacts.md) separates
common admission obligations from the selected Linux containment realization.
The [exhaustion design](minimal-ffi-exhaustion-and-ownership.md) refines common
reporting and ownership preservation in both execution modes.
