# CP-0024: Checked Foreign Host Profile

- ID: `CP-0024`
- Status: accepted
- Related: [DN-0057](../design/DN-0057-checked-ffi-module-boundaries.md),
  [TASK-0050](../tasks/TASK-0050-checked-ffi-regions-control-program.md),
  [AD-0013 at Main](https://github.com/dikini/ash-lang/blob/7949b6d9136b0152ee9104e67bd0451cb9db4727/docs/decisions/AD-0013-generated-native-bridges-and-program-builds.md)

> This accepted proposal is not current Ash. On 2026-10-21 the orchestrator
> adopted the independently reviewed recommended contract under the user's explicit
> delegation to choose recommended answers. Product implementation, verification
> and Main integration remain pending.

## Current behavior

The baseline is Main `7949b6d9136b0152ee9104e67bd0451cb9db4727`, not this
original source planning checkout's HEAD `af327e31e9f5fccc483d9c24bd7dfc9628e32426`.
Main's [source foreign declarations](https://github.com/dikini/ash-lang/blob/7949b6d9136b0152ee9104e67bd0451cb9db4727/spec/static-semantics.md#source-foreign-declarations)
already provide passive original contracts, scalar/void calls, opaque/byte owners,
initialized outputs, dependencies, consumption/retention, complete Type/Row
arguments and source-authored resource handlers. Generated Rust bridges and
private program images execute admitted contracts. Main's
[entry rule](https://github.com/dikini/ash-lang/blob/7949b6d9136b0152ee9104e67bd0451cb9db4727/spec/static-semantics.md#globals-and-modules)
discharges admitted owner-free native instances and still requires an empty
outward row. Generic cells are already implemented without native acquisition.

The note's statements that Ash has no general FFI describe an earlier baseline;
they do not supersede these Main foundations. Historical CP-0023 and cell tasks
in this checkout are retired on Main and must not return to the product tree.
Current bridges check declared facts but do not establish the proposed checked
host, transitive assumption inspection, arbitrary-native containment or isolated
session contract. Successful ABI checking does not prove native behavior.

## Proposed behavior

### Opt-in source and build boundary

Keep the existing build profile as the default. Propose explicit build options
`--foreign-profile checked --foreign-mode in-process|isolated`; checked mode
requires exactly one mode and an approved launch policy/receipt before startup.
Options name proposed interfaces, not implemented commands. A checked program
admits the complete reachable required contract closure, including initialization,
finish, hidden wrapper captures and imported operations. It rejects an unchecked
required binding or unsupported contract, even on an unexecuted reachable branch.
There is no legacy execution escape, in-process fallback, or implicit compilation
while evaluating a call. Non-foreign ordinary code remains usable in both profiles.

Use existing passive library/resource declarations and ordinary Ash wrappers.
Add the following source forms, proposed for semantic acceptance. The grammar
extends the existing library prefix, library members, symbol members and
expressions. `identifier`, `upper_identifier`, `string_literal` and `block` have their existing
lexical/block meanings. A qualified assumption reference resolves through an
admitted original library; strings describe obligations and never prove them.

```ebnf
checked_library_prefix ::= [ "pub" ] "foreign" "checked" "library" upper_identifier ;
checked_library_member ::= "assumption" upper_identifier string_literal ;
checked_symbol_member ::= "host" upper_identifier | "assumes" "{" [ assumption_ref { "," assumption_ref } ] "}" ;
assumption_ref ::= upper_identifier { "." upper_identifier } ;
foreign_host_expression ::= "foreign" "host" upper_identifier block ;
checked_owner_member ::= "host" upper_identifier ;
checked_resource_member ::= "host" upper_identifier ;
report_codec ::= "scope" | "acquired_only" | "checked_scope" ;
```

A checked library contains its ordinary profile, representation, owner and symbol
members after this prefix, using the existing braced body. Every symbol declares
one `host H` and one `assumes { ... }`, including an explicit empty set where
appropriate. H names an explicit `Type` formal in that symbol's complete ordered
parameter vector; the marker does not add an invisible parameter. Each checked
owner names `host H` as an additional owner member with the same meaning for its
explicit parameter vector. Acquisition, teardown and owner operands must agree
on that exact H. Add `host H` to source resource headers similarly; the resource's
state, interpreted operations and inherited owner arguments must preserve it.
No host parameter projects to a native ABI operand. Ordered Type/Row arguments,
including ordinary formals absent from value types, retain their current checks.
A nonchecked declaration cannot use these markers to gain checked permission.

`foreign host H { body }` binds a fresh lexical host identity H with authenticated
builtin effect `Foreign.NativeHost<H>`. It is an execution boundary, not a passive
import or ordinary handler. It checks the body under that exact host authority,
installs the admitted exact checked owner-free native interpretations for H,
subtracts only those exact native instances and that host effect, and rejects
escape of H through results,
latent rows, captures, evidence or completion dependencies. Its initializer is
trusted host setup fixed by the checked build; source cannot select a native
implementation, mode or policy. The build selects one mode/policy per activation;
nested activations are distinct and cannot exchange owned access. Host setup and
teardown occur under that activation; in-process quarantine may keep physical
backing beyond source closure without retaining usable source access.

The executable `main` explicitly encloses checked native work in a host expression.
After ordinary resource handling and this boundary its outward row is empty.
A remaining legacy owner-free native instance cannot be discharged by the checked
profile's program entry. Existing legacy entry behavior remains available only
in the existing profile. Merely writing a host expression in that profile refuses;
it cannot acquire the checked guarantee through a legacy image.

The symbol's outer source arrow retains its existing pure form: applying the
checked symbol requests the original native operation, whose latent computation
row additionally contains the selected H. A `host H` marker selects exactly one
explicit Type formal by original identity, not the first same-kind parameter.
Missing, duplicate or non-Type host selections reject.

Checked native operations carry their original exact native instance plus
`Foreign.NativeHost<H>` in their computation effects. Resource interpretation
subtracts only its listed native/resource instances; it retains H for acquisition,
actual calls and required completion. The host boundary never interprets an
owner operation outside its owning resource lifecycle. Ordinary wrapper signatures quantify H
explicitly and show the host effect in their existing row syntax. Ordinary source handlers and ordinary Core interpretations cannot eliminate
`Foreign.NativeHost<H>`; only the authenticated host boundary can. Source cannot
construct or implement `Foreign.NativeHost`; its identity comes from the builtin.
The nearest ordinary handler still handles ordinary operations. A simulated
result grants no acquisition/consumption authority; a handler that invokes native
work must retain the actual native/host rows. No new handler precedence rule is
introduced for ordinary effects.

The first source subset accepts existing scalar/void calls and opaque/initialized
byte owners only where the whole checked closure satisfies these obligations.
The marker alone is insufficient. General raw pointers, escaping native views,
callbacks, asynchronous entry and privileged lifecycle helpers remain rejected.
Ordinary wrappers express bounded SQLite state checking and copying using admitted
primitives and generic cells where sufficient; the compiler does not dispatch on
SQLite names. Additional primitive roles require a separately checked common
contract rather than a library-specific escape hatch.

### Generic violation and quarantine

A checked group is a host-owned native resource domain. An acquisition with no
declared owner dependency creates a fresh provisional group before native entry.
An acquisition depending on existing owners inherits their exact group; the first
profile rejects dependencies spanning distinct groups. Group identity is runtime
lineage separate from H: two independent owners under the same host are not the
same group. Guards, published owners, aliases and windows retain that identity.

Ordinary binding code needs a generic conservative violation path; a cell flag
cannot revoke other aliases. Add these authenticated builtins in `@builtin.foreign`:

```ash
type ViolationCause = UnexpectedStatus(Int) | UnexpectedTag(Int)
    | UnexpectedNull | InvalidNativeExtent(Int) | ContradictoryNativeResult(Int, Int)
checked_quarantine<H, S> : (S, ViolationCause) -> CheckedCall<Unit> ! {NativeHost<H>}
checked_reject_acquisition<H> : ViolationCause -> CheckedCall<Unit> ! {NativeHost<H>}
```

`checked_quarantine` requires the exact descriptor-witnessed Current or declared
Enclosing State S in a direct checked provider/lifecycle phase. H must be that
state's selected host. It selects S's authenticated group, never a pointer, an
ordinary handle, a caller-supplied group ID or a merely compatible S. During
prepare error/non-null, use the established enclosing C, never the suspect S.
`checked_reject_acquisition` is sealed to the direct acquisition phase after an
admitted native acquisition request and before source publication; its group and
host come from that exact pending request, even if no native owner was established.
No ordinary helper or generic instantiation grants either primitive's authority.

The primitive atomically marks the selected group quarantined, retires ordinary
access across every alias/proxy and invalidates its windows/row cache. It retains
all established dispositions and backing edges and marks unresolved native facts
without asserting consumption. No native call, source K discharge, extra finish
attempt or report insertion occurs. The bounded independent cause is diagnostic
binding policy; the runtime attaches the pending/current operation identity and
last admitted observations itself. Invented cause data cannot forge an observed
native fact or prove that foreign code is at fault. Explicit quarantine is a
conservative denial of access, never stronger permission.

With healthy evaluator capacity the result is always
`BoundaryFailed(Quarantined(record))`; unavailable mandatory capacity is terminal
X1, preserving the already installed quarantine. A later structural owner finish
selects K6 and obtains only that owner's synthetic finish witness. The quarantine
call's ordinary failure constructor is not a source completion witness. The
never-published acquisition path retains only guard/supervisor disposal authority,
not a source K. Other live groups under H stay separate; isolated group quarantine
stops dispatch and initiates its admitted supervisor disposal while retaining
reservations until actual reaping. No suspect pointer becomes a destructor operand.

This is the common mechanism for T1 unknown tags, T5 contradictory null, L8
suspect prepare output and similar declared violations. Ordinary Ash conditionals
choose the library policy; the runtime has no SQLite-name dispatch. Tests must
show another alias cannot enter after quarantine, the wrong group stays live,
backing persists, forged S/H/group inputs reject, and no consumed/discharged fact
is created by either primitive.

### Assumptions, summaries and authority

Mandatory compiler/parent/kernel and producer/build-correspondence assumptions
are attached automatically by the admitted profile. Every native role also
retains inherent obligations for execution, readable initialized memory intervals,
nonretention/copy windows, aliasing and disposition truth as applicable to its
authenticated operation roles. Named assumptions describe or refine these; an
empty authored set cannot remove them or claim they are proved. A future proof
may discharge only an identical role-linked obligation with separately checked
artifact/configuration applicability.

Library assumptions have fresh defining identities, precise text, affected
operations and target/configuration applicability. Symbol `assumes` references
those originals. The compiler propagates the union through wrapper calls,
selected evidence, higher-order captures, branches and bounded recursive summaries.
A wrapper cannot declare that union empty to erase a dependency. Opaque exports
hide constructors/layouts but retain body-free effect, dependency, completion and
assumption facts for independent checking. Propose `ash inspect-ffi ENTRY` as a
read-only report of required contracts, affected exports, assumptions and selected
mode/policy; it neither executes native code nor supplies approval. The same
information is retained in build receipts. Pure copied bytes do not retain H or
native owner dependencies; a closure that reads S retains S/C/H even if it returns
only strings.

Canonical checked contracts remain the single semantic facts, projected into
summaries, Core, bridge plans and image admission. Preserve original identities,
full schemes, hidden dependencies and causal origins across re-exports, opacity,
Type/Row specialization and transformations. Core independently reconstructs
these facts and bounded native-copy plans; matching types, hashes or constructors
are insufficient. Native operations remain in Effect Core. Refuse exhausted
analysis without publishing partial permission. Existing depth/stack limits and
separate cumulative meters remain; this proposal selects no new gas coefficients.

### Observation, failure and completion

Adopt the common O1–O10, X1–X5 and K1–K9 transitions, and the SQLite L1–L23 and
T1–T16 policy, from the [canonical tables](../design/foreign-authoring/minimal-ffi-transitions.md)
at the [input pins](../design/foreign-authoring/linux-profile-probe/design-input-pins.json).
These pins freeze the reviewed proposed meanings; later changes require proposal
review. The tables continue to own the combined transitions. Adoption is proposed,
not a statement that any row is implemented or that SQLite obeys its assumptions.

An ordinary boundary outcome distinguishes pre-entry refusal, admitted native
failure, conversion refusal, protocol/session loss and unknown post-entry
completion. Native status/disposition, source delivery, local completion K,
physical reclamation and diagnostic availability remain separate coordinates.
No unchecked native value or partial copy is published. Every call publishes at
most one source result. Admission precedes dispatch; observation uses the saved
pending state. Loss does not require still-live ordinary access. Prior admitted
consumption survives lost diagnostics. A lost reply never authorizes replay.

The first checked resource codec is `codec checked_scope`. Its acquisition
codec retains existing `Acquired(State,D)` / `Refused(I)` checking. Its finish
result must be the canonical `Foreign.CheckedFinish<State,E>`, and its scope
result is canonical `Foreign.CheckedScope<Answer,I,E>`. Unlike existing generic
codec matching, these checked types/constructors have authenticated builtin
identities; same-shaped user types do not substitute. The proposed public shapes
below use existing `Int`, `String`, `Bool` and products. Strings are independently
copied and bounded. `ConversionError` is the existing foreign conversion error.

```ash
type NativeStatus = NoNativeStatus | NativeStatus(Int)
type NativeFact = NoNativeOwner | NativeOwned | NativeConsumedFact | NativeUnknown
type DiagnosticAbsence = NotRequested | AllowanceRefused | NativeAbsent
    | ScanBoundExceeded | InvalidDiagnosticEncoding | DiagnosticLost
type Diagnostic = DiagnosticUnavailable(DiagnosticAbsence) | DiagnosticText(String)
type BoundaryRecord = BoundaryRecord(NativeStatus, NativeFact, Bool, Diagnostic)
type BoundaryFailure = SessionLost(BoundaryRecord)
    | DependencyBlocked(BoundaryRecord)
    | Quarantined(BoundaryRecord)
type CheckedCall<T> = CheckedReturned(T)
    | CheckedConversionFailed(ConversionError)
    | BoundaryFailed(BoundaryFailure)
type FinishResult<E> = FinishOk | FinishError(E)
type CheckedFinish<S, E> = FinishedConsumed(FinishResult<E>)
    | FinishedRetained(S, E)
    | FinishedBoundary(BoundaryFailure)
type CheckedCompletion<E> = NativeConsumed(FinishResult<E>, BoundaryRecord)
    | NativeRetained(E, BoundaryRecord)
    | LocalBoundary(BoundaryFailure)
type CheckedScope<A, I, E> = CheckedNotAcquired(I)
    | CheckedCompleted(A, CheckedCompletion<E>)
```

These declarations describe the proposed builtin shapes, not executable examples
in current Ash. `BoundaryRecord` retains last admitted native status/fact; its
Bool records a later unresolved transition rather than overwriting that fact.
No status uses `NoNativeStatus`, never a fabricated numeric success. The primary
reason is selected by the enclosing completion/failure constructor. Optional
text absence never erases mandatory facts. A report grants no native authority.
Checked source symbol validation replaces each current outer `Foreign.Call<T>`
with `Foreign.CheckedCall<T>`, retaining its exact inner output/disposition
relations. Add separate authenticated builtin functions; existing builtin identities and
signatures remain unchanged:

```ash
checked_byte_read<H, S> : (S, Int) -> CheckedCall<Int> ! {NativeHost<H>}
checked_byte_write<H, S> : (S, Int, Int) -> CheckedCall<Unit> ! {NativeHost<H>}
checked_copy_bytes<H, V> : (V, Extent<V>) -> CheckedCall<Bytes> ! {NativeHost<H>}
checked_copy_nul<H, V> : (V, Int) -> CheckedCall<Bytes> ! {NativeHost<H>}
```

These proposed names belong to `@builtin.foreign`; unqualified types above refer
to that same module. The explicit first Type argument H must equal the checked
owner contract's selected host actual, reconstructed from the exact State S or
view V lineage. A merely compatible S/V, arbitrary H or same-shaped Extent cannot
authorize access. Preserve the existing direct-provider/window, initialized-extent,
non-suspension and no-State-forwarding restrictions. Calls outside those phases
reject. Existing `byte_read`, `byte_write`, `copy_bytes` and `copy_nul` are rejected
on checked owners/views, so their empty ordinary rows cannot bypass H. Existing
pure scalar/NUL preflights, data/private-state functions and extent inspection
retain their identities and authority restrictions; pure preflights return their
existing Call codec and never touch native memory. This addition grants no new
State/view transport to ordinary helpers.
The legacy `scope` and `acquired_only` owner codecs remain ineligible for checked
ownership; existing-profile support is unchanged.

A host expression returns body type A unchanged, with only the exact admitted
native and H effects removed. Each checked scope produces its own report. The
runtime reserves one fixed owner record before publication. At K3/K4/K5/K6 it
commits only independently representable BoundaryRecord facts and the selected
primary reason to the proposed ordered resource-report channel at the structural
closing positions, S before C. The channel does not contain arbitrary source E.
That E becomes available only when authored finish actually returns and source
CheckedScope result admission succeeds; no second runtime record is inserted. Discarding an ordinary source report
does not discard that channel or its ownership facts. Host execution inspection
exposes the bounded records and diagnostic-unavailable markers; failure to reserve
mandatory history refuses before owner publication, and actual later mandatory
reporting exhaustion is terminal. Host return adds no aggregate source value.

K4/K5/K6 govern native completion admission, not erasure of authored source code.
A healthy structural exit starts the authored finish computation once with its
existing required effects/interpreters. If its native finish request has not
entered and the session is lost, quarantined or blocked, the trusted boundary
returns a synthetic checked boundary outcome without dispatch and records the
selected local reason. Checked calls return `BoundaryFailed(reason)` and source finish returns
`FinishedBoundary(reason)`, carrying only independent data and never State. The
lifecycle checker accepts `FinishedBoundary` only with the exact authenticated
boundary-failure witness from this owner's attempted finish request. A constructor
or a previous operation's failure cannot supply it. The witness remains private
to checked lifecycle checking; source can pattern-match independent error data.
The source finish receives that alternative and must
handle it without presenting it as native consumption or retention. Its enclosing
required source effects and continuation still execute. An already running
source action/finish cannot be abandoned through K bookkeeping. The native observation or synthetic finish outcome commits K3/K4/K5/K6 at
the owner's structural closing position before fallible result delivery; no
second request or local report is admitted. The required source finish
continuation remains separately owned until its actual completion. K discharge
is bookkeeping, not permission to drop that continuation.
If source finish suspends or does not return, local control obligations persist;
no unconditional cleanup/termination guarantee is added. Checked codec/lifecycle validation must preserve the separate required
source-control continuation even after the native fact and K record commit.
A finish body must account for exactly one conforming native or synthetic finish
outcome for that owner on every returning branch; a return without either witness
is rejected. When K is already discharged by loss before authored finish begins,
its one reserved failure witness is supplied at the owner's finish request
without another K transition or report. This delivery cannot be reused for a
second native attempt or another owner.

Terminal evaluator failure transfers unfinished K to host disposal without
claiming authored cleanup. Healthy Closing owners select loss before quarantine
before dependency-blocking; already discharged/transferred owners stay unchanged.
Unknown native consumption preserves backing, while local source discharge does
not extend source access. Reaping only establishes physical process reclamation.

### Containment and artifact admission

Both modes require an operator-authorized exact image/receipt, checked closure,
bridge association, ABI/runtime/protocol versions and applicable assumptions.
A digest detects changed bytes but does not authorize a producer. Local protected
approval or trusted distributed signatures bind approval to immutable executed
bytes and dependency closure before native startup. In-process execution retains
host memory/authority assumptions. Isolation treats the entire worker as faulty;
the parent validates replies and local authority. Plausible false replies remain
possible. Database truth, rollback, native correctness and eventual release are
not established by valid payloads or by process isolation.

Linux realization is separately proposed in the
[F2 experiment contract](../design/foreign-authoring/linux-profile-experiment.md).
Missing controls refuse before acquisition; static-image packaging and Linux
syscalls are not language-level effect coordinates. F2 acceptance is required
before F6/F7 product work that relies on the Linux realization, separately from
F1 semantic acceptance.

## Semantic delta

Add explicit authenticated host introduction/elimination, checked source markers,
transitive assumption projection and a whole-closure opt-in build profile. Add
checked completion alternatives and loss behavior while retaining distinct native
facts and required source-control completion. Extend hidden dependency checking
to H and session-bound authority. Existing passive modules, exact identities,
generic cells and legacy supported builds retain their current contracts.

## Affected specification areas

On Main's pinned specification, product adoption must update
[syntax](https://github.com/dikini/ash-lang/blob/7949b6d9136b0152ee9104e67bd0451cb9db4727/spec/syntax.md),
[static semantics](https://github.com/dikini/ash-lang/blob/7949b6d9136b0152ee9104e67bd0451cb9db4727/spec/static-semantics.md),
[dynamic semantics](https://github.com/dikini/ash-lang/blob/7949b6d9136b0152ee9104e67bd0451cb9db4727/spec/dynamic-semantics.md),
[elaboration](https://github.com/dikini/ash-lang/blob/7949b6d9136b0152ee9104e67bd0451cb9db4727/spec/elaboration.md)
and [name resolution](https://github.com/dikini/ash-lang/blob/7949b6d9136b0152ee9104e67bd0451cb9db4727/spec/name-resolution.md).
Cover foreign declarations/resources, exact effects, dependency/escape checks,
module summaries/linking, entry, independent Effect Core, scope reports and
runtime failure. Tool documentation must describe the proposed options/report
only when implemented. This preparation changes no specification.

## Resulting specification truth

Only after complete product retention and Main integration, checked builds will
execute native work solely within authenticated configured host activations,
publish only admitted values/access, preserve transitive assumptions and exact
owner dependencies, and distinguish source completion from native disposition
and physical reclamation. Isolated guarantees additionally require an accepted,
verified deployment realization. Neither mode promises correct native answers.

## Interactions

Generic cells can hold ordinary protocol state but cannot forge owners, H or
completion. Capture/resume moves the same ownership; required discard and cleanup
retain actual interpreters and source-control obligations. Nearest ordinary
handlers retain precedence. Regions and continuation stores are future pressure,
not prerequisites; the dependency model must not equate ordinary payload storage
with native acquisition or invent a second retention mechanism.

## Non-goals

No general borrowing, callbacks, asynchronous native stacks, shared memory,
extra platforms, general proof syntax, persistent module format, dynamic loader,
worker recovery or native-correctness theorem. The first checked owner codec
excludes `acquired_only`; it remains supported in the existing profile. No
product task, accepted architecture, publication or Main permission is created.

## Required evidence

The [complete row map](../design/foreign-authoring/checked-ffi-evidence-map.md)
covers all 63 canonical O/X/L/K/T rows. Required distinguishing traces are the
canonical table's entire final trace section, in both execution modes. Each
future receipt records actual inputs/limits, observed native and parent outcomes,
source/Core correspondence, retaining commit and explicit injected failures.
No row is accepted from this draft or the environment probes.

Additional obligations: body-free imported wrapper admission; full Type/Row and
opaque/re-export identity preservation; hidden captured-owner rejection;
wrong-host/stale-session rejection before entry; host-effect erasure and forged
independent results rejected at summary/link/Core/image boundaries; native-window
splitting/reordering and required source-finish erasure rejected after transforms;
exact budgets, one-short refusal and fresh sufficient execution without replay;
actual generated native copy/acquire/finish and both modes' supported examples;
real Linux enforcement/ABI/artifact evidence. F-core and F-final remain pending.

## Accepted choices and pending gates

The delegated acceptance selects the explicit H source binder and host markers above, complete checked
closure refusal, and `checked_scope`-only checked owners. Alternatives are implicit host
parameters (would hide new polymorphism/identity rules), adapting `acquired_only`
(would obscure completion failures), or build-only safety metadata (would move
source-owned policy into producer trust). The user authorized autonomous recommended choices and unsigned commits on
2026-10-21. Independent review cleared the preparation candidate at SHA-256
`87480f9f8dda2d218e59099e6ca179ae1bdfb18616e2bb4908727b4c1456f854`;
the orchestrator then adopted these choices under that delegation. Review is
evidence for the decision, not semantic acceptance by the reviewer.

Independent review must check the proposed synthetic finish alternative and
separate source-control obligation against the canonical table. Any disagreement
returns to this proposal before semantic acceptance. Wire/receipt encodings, Rust
structs and concrete syscall allowlist remain bounded implementation/architecture
choices under the frozen obligations. F1 semantic acceptance is recorded above. F2 deployment acceptance, authorized
product tasks, independent implementation review, full gates and Main retention
remain separate pending obligations. The reviewed preparation becomes current
Ash only through the complete product workflow.
