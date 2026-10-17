# TASK-0036: Source contracts, Core and generic execution

- ID: `TASK-0036`
- Status: active
- Related: [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [GitHub issue #2](https://github.com/dikini/ash-lang/issues/2)

> This task organizes authorized work. It does not define Ash semantics.

## Dependencies

Accepted CP-0022 and AD-0013; the linked contract issue #1 supplies review and
acceptance evidence. Coordinate the executable boundary with TASK-0037. Library
ports depend on this generic mechanism, rather than granting native authority.

## Work

1. Admit the complete foreign/resource/access grammar and passive module exports,
   retaining exact defining origins, kinds and complete ordered Type/Row arguments.
2. Prepare one immutable checked foreign contract and checked template per defining
   occurrence. Use phase-specific types and authenticated native projections;
   specialize with fresh local identities without replaying source checking.
3. Implement generic native-effect interpretation, private resource data, finite
   copy windows, initialized output/extent evidence and guarded ownership phases.
4. Reconstruct and independently validate final Core through modules/transforms;
   preserve handler precedence, capture/resume/discard and quarantine dependencies.
5. Update affected specification sections alongside verified behavior. Preserve
   bounded work, fallible allocation, iterative traversal/disposal and depth limits.

## Progress

Assignment, blockers, live progress and PR status belong to the linked GitHub
issue. This task retains scope, ordered work and durable implementation findings.

## Verification

Use public-pipeline integration cases for source admission/publication, exact
identity and tagged argument checks, malformed/transformed Core, invalid access
and escape. Observe actual native acquisition, refusal, partial-owner cleanup,
window copies, completion order, resume/discard and retained-dependent blocking
through TASK-0037 bindings. Retain the open-Delta case and separate
captured-control witness. Run connected compiler/Core/evaluator regressions
with one Cargo job; keep milestone-wide regression pending between the named
checkpoint gates in the [agent workflow](../project/agent-workflow.md). The
historical full gate was run at `868d0b43` and transferred by authenticated equality
to retained `9fae971`. PR21's focused ownership delivery is retained at
`d44138f`, PR22's focused scalar teardown delivery at `3435d62`, and PR23's
checked scalar constants at `d09b99f`, and PR24's non-callable sentinels at
`5323aee`, and PR25's pure payload helpers at `ea93b87`.
The TASK38 buffer port supplies additional focused evidence;
milestone-wide regression verification remains pending. The next
gate belongs to the PM after shared ownership/control/runtime support is
complete, including declared dependencies, retained-owner quarantine, control
and required-completion failure matrices through source, Core, copying, image,
bindings and guard storage. Focused PRs may contribute toward that boundary
without making each PR a full-gate checkpoint.

Payload-helper evidence distinguishes complete copied Type/Row actuals,
same-typed global donors, missing or duplicate image loans and a changed immutable
scheme context. Independent Core and image restoration have exact, one-short,
prefixed and fresh-retry witnesses. Current local and imported row-polymorphic
helpers execute in acquisition and finish, including a branch-selected closed
alias, while each actual native owner is acquired and released once. Ash source
is removed before host building and image/facts files before child execution.
Typed State transport and hidden native requests remain refused. These focused
checks do not complete the shared-runtime regression checkpoint.

## Discoveries

Export-summary collection now finishes before independent admission begins. A
private helper retains the existing collection checks, charges and fallible
storage; the existing freeze entry then authenticates the owned candidate once
with the same cumulative budgets. Collection scratch no longer remains on the
stack through certificate and kind admission. Partial collection and rejected
candidates retain their existing disposal paths.

Shared-runtime checkpoint 1004 at `3d6d00ba` passed formatting, metadata,
workspace checking, building and strict lint, then aborted in the library test
process during builtin Cell export freezing. The intended deep-result finish
checks had not begun; later test targets and documentation were unrun. The
unchanged 256 KiB regression passes in focused run 1008, including its exact
row-work refusal and fresh retries. Stack, depth, work and authority policies
are unchanged; a fresh integrated full checkpoint remains required.

An iterative worklist can still retain unrelated construction scratch across
reentrant calls. Core kind/row validation and source resolution keep their owned
buffers and final result checks in thin drivers, with construction work in
private noninlined helpers. Application-argument admission uses the existing
direct elaborator route; the four checking branches use a private borrowed
helper. These changes retain the same checks, charges, scheduling, guarded moves
and error cleanup.

The unchanged 64 KiB captured-control regression passes in focused run 1020.
The existing 34-test stack/kind batch first recorded 33 passes and one failure
at its own input pin. Subsequent diagnostics reached nested handler-clause
checking after resolution, application admission and cleanup returned; those
failures occurred during source compilation, before evaluator draining.
The unchanged 256 KiB owned-deep-drain regression passes in run 1037, including
successful execution and both partial-work refusal checks. The same 34-test
owning batch passes in run 1038, including both stack regressions and the prior
Finish regression. Original stacks, assertions and work, depth and authority
policies remain unchanged. Checkpoint 1014 remains a historical failure; a fresh
integrated full checkpoint is still required.

Shared-runtime checkpoint 1043 at `f21c5865` completed the owning library with
1,868 passes and eleven failures after its first five verification stages
passed. The Finish, 64 KiB captured-control and 256 KiB owned-deep-drain
regressions all passed in that library run; later test targets and documentation
were unrun. The eleven failures used predecessor exact-work expectations that
omitted paid nominal formal-kind scans or owner-head lookups introduced by
complete Type/Row owner admission.

The tests now account for those actual scans and lookups. The wide nominal
fixture funds its root and owner-head lookup before testing the same first
argument's refusal span. Type and Constraint shortages remain distinct, and
semantic, one-short, atomic publication, spent-prefix and exact-retry assertions
remain intact. Focused run 1044 passes all eleven corrected tests and eleven
directly affected boundary controls. Production code, cumulative charges,
allowances, defaults, stacks and checks are unchanged. Checkpoint 1043 remains
failed; a fresh integrated full checkpoint is still required.

Fresh checkpoint 1047 at `28335192` passed its first five stages and nineteen
owning test targets, including all 1,879 library tests. The next target,
`data_and_adts`, recorded 31 passes and one isolated child stack overflow in the
public type-wrapper regression. Cargo returned 101 and xtask recorded failure;
the outer wrapper later terminated with 143 after saving that result. Read-only
postchecks confirmed the frozen inputs. Later targets and documentation were
unrun.

The first operational fixture completed resolution and body preparation, then
reached `CheckBlock` through the ordinary expression dispatcher. Its scheduler
call did not reach the first entry marker. Block scheduling now uses the thin
engine's direct route, keeping unrelated dispatcher scratch off that call chain.
The same scheduler receives the owned expected type, declaration position and
cumulative ledger; task order, guards and error cleanup remain unchanged.

The unchanged 256 KiB regression passes in run 1051, including both operational
tuple/function and constructor-payload wrappers. Run 1052 passes all 24 selected
existing integration stack tests across fifteen targets. Run 1053 passes six
related scope, work, Finish and evaluator-disposal controls. These are focused
results under the original stacks, assertions and budgets; checkpoint 1047
remains failed, and a fresh integrated full checkpoint is still required.

Scalar destruction-input mapping A binds a producer's original `Int` input path
to an ABI slot of that owner's exact original host destructor. Producer ABI
input coverage is independent, so cleanup-only inputs need no native producer
operand. Normalization orders targets, requires complete scalar coverage and
preserves same-destructor-leaf consistency, source origins and full Type/Row
contexts. Private claims carry the same relation; structural restoration and
original-facts comparison retain distinct obligations.

The initial focused slice verifies passive public admission and refusal,
normalization/restoration/original correspondence, exact and one-short work,
spent prefixes and fresh retries. The connected runtime now captures and narrows
producer inputs into the reserved native guard vector before C; the typed
teardown bridge accepts those native scalar variants. Ordinary Finish separately
converts its explicit inputs before moving the guard.

Focused run 975 executes the generated host through imported full Row Owner
instances, copying and a private image. Normal Finish destroys owner `42` with
explicit scalar operands `5` and `999`. Refusal destroys unpublished owner `9`
once with captured operands `-7` and `18446744073709551615`, in original ABI
order. The existing harness removes Ash sources before preparation and image
and facts files before child execution. This is one real native lifecycle
discriminator, not the remaining delivery matrix.

Focused run 982 passes six metadata, bridge, pre-call, copied-Core, image and
injected-callback controls. Complete pre-call work is 67 units, with exact,
one-short, spent-prefix and fresh-retry checks. A scalar converter's work error
retains its existing absent requested-count field. Complete image restoration
uses 142,150 units with matching boundary checks. Six changed mapping claims
fail independent original-facts and startup gates before provider selection;
three missing, duplicate or wrong-role targets also fail semantic restoration.
The copied-scope donor, node map and phantom Row claims fail direct scope
authentication. Whole-Core checking rejects the altered request's stored row
before scope checking and rejects the two metadata-only claims at the registry
boundary. Counted opaque callbacks separately establish zero native calls on
injected pre-call exhaustion and one snapshot cleanup after post-return work
exhaustion. These injected callbacks are not real C execution.

Focused run 983 passes five generated-host controls. Signed and unsigned range
refusals execute zero C calls before a fresh computed-`Int` retry. A readable
nonnull typed output owner is guarded and destroyed on a native error result.
Retained Finish observes replaced `D` through explicit operands `5/123`, while
host fallback retains captured `-7/U64MAX`. A dependent child's captured `77`
is delivered beside its Current and exact live Enclosing pointer; C assertions
and the trace establish child-before-parent destruction after retained-dependent
blocking. The earlier direct-result/explicit-Finish discriminator also passes.
The same source/image-removal harness applies throughout.

Normal runs 992–998 at `9533ddd0` pass the complete owner target (77 tests),
Buffer target (13), SQLite library (34), copying target (26), architecture
target (47), expanded strict linting and formatting. All 1,737 source records
and the recorded configuration remain equal throughout. The named set of 99
native/header/tool files and four Rust tools matches before and after; this is
not an environment-wide attestation or a full workspace checkpoint.

Focused run 1000 additionally executes the reordered, cleanup-only capture
witness through an actual shared library. Its source, native generator and
result/trace oracle match the static case exactly: explicit Finish uses
`5/999`, while unpublished fallback uses `-7/U64MAX`. Run 999 had completed
Source, Final, Core, preparation and host building but failed before C because
the test library was absent from the loader search path. The correction uses
the existing Buffer harness's child-only shared-library search path; static
callers keep their previous setup. Production code and budgets do not change.

The initial setup and assertion failures remain recorded at their own pins;
they did not justify changing product guards, image literal limits or errors.
Delivery verification also requires current affected caller, architecture and
strict/fmt gates.
These changes grant no new State/view transport,
private-data permission or ABI role. Ordinary Finish remains separate from the
acquisition-time native snapshot.

The current baseline for this increment is retained PR #35 at `5893a546`, after
the complete ordered Owner Type/Row delivery. The last full checkpoint 748 at
`63197b6` is historical, with PRs #34–#35 intervening; this initial slice claims
no new full gate. Source `800*S`, Final `800*S`, separate compiler-arena rewrite
`16*S`, independent Core `345*S`, preparation `125*P`, startup `22*B`, generic
defaults and all depth/stack/checks remain unchanged. PM owns the next checkpoint;
Main's signed human gate remains separate.

The inherited-owner Row implementation retains a nominal Owner application with
complete tagged actuals. Its exact prepared Owner declaration selects that form
from the defining kind vector; ordinary applications and source-resource
identities retain their separate representations. The direct nominal head must
remain visible to native-state, private-data and imported-metadata checks even
though it is no longer a nominal child. Opaque imports retain full canonical
formal records and original kinds without materializing a private declaration.
State lifecycle mappings and pre-call destructor specialization preserve Rows
as well as Types before the native ABI projects Type arguments. Focused current
evidence compiles passive and imported aliases through independent Core and
executes copied/image-restored owners through generated native hosts with empty,
distinct and reversed phantom Rows, preserving each acquire/release trace.
Exact original/fact and semantic-copy refusals, cumulative work boundaries,
current affected callers, review and retained verification remain separate
delivery obligations. This is active implementation of accepted CP-0022;
scalar teardown input mapping A remains a separate increment.

Source handler originals retain conditional row equations and exact callback-input
coordinates until actual request captures are available. Their private
continuation specializes to the complete client residual row; direct handler
requests contribute separately to the outward row. Empty residuals and overlap
with direct effects need distinct controls, since subtracting direct requests
from the total can erase real client demand. Independent final Core derives both
rows and each request capture from checked lexical/global roots before comparing
copying claims. Private images scope unresolved original rows to their exact
pending owner before interning or memoization, then re-admit originals and final
copies. The current open-Delta and equal-substitution witnesses execute through
generated hosts; they do not replace the full criterion's existing ownership,
quarantine and failure evidence.

Copy-window row proofs reconstruct state evaluation separately from the body.
Only the body's exact native instances are interpreted, and any remaining body
demand refuses admission. The complete state row remains outward demand, including
an overlapping native instance and its row tail. These row facts do not replace
the original family, phase, access and capture checks.

Defining declaration slots require source-derived coordinates, not density of a
claim-sorted table. A bounded syntax-only walk of resident original provenance
reconstructs nominal category allocation and the separate written effect/native
symbol order. The lexer and parser share a capped loan from the consuming
validation ledger; every return debits spent work before handling its result.
This is registry provenance checking, without path loading, source resolution,
type inference or per-instance semantic replay. A coherent owner/access or
effect/operation ID permutation cannot authenticate its own defining slot.

TASK38 exposed common source-resource boundaries without requiring privileged
lifecycle helpers or source-given forwarding. Exported source access kinds retain
the original checked family header. Ordinary lexical-header duplicate checks
use that original source application/context, never an experimental forwarding
plan. Exact acquired-only restore cuts keep acquisition/body/cleanup/handler/
finish positions separate, preserving live captured-cell dependencies while
freezing completed acquisition once. Strict control discovery can retain the
same passive close rows used for independent row authentication instead of
running a duplicate inference solver. Current positive/negative and exact-work
witnesses remain distinct from actual generated C executions. Canonical cell,
cleanup and hook/registration image records cover the port-used structures;
ordinary local-newtype/non-resource dictionaries retain their existing native
image exclusion. These findings do not complete the shared-runtime checkpoint.

Ordinary pure module-global helpers now transform independent acquire/finish
payloads, including same-module and imported polymorphic definitions. Source
template preparation reuses checked declaration headers instead of allocating
unused Core binders or inlining helper bodies. Original forests retain only used
global scheme loans. Independent final Core closes every loan against its actual
lexical binder and complete scheme; copied calls retain their original defining
context and all ordered Type/Row actuals. Immutable registry-session reuse also
requires the same retained global context; moving it triggers fresh registry
authentication. Private images encode the loans canonically and reconstruct them
under the ordinary final Core gate. Each owning type is held by iterative storage.
These scheme loans grant no native permission, State transport or phase privilege.

Non-callable sentinels use a separate prepared table from ordinary scalar
constants. An all-bits-one declaration retains its exact original representation
coordinate and member identity through source admission, Core, copies and private
images. It publishes no ordinary value or callable symbol. The GNU64 generated
bridge passes the target bit pattern without constructing a Rust function value;
real static/shared C observations inspect its bits without calling it. Native
owner acquisition, source finish and separate partial-owner host destruction use
the same fixed-operand admission. This supplies a SQLite prerequisite without
implementing SQLite, temporary copy windows, nullable roles or general macros.

Checked foreign scalar constants occupy the ordinary term namespace and inherit
the defining library's publication mode. Qualified, selected and re-exported
uses retain the defining binder. Their exact mathematical literals lower as
nonrecursive `Int` bindings outside the existing function-only recursive groups;
ordinary global definitions retain their function restriction. Constant binders,
spelling copies and declaration-order permutation use precharged fallible
storage. Keeping the original declaration order preserves independent kind and
evidence checks rather than relaxing their correspondence.

Native constant operands select the original library's checked member and exact
representation before narrowing and complete call admission. Equal-valued
members are not interchangeable under executable EXPECTED_FACTS authentication.
The same selection works in owner acquisition, source finish and separate host
destruction. Static/shared scalar hosts observe signed values and full unsigned
64-bit values after sources and image/facts files are removed. An owner witness
separately observes normal finish and partial-owner host destruction with fixed
original operands. That fixed-operand delivery did not generalize
source-projected scalar teardown inputs or lifecycle callable privilege;
the Mapping A increment above supplies the separately approved scalar mapping.

The private image keeps signed i64 literal encoding and adds a canonical u64
payload only above `i64::MAX`, retaining the full range of admitted scalar
constants. This is not general arbitrary-precision literal serialization.
Literal elaboration initially enlarged a shared debug frame enough to overflow
the unchanged 256 KiB cleanup witness while compiling its fixture. Isolating
the literal-only routine reduces that shared closure from 8,456 to 7,464 bytes;
the ordinary equation path, work charges, guarded ownership and stack policy
remain unchanged.

Scalar teardown uses a separate immutable status descriptor alongside the
existing void descriptor. It retains total original literal predicates,
disposition/readability spans and the complete owner application. Source,
independent Core, copying and private image reconstruction preserve those facts;
complete generated EXPECTED_FACTS bytes authenticate foreign assumptions before
binding. Well-formed changed foreign assertions are not rejected merely by
structural Core validity. Malformed coverage, spans and applications have their
own independent refusal boundary.

The original typed status callback is admitted separately for source finish and
host destruction. Readiness pays finite selection and complete reply work and
reserves complete success cells before C. Disposition and dependency changes
precede result widening. GNU64 replies fit num-bigint 0.5.1's inline 64-bit
digit; no integer representation change or late allocation is required.
Raw scalar results are always readable, and unreadable scalar declarations
reject during source and private reconstruction. Post-call extraction failure
preserves witnessed disposition and terminates without an ordinary reply or
source continuation. Injected consumed/retained witnesses distinguish no second
consuming callback from one safe original host destruction of a retained owner;
later host success cannot turn that source failure into success. Pre-call
conversion refusal remains an ordinary result with no C entry.
BlockedDependent has no native status payload. The flat store now owns its
typed slot authority while sharing original symbols; its retention inventory is
Mixed and its existing iterative owners remain responsible for disposal.

Connected status witnesses distinguish consumed error from Closed, retained
source completion from later consuming host destruction, incomplete destruction
without retry, blocked status teardown before C, dependency-order recovery,
full unsigned widening, capture/resume/ordinary override and terminal retained
discard. Injected readiness witnesses distinguish the I32 reply's ten-unit
exact allowance from one-short atomic refusal (six units spent), prefixed
allowances and two fresh retries. That status delivery required only checked
passive status literals; ordinary exports and fixed native operands have their
separate declaration and admission evidence above. That status-only delivery
left source-projected scalar teardown inputs outside its executable profile;
the Mapping A increment above addresses those inputs. Privileged lifecycle
wrappers and the remaining shared-runtime checkpoint keep their separate scope.

Source control moves the same guard/activation through capture and resume.
Owned discard runs acquired scopes' original finish once in structural order,
with required outer resources live; it never fabricates an abandoned body value
or result wrapper. An acquisition discarded before publication revokes only its
unpublished native guard. Running finish remains a nonabandonable cleanup action,
and exact native interpretation preserves ordinary outward requests and their
required outside interpreters. The 2026-10-12 human clarification makes a consumed
`ConsumedFailure(E)` terminal on owned discard for the scope codec; normal
`Scope.ConsumedError(E)` is unchanged.

The 2026-10-13 human clarification makes witnessed `Retained(State,E)` terminal
on owned discard after ordinary access revocation and quarantine of the same
owner/dependency closure. No discarding clause or fallback continues, and no
abandoned body value or scope report is fabricated. Source finish remains a
single attempt. Later successful host destruction is distinct from failed
source completion; normal `Scope.Completed(value, RetainedError(E))` is unchanged.

The 2026-10-13 human clarification separates local lifecycle use from storage:
no current, provisional or enclosing native State belongs in ordinary `D`,
including tuples, ADT wrappers and instantiated generic payloads. Defining header
admission and final independent specialization both check this boundary.
Declared dependency access handles remain ordinary payloads; acquisition and
finish derive permitted local State from their authenticated enclosing resource.
Sealed runtime dependency/destructor operands are not `D`. Earlier State-in-`D`
prototype traces are authority-limited evidence, not admitted language behavior.

A source finish member can retain an owner while its original declared host
destructor consumes it. Generated callback selection therefore retains that
destructor independently of the resource's exact interpretation list; it grants
no extra source call permission. The connected native witness removes source,
image and facts before execution and distinguishes one source retain from one
later host release. The owned-discard variant remains terminal despite that
successful host release. The dependency-free witnesses alone do not establish
retained-child blocking or dependency-order host destruction; the ownership
delivery adds separate access-handle payload and real dependent-native witnesses.

The ownership store keeps flat slots and scalar dependency indices. Metadata,
complete typed views, destructor operands and counter storage are admitted before
native acquisition. A consumed child removes its edges once; a retained child
quarantines its same owner and transitive closure, denies ordinary access and
blocks parent consumption before C. Host destruction preserves dependency order
and makes one attempt. Incomplete destruction protects unresolved native objects
without leaking recursively owned Rust type metadata or releasing their parents.
Lifetime closure membership supplies no additional native operand role.

An admitted pending finish can locally borrow its exact, physically live direct
dependency's State despite quarantine. The source-handler hook checks the
selected original owner, complete State result and active finishing guard before
the unchanged typed-operand check. Ordinary operations remain revoked. The true
three-family native fixture retains Grand, blocks Child and Parent source
consumption, then consumes Grand, Child and Parent in host order. The separate
sibling witness distinguishes pending State borrowing from ordinary access.

One normal-budget phase observation found nine original-template registry passes
of 6,740 work units each before final Core validation. All original forests
passed, but final structural validation exhausted the remaining startup ledger;
preparation work was not that ledger. A private session now retains one complete
registry admission for the same immutable registry and exact source/module
objects. Every template still checks its graph, method evidence, binders, kinds,
rows, lineage and capture obligations; linked final Core authenticates its
registry afresh. Graph-dependent lexical method-owner contexts keep a fresh
registry check. A changed source object, module relation, header or registry
cannot reuse the receipt. Exact/one-short/prefix/fresh-retry tests protect this
boundary, and the unchanged true three-owner fixture now reaches native execution
within the original allowance. No policy limit or stack depth changed.

PR21 carried the human-approved checkpoint-gating delta from the
root workflow and milestone launch template. Existing retained one-branch,
one-checkout/shared-cache, timing and cleanup clauses remain. The linked skills
and support were already adopted from `f961470`; this is policy reconciliation,
not an isolated documentation import or a new runtime authority.

The connected control witnesses distinguish source/Core admission, real generated
native execution and injected transfer/disposal checkpoints. Native traces use
independent owner identities and byte storage, proving inner-before-outer finish,
outer access during inner finish, discarded-body nonexecution and pending-guard
revocation without invented data. At PR20's retained pin, a two-original-library
fixture fit compiler checking but exceeded the unchanged cumulative image
allowance; its passing shared-template native case was a narrower witness, not a
two-library native claim. The Core and image witnesses compare exact continuation
substitutions, output rows and native interpretation order. Image mutation refuses
before native provider selection. Exact/one-short/prefix/fresh-retry tests retain
cumulative
costs; injected source guards dispose iteratively at 32,768 depth on 64 KiB.

Imported original source headers must be inventoried by defining identity, not
spelling. Two namespace imports can both name `Probe`; a spelling map can retain
only one. Canonical family-kind reconstruction uses the complete header inventory,
with charged fallible retention, while original signatures and sealed association
remain independently checked.

Provider association checks exact method/operation names and substituted value
types, with the single associated effect row. Interface order is independent of
operation order. Checked lexical forwarding carries complete Type/Row arguments
through ordinary calls and constrained helpers, final Core and the private image.
Copied binder, operation, operand, effect and resource-owner claims require their
original correspondence; a same-typed application alone supplies no activation
authority.

Expanded source-scope construction must not enlarge the fixed transform frame
used by unrelated operations. The private source-scope rebuild routine retains
the same charged fallible forwarding and copy-map reservations, guarded Type
ownership and independent admission, without adding a heap allocation. The
ordinary-handler exact/one-short/retry/deep-disposal witness keeps its established
64 KiB stack and unchanged depth/work policies.

Retaining passive implementation census facts enlarges owning resolved-module
results. Kind checking and provenance publication run after name resolution in a
separate routine, so their result temporaries do not burden the active source
traversal. The same original-header census, sealing order, budgets and fallible
retention remain in force. The predecessor 256 KiB cleanup witness resolves its
source before evaluator execution; resolution preserves that established bound.

Canonical method spelling retention charges the original UTF-8 byte length
before fallible allocation. Independent ledger fixtures must count their actual
names, including `use`, `first`/`second`, `relate` and `relation`; equal numeric
deltas from different fixtures do not establish shared provenance.

An inner source scope retains immutable defining templates, identity maps and
copying claims. Enclosing control equations can leave its instance continuation
row temporarily unresolved. Partial normalization must preserve the complete
claim; strict finalization resolves its Type/Row payloads and substitutions
together before resume-row replay. A shared descriptor gets a charged private
copy before any instance mutation. Independent admission still rejects altered
or unresolved actuals and changed original forests. Finalization tracks only
newly pending scopes, preserving unrelated programs' work and rollback state.

Selected source-handler entry authenticates the unique live guard, original
owner and exact activation before traversing every typed access position,
including nominal payloads. Ordinary handler selection precedes this check.
Modeled guard/frame tests and real generated-native lifecycle tests establish
different boundaries. At the PR20 pin, source capture/resume and owned discard
retained those guard and selection checks; retained dependencies and quarantine
were subsequent obligations addressed by the current ownership delivery.

The acquired_only delivery authenticates the instantiated nominal report fields
in defining constructor order: body answer first, acquisition error second.
It does not impose an extra report-parameter order, so a concrete-error
`Outcome<T>` and an error-parameterized report share the same role check.
Capture-value analysis must preserve that result shape while retaining finish
as a cleanup obligation; reusing Scope/Completion assembly would fabricate a
completion field. A source consumed-completion error becomes terminal after
native consumption and cannot publish success or retry release. Native retained
outcomes were subsequent CP-0022 obligations at that acquired-only delivery,
addressed by the current ownership profile without changing its terminal
consumed-error rule.

Initialized-byte acquisition projects the original declared source leaf before
native entry, independently of ABI operands and private data. Readiness retains
the checked nonnegative `size_t` extent; infallible recording attaches it only to
the exact non-null unique guard. A zero extent preserves ownership. Missing facts
are refused during canonical foreign resolution, before resource or bridge
admission. Preflight work exhaustion follows the existing effect-work diagnostic
and remains terminal; post-return cleanup does not replay acquisition or release.
The image retains representation and original extent facts separately from the
checked executable resource template. Finite-window control remains a separate
obligation.

The human-approved byte API clarification uses compiler-sealed generic `S` and
the existing `Foreign.Call` result for these two primitives. Original call
correspondence, complete caller and defining Type/Row actuals, borrowed state
lineage and the unique live guard remain separate admission obligations. A
monomorphic State type or direct guard lookup would lose phantom applications
and branch-selected defining context. Immutable templates reconstruct original
TypeApplication/Apply relations; final Core and image restoration independently
check copied specialization and provenance. Capture-value analysis retains strict
callable and operand control edges while giving only the reply an independent
value. Ordinary generic helpers cannot manufacture descriptor permission.

Byte access retains eligibility during acquire, handler and finish before native
consumption. The original guard supplies extent and callbacks; private data does
not grant memory permission. Bounds checking precedes byte inspection and its
magnitude charge. A refusal report affordable without byte-conversion work
distinguishes this order from two simultaneously invalid inputs. Owned
specialization metadata is iteratively disposed before the callback, and complete
report work and fallible cell reservation precede every read or mutation. Existing
integer storage represents every unsigned byte inline, so no integer
representation change or post-read reservation is needed. Work/storage refusal
is terminal, independent conversion refusal is ordinary, and rejected writes do
not mutate memory.

Charged authority scans must complete their traversal before returning a match.
Early success in an unordered registry made fresh image reconstructions consume
different amounts of work, breaking exact/one-short evidence. Completing the same
charged scan preserves admission and gives deterministic costs without raising
policy limits. Pure images may retain the exact passive canonical byte prototypes
and their Type parameter rows; they cannot instantiate or execute byte calls.
General polymorphic image forms remain outside that passive boundary, and complete
retained parameter-row consumption remains an independent Core invariant.

Generated native byte witnesses use actually initialized writable storage and an
independent release identity. They exercise acquire/body/finish borrowing, both
canonical alias branches under distinct phantom Type/Row applications, nested
ordinary overrides, both report codecs and null/zero-extent disposition. Source,
image and facts files are removed before standalone execution. Injected guard,
storage and ledger refusals establish separate pre-callback boundaries; they are
not external-library failures. At PR19, copy windows, dependencies, quarantine
and finite-window control remained later CP-0022 work; byte primitives alone
completed no original issue criterion or library migration. The current ownership
delivery adds the declared-dependency and quarantine profile separately.

A self-consistent image can reconstruct a different valid integer source path;
reconstruction alone does not prove correspondence to a generated call site.
The private executable gate compares its original `EXPECTED_FACTS` before
restoration or binding. Changed initialization paths or representations must
fail that comparison; a missing required byte-initialization fact also fails
structural reconstruction.

DN-0036 supplies reusable guarded scopes, owner arguments and validation, but
Rust-authored manifests/adapters are experimental comparison evidence. They
cannot become the source authoring API. Private replaceable payloads and finite
window contracts are new obligations in CP-0022.

A zero-argument `void` call exposed a nonempty-outcome grammar gap: no output
or owner exists to justify a fact. CP-0022 now permits empty outcome fact lists
with mandatory semantic coverage, accepted on 2026-10-10. Ash still reports
Unit after the call; no native result is read.

ABI preparation must price string comparisons and NUL scans by inspected bytes
before scanning. A single borrowed mapping table decodes each authored ABI
position once, rejects repeated positions and projects each mapped source path
once. Preparation alone has no resolved type or operation authority; binding
must still authenticate the canonical result codec and complete owner arguments.

Imported opaque result errors retain defining identity, kind and provenance,
without exposing hidden constructor bodies. Canonical codec authentication must
use those retained facts rather than requiring source access to the constructor.
Native descriptors follow selected or signature-referenced effect facts through
imports; copying every descriptor from a dependency would introduce authority
without its declaring effect. Module effect copies, canonical registry effects
and the exact operation table retain the same immutable descriptor allocation.

Failure after resolving an earlier effect needs iterative guards around staged
operations and declarations, before their final owner exists. Retained spelling
bytes and origin chains require priced, fallible copying. The registry's existing
exact-ID table supplies duplicate rejection; a second linear scan per effect
adds quadratic preparation without a separate validation obligation.

Independent export-summary admission must authenticate its native operation
table before selected imports can reconstruct local tables. Otherwise a missing
summary entry can be silently recreated from an effect tag. The same charged
effect walk now checks exact table/tag correspondence, retained signatures and
ordered parameter identities/kinds, including facade publication.

Retained native signatures also need exact operation, annotation and binder
provenance. Summary and registry authentication borrow the original spans,
guarded origins and shared annotation arena; equivalent type shapes alone
cannot authorize a substituted defining occurrence.

Foreign declaration setup increased the live debug-build resolver frame enough
to overflow an existing 256 KiB nested-cleanup witness before evaluation.
Separate completed declaration preparation from body resolution so setup
temporaries leave the stack first. The unchanged witness passes without raising
stack or work limits; retained setup fields use existing iterative owners.

Separating reusable compilation from execution adds a containing compilation
timer. The calibration consumer must recognize it without making it another
charged-work owner or requiring it in historical traces. Public Pure and Effect
observer cases now pass their actual logs through the consumer; both retain the
same six work owners, and containing timers must not be summed with child phases.

Ordinary effects and native symbol groups need one source-ordered identity
inventory. Library ranges, retained declaration indices and complete parameter
vectors must follow that inventory together; appending native parameters after
ordinary parameters breaks interleaved declarations. Preparation now uses paid
linear walks and crosschecks each retained library range against declaration order.

An imported opaque nominal can be an ordinary domain leaf without becoming an
ABI operand. Its exact retained nullary `Type` fact authenticates this use without
materializing private constructors. Scalar source-path checks still require `Int`;
unsaturated nominal constructors and resource roles remain inadmissible here.

Source-native execution needs a mandatory exact Core interpreter distinct from
ordinary handler selection. Program binding admission precedes every Ash step;
request admission retains the same canonical symbol allocation and complete
ordered actual vector under the saved lexical instantiations. Row arguments
remain part of identity even when the native ABI projects only Type arguments.
The final linked expression's outward row is empty after that interpretation;
a source `main` may still name the admitted native requirements.

Scalar calls narrow borrowed mathematical integers after charging magnitude
work. Readiness prepays bounded reporting and recording work and reserves the
Returned constructor slot. The consuming return receipt removes callback
capability; the next step records fixed-size raw facts before disposal, result
construction or continuation work can refuse. A focused Machine witness injects
only ledger exhaustion after a valid Rust callback returns, then observes
recording and prepaid reporting before ordinary String work refuses. One call
and a successful fresh activation distinguish no replay from a ban on later calls.
This is injected resource evidence, not a failure from the external library.
Mathematical Integer storage still allocates internally after recording.

Runtime conversion refusal needs the original nullary private error-constructor
role from the combined builtin module. Imported source checking continues to
use only the opaque nominal's retained kind and origin; runtime admission does
not require that constructor to become a public source export.

Generic helpers use implicit ordinary term instantiation. An EffectRow parameter
in a native effect's complete vector is supplied as a row, such as `{| Before}`;
using the bare parameter there does not supply a tagged row argument. Concrete
helper annotations can constrain independent closed instances without dropping
unused row parameters or adding explicit source term type application.

Latent effect arguments must report their authenticated binder uses to the same
scheme-coverage observer as value types. A separate unrestricted observer lost
uses present only in nested row arguments and incorrectly rejected an imported
generic helper. Registry-backed environments also lacked that latent argument
traversal. They now borrow original facts and check encountered latent rows on
demand. An internal ADT assigns nested obligations to the iterative effect queue;
it supplies no validation certificate. This adds the missing paid latent work
without a metadata prepass over Pure types or a copied effect inventory. Runtime
request admission checks the Type-only projection in the complete tag scan,
without a second row walk or an increased allowance.

Native entry construction must lend its Core builder the caller's cumulative
final-elaboration meter. A builder's separate default allowance omitted paid
interpreter payload admission from that caller's ledger. The phase boundary now
restores the builder meter after both success and refusal; exact and one-short
cuts retain the caller's prior charges and fresh retries use a fresh caller.

The product resource header has its own Surface and resolved carriers. They retain
the explicit owned selector, complete Type/Row actuals, private data and lifecycle
codecs, ordered native interpretations and lifecycle patterns. The experimental
header remains a separate comparison carrier. Body-free publication retains the
original header allocation; parsing and a published header grant no executable
resource permission.

Dependency-free owner ABI preparation uses mutually exclusive scalar/acquire/
teardown call variants and tagged owner arguments. Original library member
coordinates and assumption spans survive preparation, restoration and exact
correspondence. Each symbol is normalized once; teardown checks borrow those
prepared facts. Byte owners require an initialized extent; opaque acquisition
need not declare one. An authored initialization fact remains a foreign promise,
not a consequence of its address representation or non-nullness.

Private owner restoration checks flat phase, coordinate, tag and span consistency.
It cannot recheck a source path's leaf type without the original signature; exact
correspondence authenticates the retained path, and canonical source binding
authenticates its leaf type. The executable scalar path explicitly refuses owner,
current-state and address facts. Scalar members of a library containing owners
use that same scalar path; the library's name supplies no ownership permission.

Original resource acquisition, completion and handler forests are checked once
per defining occurrence. A prepared instance owns its selected template, complete
arguments and substitutions through initializer checking into body admission.
This avoids computing those facts again after the initializer. Phase checking
lends the caller's remaining work and restores setup and builder charges on both
success and refusal; it also takes and restores one base context instead of
cloning it for each forest.

Source instance arguments retain the ordinary expected-row qualification before
entering the complete substitution. Independent evidence checking derives the
same preceding equation row; qualifying only its temporary validation copy would
leave retained rigid-row exclusion facts inconsistent with the checked instance.

Each original forest needs its own resolver-binder reservation before generated
binders are allocated. Rewalking the whole module for each reservation introduced
`1 + 3R` inventories for `R` resources, including an unused initial reservation.
Source template preparation now pays for one iterative module inventory and
reuses its immutable identities for each forest's fallible, collision-checked
reservation. Independent final validation remains a separate obligation.

Current bounded execution admits opaque and initialized-byte
owners, both report codecs, complete associated-method forwarding and ordinary
outward capture/resume/owned discard, declared dependencies, retained completion
and quarantine under void or scalar-status owner contracts. Native windows,
privileged lifecycle wrappers, source `given` forwarding and library migrations
remain CP-0022 work. These are
implementation boundaries, not amendments to the broader accepted contract.

A public source resource currently needs a public provider interface. Retaining
an interface declared privately in the same module as a hidden resource-header
dependency is not connected to the shared export closure yet. An imported hidden
interface dependency has a different existing retention route; matching names
cannot substitute for either route.

Constructor-free native state needs its own authenticated nominal category at
publication, import, linking and linked-evidence boundaries. State-only imports
retain the exact original owner declaration and formals, without selecting native
operations.
Resource headers also contribute their provider interface to the existing hidden
signature dependency closure; a facade does not need to export that interface's
spelling. Source resource parameters and the result binder belong to the exact
linked canonical-variable inventory.

Defining experimental registries retain abstract family metadata before their
separate checked provider certificates are attached during linking. Category
coverage at that boundary must first authenticate the original code and defining
export certificate, then count only their exact family identities alongside
source resource and native owner categories. Closed registry validation still
requires its attached certificates, complete canonical formals and linked native
closure. Applying the closed check prematurely rejected existing SQLite, arena
and provider-helper programs before independent Core validation.

A defining registry omits imported nominal dependencies that its closed checking
view retains. An imported opaque category can be reconstructed only in the view
that actually contains it. Final linked and restored Core must still reconstruct
every selected native codec independently; an immutable source receipt does not
replace that consuming check.

Capture projection must check the actual constructor identity before exposing
its payload. Conflating `Finish.Retained(State, E)` with `ConsumedFailure(E)` made
an independent completion error retain native state. Constructor identity changes
must also wake the projection's existing dependency equation.

Ordinary callable state restrictions apply to unused equational definitions as
well as anonymous functions and call occurrences. Independent Core needs the same
restriction, while admitting only the exact synthetic original lifecycle
wrappers. A separate source-resource capture conversion frame also preserves the
existing small-stack witness; its overflow occurred on the first ordinary node,
before any deep traversal.

The existing 256 KiB owned-cleanup witness also reached a larger source-checking
dispatcher frame before the evaluator ran. Source-resource body and completion
branches now pass their existing boxed phase carriers to separate non-inlined
helpers, keeping their local values outside unrelated expression-dispatch calls.
The branch order, guards, allocations and paid work remain the same; the witness
retains its predecessor stack bound.

Owned substitution maps must dispose displaced types iteratively. Temporary
argument and handler buffers transfer their contents through consuming,
infallible owner methods; exposing raw backing moves can leave a later error
path responsible for recursive disposal. The architecture carrier inventory
also covers named aliases introduced for shared checked-code maps and borrowed
Core image views. These repairs preserve traversal charges and fallible reserves.

Product resource instances now install checked lexical forwarding for their
associated methods. Linked evidence authenticates the exact original source
header and complete actuals, and places the fresh identity only in the body
scope. Experimental provider certificates do not grant product authority.
Passive source declarations remain admissible without executing a resource.
Associated methods' exact effectful value types select the existing Effect
carrier even when the ordinary entry has an empty row.

Header input and private data walks must prepay owner-candidate lookup on the
same cumulative validation meter. An ordinary nominal can require inspecting
the entire passive owner table; charging only its type node omits work that
grows with both payload width and owner count. Original and reconstructed
headers use the same admission check and retain the existing work limit.

The accepted pure scalar preflight functions reuse `Foreign.Call<Int>` and
preserve the input mathematical integer on success. Their canonical immutable
facts travel on the existing selected-global publication route; a facade retains
the hidden `Call` constructor family needed for independent checking without
adding source name routes or exposing `ConversionError` constructors. Shared
image annotation arenas require checking the five reachable provenance nodes
from their root, rather than requiring a five-node whole arena. Lifecycle flow
tracks these pure checks as identity-independent results; it does not enumerate
both ordinary result variants for every independent field check.
Original template structural validation borrows only those authenticated scalar
global facts; final executable graphs still require ordinary binder closure.

The full workspace gate exposed an unnecessary second scan of every published
global while collecting scalar result-codec dependencies. It charged ordinary
modules with no scalar facts and broke two exact freeze-budget regressions.
The existing paid publication walk now stages only actual codec owner IDs with
fallible storage. The later constructor closure consumes those IDs in source
order, preserving original facts, hidden-family authentication and existing
seed ordering. Ordinary globals incur no additional charge or allocation;
neither work limits nor regression expectations changed.

Matching an unknown scalar result beside current state exposed a skipped-arm
owner-flow defect: the first possible arm could hide a later `Consumed` report
without teardown. Symbolic patterns now distinguish possible from definite
matches. Only a definite match stops the arm walk; the public pipeline rejects
the mixed scalar/state counterexample without enumerating scalar variant products.

Before checked constant publication, boundary evidence obtained negative integers
through owner-free scalar replies and larger values through ordinary arithmetic
on admitted i64 image payloads. Checked foreign literals now supply signed values
and the complete u64 range directly, while ordinary negative-literal expression
syntax and general arbitrary-precision image literals remain outside this slice.

A complete product SQLite Source observation exceeded the earlier `200S`
estimate while preserving the canonical source census and cumulative meter.
The constraint case requires 8,510,624 units for 39,033 bytes, including census;
its Source-only diagnostic stopped before linking, Final/Core or native work.
After independent accounting review, the project lead selected `300S` under the
user's delegated judgment, using the existing 25% reserve rule and conservative
rounding. [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md)
governs this Source-only coefficient revision; [DN-0050](../design/DN-0050-native-program-gas-estimates.md)
records the fit and limitations. No predicate, witness, cumulative carry,
other allowance, depth or stack policy changes. The diagnostic does not close
normal caller, retained verification or checkpoint obligations.

The subsequent full SQLite run passed 30 cases and exhausted four required
cases at Source `300S` / Final `161S`. Finite phase measurements completed all
four unchanged source closures. Persistence used 28,158,349 Source units and
26,809,274 Final units for 44,512 canonical bytes. Its separate builder rewrite
meter first refused at the fixed implementation default, then completed at
510,782 units under the explicitly bounded diagnostic. No Source-credit loan,
reset or duplicate-debit repair was justified.

After independent measurement/accounting review, the project lead adopted
Source `800S`, Final `800S` and separate compiler-arena rewrite `16S` under the
user's delegated judgment. The existing paid canonical census returns S
alongside its budget; checked multiplication funds each empty compiler arena
once, and every later rewrite retains that arena's cumulative spending. Fresh
arenas inherit capacity only. Generic, standalone and private-image defaults,
other limits, witnesses and semantic checks remain unchanged.
[AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md)
holds the policy and [DN-0050](../design/DN-0050-native-program-gas-estimates.md)
records phase-separated fitting evidence and its limitations. These diagnostics
stopped before independent Core and native execution. Normal four-case and
whole-caller verification, current quality, actual-head review and retained
acceptance remain pending on [PR #34](https://github.com/dikini/ash-lang/pull/34).

The subsequent normal run completed Source, Final and independent Core in all
four cases, then exhausted the existing `51P` native-preparation meter. An exact
first-refusal observation confirmed the same carried census/encoder owner;
there was no demonstrated reset, separate fixed encoding meter or duplicated
debit to repair. One finite `204P` diagnostic completed all four preparations
and stopped before generated-host building or execution.

After independent accounting and fitting review, the project lead selected
preparation `125P` under the user's delegated judgment. The largest observation
used 4,984,019 units for P = 50,905, including 44,510 source bytes and 6,395 main
nodes. The fixture's normal fresh database-path substitution is recorded, rather
than calling it byte-identical to the earlier 44,512-byte input. A 25% fitting
reserve requires coefficient 123; 125 is the conservative rounded choice. Only
this coefficient and exact expected tests change; the same paid sizing and
cumulative preparation meter, every other allowance and every semantic/native
check remain intact. Normal full SQLite/native/caller checks, current quality,
final-head review and retained acceptance still require their actual results.

## Deviations

None authorized. Return concrete semantic gaps to CP-0022 instead of resolving
them locally. Keep excluded features outside this task.
