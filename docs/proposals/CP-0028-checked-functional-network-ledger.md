# CP-0028: Checked functional network ledger

- ID: `CP-0028`
- Status: accepted
- Related: [CP-0027](CP-0027-pinned-workers-and-copied-channels.md), [AD-0017](../decisions/AD-0017-pinned-worker-host-and-transport.md), [DN-0056](../design/DN-0056-scoped-continuation-retention-and-library-scheduling.md), [DN-0058](../design/DN-0058-pinned-worker-host-and-channel.md), [TASK-0058](../tasks/TASK-0058-pinned-worker-network.md), [N3 proof assignment](../design/retained-control/network-ledger-proof-assignment.md), [issue #78](https://github.com/dikini/ash-lang/issues/78), [issue #79](https://github.com/dikini/ash-lang/issues/79)

> This accepted transition is not current Ash. Acceptance does not establish a
> proof or product implementation.

## Current behavior

[Recursive data](../../spec/static-semantics.md#recursive-block-groups) can
contain cycles, so a recursive list type does not establish finite induction.
[Retained-control checking](../../spec/static-semantics.md#scoped-retained-control)
checks actual local root completion and uses an ascending least fixed point for
recursive normal returns. An intercepted or stale Boolean grants no release
fact. The [linked validation boundary](../../spec/elaboration.md#validation-boundary)
reconstructs control and dependencies from actual Core. It does not currently
certify an ordinary functional network ledger or a general source assertion.

[CP-0027](CP-0027-pinned-workers-and-copied-channels.md) is the accepted N1
transition, not current language truth. Its sealed channel operation
establishes control-envelope kind and sending side, not the meaning of its
bytes or completion of a computation. Its designated ordinary Ash driver path
requires the separate N3/N4 checks. [DN-0056](../design/DN-0056-scoped-continuation-retention-and-library-scheduling.md#minimal-library-core-ledger-and-inductive-invariant)
is informative paper evidence, not a checked theorem.

## Proposed behavior

### Ledger and invariant

A checked network uses ordinary private Ash values and linked functions. A
ledger has a nonnegative next serial, an ordered finite list of records, and an
ordered finite list of pending output envelopes. A record has a unique nominal
identifier, an optional parent address, an Open or Closed production phase,
and an ordered finite list of child entries. Each child entry contains an
identifier and destination. A root record has no parent; every non-root record
has one. The root remains observable and cannot retire. IDs are a distinguished
Root or `WorkId(allocator, serial)`, with distinct fixed allocator labels for
workers within one activation. Each allocator begins at zero and issues its
current serial then increments by one using Ash mathematical integers. It never
resets or reuses a serial, including after retirement. Network activation and
channel identities distinguish activations; old copied IDs confer no authority
in another activation.

The representation invariant includes finite acyclic record, child and output
lists, unique record IDs and child IDs within each list, immutable parent and
child destination fields for retained entries, and non-reused serials. It holds
initially with only an open root and empty child and output lists; other workers
start with no records or outputs. Only checked constructors and transitions
produce authoritative ledger state. No application-supplied list, cyclic
value, arbitrary copy, source assertion or matching type establishes the
invariant. The private boundary must be reconstructed through actual linked
constructors, calls, captures, selected evidence and every reachable path;
privacy by itself does not establish current state.

A registration for an absent or closed parent returns the same ledger and
rejection. For an open parent it allocates a fresh ID, increments the serial,
inserts exactly one `(ID, destination)` child and queues exactly one matching
work envelope containing that ID, the actual parent address and payload. All
other whole entries and their order are preserved. The returned successor
contains both reservation and output before dispatch or publication. Receipt
installs the corresponding local record before dispatch. One accepted dispatch
per work envelope is required; redelivery requires a separately checked
deduplication contract.

Closure changes only the selected open record to Closed. Its caller must
establish the relevant actual local completion before a non-root is closed;
root closure must account for earlier admissions and all independent producer
authority. No Closed record reopens or accepts a direct child. Retirement of a
non-root requires Closed and an actually empty child list, removes the whole
record and queues its corresponding acknowledgement in the same successor.
Other cases leave state unchanged. Processing an acknowledgement removes the
matching child only when its parent, child ID and recorded destination match
the authenticated sending peer. Unknown parents, wrong peers, unknown children
and duplicate acknowledgements leave the state unchanged. No such no-op is
allowed to remove or modify a different entry. The matching deletion preserves
all remaining whole entries and their order.

A current-state fact relates a particular activation and owner to the actual
ledger value at a control point. Checked initialization introduces it. A
checked transition's *actual returned successor* replaces it, and a possible
state-changing transition, unknown call, reentry, capture or join invalidates
any observation or authority tied to the old value unless the analysis proves
the relevant relationship survives. A proved no-op may carry equality to the
successor; a copy alone does not. All later updates, dispatch, publication and
observations must follow that successor. On suspension, exclusive update
continuation ownership and its state relation must survive until restoration;
a callback cannot reenter against an old input. These are checked control
facts, not a linear type or runtime version counter.

### Restricted plans and checking

An untrusted plan nominates a claim schema, actual target binder and
instantiation, argument and result positions, nominal list, entry, ID and
result constructors, key projections, induction argument, equality and other
helper dependencies. Candidate discovery can use metadata or structural
analysis; neither candidate nor source spelling grants a fact. The producer of
metadata is not trusted. Plans are validation metadata, not source proof syntax,
executable primitives or runtime ledger assertions. A plan must resolve
uniquely within the current linked image. The validator checks actual
identities, types, scope, selected implementations, all bodies, captures,
arguments and returned expressions; missing, ambiguous or inconsistent binding
rejects. Imported interface summaries and old certificates do not substitute
for linked bodies.

The initial checker supports the following finite, syntax-directed fragment,
with bounded normalization of transparent bindings, projections and nominal
constructor cases. It follows actual call-by-value control and every reachable
match and equality arm, including all normal returns and default arms. It
tracks path-local equalities and disequalities, original whole-entry binders,
finite/unique lists, membership and absence, exact sequence construction,
result tags and instantiated helper postconditions. A join retains only facts
valid on every incoming path. An unknown value or call is conservative; it
cannot invent a fact. Branches may be excluded only by contradictory checked
facts under actual matching semantics. The checker rejects an unsupported
construct when the needed derivation cannot be reconstructed.

Data helpers may use constructor construction and matching, projections,
transparent bindings, verified equality, conditionals, canonical integer
addition and calls to separately checked helpers. Persistent construction and
potentially large arithmetic can lower to allocation operations in Effect
Core; the checker does not erase those operations or call them pure because an
outward row is empty. The initial fragment admits them only with the actual
canonical host default allocation interpreter selected at every such request.
The validator reconstructs selection and all intervening control and rejects a
source handler, local provider, unknown callback or captured selection that
could intercept or reenter the checked computation. The modeled interpreter
must preserve existing input values and protocol state, allocate fresh valid
storage for the requested value, and return to the same continuation exactly
once on success; refusal or internal failure yields no normal return. Prove
this restricted correspondence against the actual allocation path before
publishing any dependent fact. Unknown selection or an unproved allocation
callback rejects. Calls and strict operand evaluation must themselves be in
the fragment; ordinary allocations remain subject to their existing work and
resource limits. A helper's outward effect row alone never establishes this
condition.

Equality for ID constructors compares nominal constructor identity, allocator
identity and mathematical integer serial; verified equality must terminate on admitted finite inputs when its required
allocation succeeds, and every normal return is true exactly for equal IDs.
Allocation refusal yields no comparison fact.
Arbitrary Boolean functions do not imply comparison facts. The arithmetic
rule recognizes the actual canonical mathematical integer operation `next + 1`
with operand order and result checked, and derives the strict successor only
from a nonnegative counter. Checked initialization establishes zero and the
transition frame forbids resets or other writes; allocator identities are
unique in the activation. Allocation failure gives no successor. A claimed
freshness fact additionally depends on these initialization and every-path
preservation checks, including all writes to the actual current state. No
other arithmetic follows by naming an expression increment. Ordinary helper
dependencies form an acyclic graph; an inductive self-call is the sole recursive
hypothesis for that claim. Calls to unverified helpers and mutually circular
claim dependencies reject.

The `RemoveById` schema binds a function `f(q, xs)` to its actual list, key,
result and status identities. Its preconditions are `Finite(xs)` and
`UniqueKeys(xs)`. For every normal return `(ys, status)`, `ys` equals the
ordered sequence `erase(q, xs)`: remove the first matching whole entry, or
return the whole sequence unchanged if absent. `Found` holds exactly when a
key equals `q`; `Missing` holds exactly when no key equals `q`. The result is
finite and unique. Sequence equality preserves the original whole entry values
and order, including parent, phase, children and destination, without requiring
a decidable equality for arbitrary payloads. The checked comparison must use
the bound key projection. All schema premises must be established at each use.

For the empty case, the actual return must be empty and Missing. For a matching
head, verified equality plus uniqueness gives absence in the tail; the actual
return must be that tail and Found. For a nonmatching head, decomposition gives
finite and unique tail and head-key absence in it. The recursive hypothesis is
available only for the same target applied to that actual proper constructor
tail, with all other actual arguments and claim instantiations checked and all
premises established. Its returned sequence is reconstructed under the
original head with the actual returned status. A tail binder without finite
input is not well-founded; the whole input, an unrelated tail or a recursive
call with changed unproved arguments cannot use the hypothesis. Each reachable
return must establish every clause. The checker can accept other code only if
its supported derivation proves the same complete claim.

Checked lookup, insertion and update summaries similarly establish exact
result cases and frames over finite unique lists. The transition checker
reconstructs actual initialization and each branch of registration, closure,
retirement and acknowledgement against the invariant and the operations above.
It checks all actual returned fields and corresponding envelope values; a
constructor merely occurring in a body is insufficient. The current-state
check attaches facts to actual returned values and control paths, including
no-op branches, and rejects stale or reentrant use. These checks supply data
and state-flow facts only, not completion or network release permission.

Every fact-producing schema has a soundness obligation, not just removal.
For any well-formed actual linked definition and authenticated instantiation,
if the checker accepts a schema and its premises hold on actual runtime
inputs, every normal evaluation return satisfies that schema's exact stated
relationship on the actual returned values. This family covers equality,
lookup, insertion, update and removal; initialization; registration, closure,
retirement and acknowledgement; and current-state transfer and invalidation.
The transition instances establish the entire local invariant and all frame,
status, field, counter and envelope clauses above, not only an ideal model's
preservation theorem. Each proof must justify actual branch selection, binding,
substitution, returned fields and envelope operands, verified helper premises,
and the transitive purity and acyclic dependency conditions. For state-flow
facts the theorem ranges over actual control steps and successor returns as well
as data evaluation; it must show conservative joins, captures, reentry,
unknown calls and invalidation. The proof assignment defines the required
modeled evaluation and correspondence to linked Core. A helper theorem for an
ideal function is not acceptance-to-evaluation soundness for a checker.

### Control and transport boundary

The N3 proof describes network coverage conditionally: reservation precedes
publication; a pending, accepted or delivered work envelope retains its parent
dependency; receipt and dispatch transfer responsibility; a closed childless
retirement queues an acknowledgement while its parent dependency remains; a
matching authentic acknowledgement removes only that dependency. Actual
completion, exclusion of unregistered producers and confinement of raw
publication are explicit premises, not conclusions of list induction. Under
those premises and closed root admission, current root Closed with no children
implies stable application quiescence. It does not establish endpoint or
backing settlement, scheduling progress or termination.

Control-envelope codec correspondence is an explicit premise of the N3
network theorem, not a fact this proposal's initial checker can issue. A later
accepted codec extension must bind actual encoder and decoder bodies and their
helper closure, define the supported Bytes and integer construction/parsing
rules and prove acceptance soundness. Its contract must establish exact
roundtrip of every admitted nominal ID and address, complete framing and
consumption, and that every accepted decoding corresponds to the intended
encoded message. Malformed, truncated, ambiguous, trailing or unrepresentable
input and work or storage refusal must supply no decoded protocol fact. It must
state normal-return and totality limits, and independently revalidate imports
and transforms. A separately asserted theorem, matching signature or copied
plan is insufficient. Until that extension is accepted and checked, no
codec-dependent completion or release permission is granted. The CP-0027
interpreter supplies the actual Control tag and peer from the polarized
channel; application bytes, source-constructed result constructors,
interception or a self-reported peer cannot establish these facts. Even a
checked codec cannot establish that an acknowledgement was honestly emitted.

### Source access and linked driver designation

This accepted transition refines CP-0027 admission as follows. The builtin
module publicly exports the sealed `send_control` operation under normal source
module visibility, so an ordinary separately authored or imported Ash driver
can resolve and invoke it. This export grants no permission to execute a
linked program containing an unsafe use. Its intrinsic identity and injected
`Worker<N>` determine the actual operation and activation; spelling, alias,
module privacy and a source annotation grant no driver authority. The raw
receive operation and its result remain ordinarily visible as specified by
CP-0027.

For a network whose program uses `send_control` or asks for an N4
protocol-based completion fact, an untrusted validation plan nominates the
actual worker entry, driver roots and the particular registration, transition,
codec, receive/dispatch and emission definitions for each side. Those roots
must be reached from the actual entry for that activation, with a uniquely
resolved linked binder and instantiation. The plan is a candidate description,
not an authorization: the validator reconstructs their bodies and every
reachable direct or indirect caller, callee, closure capture, returned function,
selected implementation and initializer, including imports and reexports.
The full control/value closure associates each possible operation occurrence
with the actual activation and driver control path; unknown targets, escapes or
unresolved aliases that could reach a protected operation fail admission. It
cannot omit an arm, trust a same-typed callback or infer confinement from a
function name. Source can pass messages and identifiers to application code,
but cannot pass a worker alias or callable that enables an unchecked raw
endpoint operation. Each possible use of those values is traced, including
retained or resumed control; duplicate references do not duplicate authority.

The validator admits a control send only at an actual occurrence whose
reachable path satisfies the N4 emission rule: it must consume an output from
the current checked successor, and the actual envelope and codec must match a
permitted transition and completion premise. Every raw receive and its
Control result must be consumed by the checked driver; application callbacks
receive only driver-decoded application messages, never the raw endpoint or a
Control case. On such a network all raw application sends must also follow the
checked driver and its reservation/publication ordering. A direct application
call, forged result, untracked capability escape, or an unknown possible use
rejects the linked program before execution. The same ordinary function can
serve both protocol and application roles only when all its reachable uses
satisfy these checks; nomination cannot turn an unsafe caller into a driver.
No source-level access control or compiler-injected proof capability is needed.
A one-way N2 program that uses no control send and requests no N4 completion
fact keeps CP-0027's ordinary transport behavior, including application sends
and receives. Before N4's full rule is implemented, control-send programs
cannot be admitted on the strength of this nomination alone.

N4 must compose these data and current-state facts with actual completion,
private emission, driver and producer control, codec correspondence and N1
transport. It must inspect actual transitive callers, selected evidence and
captures, confine raw control and application publication to the checked driver,
and reject forging, stale emptiness, obsolete state, unregistered dispatch and
envelope confusion. Local completion includes actual handler suffixes,
retained control and cleanup, not a wrapper's suspension return or a flag.
The N3 hook carries checked identity, input/output and premises to that analysis;
it grants no standalone release. N4 must independently revalidate this
composition at each linked boundary, including imports and transforms.

### Revalidation and limits

After ordinary Core validation, reconstruct claims against the current linked
body and dependencies before any consumer uses them. Renaming or simplification
must replay the derivation; inlining and specialization must instantiate or
regenerate it; changed representation, equality, codec or algorithm requires a
new checked derivation. An unsupported transformation must preserve a
checkable form or reject before execution. Neither an equivalence assertion nor
old node IDs, source provenance or a same-typed substitute preserve a claim.
All discovery, normalization, path exploration, instantiation, comparisons,
replay and retained facts charge the existing cumulative validator work budget
before proportional work or allocation. Exhaustion rejects the check and
publishes no partial claim, current-state fact or release permission; retry uses
only the remaining applicable budget, not a fresh hidden proof allowance.

## Semantic delta

Add independently reconstructed restricted data and state-flow facts for the
ordinary linked protocol, plus their conditional composition interface. No
existing ordinary list acquires a finiteness guarantee. No native transport,
source assertion or unchecked metadata acquires completion authority.

## Affected specification areas

Update [static semantics](../../spec/static-semantics.md#scoped-retained-control)
for admission, state flow and the N4 use of these facts;
[elaboration and validation](../../spec/elaboration.md#validation-boundary) for
plan binding, checking, budgets and revalidation; and
[dynamic semantics](../../spec/dynamic-semantics.md#effect-handlers-and-completion)
where needed to state correspondence with actual evaluation and completion.
CP-0027's future integrated network sections also require the codec and driver
boundary above. Add no specification claim before the implementation and its
required evidence are retained.

## Resulting specification truth

A successfully validated linked program may use only claims reconstructed for
its actual bodies, finite inputs and established premises. Accepted removal
preserves ordered whole entries and reports membership exactly; checked ledger
transitions preserve the stated local invariant, freshness and successor flow.
Network quiescence or release requires the separately checked control and
transport premises. A failed or exhausted check grants no permission.

## Interactions

The model uses ordinary duplicable values and mathematical integers; it does not
change recursive-data or ownership rules. N1's raw endpoint and sealed control
operation authenticate origin, not completion. N2's host and channel proof
must establish its stated transport premises. Existing M3 actual root and
suffix completion remains necessary. N4 supplies the protocol composition;
N5 separately establishes shutdown, endpoint and backing settlement. Native
failure and uncertain acceptance retain CP-0027's failure obligations.

## Non-goals

No opaque builtin ledger, trusted runtime completion assertion, general source
proof language, arbitrary invariant discovery, unrestricted induction,
arbitrary program-equivalence checker, worker recovery, liveness, fairness,
deadlock freedom, or native memory-safety proof is introduced. The checker is
not tied to a particular application's function names. Valid programs outside
this restricted fragment may be rejected.

## Required evidence

The [bounded assignment](../design/retained-control/network-ledger-proof-assignment.md)
sets the formal theorem boundaries, correspondence and adversarial cases.
The contract and proof assignment passed independent review at
`94c0be0375d19f8e60900d5d77be2f5caa746eb0`; that review establishes adoption
readiness, not a proof or product gate. Before N3's gate, mechanize the full
finite ledger and restricted checker soundness, map each modeled rule to actual linked Core and
implementation, and review the proofs and correspondence. Exercise positive,
negative, import, transform, stale-state, dependency and exact/short budget
cases against actual linked definitions. The later codec extension must supply
its own actual-definition and malformed-input cases before N4 uses it. Record source and configuration
pins, commands, assumptions and limitations. A proof of one removal function or
a standalone model does not prove the checker or the implementation. N-proof
and later N4/N5 integrated gates remain separate under TASK-0058.
