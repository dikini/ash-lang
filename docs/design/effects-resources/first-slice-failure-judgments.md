# First Slice: Failure and the No-Error Judgment

This record addresses the failure gap in the [first-slice rule status](first-slice-rule-resolution.md).
It defines what a proposed type-system judgment must establish for the
[DN-0060 correctness target](../DN-0060-typed-data-and-control-roadmap.md#program-checking-and-correctness).
The admission direction below is agreed for this slice. This record does not
change the [current specification](../../../spec/README.md), introduce a new
failure mechanism, or claim a completed proof of the system.

## The conflict in the current rules

The target is that a successfully checked program runs without an execution
error, under its stated assumptions and barring external events that violate
them. It does not require termination or guarantee the intended result. A
typed failure represented as an ordinary result is different from a terminal
runtime failure.

Current [cell acquisition](../../../spec/dynamic-semantics.md#scoped-cell-execution)
can fail internally before publishing an owner. Current
[discard preparation](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
can fail before consuming the capability; later closing can fail after effects
have occurred and without finishing other actions. Current
[observation](../../../spec/dynamic-semantics.md#observation) includes
capacity exhaustion and invalid control among internal runtime failures. These
are specified outcomes, not facts that the existing type system has already
proved impossible. Internal failure cannot simply be relabelled an external
event or divergence.

The existing [cleanup-capacity fixture](../../../src/eval/machine.rs#L10121)
gives a concrete distinction. It builds and validates a program with 24 nested
cleanup scopes. With a test-configured capacity of 24, execution returns; with
capacity 23, it reports an internal capacity failure. This demonstrates the
current behavior under those test configurations, not a claim that the program
fails under the default capacity. The fixture was inspected, not run here.
The same checked control and cleanup types do not by themselves distinguish
the two test capacities.

## A reusable failure cover

A certified behavior contract must cover relevant failure possibilities as
well as returns, requests and non-return. Write `error_case(B, phi, f)` for a
covered possibility that execution of the certified behavior `B` reaches the
internal failure event `f` under correlated condition `phi(w0, wf, z)`.
`w0` is the entry world, `wf` is the failure observation and `z` holds
case-local witnesses. The observation is an actual failure world when one
exists, or the no-post-state marker defined below. The condition conservatively
relates those observations, actual activations and owner states. It does not
assert that every represented path occurs. Entry facts are historical facts
about `w0`; only established stable facts and postconditions describe an
actual `wf` state. A may-case does not assert that `f`
occurs. A missing case or
summary is not evidence that it cannot occur. Calls and other opaque boundaries
must supply their own established behavior and failure facts or an explicit
obligation; this slice does not inspect their implementations.

`covers_failures(B, Cases)` means the established contract soundly covers
every in-scope internal failure event along every finite execution prefix under
its stated assumptions. A recursive or unknown contract must be covered by a
valid recursive or conservative case, not assumed empty. This is a semantic
requirement on the certificate's producer and the system's rules; the compiler
does not run an execution or separately prove the system sound for each use.

For the intended no-error result, the failure universe also has to cover
implementation-level terminal outcomes relevant to that result, including an
in-slice host panic or abort where an operation such as an infallible
allocation does not return a `RuntimeFailure`. The same applies during
internal disposal. The correspondence to the operational semantics must
identify which such outcomes are admitted by its stated external assumptions
and which are internal failures to exclude. A missing host contract is not an
empty failure cover and does not itself classify a failure as external.

An abort need not produce a final machine state. In those cases `wf` is a
distinguished no-post-state observation rather than an invented state; `phi`
retains the same reached pre-operation state and relevant witnesses when
established, or conservatively leaves them unknown. Recoverable failures can
still use their actual failure state. Neither representation assumes that a
failed operation rolled back. A producer can instead establish that the host
outcome is impossible under a stated, applicable platform contract; the
contract and its scope must then remain among the judgment's assumptions or
established facts. This extends the candidate coverage requirement; it does
not claim that the current source semantics specifies host aborts as ordinary
Ash error values.

### Introduce and compose failure cases

The producer of a primitive transition's contract must describe its failure
alternatives at the point where they can occur. A failure case relates the
state at that point to the same entry and preceding behavior as the transition;
it does not assume the entry state is still current. A primitive's case table
is part of the rules justified against its operational semantics, once for the
system. Checking a particular composition instantiates that table and uses
the already certified behavior of its operands and context.

For a finite primitive `p`, let `reach_p(w0, s, z)` be its established entry
case and let its justified table contain guarded internal-failure alternatives
`(g_i(s, z), f_i)`. The table must cover every internal failure from that
step, including failures after a state change; its success alternatives must
state the corresponding post-state. A conservative alternative may include
several causes, but an unspecified alternative remains a possible failure.

```sequent
F-Primitive-Cases :=
  GAMMA; L, entry |- reach_p is a covering entry case for primitive p
  GAMMA; L |- the admitted table for p covers every internal failure of p
  Cases = {(exists s. reach_p(w0, s, z) and g_i(s, z) and wf = failure_observation_i(s, z), f_i) | i in table(p)}
  ===>
  GAMMA; L, entry |- covers_failures(p, Cases)
```

The displayed equation is schematic: a table may give a relation rather than
one function `failure_observation_i`, and may retain additional witnesses.
Its observation may be an actual state or the no-post-state marker; the
reached state `s` remains correlated with either one. Its
coverage premise is established for the rule and operation, not guessed from
a missing row or obtained by replaying a certified operand. If a table or
entry contract is incomplete, retain a guarded unknown-failure case; it cannot
be eliminated merely because its cause is unknown. An excluded construct
supplies its own certified failure interface or an explicit obligation.

For a new sequencing composition, let `C_e` cover the initializer's failures,
`C_s(x, s, d)` cover the already certified remainder under its conditional
entry, and `C_frame` cover the new frame and its preparation. Let
`return_e(w0, x, s, d, z)` range over the initializer's certified, correlated
normal-return cases. Then the composed initial-failure alternatives are the
union of `C_e`, `C_frame`, and the alternatives from `C_s` conjoined with
`return_e` for the same value, state and dependencies. Requests and their
residuals retain the pending frame; they do not enter the remainder until an
actual normal return. Non-return contributes no remainder case. A recursive
or unknown constituent uses its established recursive or conservative cover.

An initial failure may start internal disposal, which can itself fail. A
certified disposal contract must cover its possible later failures and final
observations under that same initial failure and the state at which disposal
starts. Combine those cases with the initial alternatives; do not assume that
disposal succeeds or repeats a source cleanup. This applies to primitive and
composition failures alike. If that contract is unavailable, the disposal
failure remains an obligation. This construction supplies the partition needed
by `J-No-Error-Binding`; it checks the new interface and reuses both operand
covers, without inspecting either operand again.

#### Project outcome covers from a certified behavior

The sequencing rule below needs complete normal-return and failure covers.
Those covers can be retained when a behavior certificate is produced; they
must not be reconstructed by checking its subject again. They cannot be
obtained by collecting only the immediately visible `return` and `failure`
cases: a request may lead to either outcome after an admissible reply, an
outside interaction may have its own failures, and an unknown may contain
either outcome.

For one established behavior `B` and its stated entry and surrounding
contracts, let `Project(B, R, F)` be the following general, guarded outcome
composition. A covered normal return contributes its same value, world,
dependencies, guard and witnesses to `R`. An internal failure contributes
its origin and all applicable later disposal-failure observations to `F`,
including a no-post-state observation where appropriate. For a request, the
established request, outside and reply interfaces contribute their applicable
failure cases; each admitted reply uses the projection of its correlated
residual under the actual reply and post-reply context. Abandoned, nonreturning
and unknown alternatives retain their own applicable covers. In particular,
an unknown alternative needs a conservative normal-return and failure cover
unless its established interface excludes those outcomes; an unclassified
`nonreturn` case is not by itself evidence that failure is impossible.

```sequent
F-Project-Behavior-Outcomes :=
  GAMMA; L, entry |- certified(subject, B) with complete guarded behavior coverage [O_B]
  each covered immediate case supplies the applicable return and failure projections above, with the same subject, guard, witnesses and obligations
  each covered request, outside interaction and admissible reply has a fitted projection for the same context and residual, or a conservative projected unknown
  Project(B, R, F) combines those projections and binds all local case and intermediate-world witnesses at their original scopes
  the projection evidence is non-circular and covers every admitted finite prefix, including any recursive or unbounded residual family
  O_project retains O_B and every undischarged projection, fit and outside-contract obligation under its original guard
  ===>
  GAMMA; L, entry |- subject has complete normal-return cover R and failure cover F [O_project]
```

This is a rule for the certificate's producer or a new composition's case
interface, not a second analysis of the certified program. It may reuse
already certified projections for residuals and outside boundaries. A future
multishot contract must account for every admitted residual entry and its
actual authority and state; the projection neither grants duplication nor
assumes a single reply or entry. For recursive or unbounded interfaces the
finite-prefix coverage requires separately justified inductive or guarded
evidence, not a circular assertion of this conclusion. If that evidence, an
outside fit, or a projected unknown cannot be established, retain the
scoped obligation; neither an empty cover nor closed no-error follows.

For an alternative, the shared
[`J-Alternative-Join`](first-slice-judgment-requirements.md#join-guarded-alternatives)
constructs the guarded behavior, including the selector, entered branches,
authority dispositions and new interface cases. This projection produces
its failure cover under those same guards; `J-No-Internal-Error` eliminates
a covered failure only when its same-case guard is proved impossible.
`J-No-Error-Constructor` can instead reuse fitted child no-error certificates
and check the new failures. Unknown, outside and
disposal cases remain covered or conditional. The required completeness and
projection evidence is still a design gap in the
[rule ledger](first-slice-rule-resolution.md#design-and-implementation-gap-ledger),
not an extra verification of the selector or its branches.

#### Compose failure covers in sequence

The following shared rule constructs a failure cover for a new sequential
composition of arbitrary certified behaviors. `B_1` is entered first;
`B_2(beta)` is a single conditional certificate for the later behavior.
`R_1(w0,s1,z1)` is a complete cover of normal returns from `B_1`, including
returns after any admitted request/reply interactions. It retains the actual
result, dependencies and state in its witnesses. `bridge_ok(s1,z1,s2,beta,zb)`
is the new composition's successful transition from that same `s1` and `z1`
to the later entry, including the actual result, dependency, ownership and
context mapping. It does not assert that the first
behavior returns or that the bridge succeeds.

`F_1` and `F_2(beta)` are the previously certified failure covers, under
their respective entry assumptions and scoped obligations. `F_new` covers failures newly introduced
by the composition at their actual phases, including bridge preparation and
any applicable disposal after a child or new failure. It is indexed by the
same outer entry and covers any such phase reached before or after the first
normal return. Each case's `wf` is its actual failure observation or the
no-post-state marker; it is never used as a later entry state.

```sequent
F-Sequential-Composition :=
  GAMMA; L, entry |- B_1 has complete failure cover F_1 and complete normal-return cover R_1 with obligations O_1
  GAMMA_2; L_2, psi_2(beta) |- B_2(beta) has complete failure cover F_2(beta) with obligations O_2(beta)
  for each covered normal return and successful bridge, the correlated result, state and context establish the same beta and applicable GAMMA_2, L_2 and psi_2(beta) assumptions, or retain them as obligations
  every admitted request, reply and residual needed to reach either phase fits its own certified assumptions, or remains a covered obligation
  GAMMA; L, entry |- F_new covers every failure of the new interface and its applicable disposal at the actual reached phases
  F_later contains each F_2 case guarded by exists s1, s2, z1, zb, beta. R_1(w0,s1,z1) and bridge_ok(s1,z1,s2,beta,zb) and the same case's F_2 guard from s2 to wf
  the established sequencing interface covers every failure by F_1, F_new or F_later, including applicable outside behavior
  F_seq = F_1 union F_new union F_later
  O_seq retains O_1, new and outside obligations, and O_2 and entry-fit obligations under their same scoped return and successful-bridge guards
  ===>
  GAMMA; L, entry |- the new sequential composition has complete failure cover F_seq with obligations O_seq
```

The guards in `F_later` retain the same first result and post-state, the
successful bridge and the later failure observation. A failure or non-return
before that bridge contributes no later entry. An outward request may be
resumed, abandoned or fail: the relevant certified request/residual and
outside contracts must cover those alternatives. A no-post-state failure does
not manufacture a retry or rollback. The sets may overlap; coverage, not a
disjoint partition, is required.

This rule consumes the constituents' covers and checks only the new bridge,
case relationships and any assumptions required at their actual entries.
Unknown covers and unproved fits remain obligations, not empty alternatives.
The conclusion is conditional on `O_seq`; its case witnesses do not become
free at the enclosing boundary. A closed no-error use must discharge every
applicable obligation.
For recursive or unbounded residual families, complete coverage needs the
separate justified finite-prefix evidence described under
[`J-No-Internal-Error`](#disposal-state-and-final-observation). This is a
candidate general inference rule for any in-slice operation or boundary
contract, not another traversal or a specialized checker.

The following table identifies the in-slice transitions that must introduce
their own cases. Operand, clause, action and outside-boundary cases come from
their existing contracts; each line adds only cases belonging to the new
transition and its disposal.

| Transition | New cases the table must cover |
| --- | --- |
| Handler entry, request selection and forwarding | Boundary or request preparation; exact selection and transfer; malformed or missing applicable control where the semantics permits an internal failure. Passed boundaries and outside behavior retain their own cases. |
| Resume and discard | Owner lookup and one-shot transfer; resume restoration; discard ownership validation and fallible preflight before consumption. Subsequent close actions use their own contracts. |
| Cell acquisition and return | Initializer-frame and acquisition preparation, capacity and fresh-key checks before publication; normal or abandoned release and its applicable disposal. |
| Cell read and write | Selection and authentication, reply and replacement preparation; for write, the distinct disposal case after replacing the root. A preparation failure leaves the old root in place. |
| Cleanup acquisition and completion | Initialization-frame and acquisition preparation before publishing an armed owner; starting and finishing an action; failures in the established action contract and in subsequent close or disposal. |

This table is an inventory of required case producers, not a claim that the
current specification provides a complete, checkable primitive table for each
line. In particular, host reservation, work limits, and internal disposal need
precise interfaces and evidence; a single broad unknown case is safe but cannot
establish the closed program's no-error conclusion by itself.

### Construct cases for ordered primitive phases

The following candidate rules make the resource and cleanup part of that table
more concrete. They describe the current execution order as implementation
evidence; the [cell](../../../spec/dynamic-semantics.md#scoped-cell-execution)
and [cleanup](../../../spec/dynamic-semantics.md#scoped-cleanup-actions)
specification governs source behavior. A proposal must connect its operational
rules to these contracts before they can replace verification.

For a particular primitive invocation, let `s_i` be the state at the start of
phase `i`, not the state at entry to its enclosing expression. Each phase has
an established relation `ok_i(s_i, s_next)` and a failure relation
`fail_i(s_i, failure_observation, f)`. The failure observation is either an
actual failure state or the no-post-state marker, with `s_i` retained as the
reached pre-phase state in both cases. The relations include changes to work, pending
disposal, control, ownership and other relevant state, even when the table below
only describes one projection. Where a precise relation is not yet available,
its conservative failure relation includes an unknown failure; it is not the
empty relation. An excluded operation supplies its own established relation or
an outstanding obligation. In particular, a host reservation proposition is
not a proof that reservation succeeds.

The producer forms each `reach_i` from the *same* certified entry case and the
successful relations of all earlier phases on that branch. The following rule
adds the failure of phase `i`; its guard contains those correlated relations,
including the phase's actual input and failure observation. The first phase has the
entry case as its reach relation. Branches use only their own preceding phases.

```sequent
F-Ordered-Phase :=
  GAMMA; L, entry |- reach_i(w0, s_i, z) covers reaching phase i
  GAMMA; L |- fail_i(s_i, wf, f) covers phase i internal failures
  phi_i(w0, wf, z, s_i) = reach_i(w0, s_i, z) and fail_i(s_i, wf, f)
  ===>
  GAMMA; L, entry |- error_case(B, exists s_i. phi_i(w0, wf, z, s_i), f)
```

If phase `i` succeeds, its `ok_i` relation produces the next reach relation.
The union of the phase cases, the certified operand cases and any later
disposal cases covers the primitive only when the phase contracts and the
branch partition cover all its execution paths. This is symbolic composition
of certificates; the type checker does not execute these phases, recheck an
operand or inspect an opaque callable. If a phase can both succeed and fail
under the facts available, retain both alternatives. A guard's inconsistency
must be derived from established facts or stated assumptions, not assumed
because the path is inconvenient.

For example, current [`TypeWorkBudget::charge`](../../../src/types.rs#L79)
with valid `used <= limit` fails exactly when `used + requested` overflows or
exceeds `limit`; on success it updates `used` to that sum. A prior successful
charge remains spent when a later phase fails. A work-bound certificate can
exclude this guard at the same phase state. It does not exclude a reservation
or disposal failure.

In particular, define `charge_bad(s, d)` to mean that the natural-number sum
`used(s) + d` is not representable by the ledger or exceeds `limit(s)`. The
following rules introduce and exclude only that phase's work failure. `d(s)`
is the actual amount for the covered phase, or a certified upper bound on it;
in the latter case the failure guard is a conservative may-case. The bound and
ledger refer to the same phase state reached from `w0`.

```sequent
family work-charge-cases:
  F-Work-Charge :=
    GAMMA; L, entry |- reach_i(w0, s, z) covers reaching charge i
    d(s) bounds the actual charge at i
    phi(w0, wf, z, s) = reach_i(w0, s, z) and charge_bad(s, d(s)) and wf = s
    ===>
    GAMMA; L, entry |- error_case(B, exists s. phi(w0, wf, z, s), work_exhaustion)

  J-Exclude-Work-Charge :=
    GAMMA; L, entry |- reach_i(w0, s, z) implies used(s) + d(s) is representable and <= limit(s)
    d(s) bounds the actual charge at i
    ===>
    GAMMA; L, entry |- charge i cannot fail from work exhaustion
```

On a failed current charge the ledger itself is unchanged, so `wf = s` is the
state at this charge, not the enclosing operation's entry state. A subsequent
failure-disposal observation has its own case. For cleanup acquisition, the
current requested amount is `2.saturating_add(environment.len())`; for a
non-preflighted cleanup start it is `2`. These facts introduce two different
cases, even when both refer to the same owner. Any additional work performed by
callable inspection or another preparation must be covered separately.

### Source-handler request, resume and discard cases

The following phase tables refine the source-handler and ordinary one-shot
cases in the inventory. Their operational source is the current
[handler semantics](../../../spec/dynamic-semantics.md#effect-handlers-and-completion);
the implementation order comes from
[`return_request`](../../../src/eval/machine.rs#L4440),
[`capture_from`](../../../src/eval/machine.rs#L4977),
[`return_resume`](../../../src/eval/machine.rs#L5019), and
[`discard`](../../../src/eval/machine.rs#L5254). They describe distinct
phases of the same transition, not a second analysis of the clause, operand,
captured control or close actions. A selected builtin cell, native interpreter,
Store or other excluded boundary follows its own applicable contract. Every
conditional source selection still needs a complete nearest-boundary case
cover; an effect-row member alone does not select a handler.

For these tables, `s` is the actual phase state, `N` the active frame-vector
length in that state, `c` the captured-frame accounting, and `m` the configured
capture limit. A source capture at selected index `i` moves `l = N - i`
frames, including the selected handler. Its `l` is a physical frame count;
it is not the number of cell owners or source expressions. For discard, `q`
is the checked total number of frames in the selected capture and its nested
owned captures, and `o` is the inspected owner count. These counts and the
relevant trace configuration belong to the same guarded execution case.
The logical type-level control interface can provide them or safe bounds; it
must not reconstruct a certified capture. A reservation or work charge that
succeeds earlier may have changed capacity or spent budget even if a later
phase fails.

On an ordinary return the evaluator has already popped the `REQUEST` or
`RESUME` frame before entering the corresponding helper. Thus, before capture
or resume transfer, the selected handler or live clause still owns the
relevant control, but the popped operand frame is not restored on error.
`disposal::check` reports a previously pending disposal failure; dropping
temporaries or abandoned frames may record another failure observed later.
Failure starts terminal teardown, not a source-level retry.

| Request and source selection phase | Internal failure or required guard | State at the failure or successful boundary |
| --- | --- | --- |
| Operand and request frame | The operand's certified failure and request cases, or its frame and dispatch contract, can fail. | No new handler capture has been published. Earlier operand effects remain. A request from the operand carries the pending frame and its own certified behavior. |
| Instantiate and select | Pending disposal, invalid request or boundary descriptors, effect instantiation, work charges, comparison, or no applicable interpreter can fail. | After the request frame has been popped, the selected handler has not been captured. Prior successful charges remain spent. Selection is exact and ordered; builtin and excluded selections use their own cases. |
| Prepare source clause | A missing selected clause, invalid pattern or heap operation, unsuccessful match, pattern storage, saved-environment extension, its length overflow, pending disposal, or optional trace reservation can fail. | The selected boundary remains active and no clause owns its capture. The selected clause's checked pattern and actual payload address match validity; their ordinary contracts do not by themselves prove storage or disposal succeeds. |
| Prepare capture | Work charge of the current active frame count, invalid selected index, `c + l` overflow or `c + l > m`, and exact reservation of a new `l`-frame vector can fail. | No frames have moved and `captured_cells` is unchanged. The selected handler remains in the active vector; the request frame was already popped. |
| Publish capture | All preceding preparations succeed. | Move the selected suffix into one captured continuation, set accounting to `c + l`, and publish the live clause boundary and its prepared environment. The captured suffix is not copied. The new clause and its further behavior use their established contracts. |

The source-pattern path uses [`matches_pattern`](../../../src/eval/machine.rs#L6709)
without its optional work meter. Pattern-vector reservation and heap-location
checks therefore remain separate cases; they are not paid for by the capture
work bound. For this ordinary source selection, effect tracing reserves three
entries before moving the frames. The saved environment is extended before
capture, one binding at a time. A count bound excludes length overflow but
does not establish successful allocation or no pending disposal.

| Resume phase | Internal failure or required guard | State at the failure or successful boundary |
| --- | --- | --- |
| Operand | Its certified cases apply before a reply value is available. | The clause still has its live capability while the operand runs; requests carry the pending resume frame. An operand request does not itself supply a reply. |
| Resolve and prepare | After the resume frame is popped, pending disposal, invalid node or matching clause owner, an unavailable capture or invalid completion count, captured-accounting underflow, applicable excluded-owner checks, optional trace reservation or active-frame reservation can fail. | Before `continuation.take()`, the particular clause still owns its capture and the captured-frame accounting is unchanged. Earlier charges and reservations remain. The operand frame is not reconstructed. |
| Transfer and restore | The implementation takes the capture, records resume/restored-handler trace events, updates accounting to `c - l`, and appends the original frames. | A handler-descriptor lookup in the trace loop can report invalid control **after** `take()` and before the accounting update. In that malformed case do not claim the owner or accounting is restored; dropping the local capture can also create a disposal failure. A valid typed-control interface must establish that every descriptor needed by this loop resolves. On the valid path the same frames are restored in order and the clause owner is consumed once. |

Optional tracing reserves `l.saturating_add(1)` events, then the active frame
vector reserves `l` entries before `take()`. Checks involving registrations or
retained roots are excluded-boundary inputs, not new rules for those owners.
Where such owners are live, their contracts must also cover the additional
work and validation performed by the implementation. A successful restore
does not establish the resumed body's return or absence of later failure.

| Discard phase | Internal failure or required guard | State at the failure or successful boundary |
| --- | --- | --- |
| Select and inspect | Pending disposal; absent, consumed or nonordinary owner; invalid captured-handler descriptor; forbidden running or unfinished completion; malformed nested completion; work and inspection-vector reservations; or overflow while summing `q` can fail. An associated registration key with no matching captured registration owner is invalid control. | Before transfer, the live clause still owns the capture and `c` is unchanged. Inspection pays work and may reserve temporary storage. Nested owner and excluded-boundary facts must describe this actual capture and phase. |
| Prepare close storage | Captured-accounting subtraction `c - q`, the final work charge `q.saturating_add(o).saturating_add(1)`, work-vector reservation of `q`, closing-vector reservation of `o`, active-frame reservation of `o.saturating_add(1)`, or optional one-event trace reservation can fail. | The owner still holds the captured continuation and `c` has not been released. The new reservations, including failed allocator requests, have their own guards. |
| Consume and schedule | The preflight succeeds and the owner transfers its captured continuation. | The live owner becomes consumed, owned close frames are scheduled in structural order, and accounting becomes `c - q`. Abandoned non-owning frames are dropped; their disposal can record a later failure. Closing and its actions run through their own certified cases and can fail after earlier effects; they do not replay the abandoned body. |

The discard inspection also charges one unit for the selected-handler query,
one for starting the pending-capture scan, and
`capture.frames.len().saturating_add(1)` for each scanned capture; nested
selected-handler queries and any excluded-owner checks add their own charges.
For each associated registration key, the current check also charges the
number of captured registrations before testing membership; an unmatched key
fails before accounting subtraction or transfer. Its authentication is an
excluded-boundary contract, not a rule for using registrations in this slice.
These are ordered charges against the same ledger, rather than one free scan.
The current [`selected_handler_for_discard`](../../../src/eval/machine.rs#L1041)
returns `false` when the first captured frame is not a handler, and the caller
does not reject that Boolean by itself; a first handler with an invalid or
mismatched descriptor is a distinct failure. The proposed control contract
must justify its own exact shape and cannot claim a stronger current runtime
test than this.

The next rules exclude individual guards using facts certified for this exact
phase and activation. `reach_i` relates the entry world to the reached state;
it is the already established reach case from `F-Ordered-Phase`. All
quantification includes every covered execution, substitution and applicable
outside contract. The rules exclude only the named failure alternative.

```sequent
family handler-phase-exclusions:
  J-Exclude-Source-Capture-Quota :=
    GAMMA; L, entry |- reach_i(w0, s, z) implies l is the selected physical suffix length at s
    GAMMA; L, entry |- reach_i(w0, s, z) implies c(s) + l is representable and c(s) + l <= m(s)
    ===>
    GAMMA; L, entry |- capture at phase i cannot fail its configured captured-frame quota check

  J-Exclude-Control-Vector-Limit :=
    GAMMA; L, entry |- reach_i(w0, s, z) implies d(s) bounds the actual additional reservation
    GAMMA; L, entry |- reach_i(w0, s, z) implies d(s) <= max_T - min(length(s), max_T)
    ===>
    GAMMA; L, entry |- this reserve_control call cannot fail its representational count check

  J-Exclude-Captured-Accounting-Underflow :=
    GAMMA; L, entry |- reach_i(w0, s, z) implies n(s) is the exact prospective frame count being subtracted at this check
    GAMMA; L, entry |- reach_i(w0, s, z) implies n(s) <= c(s)
    ===>
    GAMMA; L, entry |- this transfer cannot fail its captured-accounting subtraction

  J-Exclude-Resume-Posttake-Handler-Failure :=
    GAMMA; L, entry |- the captured control's certified interface covers every handler descriptor in the restored segment
    GAMMA; L, entry |- every such descriptor resolves in the same immutable executable program at this restore
    GAMMA; L, entry |- the actual taken segment is that certified capture under this activation and guard
    ===>
    GAMMA; L, entry |- the post-take restored-handler loop cannot fail descriptor lookup
```

`max_T` is the representable element count for that reservation's element type
as defined in [control preparation](#bound-control-preparation-and-work).
The arithmetic uses the same saturating subtraction as `reserve_control`;
it says nothing about its subsequent allocator reservation. For resume,
`n = l`; for discard, `n = q` includes nested owned captures and must match
the implementation's ledger. A certified case can use an upper bound for the
reservation only if it covers the actual request. The separate
`J-Exclude-Work-Charge` applies at each actual charge. The
[inline-disposal rule](#one-disposal-bound) can exclude its particular spill
growth when its premises hold, but does not erase other disposal outcomes.

#### Exclude a selected wildcard clause's nonmatch

For one actual source-handler request, let `s` be the reached state after
selection and its preceding checks, immediately before looking up the selected
clause. The physical request frame has already been popped; the same selected
handler frame remains active. The request and handler frame certificates
retain their respective saved lexical instantiations and the actual operand
result. The following case uses an admitted wildcard pattern; it makes no
claim that every checked handler has that pattern.

```sequent
J-Selected-Wildcard-No-Nonmatch :=
  GAMMA; L, phi |- J-Selected-Clause-Descriptor holds for this request, selected handler frame and immutable executable P at s
  GAMMA; L, phi |- the corresponding clause's actual checked Core pattern is Wildcard
  GAMMA; L, phi |- the matcher's initial work-vector reservation and actual payload clone complete successfully
  GAMMA; L, phi |- dropping the matcher's cloned payload completes without host panic or abort
  ===>
  GAMMA; L, phi |- the selected descriptor and clause lookups succeed and this match returns true with no pattern bindings
```

`J-Selected-Clause-Descriptor` reuses the certified request and handler
descriptors, exact nearest selection and operation coverage for the same
dynamic frame; it does not search a previously certified clause again. The
[selected-clause path](../../../src/eval/machine.rs#L4654) then invokes the
matcher with an empty binding vector. Its
[wildcard branch](../../../src/eval/machine.rs#L6730) cannot return `false`
and introduces no bindings or further pattern work. Consequently this case
cannot reach `ImpossibleMatch` or the preceding missing-clause invalid-control
guard. A Boolean, tuple, constructor or opaque pattern needs its own certified
representation and match correspondence.

The initial matcher reservation and payload clone are separate potential
storage or host failures. Dropping that clone may record a pending disposal
failure even when the wildcard match returns true; the next applicable
disposal check and final observation retain that case. Saved-environment
cloning and extension, trace reservation, capture preparation, earlier search
and excluded-owner checks remain separate. No selection, successful capture,
or eventual clause result follows merely from an effect-row member or from
this local nonmatch exclusion.

#### Exclude the discard inspection count overflow

The discard inspection adds the physical length of each visited capture to
`count` before examining that capture's frames. A certified discard interface
can exclude that addition's overflow using the same captured-frame ledger as
the later subtraction. Let `s` be the actual state after the live ordinary
owner is selected and before inspection starts. Let `q` be the mathematical
sum of the lengths of a covering set of disjoint segments that this same
inspection can visit, including any nested segment supplied by an applicable excluded
owner contract. At a reached addition, `prefix` contains the previously
visited segments and `next` is the segment being added; their identity and
order come from the certified inspection interface.

```sequent
J-Discard-Inspection-Count :=
  GAMMA; L, phi |- CaptureCountInv(s) and ClauseFact(s, k, h, C, O0, live)
  GAMMA; L, phi |- the same discard's certified inspection interface covers its disjoint counted segments with total physical length q
  GAMMA; L, phi |- the reached prefix contains no repeated segment, next is not in it, and all are members of that same covered inspection
  GAMMA; L, phi |- count is the sum of the reached prefix lengths and the captured-frame ledger remains c(s)
  ===>
  GAMMA; L, phi |- count + length(next) <= q <= c(s), so this checked_add cannot overflow
```

`CaptureCountInv` counts each actual owned segment once in a representable
ledger, so the covered subset has `q <= c(s)` for this same discard.
The [inspection loop](../../../src/eval/machine.rs#L5291) starts `count` at
zero and updates it only by this checked addition; the certified inspection
interface relates each reached prefix to the same accumulator. This is an
inductive fact about the interface, not a request to traverse a certified
capture again. It applies only while inspection has reached that addition;
an earlier descriptor, work or reservation failure remains its own case.

If inspection completes, its exact final count is at most `q`, so the separate
`J-Exclude-Captured-Accounting-Underflow` applies to that actual count before
transfer. Equality with `q` needs a separate exact-enumeration fact. Neither
result establishes storage reservation, work availability, valid excluded
owner associations, safe closing or disposal. If an opaque nested owner does
not certify its counted segments and inspection correspondence, retain that
obligation instead of assuming its contribution is empty. Failed preflight
does not consume the original clause owner.

The selected handler's type and control contracts must separately establish
request descriptor validity, exact interpreter selection, clause coverage,
payload/pattern compatibility, live owner identity and one-shot availability.
An already certified discard plan must also establish its own outside and
running-completion obligations. Those facts do not alone prove quota, work,
storage or disposal safety. Conversely, the numeric exclusions do not prove
valid control. The primitive tables still need a justified complete
instantiation relation, pattern/heap and host-reservation contracts, a proof
that all runtime descriptor and ownership invariants follow from the typed
interfaces, and complete disposal and teardown contracts. Until then a
guarded unknown-failure case remains; it cannot be discarded to conclude
no-error for a closed program.

### A common operation and boundary failure interface

The following interface applies uniformly to an effect operation, handler,
resource or other in-slice boundary. Let `K` be its established type-level
behavioral contract. For each transition `p` that `K` actually provides, it
identifies the relevant input, entry state, applicable authority and owner
facts, its possible successful outcomes and state changes, and a complete
cover of its internal failures and applicable disposal. It also identifies
which constituent or outside contracts apply.
Those facts are conditional on the same actual case and activation; a static
declaration, ordinary value type or effect-row member alone does not establish
a runtime selection. Each `K` declares its own operations, transitions and
state. This notation does not introduce a declaration, require a common
runtime representation, or bring an excluded resource family into this slice.
For this rule, `phi(w0,z0)` identifies the same reached transition and subject
from entry world `w0`, with its scoped case witnesses `z0`. Each failure guard
`chi(w0,wf,z0,z)` retains that subject and case; `wf` is its failure
observation and `z` contains only that failure case's local witnesses.

```sequent
J-Behavior-Transition-No-Error :=
  GAMMA; L, entry |- K is the established behavioral contract for this boundary [O_K]
  the applicable producer-to-contract correspondence is separately justified under permitted assumptions, or its precise scoped obligation O_corr is retained
  GAMMA; L, entry, phi(w0,z0) |- the reached transition p and its same subject satisfy K's applicable entry, authority, owner and context premises [O_entry]
  GAMMA; L, entry, phi(w0,z0) |- already certified constituent and applicable outside no-error contracts fit their actual entries, replies and reentries [O_fit], including their inherited obligations
  GAMMA; L, entry, phi(w0,z0) |- F covers every internal failure introduced by this p and its applicable disposal under K [O_F]
  for each (chi, f) in F, GAMMA, w0, wf, z0, z; L, entry(w0), phi(w0,z0), chi(w0,wf,z0,z) |- false [O_case(chi, f)]
  the established transition interface covers every in-slice failure of this same subject and case by a fitted constituent, an applicable outside contract, or F, retaining O_partition
  the constituent certificates, correspondence, F coverage and guard contradictions are established without assuming this same no-error conclusion or any discharge cyclically
  O_transition carries O_K, O_corr, O_entry, O_fit, O_F, O_case and O_partition under their original scopes and guards, universally binding case-local witnesses where their contexts are exited
  ===>
  GAMMA; L, entry, phi(w0,z0) |- this reached transition and subject have no internal error under K [O_transition]
```

The contradiction premise quantifies over all applicable entry worlds, failure
observations and scoped witnesses for each covered case; it cannot combine a
guard or state from a different activation. The conclusion remains conditional
on `O_transition`; an unconditional result requires its applicable obligations
discharged. Inherited unconditional structural obligations keep their original
scope rather than being guarded by a runtime case. Producer-to-contract
correspondence is a system-level justification or an explicit permitted
boundary assumption, not a soundness proof performed anew for each program or
use. Without that justification or applicable assumption, retain `O_corr`;
the claimed no-error result remains conditional. The failure observation `wf`
includes the no-post-state marker. For recursive cases, the non-circular
evidence requires the justified well-founded or guarded finite-prefix
argument, or discharged recursive assumptions, described by
[`J-No-Internal-Error`](#disposal-state-and-final-observation). A cycle
assuming this same conclusion is not evidence. An unknown failure or missing
contract remains an obligation; it is not an empty `F`.
The rule applies to each covered operation, handler transition, acquisition
or release only where `K` supplies that transition and its actual entry facts.
A successful transition can introduce a fresh owner if its contract says so;
failure before publication is separate. A contract for an owned boundary
must describe transfer, retained completion and discharge at the relevant
boundaries. The rule does not infer those facts from a handle or repeat a
certified constituent's checking. Selection, reply, interception, no reply,
failure and non-return cases retain their own contracts when applicable.

The common checker consumes `K` and the propositions supplied with the same
typed Core subject. It does not dispatch to a separate cell or effect
typechecking pass or verify an already certified implementation again. The
named handler and cell cases in this record are concrete *evidence facts* for
instantiating this common interface and auditing the current evaluator; their
names do not require special typing rules. For example:

| Existing facts and guards | What is specific to the current implementation |
| --- | --- |
| `J-Selected-Wildcard-No-Nonmatch` | The matcher work vector, cloned operand and `ImpossibleMatch` result are facts of this evaluator's selected-clause path; a wildcard's contract uses the common interface. |
| `J-Exclude-Source-Capture-Quota`, `J-Exclude-Resume-Posttake-Handler-Failure` and `J-Discard-Inspection-Count` | These refer to this evaluator's physical frame counts, descriptor lookups and captured-control ledger; effect contracts need not use that representation. |
| `J-Cell-Initializer-Entry` | The `ResourceInitializer` frame and ordinary trace/frame pushes are this evaluator's representation and ordering; a resource contract need not expose them. |
| `F-Cell-Read-Authenticated` and `F-Direct-Cell-Write-Pair` | Generic-cell operation ordinals, `ResourceHandle(key)`, the pair's heap layout and its paid alias resolution are cell/API and evaluator facts. Other declared operations require their own contracts. |
| `F-Cell-Release-No-Underflow`, `J-Exclude-Resource-Owner-Capacity` and `J-Exclude-Activation-Key-Capacity` | These use the current shared owner counter, monotone activation-key counter and their actual accounting interfaces. Their arithmetic can be reused only for a transition using the same ledger and assumptions. |
| `J-Cell-Leaf-Metadata-Disposal`, `J-Copy-Immediate-Cell-Value` and `J-Immediate-Cell-Root-Replacement` | The instance's `Inference` activation atom, `Type` worklist, immediate `Value` forms, current-root replacement and copy charges are concrete representation facts, not generic resource requirements. |

The language mechanisms here are the shared type, effect, handler, resource,
continuation and interface rules, and the proposed proposition and evidence
rules. A concrete cell, handler or other operation is an instance or
implementation of those mechanisms; its runtime implementation is not thereby
legacy. Legacy can include explicitly identified constructs and implementations
as well as verification machinery. For example,
[CP-0031](../../proposals/CP-0031-remove-legacy-integer-cell.md) separately
proposes removing the integer cell; that proposal does not change current Ash.
This failure record focuses on existing verification and reconstruction paths
for facts that the new shared rules will establish and carry. An existing check
can be retired only after the replacement covers its exact subject and every
affected consumer, with the required correspondence and governing specification
changes established.
Until then the current validation remains in force. This distinction does not
call for a separate checker for each instance or rechecking a certified
fragment at each boundary.

Current builtin special paths were introduced while the necessary general
language facilities were absent. Their present hardcoded authority and
runtime guards are evidence to account for, not a requirement that the common
type-system interface preserve builtin privilege indefinitely. Any facility
needed to express their contracts remains a design gap until specified; this
record neither changes their current authority nor introduces a general
user-defined resource facility.

A declared contract alone does not prove that its implementation satisfies
it. An Ash implementation supplies its checked judgment once; a primitive or
host implementation needs separately justified correspondence to the contract
or explicit, permitted external assumptions. The correspondence and soundness
of the rules are system-level obligations, not proofs reconstructed by the
compiler for each use. A later composition reuses the resulting certificate
and checks its own premises. If correspondence or an applicable assumption is
missing, the corresponding obligation remains open; it cannot establish the
unconditional no-error conclusion.

Each remaining current guard, including trace or frame reservation and
platform-dependent storage, requires its own actual transition and failure
contract. The shared rule does not infer that any of these concrete guards
apply to every effect or resource or that their failure alternatives have been excluded.

#### Apply the common interface to one cleanup-start charge

On the current ordinary, non-worker return path, the evaluator has popped the
armed cleanup boundary and checked pending disposal before it reaches the
non-preflighted [cleanup-start work charge](../../../src/eval/machine.rs#L3372).
At that same reached state, `TypeWorkBudget::charge(2)` fails if the sum of
the actual used count and two overflows or exceeds the actual limit; a failed
charge leaves that ledger unchanged. The action has not started. The
[fixture](../../../src/eval/machine.rs#L9944) inspects this case with an
allowance of one; it does not establish a general runtime bound. Strict
[close analysis](../../../src/core/capture/control.rs#L7032) checks control
and completion relationships; its success is not a runtime work allowance.

The common transition interface consumes the established same-case start
contract and the existing `F-Work-Charge` case. An applicable `WorkBound` or
other certified arithmetic fact that entails a representable `used + 2`
within the limit at this actual charge can exclude that one guard. Any
unresolved bound or evidence remains in `O_transition`. The failure cover
must also retain the earlier pending-disposal case, later frame-reservation
and action cases, and applicable teardown; an abort without a post-state uses
the no-post-state observation rather than an invented state. The preflighted
and owned-close paths use their own contracts.

The missing producer is a sound cumulative bound for the same runtime ledger
and all applicable preceding control, including outside calls and reentries,
plus complete reservation, disposal and host correspondence where needed.
Neither successful control verification nor one local charge bound supplies
those facts. A conditional exclusion does not certify a closed no-error
program, prove that the action starts or returns, or cause the action to be
checked again. The [general work-bound rules](#instantiation-reservation-and-cumulative-work-propositions)
state the candidate evidence; their representation and producers remain open.

#### Contract expression and production gaps

`K`, its failure cases and their evidence are candidate type-system interfaces,
not existing source declarations or completed typed Core facts. The
[surface grammar](../../../spec/syntax.md#grammar) currently provides effect
operations, interfaces and ordinary types; it has no general proposition, law
or proof declaration. The following gaps concern what the *common* interface
must express and establish. They do not prescribe a separate checker for a
particular effect or resource.

| Required fact | Current expression and remaining gap |
| --- | --- |
| Possible outcomes and failure | Ordinary data and effects can express a declared recoverable outcome, including [cleanup reporting](../../../spec/dynamic-semantics.md#typed-failure-reporting) and declared allocation refusal. Current [internal failures](../../../spec/dynamic-semantics.md#observation) are terminal and are not automatically source outcomes. `K` needs a complete guarded account of success, request, non-return and internal failure; changing an internal failure into a recoverable one requires a semantic change. |
| Work, capacity and host assumptions | Existing kinds, types, rows and interface requirements do not by themselves state the phase-indexed demand and ledger inequalities used by the failure guards, or a scoped platform allocation promise. A type-level proposition or other checked evidence may be needed to express and compose those bounds. A host assumption must name its subject and scope; it cannot turn an internal limit into an external event. Current [native signatures and link names](../../../spec/static-semantics.md#source-foreign-declarations) contain an assertion the compiler does not prove, but do not by themselves establish these bounds. |
| Owner and control disposition | Current [handler and resource semantics](../../../spec/dynamic-semantics.md#effect-handlers-and-completion) and their checks impose one-shot use, transfer, close and crossing obligations. A row or ordinary function type does not publish the correlated owner, phase, selected boundary and surviving obligations required to compose them opaquely. Typed Core needs a checked representation of those facts and their scoped assumptions; surface inference may supply it where possible. |
| Disposal and observation | Current semantics distinguishes [internal failure disposal](../../../spec/dynamic-semantics.md#scoped-retained-control-execution) and incomplete cleanup from [source cleanup actions](../../../spec/dynamic-semantics.md#scoped-cleanup-actions). `K` needs a cover for the actual failure point, owned disposal, possible later failure and final observation, including any separately justified host premise. A normal-result type or a successful close plan does not supply that cover. |

For each missing relation, the slice must determine a well-scoped type,
proposition or other evidence form, its introduction and elimination rules,
and how checked Core retains it at opaque boundaries. A law or assumption
must carry its justification status and applicability; writing one is not a
proof. General resource declarations are not a prerequisite for this slice:
the current [cell rules](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
explicitly do not add them. If existing forms cannot represent a required
fact, the design must record the missing form and resolve its semantics before
using the fact to remove a legacy check. This record does not choose new
surface syntax, assert inference completeness, or implement those forms.

#### Instantiate an existing failure contract

One missing general rule is elimination of a previously established
polymorphic failure contract at its use boundary. Let `K(alpha)` describe
one certified subject with formal parameters `alpha`, entry assumptions
`psi`, complete failure cover `F` and scoped obligations `O`. `theta` is the
actual, kind-correct specialization at the new composition. Substitution
applies to the subject interface, assumptions, case guards, states and
obligations together; it does not inspect or check the subject again.

```sequent
F-Contract-Instantiation :=
  GAMMA_0; L_0, psi |- K(alpha) has complete failure cover F with obligations O for the certified subject
  GAMMA; L, entry |- theta is a well-scoped, kind-correct specialization of alpha and preserves the contract's binders and substitutions
  GAMMA; L, entry, phi |- this actual boundary use is the corresponding specialization of that same certified subject
  GAMMA; L, entry, phi |- the applicable GAMMA_0_theta, L_0_theta and psi_theta assumptions hold for this actual entry and its surrounding context
  the general substitution and observation-correspondence rules preserve coverage and case witnesses for this specialization
  ===>
  GAMMA; L, entry, phi |- K_theta has complete failure cover F_theta with obligations O_theta for this boundary use
```

The current specification already requires relevant dependency relationships
to survive [Type/Row instantiation](../../../spec/static-semantics.md#generic-cell-foundation);
this rule extends the same reuse requirement to the proposed complete failure
interface. The substitution and correspondence rules are properties to establish for
the type system, not a per-use proof of its soundness. They must preserve the
same applicable failure observation, including no-post-state, and bind any
case-local owner or state witnesses in the resulting interface. Specialization
may identify previously distinct parameters: substitute guards and prove their
actual constraints instead of assuming the parameters remain unequal. If an
entry assumption, substitution relation or obligation cannot be established,
keep it scoped and do not conclude unconditional no-error.

The new composition applies `J-Behavior-Transition-No-Error` to the
instantiated contract and separately checks any failure introduced by that
composition. It does not reproduce a constituent's proof, infer absence from
an omitted case, or turn a possible failure into an actual one. The general
substitution and obligation-transport rules still need a concrete form and
system justification; this schema does not assert that today's Core produces
them.

### Cell acquisition, access and release cases

The following ordered cases and named local derivations are facts about the
current **generic** cell implementation. They supply propositions to the
common interface above; they do not prescribe a cell-specific
typechecking pass or re-verification of a certified operation. `a` is the fresh
activation, `root(a)` is the owner payload, and `live` and `next` are the
resource count and next activation key at the indicated phase. They are
resource-state projections, not complete machine snapshots. Initializer
evaluation and its failures come from its existing certificate; the cell owner
does not exist during that evaluation.

| Phase | Failure condition or remaining proposition | Ownership and control consequence |
| --- | --- | --- |
| Enter initializer | The ordinary entry trace and frame pushes may need storage; node dispatch, pending disposal and environment sharing have their own conditions. Initializer failures and requests come from its existing contract. | No new cell is published. Preserve the actual entry, frame and initializer states and any effects already reported by the initializer or its context. |
| Observe pending disposal | On return from the initializer, the return machinery and acquisition check any already recorded disposal failure before validating the resource or checking its limits. | The initializer frame has been popped on the ordinary return path. No new cell has been published, and no source-level retry follows from this failure. |
| Validate acquisition and capacity | Invalid resource/API control, or `checked_add(live, 1)` overflows or exceeds the configured resource-owner limit. | No new owner or activation is published. A capacity proof must count all owners in the current machine ledger, including captured cells and any excluded owner kinds that share that ledger. |
| Fresh key | After the preceding checks succeed, `checked_add(next, 1)` overflows. | No new owner or key is published; live-owner capacity being available is insufficient to exclude this case. |
| Prepare publication | Frame and enabled-trace reservation; lexical instantiation; binding the handle; constructing and instantiating the generic effect instance; their work, malformed-control and pending-disposal failures. Each check has its own state and guard. | No new cell or authority is published if any preparation fails, but earlier work and preparation effects need not be rolled back. Exact instantiation, environment and reservation contracts remain obligations. |
| Publish | Every preparation succeeded; publish exactly one owner with its payload and complete instance, then update `live` and `next` and enter the body. | The body contract applies to this fresh owner and this actual state. Other existing owners are preserved according to their contracts. |

The ordering is supported by
[`acquire_resource`](../../../src/eval/machine.rs#L4210). Frame and trace
reservation use `try_reserve` in that path. A storage-reservation error does
not by itself reveal whether a representational limit or allocator refusal was
responsible; the proposed guard must not classify the event more narrowly
without an appropriate premise. A finite capacity bound also cannot establish
success of lexical instantiation or handle binding.

#### Enter the generic initializer

The [source rule](../../../spec/dynamic-semantics.md#scoped-cell-execution)
starts the initializer in the preceding environment before any cell owner
exists. Source checking already checks it against the generic payload `T`;
the [Core resource constructor](../../../src/elaborate.rs#L14382) retains
that checked initializer and the body as children. The current evaluator's
[`dispatch_entry`](../../../src/eval/machine.rs#L5669) constructs
`ResourceInitializer { node, environment }` and evaluates the initializer
under a clone of that same environment. The runtime frame stores the Core node
and environment; the checked payload type and body are associated with the
node, not separately stored as fields in the frame. The abstract `GINIT` in
`E-Generic-Initialize` denotes that information and control relationship.

For one actual entry, the current
[run loop](../../../src/eval/machine.rs#L1835) first checks pending disposal,
takes `Control::Evaluate(node, E)`, and pushes an entry into the ordinary
trace. After the applicable dispatch path constructs the provisional
transition, a second disposal check precedes `apply`. `apply` pushes the
initializer frame and installs the initializer control. In particular, the
ordinary trace and frame calls are `Vec::push`, not the later fallible
`try_reserve` calls in cell acquisition. The latter do not establish capacity
for these earlier pushes. The test-only work trace and its configuration need
their own applicable contract.

Let `PushRoom(v,s)` mean the actual vector `v` in state `s` is valid and has
`len(v,s) < capacity(v,s)`. The container's no-growth property supplies this
local rule for the actual push. It is distinct from
`J-Reserve-Within-Vector-Capacity`: this operation is a push, not a
reservation.

```sequent
J-Vector-Push-With-Room :=
  GAMMA; L, phi |- PushRoom(v,s) for the actual vector and state of this push
  GAMMA; L, phi |- x is the actual already prepared element moved by this push
  ===>
  GAMMA; L, phi |- pushing x uses no vector growth and yields v ++ [x]
```

The vector length increases by one; its prior contents and capacity are
preserved. This proves no vector allocation or representational growth failure
at that specific push. It does not prove that constructing `x`, sharing its
environment, executing a later operation or disposing of `x` cannot fail.
When the vector is full, lack of room does not itself prove a failure: it
leaves the actual growth outcome, internal capacity/layout conditions and host
allocation behavior to their applicable contract. `Vec::push` does not return
a `RuntimeFailure` on that path, so an abort or panic must not be described as
a recoverable source branch or silently omitted from the no-error target.

The following rule supplies the successful `start` premise of
[`Enter-Strict`](first-slice-behavior-coverage-rules.md#enter-a-new-expression)
for this exact Core cell node. The capacities refer to the two **different**
vectors at their actual push states. `E_copy` is an ordinary immutable snapshot
of `E` with the same lexical instantiation; sharing its `Arc`-backed metadata
must itself satisfy the applicable platform representation contract. `P` is the
same executable program that owns `node` and its checked children.

```sequent
J-Cell-Initializer-Entry :=
  GAMMA; L, phi |- the checked generic Resource node in P has initializer e, body b and payload type T
  GAMMA; L, phi |- this actual entry has control Evaluate(node,E) and the certified initializer judgment applies to E
  GAMMA; L, phi |- the initial pending-disposal check is clear and the entry trace push has room at its actual state
  GAMMA; L, phi |- the actual environment sharing for dispatch completes as E_copy with the same lexical facts as E
  GAMMA; L, phi |- dispatch in this same P produces Evaluate(e,E_copy) and ResourceInitializer(node,E)
  GAMMA; L, phi |- the post-dispatch disposal check is clear and the active-frame push has room at its actual state
  GAMMA; L, phi |- the apply control slot is empty and the applicable outside-control facts are preserved
  ===>
  GAMMA; L, phi |- start(cell_initializer,E) succeeds with that frame and entry Evaluate(e,E_copy)
```

The checked node's descriptor and child relation exclude a wrong or missing
resource node in this dispatch case; they do not establish either vector's
capacity. The two `PushRoom` facts can come from a certified preceding capacity
and a bound on **all** intervening mutations of the same vector, including
outside control; otherwise they remain obligations. `J-Vector-Push-With-Room`
is applied once to each different push. The rule also requires the actual
environment-sharing and outside contracts, rather than treating them as facts
of `T`. It proves only successful entry into the initializer, not that the
initializer returns, acquisition succeeds or the complete program is safe.

If a pending failure is observed at either disposal check, reuse the
[pending-disposal case](#disposal-state-and-final-observation) at that actual
state. At the second check the control has already been taken and the
provisional transition holds the initializer control and frame; dropping those
temporaries may contribute later disposal behavior. No initializer frame has
been installed and no cell owner has been published. An invalid or missing
node reports the dispatch failure at its actual point after the entry trace;
an unproved node or environment contract remains a covered unknown case.
If an initializer then requests, diverges or fails, its already certified
behavior describes that outcome with the frame pending. A captured and
discarded initializer frame does not acquire a cell or execute its body.
Only its actual normal result reaches the separate acquisition and failure
cases above; neither this rule nor a caller rechecks the initializer.

After a request is selected for this particular cell, the following access
cases are added to the already certified operand and selection cases. A nearer
source handler may intercept the request, in which case its clause contract
applies instead and these builtin read/write cases do not run.

| Phase | Failure condition or remaining proposition | Ownership and control consequence |
| --- | --- | --- |
| Authenticate | Wrong selected owner, operation, full instantiated identity, handle or write-pair representation; paid alias resolution may also fail. | No builtin read reply or root replacement. The ordinary typing, selection and dependency judgments must establish their corresponding facts; neither identity nor pair shape follows from payload type `T` alone. |
| Prepare write | Copy the actual replacement, pay work and reserve enabled trace capacity; each can fail under its own primitive contract. | Until all preparation succeeds, `root(a)` remains the old root. Previously evaluated operand effects and spent work remain. |
| Prepare read | Pay common work and reserve enabled trace capacity; copying the actual current root can also fail. | On failure, `root(a)` remains the current root and no builtin read events or reply are committed. The copy cost may depend on the value, even with polymorphic `T`. |
| Commit | On successful read, return the copied value and keep the root; on successful write, replace exactly `root(a)` and return `Unit`. Commit the corresponding builtin trace events. | A last-owned old root can fail during internal disposal **after** replacement. That failure uses the post-replacement state and cannot be treated as failed preparation or as a rollback. |

The [generic interpreter](../../../src/eval/machine.rs#L4902) supplies the
ordering. Its value-copy helper can charge for integer magnitude or callable
origin; its other details come from the applicable value and instantiation
contracts. A disposal failure can be recorded during replacement and observed
at a subsequent check. The
[failure fixture](../../../src/eval/machine.rs#L11875) illustrates the committed
root and trace before such a failure; it is evidence, not a new source rule.

#### Exclude the builtin read's operation and handle failures

Let `s` be the actual generic-cell interpreter state after its
pending-disposal check. Exact nearest selection has selected the same live
generic cell owner `a`, whose physical frame has key `key` and complete
instance `I`. The read's operand is the actual handle `h` returned by its
already checked operand. The selected owner, request and handle are correlated
in this case; a possible target or a shared payload type is insufficient.

```sequent
F-Cell-Read-Authenticated :=
  GAMMA; L, phi |- OwnerInv(s, M, Q) and cell_owner(s, a, root, P, I)
  GAMMA; L, phi |- exact selection for r at s chose this same generic owner a with physical key key and instance I
  GAMMA; L, phi |- r is the sealed read operation OperationId(I.effect, 0) and its actual operand is h
  GAMMA; L, phi |- InstanceFact(I, R, P, a) and HandleFact(h, R, P, a)
  GAMMA; L, phi |- the actual representation contract for this HandleFact identifies h as Value::ResourceHandle(key)
  ===>
  GAMMA; L, phi |- the generic read operation branch and its handle-key guard succeed for this r at s
```

Successful acquisition supplies the owner, handle and exact instance facts;
`J-Cell-Handle-Copy` and the operand's ordinary value contract preserve the
same handle through aliases and opaque boundaries only where their actual
relationship is certified. The matching physical key is a property of that
handle and activation, not an equality inferred from `Cell<R,P>` alone. The
[nearest-boundary contract](first-slice-nearest-boundary-judgments.md#candidate-composition-rules)
must select this builtin: if a nearer source handler intercepts, its clause
contract applies instead.

The [generic interpreter](../../../src/eval/machine.rs#L4902) checks the
selected generic frame, selects operation ordinal zero and then compares the
actual `Value::ResourceHandle` with that frame's key. This rule excludes the
wrong-operation and wrong-handle invalid-control branches at that point; it
does not prove that the read returns. After those guards, the interpreter
charges two work units and, when tracing is enabled, reserves two trace entries
before reborrowing the selected generic frame and copying its current root.
On successful charge and reservation those operations do not move or replace
the frame, so its same-owner representation also excludes the later generic
frame-shape failure. The charge, reservation, root-copy and applicable host
or disposal failures remain separate, as do the earlier descriptor, selection
and pending-disposal checks. A missing representation, owner or opaque-boundary
contract remains an obligation. The
[specified read](../../../spec/dynamic-semantics.md#scoped-cell-execution)
additionally requires successful reply preparation; no reply is inferred here.

#### Exclude direct write-pair control failures

This case specializes `J-Cell-Request-Authentication` to a write operand
produced as a direct ordinary tuple. The facts describe the same actual
request, selected owner, heap and point of execution; they do not follow from
the generic payload type. Let `s` be the reached generic interpreter state
after its pending-disposal check, before write-operand resolution. Let `key`
be the physical activation key represented by this same logical owner `a`.

```sequent
F-Direct-Cell-Write-Pair :=
  GAMMA; L, phi |- exact selection of request r at s chose generic cell owner a with physical key key and instance I
  GAMMA; L, phi |- r is this I's sealed write operation and its actual operand is Value::Location(loc)
  GAMMA; L, phi |- heap(s)[loc] = HeapCell::Tuple([Value::ResourceHandle(key), replacement])
  GAMMA; L, phi |- HandleFact(Value::ResourceHandle(key), R, P, a) and InstanceFact(I, R, P, a)
  GAMMA; L, phi |- the actual access-work ledger at s can charge one unit
  ===>
  GAMMA; L, phi |- resolving this operand returns loc after one charge and the write's tuple-shape and first handle-key guards succeed
```

The ordinary [tuple-return transition](../../../src/eval/machine.rs#L6139)
can produce the direct location and ordered field fact after the two fields
have actually returned and allocation succeeds. Acquisition supplies the
same owner's handle and instance facts; certified copies and intervening
transitions must preserve the particular tuple and handle through selection.
No caller rechecks the tuple's fields. If an opaque producer cannot supply the
actual representation and preservation fact, this case remains an obligation;
a checked pair type alone does not supply the heap fact.

At this exact location [`resolve_location_with_work`](../../../src/eval/machine.rs#L6690)
charges once and returns without following an alias. The ordinary tuple's
first field is a resource handle, so [`tuple_fields`](../../../src/eval/value.rs#L100)
does not reject it as a constructor or closure representation; the actual
two fields and matching key then satisfy the
[write guards](../../../src/eval/machine.rs#L4920). If replacement copying
subsequently succeeds and preserves the selected frame and key, the later
common handle-key check also succeeds for this same handle. Copy failure,
the later two-unit work charge and trace reservation, retention, replacement
disposal, and all earlier selection and disposal failures remain separate.
An alias, native tuple or changed heap needs its own representation and
resolution contract. The [generic-cell semantics](../../../spec/dynamic-semantics.md#scoped-cell-execution)
requires the authenticated pair; this rule accounts for one concrete runtime
representation of that pair.

On normal return, or when an admitted owned close reaches this cell's position,
the ordinary return path has already popped the cell frame before checking for
pending disposal and then checking the live-resource count. If the count can be
decremented, it is decremented and the payload is dropped; an earlier pending
disposal failure or an underflow can drop the moved payload on the failure path.
The typed ownership invariant must exclude underflow for this actual owner and
state. A separate worker path preflights
the count before popping; that excluded path needs its own contract and does
not change the ordinary ordering. Dropping the payload can record an internal
disposal failure after the count change; the failure contract must retain that
state and any earlier effects. The result dependency rule independently
prevents returning a value that depends on the released activation. A failed
release or teardown does not promise source cleanup or completion of later
close positions. The [return loop](../../../src/eval/machine.rs#L1930) and
[resource return](../../../src/eval/machine.rs#L3469) are evidence for the
frame, count and disposal order; the concrete disposal demand remains an
obligation, not a consequence of independence.

#### Exclude the ordinary cell-release count failure

For one reached generic-cell return, the owner accounting rules make the
underflow guard precise. Let `s_before` be the state immediately before the
ordinary return loop pops its top frame, and `s_guard` the state at the cell
count check after that pop and a successful pending-disposal check. The popped
frame and payload are held by this same return transition at `s_guard`; they
are not still on the active stack. `M` includes that temporary owner.

```sequent
F-Cell-Release-No-Underflow :=
  GAMMA; L, phi |- OwnerInv(s_before, M, Q) and cell_owner(s_before, a, v, T, I)
  GAMMA; L, phi |- this is the ordinary non-worker return path
  GAMMA; L, phi |- the actual next ordinary return frame is this same generic cell owner a
  GAMMA; L, phi |- the pop and pending-disposal check succeed and reach s_guard
  GAMMA; L, phi |- those steps preserve the counted owners and counter, holding a in the return transition
  ===>
  GAMMA; L, phi |- resource_count(s_guard) = |M| > 0 and checked_sub(resource_count(s_guard), 1) succeeds
```

Successful acquisition introduced `a` into `M` by
[`J-Account-Cell-Acquire`](first-slice-resource-rules.md#introduce-and-move-the-counted-owners);
certified capture, restore and close transfers preserve that same owner and
the count. The temporary-owner convention and `J-Cell-Count-Positive` then
apply at this precise guard. A fragment entered under an existing context
requires its established accounting interface, including excluded owners
sharing the counter. These premises use the correlated case and do not inspect
the body or captured segment again. If the interface or preservation fact is
missing, the failure is not excluded.

In the implementation the ordinary loop pops before
[`return_from_preflighted`](../../../src/eval/machine.rs#L2920), whose first
action checks pending disposal. The generic-cell arm then uses
[`checked_sub(1)`](../../../src/eval/machine.rs#L3469) before dropping the
payload. The pop and successful disposal check do not decrement this count;
there is no store-only preflight in the generic-cell arm. This judgment
excludes only that particular invalid-control branch: a failed pending
disposal check and a failure recorded while dropping the payload remain their
own cases. [`E-Generic-Return`](../../../spec/dynamic-semantics.md#scoped-cell-execution)
specifies the source transition; the accounting proposition connects that
transition to the additional implementation guard.

#### Bound disposal of leaf cell metadata at release

The generic owner frame also retains its fully instantiated effect instance.
The following sufficient case excludes the current type-disposal worklist
growth failure for one concrete representation. Write `LeafType(t)` when the
actual runtime `Type` is `Bytes`, `String`, `Int`, `Bool`, `Unit`, `Nominal`,
`Variable` or `Inference`, all of which have no structural Type children.
This is a property of the instantiated metadata, not a restriction on the
generic cell's source payload type.

```sequent
J-Cell-Leaf-Metadata-Disposal :=
  GAMMA; L, phi |- the actual popped generic cell payload contains instance I for this same owner a
  GAMMA; L, phi |- I has exactly TypeArg(Type::Inference(key)) and TypeArg(t), in that order, and LeafType(t)
  GAMMA; L, phi |- the release count decrement has succeeded and no disposal failure is pending immediately before dropping I
  ===>
  GAMMA; L, phi |- dropping I introduces no TypeDisposal worklist-growth failure
```

Successful acquisition constructs and instantiates the exact generic
`Ops<R,P>` instance before publishing the frame; the acquisition and
instantiation contracts must establish this particular argument representation
for the same `a` and preserve it through transfers. At runtime the owned
activation is represented by the `Inference(key)` leaf; an abstract `P`
does not itself prove that its instantiated argument is a leaf. The fact may
be supplied when specialization produces a leaf, without reopening the
producer or cell body. Compound types, row-bearing metadata and unknown
instantiations retain their own disposal bound or obligation.

[`EffectInstance::drop`](../../../src/types.rs#L745) drains the two arguments
separately. Each `TypeArg` uses
[`discard_type_iteratively`](../../../src/types.rs#L2274), whose fresh
`Pending::new` receives one leaf, pops it and adds no children. Thus each
worklist stays within one of its eight inline slots; no spill reservation is
attempted. This is a concrete producer for the earlier inline-worklist bound.
The ordinary release loop has already popped the owner and the
[resource arm](../../../src/eval/machine.rs#L3469) has decremented its count
before dropping the payload. If its value is separately established to be an
immediate value as in `J-Immediate-Cell-Root-Replacement`, its own drop cannot
set a disposal failure before this metadata is drained; other values need
their own drop contracts. This rule does not cover earlier failed disposal or
count checks, a different metadata representation, later trace or environment
disposal, or unmodelled host/deallocation panic or abort. Those remain
separate cases or explicitly stated platform assumptions.

### Cleanup acquisition, start and finish cases

The action initializer and the body and action behaviors have their own
certificates. The following adds only cleanup-owner transitions. A source
initializer is evaluated once before acquisition; at the Core acquisition
point the current implementation looks up and checks the already prepared
callable. Source lowering uses an ordinary callback binding and may include a
saved-allocation-context query before that Core node; it does not install a
cleanup-specific initializer frame or re-evaluate its source initializer.
Their established behavior and failure contracts apply before acquisition.

| Phase | Failure condition or remaining proposition | Ownership and control consequence |
| --- | --- | --- |
| Initialize action | Initializer, framing or its preceding context fails or does not return. | No cleanup invocation owner has been acquired. Preserve the initializer's certified effects and requests. |
| Prepare acquisition | Pending disposal; work charge `2.saturating_add(environment.len())`; missing callback binding or failure to read its callable; then `checked_add(live_cleanups, 1)` overflow or configured limit; then frame reservation. | No armed owner is published and the body is not entered. Work spent by successful earlier phases remains spent. Callable and storage contracts are separate from the count bound. |
| Publish armed owner | All acquisition preparation succeeds. | Publish exactly one armed owner, increase the live count and enter the body. Capture and resume transfer this owner without another acquisition or action invocation. |
| Start | After normal body return or admitted owned close, pending disposal, the cleanup work charge and completion-frame reservation may fail. | If preparation fails, the action has not started. The ordinary return path has already popped the owner frame; do not infer it remains available to source code or that another attempt occurs. A preflighted path uses its own established preflight result. |
| Run action | Apply the action's existing behavior and failure contract to the selected surviving context. | Starting makes the invocation ineligible for a second start; capture may move its running state. Requests and effects already made remain made, and failure does not run remaining cleanup actions. |
| Finish | A non-`Unit` action result or an underflow of the live-cleanup count is invalid control; pending disposal can also be observed. | On valid finish, decrement the count once and restore the saved body value or advance the owned close. The action result and owner-state premises must come from the established contracts, not be assumed from reaching this phase. |

The [acquisition](../../../src/eval/machine.rs#L3719),
[normal start and finish](../../../src/eval/machine.rs#L3372), and
[preflighted owner return](../../../src/eval/machine.rs#L2898) are distinct
implementation paths. For example, a start work allowance of one cannot pay
the current charge of two; the inspected
[fixture](../../../src/eval/machine.rs#L9944) shows that the action has not
started after that failure. The source semantics does not promise retry or
completion on internal exhaustion. Neither the owner count nor the action's
ordinary type establishes successful allocation, enough work, or disposal.

#### Exclude the ordinary cleanup-finish control failures

At one reached normal finish, let `s_before` be the state immediately before
the ordinary non-worker return loop pops this invocation's
`CleanupCompletion`, and `s_guard` the state after the pop and successful
pending-disposal check. The popped completion and its saved body value are held
by the return transition at `s_guard`. The running owner remains in the
accounting set `Q` until its successful finish.

```sequent
F-Cleanup-Finish-Valid-Control :=
  GAMMA; L, phi |- OwnerInv(s_before, M, Q) and cleanup_owner(s_before, o, running, A)
  GAMMA; L, phi |- the actual next ordinary non-worker return frame is o's CleanupCompletion
  GAMMA; L, phi |- the actual action A has returned value v and its certified result and representation give v = Value::Unit
  GAMMA; L, phi |- the pop and pending-disposal check succeed and reach s_guard
  GAMMA; L, phi |- those steps preserve Q and its count, holding o's completion in the return transition
  ===>
  GAMMA; L, phi |- the Unit guard and checked_sub(cleanup_count(s_guard), 1) both succeed for this finish
```

Successful `Core-Cleanup-Acquire` and
[`J-Account-Cleanup-Acquire`](first-slice-resource-rules.md#introduce-and-move-the-counted-owners)
introduced the invocation in `Q`; `J-Cleanup-Start-Phase` changes that same
owner to running, and certified capture and resume transfer it without
duplicating or completing it. `OwnerInv` counts even the temporarily popped
completion. Thus `J-Cleanup-Finish-Valid` supplies the positive count and the
actual action-result representation supplies the Unit guard. This uses the
action's already certified normal result; it does not recheck its body or infer
that it terminates.

The [return loop](../../../src/eval/machine.rs#L1930) pops first;
[`return_from_preflighted`](../../../src/eval/machine.rs#L2920) then checks
pending disposal. The [cleanup-completion arm](../../../src/eval/machine.rs#L3392)
checks the actual `Unit` value before decrementing the live-cleanup counter;
only after both guards does it continue with the saved value. This corresponds
to [CleanupFinish](../../../spec/dynamic-semantics.md#scoped-cleanup-actions).
The rule does not exclude a failed disposal check, failure or non-return of the
action, earlier start or acquisition failures, or later failure. A missing
action representation, running-owner or shared-count contract remains an
obligation. The worker and owned-close paths require their own applicable
transition interfaces.

### One disposal bound

Some disposal failures have a concrete sufficient exclusion even before a
general disposal contract exists. The current
[`Pending::new` worklist](../../../src/eval/disposal.rs#L142) starts with an
empty spill vector and eight inline slots. With no pending failure, a push uses
an inline slot whenever the spill is empty and an inline slot is available. It
tries to grow the spill only after that condition fails. With a pending
failure, it abandons further work instead of promising completion.

Define `fresh_inline_disposal_bound(B, w0, 8)` to mean that, over every
disposal run relevant to `B` under entry `w0`, each worklist covered by this
fact starts with `Pending::new`, and its number of pending items immediately
before every attempted push plus the attempted item is at most eight. This
counts a push even if it would fail and forget its item. It includes each nested
or later worklist separately. It is a property of the actual disposal behavior
and ownership, not merely a bound on the size of an ordinary type or an
unchecked annotation.

```sequent
J-Exclude-Inline-Disposal-Growth :=
  for every covered entry w0,
    GAMMA; L, entry(w0) |- fresh_inline_disposal_bound(B, w0, 8)
    GAMMA; L, entry(w0) |- no other failure is pending before these covered pushes
  ===>
  GAMMA; L, entry |- no covered Pending::new spill-growth failure during B
```

The induction is local to each fresh worklist: since it starts with no spill
entries and each attempted push has prospective demand at most eight, no push
needs to create a spill. This excludes only those worklist growth failures. It
does not establish absence of other disposal failures, cover a worklist
initialized from existing spill storage, establish that a destructor completes,
or prove the bound for an opaque value. A producer may retain the bound with the
value and its owner; the consumer reuses it at the actual disposal point instead
of traversing the already certified value again. If replacement leaves the old
value's last owner, the required bound applies to that old value's disposal after
replacement, not to the new cell root.

These tables identify concrete guards and the states to which they apply, but
they are not yet complete primitive contracts. The unresolved parts are the
precise storage, instantiation, callable, request-selection and disposal
relations; the link from type-level ownership and ordinary typing facts to each
invalid-control guard; and a system-level coverage argument for the tables.
Until those are established, the corresponding unknown cases remain in the
failure cover. They may not be erased by the agreed no-error admission rule.

### Derive capacity cases

The existing cleanup acquisition first performs other checks, then computes
`live.checked_add(1)` and checks it against `cleanup_limit`. In a correlated
case that has reached this check with count `live` and limit `limit`, the
configured-owner-capacity alternative has guard
`checked_add(live, 1) fails or checked_add(live, 1) > limit`. Its successful
alternative has the complementary representable value at most `limit`; it
does not publish the owner until later preparation succeeds. Failures in the
earlier checks and later frame reservation are separate cases. The
[implementation](../../../src/eval/machine.rs#L3720) is evidence for this
ordering; the proposed type-level table still requires semantic justification.

Cell acquisition similarly checks its live-owner count and then the fresh
activation counter. Under the case that reached the latter check, the key
capacity guard is `checked_add(next_activation, 1) fails`. It is separate from
the guard on `live_resources + 1`, and successful checking does not publish the
new owner until all later preparation succeeds. Earlier and later failures have
their own cases. These guards let a checker apply established arithmetic and
resource bounds at the actual check state; they do not themselves establish
the bounds or success of other preparations.

The owner-limit and fresh-key cases require different facts. Define
`resource_demand(B, w0) <= n` as an established bound, over every attempted
resource acquisition during `B`, on the actual shared live-resource count at
that attempt plus one. It includes captured owners and every applicable owner
kind sharing the ledger, including those supplied by outside contracts. Define
`activation_demand(B, w0) <= q` as an established bound on both the total
number of actual advances of this counter during `B` and, at every reached
in-slice cell key check, the number of preceding advances plus one for that
prospective check. The bound includes advances made by outside control running
within `B`, as established by its contracts. Counting all attempts and any
additional advances can provide such a bound; an attempt that fails before
advancing may be counted conservatively. The counter begins at `next(w0)` and
advances at each successful reservation or publication step that uses it;
release does not decrease it. Different boundary contracts can have different
advance points:
the current [region preparation](../../../src/eval/region.rs#L958) advances
the shared counter before evaluating its provider and before publishing the
region, while the [cell acquisition](../../../src/eval/machine.rs#L4270)
advances it at publication. Thus a region's later provider failure does not
undo that advance. The rule consumes the outside boundary's established
accounting facts; it does not introduce region verification into this slice.
The following
candidate rules exclude their respective guard, not the other preparation
failures. The quantifiers cover every entry admitted by the certificate.

```sequent
family cell-acquisition-bounds:
  J-Exclude-Resource-Owner-Capacity :=
    for every covered entry w0,
      GAMMA; L, entry(w0) |- resource_demand(B, w0) <= n
      GAMMA; L, entry(w0) |- n is representable and n <= resource_limit(w0)
      GAMMA; L, entry(w0) |- resource_limit remains valid during B
    ===>
    GAMMA; L, entry |- no_configured_resource_owner_capacity_failure(B)

  J-Exclude-Activation-Key-Capacity :=
    for every covered entry w0,
      GAMMA; L, entry(w0) |- activation_demand(B, w0) <= q
      GAMMA; L, entry(w0) |- next(w0) + q <= max_activation_counter
      GAMMA; L, entry(w0) |- the counter advances only as accounted by that bound
    ===>
    GAMMA; L, entry |- no_in_slice_cell_activation_key_check_failure(B)
```

The second rule excludes only the in-slice cell check `next_activation + 1`.
It does not exclude key checks in outside operations. For example, current
[network owner preparation](../../../src/eval/machine.rs#L2114) also checks
`next_activation + 2`; its separate guard needs its own contract and bound.
For example, with `next = max_activation_counter - 1`,
two sequential cell scopes may each fit a live-owner limit of one, but the
second key attempt cannot satisfy the sufficient bound, even if the first cell
has already been released. This does not assert that the second attempt is
reached or that no other proof can exclude it. Both bounds must be derived
from the already certified constituent behavior and the new composition's
interleavings. A recursive computation or an opaque outside behavior can leave
one or both bounds as explicit obligations.

The bounds can themselves be composed from certified behaviors. For a
sequential composition `B = B1 ; B2`, suppose the new control and all its
interpreters run each constituent at most once, and a nonreturning or failing
`B1` does not start `B2`. Suppose the constituent bounds apply at every actual
entry reached by that composition, including the control invoked while each
constituent is active. Let `q_new` bound both the actual advances made by the
new composition outside those constituent executions and, at each cell key
check there, its preceding such advances plus one. Let `n_new` bound the
corresponding absolute live-resource demand there. The propositions cover
the same resource and activation ledgers. Then:

```sequent
family compose-resource-bounds:
  J-Sequence-Activation-Bound :=
    GAMMA; L |- B1 and B2 have the covered entries and single-execution property
    GAMMA; L |- activation_demand(B1) <= q1 and activation_demand(B2) <= q2
    GAMMA; L |- new_activation_demand(B1 ; B2) <= q_new
    ===>
    GAMMA; L |- activation_demand(B1 ; B2) <= q1 + q2 + q_new

  J-Sequence-Resource-Demand :=
    GAMMA; L |- B1 and B2 have the covered entries and single-execution property
    GAMMA; L |- resource_demand(B1) <= n1 and resource_demand(B2) <= n2
    GAMMA; L |- new_resource_demand(B1 ; B2) <= n_new
    ===>
    GAMMA; L |- resource_demand(B1 ; B2) <= max(n1, n2, n_new)
```

Each demand bound is an absolute count at the actual attempt, so `n2` must
already account for owners still live after `B1`; it is not merely the number
of owners introduced by `B2`. The sum and maximum are mathematical naturals,
and the separate exclusion rules check the machine limits. A continuation,
handler or outside callable that can invoke a constituent more than once needs
an appropriate iteration bound instead; these rules do not assume one or
restrict future multishot behavior. The checker consumes the constituent
certificates and checks the new composition's relationships without tracing
their implementations again.

For source-handler capture, the current
[capture preparation](../../../src/eval/machine.rs#L4983) first determines
the number `captured_len` of frames to move. At the capacity check, the
configured capture-capacity alternative has guard
`checked_add(captured_cells, captured_len) fails or the sum > capture_limit`.
On the complementary capacity case, reservation can still fail before the
frames are moved and the accounting is updated. Work and invalid-control
failures have their own cases. A bound on cell owners is not a bound on these
captured frames; the required demand includes both the already counted
captures and the new segment. Restore and discard have their own preparation
and accounting conditions, so proving this capture check safe does not prove
them safe.

### Bound control preparation and work

The implementation also checks a representational limit before some control
reservations. For [`reserve_control`](../../../src/eval/machine.rs#L5560),
let `n` be the current vector length, `d` the additional requested entries,
and `max_T` the largest representable count for its element type. The
configured-capacity guard is `d > max_T.saturating_sub(n)`. For nonzero-size
elements, `max_T` is `isize::MAX / size_of(T)`; for zero-size elements it is
`usize::MAX`. Proving the complementary inequality at that particular
reservation excludes this guard only. It does not establish that the later
allocator reservation succeeds, whose reported cause can remain undetermined.

The new composition can derive `d` from its certified capture or close-plan
size and retain the actual storage length and element representation as
assumptions. In the current implementation, capture reserves the size of the
selected segment; resume reserves that many active frames and, when effect
tracing is enabled, a trace amount computed from that size. Discard separately
reserves traversal and close storage and active frames from its inspected
frame and owner counts. Each reservation is a separate guarded case with its
own vector and actual program point. The counts must cover nested owned
captures, and tracing assumptions must match the active configuration.
Preserve the actual checked or saturating arithmetic used by each operation;
an abstract source nesting depth alone is not the required bound.

Work is a different finite resource. A certified behavior may state a bound
on the total work charges over the relevant execution prefixes under its
entry and surrounding-context assumptions. Composing it with a new transition
adds that transition's charges and accounts for earlier charges from the same
ledger. For example, current capture charges for the active frame count;
discard charges for inspected captures and its close preparation. Generic
cell access can charge for a copied integer's magnitude or a callable's origin,
and for other preparation. Such facts need the actual size or an established
upper bound; the payload's ordinary polymorphic type is not one. A sufficient
work bound must fit the actual remaining budget at each charge. It rules out
work exhaustion only, not control-vector limits, allocation, malformed
control, or disposal. Source-handler pattern matching also has preparation
and reservation cases; it must not be charged to this ledger unless its
actual path does so.

In the current [source-handler selection](../../../src/eval/machine.rs#L4654),
the matching clause's bindings extend its saved handler environment before
capture. Each extension checks the environment length for overflow. An
established bound `b` on the actual pattern bindings and saved length `n`
with representable `n + b` excludes those particular length-overflow
failures. It does not establish successful pattern preparation, other
allocation, trace reservation or capture. The count belongs to this selected
clause and its saved environment, not to an unrelated handler or call.

### Instantiation, reservation and cumulative work propositions

Cell acquisition extends the current lexical instantiation before publishing
the cell. The current
[`Instantiation::acquire` and `apply_in_phase`](../../../src/eval/instantiation.rs#L123)
first compute counts for retained type entries, retained row entries and new
arguments; charge their sum; and reserve two new maps. They then copy the
previous bindings, charge for each parameter, and substitute the new
arguments. Each operation has its own ordered work, storage and invalid-control
cases. The acquired instantiation is prepared under a fresh activation but is
not yet published as a cell if a subsequent preparation fails. Earlier work and
successful reservations are not rolled back. Dropping partially prepared
metadata can itself contribute a disposal case.

For a reached `apply_in_phase`, let `p` and `r` be the actual numbers of
previous type and row entries, and `a` and `b` the numbers of new type and row
arguments. The implementation checks, in order, that `p + a`, `r + b`, and
their sum are representable by `usize`; it charges that final sum before the
two map reservations. This is a count of requested entries, not necessarily
the final number of distinct keys after replacement. For a cell's `acquire`,
`a = 1` and `b = 0`, even when a recursive execution shadows a prior binding
of the same lexical identity. The first charge is therefore `p + r + 1`,
when the checked additions succeed. It does **not** include the later copying
and substitution charges.

The exact effect instance is then instantiated using
[`Instantiation::effect`](../../../src/eval/instantiation.rs#L387). With `n`
actual effect arguments it checks `n * 2`, charges that amount, reserves an
argument vector, substitutes each actual Type or Row argument, and reserves a
second retained vector. Each substitution may perform further work and
storage reservations. Generic `Ops<R,T>` has two arguments, so its initial
charge is four when this phase is reached; building the instance before this
call, the two vector reservations, and substitutions are separate. Kinds,
row lacks, argument arity, lexical activation binding and correct full effect
identity remain the corresponding established typing and control premises.
Neither a work bound nor the fact that the API is generic proves them.

The following rules exclude the **checked arithmetic** failures at these
particular phases. `reach_i` and all counts refer to the same actual invocation
and state, under the same substitutions and guard. The premises are universal
over the cases represented by the certificate.

```sequent
family instantiation-count-exclusions:
  J-Exclude-Instantiation-Entry-Overflow :=
    GAMMA; L, entry |- reach_i(w0, s, z) implies p, r, a, b are the actual apply_in_phase counts at s
    GAMMA; L, entry |- reach_i(w0, s, z) implies p + a, r + b and p + a + r + b are representable by usize
    ===>
    GAMMA; L, entry |- this apply_in_phase cannot fail its three entry-count additions

  J-Exclude-Effect-Argument-Overflow :=
    GAMMA; L, entry |- reach_i(w0, s, z) implies n is the actual effect argument count at s
    GAMMA; L, entry |- reach_i(w0, s, z) implies n * 2 is representable by usize
    ===>
    GAMMA; L, entry |- this effect instantiation cannot fail its argument-count multiplication
```

For a successfully reached generic cell instance, its established effect
declaration gives `n = 2`, so `J-Exclude-Effect-Argument-Overflow` discharges
that multiplication without inspecting the payload type. The entry-count rule
does not exclude either map reservation, a later argument substitution, work
exhaustion or disposal. An applicable operation may inherit previous bindings
from its environment; a bound only on the current resource declaration is not
a bound on `p` and `r`.

Each of these counts can feed a work certificate. Write `WorkBound(B,w0,W)`
when, for every execution prefix represented by the certified behavior `B`
from `w0`, the mathematical sum of all **attempted** charges to this particular
ledger during that prefix is at most `W`. It includes the charge that would
otherwise fail, requests and their interpreted residuals, and applicable
outside behavior that can run before the stated exit. This is an established
conditional bound, not a cost inferred from an ordinary type. It does not
cover a different ledger or a host allocation unless their own contracts say
so. A finite `W` need not exist for a recursively repeating or divergent
behavior.

The following composition uses the already certified child bounds. `W_step`
covers only charges introduced by the new sequencing or boundary transition;
it excludes charges already counted in either child. Each second-child bound
is instantiated for the actual correlated normal result and state of the
first, and its assumptions include all intervening interpreter behavior.

```sequent
family cumulative-work-bounds:
  J-Work-Bound-Sequence :=
    GAMMA; L, entry |- WorkBound(B_1, w0, W_1)
    W_1 covers cumulative B_1 work across every entry and resumed residual represented by this sequence activation
    for each covered normal exit (v, s, d) of B_1, GAMMA; L, exit(v,s,d) |- WorkBound(B_2(v,s,d), s, W_2)
    GAMMA; L, entry |- WorkBound(new sequencing and its applicable boundary work, w0, W_step)
    this represented sequence activation enters B_2 at most once, including through suspended and resumed control
    the three bounds cover every charge on this ledger without omitting or counting a charge twice
    W = W_1 + W_step + W_2
    ===>
    GAMMA; L, entry |- WorkBound(sequence(B_1,B_2), w0, W)

  J-Exclude-Work-Bound :=
    for every covered entry w0, GAMMA; L, entry(w0) |- WorkBound(B, w0, W)
    for every covered entry w0, used(w0) + W is representable and <= limit(w0)
    the same ledger and limit remain in force throughout B
    ===>
    GAMMA; L, entry |- no covered charge of that ledger during B fails from work exhaustion
```

The `W_1` premise is a cumulative bound across all represented entries and
resumptions of the initializer, not a separate allowance for each one. The
at-most-once premise counts entries of this particular remainder, not
occurrences of the source location in other activations. If an applicable
interpreter can resume the same continuation more than once, a single
per-entry `W_2` is insufficient; use an established bound on the cumulative
work of all its entries instead. This leaves future multi-shot behavior
conditional on its own bound rather than assuming one-shot use.

The sequence bound covers failures and non-returning prefixes of `B_1` as
well as normal entry to `B_2`; no return from `B_1` is assumed. Alternative
covered branches can use an established maximum over their individual bounds,
while an unknown branch retains its obligation. The result is a sufficient
bound: it may be larger than actual work, but must include attempts that would
fail. `J-Exclude-Work-Bound` applies the existing charge rule to every covered
prefix, including prior charges from the same ledger. The evaluator's
`unbounded` work configuration still uses a finite `usize::MAX` limit and
checked addition; its name does not prove an unlimited execution cannot
exhaust the ledger. A separate ledger, changed limit, failure teardown or
uncovered native operation needs its own contract.

Storage reservation is a different proposition. For a reached particular
reservation call `r` in phase state `s`, let `ReserveSucceeds(r,s)` mean that
the **actual** reservation operation, including its applicable container and
allocator behavior, returns success for the actual storage, requested amount
and configuration. It is an assumption or a fact proved by an applicable
host/container contract; merely introducing this proposition does not prove
it. In particular, direct `try_reserve` calls in cell and cleanup acquisition
map an error to `StorageReservationFailed` without distinguishing a capacity
limit from allocator refusal. `reserve_control` has the separate checked
representational guard described above, but its subsequent reservation
failure can still have an undetermined cause. Neither case may be relabelled
as an external event simply because storage comes from a host allocator.

```sequent
J-Exclude-Reservation-Failure :=
  GAMMA; L, entry |- reach_i(w0, s, z) identifies the actual reservation r and phase state s
  GAMMA; L, entry |- reach_i(w0, s, z) implies ReserveSucceeds(r,s)
  ===>
  GAMMA; L, entry |- this reservation cannot return a storage failure
```

For a `reserve_control` call, its own count guard must also be excluded before
the subsequent container reservation is reached. A host promise is scoped to
the actual container, capacity, request, allocator configuration and state;
one successful earlier reserve does not prove a later or larger reservation.
A producer may publish a conditional reservation contract or an established
capacity fact from the initial check. A new composition proves its own call
preconditions and reuses that contract without opening the producer. If no
applicable promise is supplied, the failure remains a guarded obligation. In
particular, `Arc::new` and other infallible allocation paths are not made into
recoverable reservation results by this rule; their exact host behavior and
the relationship to the no-error target require separate justification.
Reservation success also does not prove that prior or later disposal succeeds.

### Derive reservation success from retained capacity

Some vector reservations need no host allocation at all. For the actual
`Vec` at the actual reservation point, let `len` and `cap` be its established
length and capacity, and let `d` be the requested additional elements. The
container's `try_reserve` and `try_reserve_exact` contracts leave the vector
unchanged and return success without growing when `d <= cap - len`. This
requires the valid-container invariant `len <= cap`. These are facts about the
particular storage object in state `s`; a capacity of a different vector or an
earlier capacity without a preservation fact does not establish them.

```sequent
J-Reserve-Within-Vector-Capacity :=
  GAMMA; L, entry |- reach_i(w0, s, z) identifies this actual vector v and request d
  GAMMA; L, entry |- reach_i(w0, s, z) implies len(v,s) <= cap(v,s)
  GAMMA; L, entry |- reach_i(w0, s, z) implies d <= cap(v,s) - len(v,s)
  ===>
  GAMMA; L, entry |- ReserveSucceeds(the direct vector reservation, s)
```

For a call to `reserve_control`, also apply the already established
`J-Exclude-Control-Vector-Limit` to its preceding representational check and
account for any enabled test fault injection. Do not run the vector proof a
second time. Successful capacity is a postcondition of an earlier reservation;
intervening pushes, other mutations and disposal change what it can establish
at a later one. A certificate for the new composition relates those changes to
the particular vector; it does not reopen the producer. This rule excludes
only that reached vector reservation, not a later `Arc::new`, a map reservation
or other host action. The container contract is evidenced by the installed
Rust `Vec` API and must be part of the implementation correspondence for this
candidate rule.

The actual in-slice sites have different subjects and demands:

| Preparation | Vector and demand at that point | Reusable fact and limit |
| --- | --- | --- |
| Source-handler capture | A fresh empty capture vector reserves the selected physical length `l`. | An exact source selection includes its handler, so `l > 0`; empty-vector slack cannot prove this reservation. Its capacity and allocator behavior need their own justified contract. |
| Resume | Active frames reserve `l`; enabled trace separately reserves `l.saturating_add(1)`. | Apply the capacity rule independently to each actual vector and request after any earlier phases; captured accounting is a separate invariant. |
| Discard | Fresh inspection vectors grow during the scan; after it, fresh work and closing vectors reserve `q` and `o`, and active frames reserve `o.saturating_add(1)`. | Each successful reservation establishes only its own vector capacity. A bound on owner count does not prove slack in a fresh vector. |
| Cell acquisition or cleanup acquisition/start | The actual active-frame vector reserves one; cell acquisition may also reserve one enabled trace entry. | Existing frame or trace slack can discharge its own call. Instantiation, action/callback preparation and disposal still have independent cases. |
| Generic cell read/write | Enabled trace reserves two before the read reply or root replacement is committed. | A trace-capacity fact can discharge that reservation. Value copy, alias resolution and work have their own guards. |
| Generic effect instantiation | Two fresh vectors each reserve the two `Ops<R,T>` arguments. | Both start empty and their nonzero requests need separate growth contracts; a bound on `T` or work alone does not establish either reservation. |
| Source-clause pattern | Fresh pattern work and binding vectors reserve according to the actual pattern traversal. | The certified pattern may supply a bound; every actual reservation needs a corresponding capacity or growth contract. |

The use of an actual host growth contract is narrower than assuming
`ReserveSucceeds` for the whole operation: it must cover the allocator request
made after the container's internal layout and growth calculations have been
established valid. Those internal calculations and representational limits are
internal obligations. If the implementation cannot distinguish an internal
capacity failure from allocator refusal, retain the undetermined failure unless
both applicable cases are excluded. Direct `HashMap::try_reserve` in lexical
instantiation needs its own container contract; a `Vec` capacity fact does not
apply to it.

### Instantiate with the actual argument and row facts

The immutable lexical instantiation and the actual argument vectors are
correlated with one reached operation. A checked scheme carries its ordered
parameter kinds, substitutions and row constraints; a caller supplies the
actual instantiation facts at the boundary. The existing substitution result
is reused instead of rechecking the generic function or type expression.
The following rule addresses the iterator-shape checks in
[`apply_in_phase`](../../../src/eval/instantiation.rs#L224), not its earlier
count, work or reservation failures and not errors from substituting an
individual argument.

```sequent
J-Instantiation-Argument-Shape :=
  GAMMA; L, phi |- the actual parameters have n_type non-EffectRow kinds and n_row EffectRow kinds
  GAMMA; L, phi |- the same checked application supplies exactly n_type type arguments and n_row row arguments
  GAMMA; L, phi |- the actual runtime parameter order is the certified order
  ===>
  GAMMA; L, phi |- apply_in_phase cannot fail from a missing or leftover argument
```

For cell acquisition the producer is concrete: the one parameter has kind
`Type`, the one argument is the runtime atom for this actual fresh activation,
and the row-argument vector is empty. Thus this particular shape check is
discharged even if a previous invocation used the same lexical binder. The
earlier counts still include previous entries, and the argument's work and map
storage remain separate. The generated effect instance is `Ops<R,T>` at the
same actual activation and payload type; its declaration gives two kinded
arguments, so the `2 * n` work charge begins with `4`. This does not imply that
substituting an abstract `T` or nested rows costs four in total.

For the specific
[`substitute_owned_tail_for_reconstruction`](../../../src/types.rs#L1057)
check, the following fact excludes the two row errors it tests. `rho` is the
actual target tail, `lacks` its actual substituted exclusions, and `eta` the
actual replacement in this invocation. Equality compares complete effect
instances after the relevant lexical substitutions; an unknown equality is not
inequality. The result does not exclude work or storage errors in comparing or
rebuilding the row.

```sequent
J-Row-Reconstruction-Guard :=
  GAMMA; L, phi |- the reached row tail is not rho, or eta is the identity row with only tail rho
    or eta's tail is not rho and every known member of eta differs from every member of lacks
  GAMMA; L, phi |- those facts hold for the actual substituted instances and this reached check
  ===>
  GAMMA; L, phi |- this reconstruction cannot report its Infinite or Missing row guard
```

The row and kind certificates supply these facts only where their actual
constraints imply them. An unresolved tail, a possible generic coincidence,
or a different row-substitution helper retains its conditional case or
obligation. In particular, this local rule is not a proof that all nested
substitutions succeed. Establishing that the checked Core substitution and its
runtime representation correspond is a system proof; a checked use consumes the
same certified substitutions and does not rerun that proof for the program.

### Callable and payload-copy cases

Cleanup acquisition looks up the callback bound by the source-to-Core cleanup
lowering and invokes `read_callable` only to check it; its action runs later.
The [direct callable branch](../../../src/eval/region.rs#L694) returns a clone
when the actual value is `Value::Function`. It does not consult the work ledger
or return a structured lookup error in that branch. The callback-binding fact
comes from the preceding certified binding; the actual value representation,
lexical environment and any backing validity come from its value contract.
This is not an instruction to typecheck the callable's body again. A missing
binding or wrong value representation stays a malformed-control case unless
those separate facts exclude it. Infallible `Clone` may still use host
allocation for nontrivial origin metadata; the no-error claim needs its
applicable platform/host contract and cannot be inferred from the absence of a
`Result` error.

A region-backed callable takes a different path: it resolves the actual
location or view, verifies the code descriptor, field count and capture
descriptors, charges for fields and extends an environment for its captures.
Its region/backing validity and descriptor representation are excluded-boundary
inputs; each charged or fallible step has its own work, storage and invalid
representation case. The action contract obtained after acquisition describes
later invocation, including requests and failures; successful lookup does not
prove that invocation returns.

For a generic cell's immediate `Unit`, `Boolean` or `SmallInteger` root or
replacement, [`copy_generic_cell_value`](../../../src/eval/machine.rs#L5627)
charges exactly one work unit and returns the same immediate value. The rule
uses the established current root or replacement, not merely its generic type.
The copy helper is reached only after the preceding access phases have passed.

```sequent
J-Copy-Immediate-Cell-Value :=
  GAMMA; L, phi |- the actual reached value v is Unit, Boolean or SmallInteger
  GAMMA; L, phi |- the actual ledger at s can charge one unit
  ===>
  GAMMA; L, phi |- the cell copy helper returns v and the ledger is charged once
```

The rule excludes failure **inside that helper** for those representations;
selection, trace reservation, later disposal and the rest of the operation
still have their own cases. A large `Integer` may require a magnitude-dependent
charge and a representable size. For a direct function with inline
`Origin::Source`, the origin-copy helper adds no origin traversal or
reservation after the initial copy charge, subject to the ordinary shared
handle and host contract. Generated or related origins are different:
[`clone_effect_origin_with_budget`](../../../src/resolved.rs#L17754) can fail
either its work charge **or a vector reservation**, but the cell helper maps
both to its work-exhaustion report. Therefore a work bound alone cannot rule
out every reported work-exhaustion event for such a callable. Preserve the
underlying storage obligation and the actual failure-state correlation; do not
classify the event solely by its reported cause.

#### Produce an immediate-root disposal fact

The following case gives a concrete producer for part of the disposal
guarantee, without inspecting a polymorphic payload type. Write
`Immediate(v)` when this actual runtime value is `Value::Unit`,
`Value::Boolean(b)`, or `Value::SmallInteger(n)`. These variants contain only
their immediate fields: dropping the value does not invoke a `Pending`
worklist or record an internal disposal failure. This is a representation
fact about the particular value, not a claim about all values of its source
type. It can be published by the certified value producer: for example, the
Core [Boolean and Unit constructors](../../../src/eval/machine.rs#L5756)
return the corresponding immediate variants. A certified immediate copy
preserves the same fact by `J-Copy-Immediate-Cell-Value`.

```sequent
J-Immediate-Cell-Root-Replacement :=
  GAMMA; L, phi |- the actual selected generic cell's current root is old
  GAMMA; L, phi |- Immediate(old) and no disposal failure is pending at s_before
  GAMMA; L, phi |- the same builtin write has completed its fallible preparation at s_before
  GAMMA; L, phi |- this assignment replaces old by the prepared replacement and reaches s_after
  ===>
  GAMMA; L, phi |- the cell root at s_after is that replacement and no disposal failure is pending at s_after
```

The premise identifies the **old** root at the commit point. The acquisition,
write and capture/restore certificates carry its actual root fact as control
moves; an intervening write must supply its own updated fact. The
[specified write](../../../spec/dynamic-semantics.md#scoped-cell-execution)
replaces the selected cell's root; this candidate fact addresses one
implementation-side disposal condition of that step. The
[generic-cell write](../../../src/eval/machine.rs#L4940) drops the old `Value`
as part of root assignment after copy, work and trace reservation preparation.
[`Value`](../../../src/eval/value.rs#L584) has no custom destructor, and
these three variants have no owned fields whose destruction can use the
disposal worklist. Therefore their drop leaves the first-failure state clear.
This excludes only a disposal failure caused by dropping that old root. It
does not exclude a failure already pending before assignment, earlier
preparation failure, later disposal, or disposal of the cell's separate
instantiated metadata on release. If the actual old representation is not
established, retain its disposal contract or failure case.

### Disposal state and final observation

The disposal scope keeps a first pending failure, not an implicit guarantee
that cleanup completed. At an active
[`disposal::check`](../../../src/eval/disposal.rs#L94), a pending failure is
reported; absence of one permits that check to return. This is a local state
test, not proof that later destruction will not set one.

```sequent
family disposal-check-cases:
  J-Disposal-Check-Clear :=
    GAMMA; L, phi |- the actual active disposal state at s has no pending failure
    ===>
    GAMMA; L, phi |- disposal_check(s) returns normally

  F-Disposal-Check-Pending :=
    GAMMA; L, phi |- the actual active disposal state at s has first pending failure f
    ===>
    GAMMA; L, phi |- disposal_check(s) reports f with incomplete teardown
```

For an active `Pending` worklist, a push with no pending failure uses an
available inline slot when its spill is empty, otherwise uses already reserved
spill capacity if available. A full spill requires the actual growth contract:
in a no-growth mode it records configured capacity failure; otherwise its
fallible vector reservation can record an undetermined storage failure. Once a
first failure is pending, later pushes abandon their item and do not prove
successful teardown. `Pending::new` starts with eight inline slots; a captured
continuation's `Pending::from_vec` instead starts with its actual existing
spill vector. The earlier `J-Exclude-Inline-Disposal-Growth` covers only the
fresh-worklist case and its stated prospective bound.

The result of [`Scope::finish`](../../../src/eval/disposal.rs#L37) depends on
the state **after** the machine has dropped its retained state inside the
scope. With no pending disposal failure, a normal result remains normal. With
a pending failure, a normal result is dropped and the first failure is
reported with incomplete teardown. For an existing primary error, a different
pending disposal failure is attached as an incomplete-teardown error only if
the report has no teardown error already; an existing teardown error is
retained. If the whole primary error equals `report(first)`, the scope returns
that error unchanged; matching only the underlying cause is not enough. If no disposal
failure is pending, an existing structured report is marked complete. These
cases preserve the primary reason and any existing teardown entry; the pending
failure is attached only where stated. They do not invoke source cleanup or
undo a cell replacement, consumed capture, or earlier effects.

The scope and worklist cases are only part of a complete disposal contract.
Each dropping operation must supply the actual last-owner and reachable
worklist bounds, including metadata, environments, frames and nested owned
captures. A shared value may become uniquely owned after another owner is
dropped; a static value type or an earlier sharing fact does not fix that
later state. `Pending::from_vec` and any unmodelled host destructor need their
own contracts. An unspecified case remains a failure obligation, including
when it happens after the source operation's successful state change.

For a covered set, the following rule discharges the in-slice failure
alternatives only when each guard is inconsistent with the established
assumptions. `L` contains only established stable facts, `entry(w0)` records
the entry assumptions, and the freshly scoped entry worlds and witnesses are
universally quantified in each case premise. `wf` ranges over the entire
failure-observation domain, including the no-post-state marker. The symbolic rule does not
enumerate runtime executions or replay a constituent's verification.

```sequent
J-No-Internal-Error :=
  GAMMA; L, entry |- covers_failures(B, Cases) [O_cover]
  for each (phi, f) in Cases,
    GAMMA, w0, wf, z; L, entry(w0), phi(w0, wf, z) |- false [O_case(phi, f)]
  the coverage and contradiction evidence is non-circular with respect to this no-error conclusion and each discharge it uses
  O_no carries O_cover and every O_case under its original scope; case-local obligations quantify their own w0, wf and z under the same entry and guard
  ===>
  GAMMA; L, entry |- no_internal_error_in_slice(B) [O_no]
```

For a finite case this may use ordinary equality, owner-state, row or resource
facts. A proved empty cover makes the case premises vacuous; an unknown cover
does not. The conclusion remains conditional on `O_no`: in particular, a
conditional projected cover does not become an unconditional no-error fact.
Inherited unconditional structural obligations retain their original scope;
they are not made conditional on reaching a failure case. For recursive
behaviors the rule requires a sound finite recursive
argument or other established evidence of coverage and guard elimination. A
recursive safety fact requires a justified well-founded or guarded
finite-prefix argument, or a separately stated and discharged recursive
assumption; a cycle that assumes its own no-error conclusion is not evidence.
The rule does not assume that the checker decides arbitrary reachability. If any failure
guard cannot be ruled out, `no_internal_error_in_slice(B)` is not established. A
separate conditional obligation may be retained only if its assumptions remain
visible; an unconditional judgment cannot use it.

The ordinary typing and structural usage rules still apply even to code with
no normal return. `J-No-Internal-Error` does not turn a false behavioral
assumption into an ordinary typing judgment or permit a second one-shot use.
It also does not prove that an action, close or whole program terminates.

### One capacity failure

For the configured cleanup-owner limit, a sufficient proposition can be
stated without claiming that all allocation or work failures are impossible.
Let `cleanup_demand(B, w0) <= n` mean that the certified behavior, under entry
`w0`, bounds the prospective total at **every attempted acquisition**: the
currently counted live cleanup owners plus the one being acquired. The total
includes owners in surrounding control, captured owners and running actions,
not just new lexical scopes inside `B`. A bound on only successfully acquired
owners is insufficient: an attempt may fail before its owner is published.
The proposition must cover every relevant execution prefix. Let `limit(w0)`
be the actual configured bound and require its stability for that execution.

```sequent
J-Exclude-Cleanup-Owner-Capacity :=
  for every covered entry w0,
    GAMMA; L, entry(w0) |- cleanup_demand(B, w0) <= n
    GAMMA; L, entry(w0) |- n <= limit(w0) and that limit remains valid during B
  ===>
  GAMMA; L, entry |- no_configured_cleanup_owner_capacity_failure(B)
```

This conclusion rules out only that particular configured-owner-limit
failure. It does not establish successful memory reservation, sufficient
work or activation identifiers, external provider behavior, or successful
disposal. The demand fact must itself be established from the certified
constituent contracts and the new composition's owner relationships; a row,
ordinary type or an unchecked annotation is not that fact. Recursive or
unknown behavior can leave it unproved. A type system that cannot establish
the proposition must retain the resulting obligation or use an applicable
specified failure response; it cannot claim this rule's conclusion.

For a concrete derivation, consider a cleanup acquisition reached with `c`
live owners and a stable limit `m`. The surrounding context and the already
certified body and action establish that, until this owner is released, there
are no other cleanup-acquisition attempts; this statement includes any
interpreter or outside control entered while the owner is live. The attempted
acquisition therefore has prospective demand `c + 1`, and there are no later
attempts in that interval. Established arithmetic facts that `c + 1` is
representable and `c + 1 <= m` rule out the configured cleanup-owner failure
for that interval. The rule does not assert that the body or action returns.
When another scope is introduced, the new composition must account for its
attempt and the owners live at that point; it reuses the constituents' certified
bounds instead of tracing their bodies again. Other work, reservation and
disposal cases remain separate.

The live-owner bound is not enough for every configured capacity. The current
[cell acquisition](../../../src/eval/machine.rs#L4270) also advances a bounded
fresh-activation counter. The existing [capacity test](../../../src/eval/machine.rs#L11935)
shows that sequentially released owners free live-owner capacity while their
activation keys remain fresh. The test then explicitly sets the counter to its
maximum and checks that acquisition fails; it does not reach exhaustion by
running the preceding short sequence. The checked increment in the acquisition
code is the evidence for the bound. That fixture was inspected, not run here.

For this particular failure, the needed proposition must cover the
**prospective counter value at each attempted acquisition**, including all
applicable operations that share the counter. It cannot be derived merely from
the maximum number of simultaneously live cells. A fragment that can perform
unboundedly many acquisitions needs either a separately established bound under
its applicable assumptions or a specified response to eventual exhaustion.
Neither an absent bound nor divergence proves that the counter cannot fail.
The exact bound for an opaque caller is a boundary fact or obligation, not a
reason to inspect its body again.

## Composition without rechecking

For a new composition, reuse each constituent's certified failure cover and
any already established `no_internal_error` judgment. The composition rule
must also cover failures caused by the **new interface**: for example, a
newly formed handler selection, capability transfer, resource acquisition,
reply preparation, owned-close plan or binding frame. It checks only those
new compatibility and failure premises. It must preserve the guards and
activation correlations of the constituent cases; it does not inspect the
constituent implementation or replay its verification.

For an ordinary binding, the established initializer cover contributes its
cases. The established conditional remainder cover contributes only under a
covered normal initializer return, with that same result and resulting facts.
Initializer requests keep the binding pending; an abandoned binding frame
does not enter the remainder. New frame and composition failures must be
covered separately. An initial failure can trigger failure disposal; the
contract must retain any later disposal failure and observations rather than
asserting that the original reason is necessarily the final report. The
[sequencing cases](first-slice-sequencing-cases.md#non-return-failure-and-unknown-behavior)
record that outstanding disposal behavior.

The binding's no-error conclusion can reuse its constituents' established
no-error judgments where their stated entry and surrounding-context
assumptions are proved for this composition. `state` and `deps` are fresh
symbolic indices of the one conditional remainder judgment. `New` below covers failures caused by the new binding
frame and composition, including any applicable preparation and disposal
behavior; it does not include failures already covered by either constituent.
The cover-partition premise must establish that all binding failures fall
under the initializer, an actually entered remainder, or `New`. It is a
requirement on the binding rule's failure interface, not an instruction to
inspect those constituents again.

```sequent
J-No-Error-Binding :=
  GAMMA; L, entry |- no_internal_error_in_slice(B_e) [O_e]
  GAMMA, x : A; L, psi(x, state, deps) |- no_internal_error_in_slice(B_s(x, state, deps)) [O_s]
  the certified entry and context assumptions of B_e and B_s hold at their respective composition boundaries, or retain the scoped obligations O_context
  GAMMA; L, entry |- normal_fits(B_e, psi) [O_fit]
  the ordinary, structural and behavioral premises of J-Bind-Behavior hold, retaining their obligations O_bind
  GAMMA; L, entry |- New covers every failure newly introduced by this binding and its failure disposal [O_new]
  for each (phi, f) in New,
    GAMMA, w0, wf, z; L, entry(w0), phi(w0, wf, z) |- false [O_case(phi, f)]
  established failure interfaces cover every binding failure by B_e, an entered B_s, or New, retaining O_partition
  the constituent, coverage and contradiction evidence is non-circular with respect to this conclusion and its discharges
  O_seq carries O_e, O_s, O_context, O_fit, O_bind, O_new, O_case and O_partition under their original scopes and guards; it universally binds the same actual normal-return (x, state, deps) and failure-case witnesses wherever those behavioral obligations depend on them
  ===>
  GAMMA; L, entry |- no_internal_error_in_slice(Seq(B_e, (x, state, deps) -> B_s)) [O_seq]
```

The remainder's no-error judgment is applied only to actual normal returns
whose correlated facts establish `psi`; it does not check the remainder once
per return. Its behavioral obligations stay under those same entry witnesses
and guards; its unconditional typing and structural obligations retain their
original scope. Each failure-proof obligation binds its own entry world,
failure observation and witnesses universally under its actual guard. An
unresolved premise leaves `O_seq` and the conclusion conditional; an
unconditional no-error result requires the applicable obligations discharged.
The new-failure cases must include any failure caused by the
binding's own capacity or preparation requirements. A previously certified
no-error fact cannot cover such a new failure simply because the constituent
was safe. Conversely, the rule does not prove those constituent facts again.
This schema requires a separately justified failure partition and coverage;
it does not assert that current Core supplies one.

### Reuse no-error facts for an in-slice constructor

The following schema covers a newly composed handler, resume, discard, cell
or cleanup constructor. It uses each child's existing *conditional* no-error
certificate. `B_i(alpha)` is the certified behavior of child `i`, indexed by
its own entry facts, local witnesses and applicable surrounding-control
assumptions `psi_i(alpha)`. `B_new` is the constructor's already established
complete behavior composition. `New` covers every failure introduced by this
constructor and its interfaces, including applicable internal disposal after
either a child failure or a new failure. It does not stand for a new traversal
of the children.

An entry fit relates each reached child entry to its own `psi_i` using the
actual correlated value, state, dependencies, lexical instantiation and owner
placement. A reentry or reply fit does the same for a suspended child and its
certified residual under the *same* request, selected boundary, actual reply
and post-reply state. The constructor's established case interface must cover
all applicable entries, reentries, replies and outside-boundary behavior;
an unresolved residual or an opaque outside contract is not an empty case.

```sequent
J-No-Error-Constructor :=
  for each child i and its symbolic entry alpha,
    GAMMA_i; L_i, psi_i(alpha) |- no_internal_error_in_slice(B_i(alpha)) [O_i(alpha)]
  GAMMA; L, entry |- B_new is the established complete behavior composition of these child contracts [O_behavior]
  the child, recursive, coverage and contradiction evidence is non-circular with respect to this conclusion and its discharges
  for each covered actual child entry, reentry and admissible reply, the same case's facts entail the corresponding child or residual entry and context assumptions, retaining O_fit
  every applicable outside boundary has a certified no-error contract and its assumptions hold for the same case, retaining O_outside
  GAMMA; L, entry |- New covers every constructor-introduced internal failure and applicable subsequent internal disposal failure [O_new]
  for each (phi, f) in New,
    GAMMA, w0, wf, z; L, entry(w0), phi(w0, wf, z) |- false [O_case(phi, f)]
  the established composition interface covers every internal failure by an entered child or its residual, an applicable outside contract, or New, with the same guards and witnesses, retaining O_partition
  O_result carries O_i, O_behavior, O_fit, O_outside, O_new, O_case and O_partition under their original scopes and guards; it universally binds each applicable child entry, reentry, reply and failure-case witness wherever those behavioral obligations depend on it
  ===>
  GAMMA; L, entry |- no_internal_error_in_slice(B_new) [O_result]
```

Each child and outside behavioral obligation retains its same actual entry,
reply and case witnesses; failure-proof witnesses are universally scoped under
their own entry and guard. Inherited unconditional typing and structural
obligations retain their original scope. If an outside contract or assumption
is unresolved, the conclusion remains conditional on that scoped obligation;
it cannot establish unconditional no-error. Failure coverage must account for every
applicable activation, including later child entries and residuals after
requests. For a recursive or unbounded family, a separately established
inductive or recursive interface must cover those entries and preserve the
fit, with the justified finite-prefix evidence required above. This rule does
not assume the desired conclusion as its own premise. An
unknown failure in `New` stays possible unless its guard is actually
contradictory. A missing child, reply or disposal cover remains an obligation.

The partition assigns a failure to its actual subject; it need not assert
that the partitions are disjoint. For example, the selected handler's
certified clause supplies its own failures under the fresh clause entry,
while request selection and capture preparation belong to `New`. A generic
cell uses the initializer and body certificates at their respective entry
cases; its acquisition, builtin operation and release failures belong to
`New`. The same applies to an action only when that actual action is entered.
If a request is abandoned, no reply or resumed child entry is invented. The
schema proves neither successful return nor eventual cleanup, and cannot
eliminate a child's error by inspecting or verifying the child again.

For a cell acquisition, the successful rule requires actual preparation to
succeed before publishing the owner. Its failure alternative must be ruled out
by applicable established evidence or handled by a revised specified
semantics. The same distinction applies to close preparation and to each later
potentially failing close action. A proof that a plan is structurally safe does
not prove that storage preparation succeeds or that the action terminates.

## Agreed admission rule for the first slice

Use the first route below for this slice: a closed program receives the
no-error conclusion only after every applicable internal-failure case has
been ruled out by established type-system facts under its stated assumptions.
An opaque fragment may remain certified with explicit obligations, but a use
that needs its no-error conclusion must establish them. A closed program cannot
treat an unresolved guard as a successful proof. This agreed design strengthens
admission. It is not current Ash semantics, a claim that the current checker
already does it, or a change to current runtime outcomes. A language change
proposal and its required evidence are needed before implementation.

For an internal configured limit, its obligation must relate the complete
applicable execution demand to that limit; it cannot be discharged by calling
the limit external. A host allocation contract may state an actual promise
about host reservations. A failure of that promise can be an external event only
under the explicitly stated contract; a result that conflates host refusal and
an internal representational limit needs evidence covering both possibilities.
The proof and assumptions must be retained at the boundary at which they apply.
No rule assumes that all such evidence can be inferred: an otherwise safe
program can be rejected or retain an obligation when a required bound cannot
be established. In particular, a live-owner peak alone cannot discharge a
monotone activation-key or cumulative-work bound.

There are two distinct ways for a particular failure alternative to stop
contradicting the target:

1. Establish, in the type-system judgment and its discharged assumptions,
   that the failure guard is impossible. For capacity or work failure this
   requires actual evidence relating the relevant execution demand to the
   available capacity, preparation and allocation guarantees. A row, ordinary
   value type or one-shot ownership fact alone does not establish that bound.
2. In a later semantic proposal, specify a different response in which the condition is an explicit typed
   outcome or effect with a defined continuation and resource behavior. This
   is a semantic change, not a reinterpretation of the current terminal
   internal failure. Its own typing and composition obligations must be
   specified and justified.

An actual external event may violate an explicitly stated external assumption;
the semantics must identify the event and Ash's response. This does not make
an invalid owner, failed internal invariant or configured capacity limit an
external event merely by naming it one. The displayed conclusion covers only
the slice's failure universe. A whole-program no-error conclusion also needs
the established failure covers and no-error facts or discharged obligations
for every applicable outside boundary, under the final stated assumptions.

The first route is the agreed admission choice here. The second is an
alternative if later work changes the specified response; it is not silently
assumed by the rules. The rule above resolves how a proven failure cover is
consumed; it does not produce covers for every operation, prove capacity
sufficient, or prove the system sound. The current specification and
implementation therefore do not yet establish DN-0060's no-error target under
its stated conditions.
