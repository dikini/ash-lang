# Effect Core alignment evidence

This comparison is governed by [DN-0033](../../DN-0033-direct-effects-and-continuation-capabilities.md)
and organized by [TASK-0032](../../../tasks/TASK-0032-core-one-shot-alignment.md).
It is experimental evidence, not the Ash specification. No general Core
admission or execution simulation theorem is established yet.

## Baseline

The inspected product baseline is `124e164`. The current annotated calculus
constructs initial admission through
[InitialAdmission.Program](SourceScheduledInitialAdmission.lean) and preserving
bounded execution through [M4](SourceScheduledM4.lean). These results do not
prove that a validated Core graph supplies the initial admission fields, or that
an arbitrary raw annotation choice preserves typing. Earlier open obligations
in KERNEL.md describe earlier models; the final M0–M4 sections and endpoint code
determine this baseline.

Core independently validates typed nodes, exact rows, declaration identities,
scope and capture/completion relationships. Its accepted representation is a
finite acyclic arena. Runtime closures retain Core code and explicit environments;
the heap stores tuple/constructor cells and recursive aliases. Captured frame
vectors own resources and nested live continuations. These representation facts
come from [Core](../../../../src/core/dialect.rs),
[validation](../../../../src/core/validate.rs) and
[the evaluator](../../../../src/eval/machine.rs), not from the calculus.

## C1.1 intended comparison boundary

The target is an explicitly checked monomorphic one-shot fragment containing
unit, Boolean and integer values, variables, binary products, nonrecursive
functions and application, sequencing, Boolean branching, exact operations,
handlers, resume, discard, scoped cells and cleanup. Functions retain their
lexical environments and resource support. Higher-order resource support remains
an admission obligation; this boundary is not a claim that it is already solved.

The input must be independently validated Effect Core. Admission must also
check membership in the declared fragment and authenticate any added finite
annotations. Rejecting an unsupported construct is a translation limitation,
not a source-language error. The first vertical fixture cannot by itself define
or certify this boundary.

| Feature | Intended treatment and outstanding obligation |
| --- | --- |
| Scalar values, variables, nonrecursive binding/functions/application | Direct structural translation; environment/closure substitution needs a runtime relation. |
| Binary tuples and Boolean matches | Translate to pair and branch; authenticate pattern and branch coverage. Heap-backed Core tuples require a value relation. |
| General tuples, constructors, arbitrary patterns, arithmetic | Outside the direct initial calculus grammar. Any required normalization or calculus extension must be proved and added explicitly. |
| Nonrecursive global entry wrappers | The first linked fixture has a single-member `RecursiveBind` for nonrecursive `main`, an entry application and a Unit-pattern match. Justify finite expansion and match erasure; these wrappers are present in actual Core. |
| General recursive bindings | Excluded from the initial declared fragment; no current recursive-expression calculus constructor. |
| Exact parameterized effects | Preserve defining effect/operation identities and complete closed arguments; resource arguments instantiate with fresh activations. |
| Polymorphism | Open polymorphism is outside the initial fragment. Closed specialization and sealed builtin wrappers still need explicit instantiation/erasure evidence. |
| Synchronous hooks | General registration owners and pending callbacks are outside the initial fragment. Ordinary handler lowering alone does not prove their coverage. |
| Native buffers | Outside the initial fragment. Cell ownership does not establish native allocation, failure, payload or release behavior. |
| Multishot, escaping continuations, suspension, asynchronous hooks | Explicitly excluded by the objective. |

These exclusions classify the initial comparison target. They do not change Ash
or permit reducing the required handler/request/sequence/resume/discard/cell/
cleanup coverage to whatever examples pass.

## C1.2 cleanup during discard

Current [dynamic semantics](../../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
removes captured source handlers from owned close control. Current
[static semantics](../../../../spec/static-semantics.md#scoped-cleanup-actions)
rejects cleanup when its nearest interpreter at the closing position would be a
removed source or generated handler. A farther same-instance handler or builtin
provider cannot replace that candidate.

The calculus's [lexical discard](SourceResourceRoutes.lean) retains the captured
stack and unwinds it. It removes each handler only when traversal reaches that
handler. `LexicalUnwind.DisposalExample.execution` records this explicit sequence:

1. Consume the outer ticket and enter captured-stack unwind.
2. Start the armed cleanup callback.
3. Apply its lambda.
4. Its request captures the still-retained inner source handler.
5. The inner clause resumes.
6. The callback finishes.
7. Unwind removes the inner handler.
8. Unwind removes the consumed inner clause.
9. Unwind removes the outer handler.
10. Finish the close operation.
11. Return through the consumed outer clause.

This raw-machine difference is not an accepted-Core disagreement:
[SourceCleanupRoutes.initial_program_rejected](SourceCleanupRoutes.lean)
rejects the corresponding source shape under the stricter compatibility rules;
`outside_copy_rejected` proves that adding an outer copy does not repair it.
Executable [Core regressions](../../../../tests/core_alignment_cleanup.rs)
establish the following comparison:

| Fixture | Observation |
| --- | --- |
| [Minimal removed handler](fixtures/core-cleanup-removed-handler.ash) | `effect.row-union-ambiguous`: the outward cleanup-row gate rejects it first. |
| [Outside copy](fixtures/core-cleanup-outside-copy.ash) | `effect.cleanup-context`: supplying the outward row isolates the forbidden nearest-interpreter replacement. |
| [Surviving handler](fixtures/core-cleanup-surviving-handler.ash) | Returns Unit; cleanup selects the surviving interpreter. |
| [Passed body handler](fixtures/core-cleanup-passed-body-handler.ash) | Returns Unit; a handler passed before the closing position does not replace the cleanup interpreter. |
| [Nested discard](fixtures/core-cleanup-nested-discard.ash) | Returns `70213`; cleanup records 2 then 1, then the clause records 3. Three cell owners release in reverse acquisition order. |
| [Nested resume](fixtures/core-cleanup-nested-resume.ash) | Returns `424213`; resumed body records 4 before the same cleanup and clause order. |
| [Restored clause suffix](fixtures/core-cleanup-restored-clause-suffix.ash) | Returns `11`; actual Core node entries invoke write applications with operands `[7, 11]` and skip `99`. |

The last fixture contains all requested kernel constructs. Its 55 reachable Core
nodes include a single-member nonrecursive `RecursiveBind` entry wrapper, Unit
and Boolean matches, and callable cell read/write helpers. There are no type
abstractions/applications, primitive operations or registrations in this graph.
The wrapper and builtin-helper correspondence remain proof obligations.

The candidate bridge retains Core's same-interpreter condition.
[Admission.OpenRequests](Admission.lean) compares original and surviving dispatch;
`OpenCloses` recursively checks the actual closing positions, including nested
captures. [SourceResourceRoutes.Realizes.route](SourceResourceRoutes.lean)
already proves dispatch equality for its represented scopes. C3 must extend that
argument through actual callback execution, capture and resumption. Retained
handlers being irrelevant cannot be assumed merely because a program validates.

## C1.3 direct effectful resume operands

Fresh baseline regression results:

| Fixture | Baseline observation |
| --- | --- |
| [Bound form](fixtures/open-owner-resume.ash) | `17 : Int` |
| [Direct form](fixtures/open-owner-resume-operand.ash) | Core construction fails with `InvalidPayload` / `internal.core-build`. |
| [Unsafe discard](fixtures/open-owner-discard.ash) | Source rejection `effect.discard-unsafe`. |

The failing replay replaces the matching resume node's entire row with its
owner's output row. That drops the operand's local effect; exact removal at the
nested handler then fails. The baseline independent validator and T-Resume also
require the operand effects to be a subset of the owner's output row. Changing
this contract therefore needs a semantic proposal, not only a local builder fix.
[CP-0021](../../../proposals/CP-0021-local-effects-in-resume-operands.md)
records the accepted union rule and required evidence. The source inference and
least-handler-output traversal already retain the operand's direct requirements.

## C1.4 discrepancy inventory

| ID | Classification | Finding | Required response |
| --- | --- | --- | --- |
| D1 | Admission/raw-machine difference | Lexical calculus unwind retains handlers that Core close projection drops. | Preserve Core's cleanup compatibility and prove inactive-handler simulation; do not claim an accepted-program disagreement from the raw witness. |
| D2 | Demonstrated construction failure and static restriction | Direct effectful resume operand fails while its bound form returns 17. | CP-0021 changes the row contract; repair replay and independent validation with positive/negative regressions. |
| D3 | Missing static evidence | Core discards the capture-analysis result after validation; the stored program lacks a calculus admission certificate. | Derive or retain finite authenticated annotations and prove their structural compiler sound. |
| D4 | Admission representation gap | M4 callable ports require retained resource support to occur in input/output/requests. The [pure closure fixture](fixtures/core-cleanup-pure-closure-capture.ash) returns Unit in validated Core with only cell acquisition/release and no requests. | Justify capture erasure or an explicit support annotation. No broad closure claim before resolution. |
| D5 | Representation/proof gap | Core environments, tuple heap and frame vectors differ from substituted calculus values/stacks. | Define the relation and prove every applicable step. |
| D6 | Explicit implementation boundary | Fallible reservation, work limits and bounded identities are not mathematical freshness. | State/model successful preparation and failure outcomes; do not count malformed-state failures as allowed progress. |
| D7 | Unsupported families | General recursion, unresolved polymorphism, registration and native buffers lack direct initial-calculus cases. | Keep coverage explicit; justify any subsequently required extension. |
| D8 | Admission-interface gap, repaired | A sourced store and a row-checking context could disagree about a nested owner's protection. The earlier interface refuted the chosen post-resume suffix certificate. | The conditional `Interface.closingSeparate` field excludes that mismatch; actual capture constructors derive it from ownership and uniqueness. Complete normalized kernel admission now validates the repair in context. This is not a coherent Rust runtime counterexample. |
| D9 | Declaration-recipe gap, repaired | The earlier `ClauseRecipe` grammar could not describe the normalized clause's resume followed by a cell write. | The structural suffix extension constructs the exact declaration certificate from request footprints and receiving-tail checks. Complete normalized kernel admission passes. Historical rejection evidence is retained in commit `f44ff78`; the fixture is unchanged. |

## C1.5 finite case inventory

Core has 23 node alternatives at its closed assembly boundary: five value
alternatives, variable, ten ordinary computations and seven effect operations.
The following map is an implementation inventory; no row is marked proved yet.

| Core alternatives | Calculus translation or separate treatment |
| --- | --- |
| Integer, Boolean, Unit | `integer`, `boolean`, `unit` |
| Function; Variable | `lambda`; `variable`, with explicit lexical binder mapping |
| Constructor | General nominal data excluded initially |
| Bind; Apply | `bind`; `app` |
| Tuple; Match | Binary `pair`; exhaustive Boolean `branch` subset |
| RecursiveBind | General recursion excluded; inspect nonrecursive global wrappers separately |
| Primitive | No direct constructor; separate pure-extension obligation if required |
| NewtypeConversion; LocalNominalScope | Erasure/identity authentication requires separate evidence |
| TypeAbstraction; TypeApplication | Closed specialization requires separate evidence |
| Request; Handler | `perform`; `handle` with exact declarations and exhaustive clauses |
| Resume; Discard | `resume`; `discard` with lexical owner mapping and capabilities |
| Resource | `resource` for authenticated cells; bind the handle to its activation reference |
| Cleanup | `cleanup`; authenticate preceding callback binding and stored invocation |
| Registration | Excluded initially; handler lowering does not erase its ownership obligation |

The actual evaluator has three control forms (`Evaluate`, `Return`, `Discard`)
and 19 frame alternatives. The frame correspondence inventory is:

| Core frame alternatives | Required relation |
| --- | --- |
| Bind, ApplyFunction, ApplyArgument, Tuple, Match | Ordinary strict calculus contexts, lexical environments and heap value projection |
| ResourceInitializer, ResourceBoundary | Initializer context; fresh cell activation, payload and release owner |
| HandlerBoundary, Request, Resume | Exact lexical selection and operand contexts |
| ClauseBoundary | Live captured segment or consumed owner, preserving the full active clause prefix |
| CleanupBoundary, CleanupCompletion, CloseCompletion | Armed action, required running completion and close completion; ordered callbacks |
| PrimitiveLeft, PrimitiveRight | Outside direct initial grammar |
| InitializeRecursive | General recursion outside initial grammar; entry-wrapper analysis remains explicit |
| TypeApplication | Closed-instantiation normalization obligation |
| RegistrationBoundary | Outside initial fragment |

The calculus has 16 expression constructors and 32 existing transition families:

| Group | Exact families |
| --- | --- |
| Ordinary, 20 | Focus; plug; bind; beta; true/false branch; enter/leave handler; enter/leave cell; register/start/finish normal cleanup; capture; resume; leave clause; finish-close-unit; retire-unit; read/write cell. |
| Unwind, 6 | Skip plain; skip handler; release cell; skip spent owner; open nested live capture; retire owner. |
| Outer lexical, 6 | Start/finish unwind cleanup; discard; finish unwind close; retire returned value; close returned value. |

Focus contains ten strict expression positions. Unit and general close/retire
cases overlap intentionally. Core may match several administrative calculus
events; C3 must give a decreasing measure for any zero-event administrative
match. This inventory does not establish coverage by counting constructor names.

## C2–C5 proof and implementation boundary

The recommended bridge exports finite Core data and annotations and checks them
independently. A distinct formal Core validation derivation should compile into
the existing source, authentication, structural admission, resource and
accounting judgments. An annotation must not contain `InitialAdmission.Program`,
an execution trace, successor validity or a claim about every future execution.

The runtime relation must use an independently defined Core step and match the
step actually taken. M3's existence of a preserving calculus successor does not
prove this correspondence. Observable result, callback order, cell operations
and owner completion need separate relations; ledger permutations alone do not
establish order. Rust tests and exported examples remain implementation evidence,
distinct from the general theorem about the formal Core model.

### Independent Core machine

[CoreMachine.lean](CoreMachine.lean) evaluates the finite Core graph directly.
Its control, lexical environments, tuple heap, frame stack and nested captured
segments are distinct from calculus configurations. It covers the declared
ordinary constructs, singleton nonrecursive entry template, cells, handlers,
resume, discard and cleanup. Successful `Step` is an equation for this machine's
own `next` function; rejected and terminal outcomes cannot supply such a step.
Storage and identities are mathematically unbounded. Successful correspondence
with Rust's fallible preparation remains a separate obligation.

[CoreMachineExamples.lean](CoreMachineExamples.lean) kernel-checks the actual
exported graph: `exported_result` gives 11 and `exported_write_order` gives
`[7, 11]`. Additional checks cover lexical closure lookup, repeated resource
activations, nearest exact handler selection, missing-clause masking, complete
capture restoration, consumed-owner rejection and nested structural closing
order. Fresh independent compilation passed; the named result, write-order and
non-step theorems report only `propext`.

The first monolithic `rfl` check exhausted practical host memory and was stopped
deliberately. Kernel-checked `decide` verifies the same full-graph assertions
without that reduction cost; no native decision axiom is used. These examples
do not prove graph admission, a general state relation or simulation. Dynamic
occurrence counters are ghost metadata, and internal `entered` observations
include cleanup registration, as does Rust's loop entry trace. Registration
bypasses `dispatch_entry` after the loop records the entry; the separate Rust
effect trace has no model ghost identities.

### Actual Rust configurations

The test-only [alignment observer](../../../../src/eval/machine/alignment_trace_tests.rs)
records pre-step configurations in the actual `Machine::run_loop`. It retains
structured controls, lexical environment entries and recursive function
templates, resource instantiations, heap contents, active and captured frame
vectors, live/consumed clauses, counters, limits, work accounting and traces.
Raw snapshots retain identity tokens. A separate comparison view renumbers
environment references and uses a consistent module map across the observed
run; it preserves distinct modules and rejects foreign closure arenas.

Eleven focused tests pass, including a fresh independent run. They check result
and trace agreement with observation disabled, result 11 and cell writes 7 then
11, nearest exact owner selection and full-prefix restoration, lexical cell
capture, deterministic comparison across independent compilation, and an
unchanged resource-capacity failure with its observed prefix, and exact trace
regeneration using the static graph exporter's frozen identity maps. Clippy with
warnings denied and formatting checks also pass.

The observer explicitly rejects arithmetic frames, general data, polymorphism,
hooks and native buffers. Such a rejection stops observation while evaluation
continues; two arithmetic cleanup fixtures exercise this distinction. Tests of
native/hook/polymorphic rejection use constructed states. These exclusions are
observer coverage limits, not new exclusions from Ash or changes to the declared
Core fragment. The capacity test concerns a failed acquisition; it does not establish
discard atomicity or observation accounting inside every failing step.

### Checked finite implementation trace

[CoreObservation.lean](CoreObservation.lean) projects model states and raw Rust
snapshots to common semantic data. It retains controls, lexical environments,
heap contents, active and recursively captured frames, consumed owners and cell
payloads. Raw tuple metadata receives separate consistency checks. Ownership
accounting includes dormant captures. The checker compares loop node entries,
cell events and cleanup-start boundaries; model-only handler, ticket, cleanup
and close labels remain explicit ghost data. Rust request trace events retain
declaration identities only; exact effect arguments and lexical instantiation
are checked in the configurations.

[CoreObservedTrace.lean](CoreObservedTrace.lean) contains 91 snapshots generated
only from the actual Rust `run_loop`. Its `actual_steps` theorem applies checker
soundness to obtain exactly 90 successful independent Core transitions, a
related snapshot at every boundary and a terminal result. Further kernel checks
establish result 11, cell writes `[7, 11]`, cleanup action start `[27]` in the
shared graph numbering, final cell release, distinct model owner tickets and
rejection of missing or extra terminal boundaries.

The first direct reduction attempt encountered opaque generated recursive
comparisons. Transparent structural comparisons now have equality-soundness
proofs; no snapshot data or compared field was removed to pass the check.
Fresh independent compilation of both leaves passes with only `propext` and
`Quot.sound`. The fresh combined Rust run passes 18 tests (11 observer and seven
graph exporter tests); both regeneration tests are deliberately ignored.

Capacity limits remain fixed across this successful trace, work accounting is
monotone with constant total budget, and frame/capture/owner bounds are checked
at each boundary. These facts do not establish general failure atomicity or
identify finite host capacity with mathematical freshness. This finite checked
Rust/model trace does not prove general Rust correspondence or the model's
calculus simulation.

### Value and environment correspondence

[CoreValueRelation.lean](CoreValueRelation.lean) relates independent Core values,
lexical environments and tuple heap locations to scoped calculus code. It reuses
the graph translator, substitution and resource instantiation. Finite derivations
expand a used function template over its captured environment tail; removing
its self binding requires explicit nonrecursion evidence. Inserted values are
closed, so outer substitutions cannot change their lexical meaning.

Theorems preserve the relation under heap extension and establish actual Core
variable/resource lookup, closure shape and parameter shadowing. Examples check
the captured value 17 against a caller binding of 99, the exported-style `main`
template, resource shadowing and tuple allocation. Fresh independent compilation
passed with standard axioms only.

Closure constructors retain a finite `ClosedValue` witness; this file does not
derive that witness or template nonrecursion from validated Core. Static
authentication, construction of the relation for reachable heaps, relation of
continuation scopes and full configuration/transition simulation remain open.
The relation takes no future-execution premise. Resource activations currently
use matching numeric identities; simulation must choose the same fresh identity
in the existing calculus allocation request and prove its freshness.

[CoreOwnerMapBoundary.lean](CoreOwnerMapBoundary.lean) identified a coverage gap
within D5. The retained [reentry fixture](CoreOwnerMapReentry.ash) returns Unit
in the current validated Rust evaluator: a nonrecursive callable reenters its
static handler while another activation is live. Separate finite graph proofs
show that public root translation succeeds, but translating the callable under
a colliding caller owner map fails at every fuel. The original fixed-map value
relation consequently could not represent that callable; commit `48caa0d` retains
that negative proof. This was a relation limitation, not a Core runtime disagreement.

The repaired single value/environment relation certifies each callable's source
site, empty-map body translation and absence of free tickets. Its meaning is
independent of the caller map. `ComponentWithMaps` separates the current code's
map from the saved-frame map, and generic beta enters the empty callable map
while preserving the caller continuation. The boundary example now proves this
actual beta transition and positive representation under a colliding caller map.
The per-frame extension below carries this boundary through ordinary body steps
and caller return. Initial/reachable relation construction remains open. Existing
translator checks and legal clause bindings are unchanged. Fresh independent
compilation of the original eight affected/dependent modules and the retained
Rust reentry fixture pass.

[CoreCallableChecks.lean](CoreCallableChecks.lean) constructs the exact callable
certificate used by that relation from finite Core graph data. It checks the
function site, empty-map translation and free-ticket absence. An ambient-map
check compares the complete translated body with a sound structural equality
checker. `checked_lambda_evaluate` feeds its result directly into the actual
lambda-entry theorem. The exported getter supplies a concrete certificate.
Environment closing and `ClosedValue` remain explicit current premises;
authentication against Rust validation and construction for every reachable
callable remain open. Independent compilation and statement review pass.

### Completed strict redexes

[CoreStrictSteps.lean](CoreStrictSteps.lean) connects completed application,
bind and Boolean selection to positive calculus steps. Each theorem records the
actual independent Core successor, one ordinary `RawStep`, and the successor's
lexical closing relation. Closed substitution commutation in `CoreValueRelation`
proves that the supplied argument takes precedence over captured bindings and
retains its resource activation under outer resource instantiation.

Fresh independent compilation passes with standard axioms only. Examples cover
lexical capture, the self-inclusive nonrecursive entry template, parameter and
resource shadowing, bind and both Boolean arm orders. Bind retains an explicit
current `ClosedExcept` premise. Core and target stack tails remain arbitrary,
unchanged parameters; these theorems do not yet relate whole configurations or
construct the required static premises from Core validation. No discard rule is
used.

### Ranked administrative values

[CoreAdministrativeSteps.lean](CoreAdministrativeSteps.lean) proves the
administrative value cases: literal, lexical variable and lambda entry, plus
completed binary tuple allocation. Cell handles use ordinary variable lookup.
Each witness retains the current translated/closed value interpretation, the
actual Core successor, the successor value relation and a strictly decreasing
rank. Value entry removes an evaluation bonus; tuple allocation removes a frame
and preserves existing heap relations. Unsupported nodes and rejected lookups
cannot provide a witness.

Fresh independent compilation and statement review pass with standard axioms
only. The rank justifies these specific zero-step target matches; it does not
permit arbitrary Core steps to match by stuttering. Whole-frame and configuration
relations and construction of the current static premises remain open.

### Ordinary saved frames

[CoreStrictFrames.lean](CoreStrictFrames.lean) relates saved bind, application,
binary tuple, Boolean-match and Unit-match frames to calculus contexts. The
relation retains lexical closing evidence and transports it under heap extension.
Application focus decomposes one closing derivation, preserving its exact lexical
replacements. Returning a function takes positive plug and focus steps when its
argument is not a value. With a value-ready argument, the target reconstructs the
application and delays beta until Core finishes the argument.

Fresh independent compilation and statement review pass with standard axioms
only. Examples cover lexical capture, the entry template, positive application
focus/return and rejection of premature value-argument focus. Static
authentication of supplied `PlainData`, the whole-stack relation and integration
of flattened value-ready frames remain open.

[CoreStrictStack.lean](CoreStrictStack.lean) composes a contiguous inner prefix
of reconstructed contexts with ordinary pushed frames. Ranked Unit entry keeps
one identical target configuration; completed beta takes a positive target step
and retains the outer stack. The lexical examples prove actual transitions from
supplied states, not initial-state reachability. A reconstructed application is
not a value, so another outer frame cannot extend that flattened prefix. This is
a representation discipline whose preservation still needs phase/focus proofs.

[CoreStrictPotential.lean](CoreStrictPotential.lean) supplies one structural
potential for the covered administrative cases. Node costs follow the checked
graph's strict postorder; frame weights include saved operand costs. Actual
application and tuple traversal strictly decrease this potential while preserving
one identical target configuration when the target operand is already a value.
The potential also decreases for every earlier `ValueWitness`. An explicit
family guard limits silent steps to the named administrative families, and an
unchanged state cannot supply a witness. The completion and effect components
below extend traversal to bind, Unit match, exhaustive Boolean match and
value-ready resource entry. Arbitrary mixed-prefix
traversal and complete ordinary simulation remain open. Fresh independent
compilation and statement review pass with standard axioms only.

[CoreAdministrativeTransport.lean](CoreAdministrativeTransport.lean) transports
value entry and tuple allocation through arbitrary existing mixed ordinary
stacks. It reuses the current lexical interpretation and preserves one identical
target configuration. Allocation extends the heap and removes exactly its ready
inner tuple frame; further ready pair frames and saved lexical continuations
remain related. The same family guard and strict potential rule out an unchanged
source state. A nested tuple example checks both allocations over a saved caller
binding. Traversal of arbitrary mixed prefixes remains open; the boundary
component below adds exact handler/cell frames.
Fresh independent compilation and statement review pass with standard axioms.

`PushedWithMaps`, `FlattenedWithMaps` and `OrdinaryWithMaps` now give each saved
frame an explicit map; the earlier uniform relations are abbreviations of these
same judgments. `ComponentMapped` checks that the supplied annotations project
to the actual Core frame list. Traversal pushes the current map with a saved
frame, restores that frame's map when returning to its operand, and preserves
older annotations. Value entry and tuple allocation retain their family guard,
identical target and shared decreasing potential across these separate maps.

`beta_admin_caller_bind` composes actual Core beta, integer-body entry and caller
bind return. It derives the body interpretation from the current callable,
keeps the target fixed during the ranked body step, and takes positive target
beta, plug and bind steps. The saved caller map and supplied scope are restored
without an empty-map restriction; older annotations persist. It assumes neither
the desired successor interpretation nor future validity. This is ordinary
component correspondence: authentication of `PlainData`, reachable maps,
remaining phase cases and full effect correspondence are still open.

[CoreOrdinaryCompletion.lean](CoreOrdinaryCompletion.lean) derives singleton
nonrecursive wrapper entry from its current lexical interpretation. Its actual
Core successor installs the self-inclusive function template; the target takes
a positive binding step. The generic theorem retains explicit finite
nonrecursion, callable, translation and closedness checks. Bind, Unit-match and
Boolean-match entry preserve one target configuration and decrease the common
potential when the selected operand is already a value. Unit and Boolean return
restore the saved frame map and supplied scope, preserving the Core environment
and older mapped frames. Unit return erases the target's generated dummy binding
using its absence certificate; an integer scrutinee is rejected.

The exported examples instantiate wrapper54/function50 and connect main's beta,
Unit-match entry, variable return and match completion to effect node48. They
start from the stated Core configurations; they do not establish whole-program
reachability or execute the effect body. Fresh independent compilation passes
with standard axioms. Non-value traversal, reachable annotation authentication
and complete effect correspondence remain separate obligations.

### Handler and cell boundary components

[CoreEffectFrames.lean](CoreEffectFrames.lean) relates actual saved handler and
resource boundaries to target handler/cell frames. Handler body, exact effect
instantiation and clause header are derived from one current `EnvCloses`
derivation. Resource opening preserves the lexical resource barrier, including
shadowing and stored templates. Resource initializers retain the same derived
body carrier in both pushed and value-ready flattened stack positions.

[CoreEffectEntry.lean](CoreEffectEntry.lean) constructs mapped handler entry and
normal return, cell acquisition and normal release. Acquisition takes the actual
Core transition and two positive target steps: resource entry and the generated
handle binding. Normal return restores the boundary's supplied map and scope;
cell release names its exact key. Value-ready resource entry uses the common
strict potential and preserves an identical target expression. No arbitrary
effect transition receives a silent-step witness.

The exported acquisition prefix runs resource48's integer initializer and enters
body47 with its cell handle. It instantiates a supplied counter at key7 and
retains arbitrary older mapped frames; it does not establish that supplied
state's reachability or execute the remaining body. Closedness checks are
computed for the fixture. Generic freshness, target-world correspondence,
reachable map/scope authentication, captured owners and cleanup remain open.
Six new or affected modules pass fresh independent warnings-as-errors
compilation and statement review, using only standard axioms.

The separate [initial-prefix proof](CoreInitialPrefix.lean) now starts at
`CoreMachine.initial graph`. Twelve linked actual Core transitions evaluate the
wrapper, application, Unit match and initializer, then reach body47 with key0
and counter1. Every intermediate configuration has the component relation.
Silent links use the existing named strict-potential witnesses; the other links
take five positive target steps. The exact target ledger creates `[resource 0]`
and discharges nothing. This proves that fixed raw prefix, without assuming a
reachable starting state. It does not construct M4 validity or authenticate the
source annotations, and it does not execute the remaining handler body.

[CoreAllocationHistory.lean](CoreAllocationHistory.lean) derives the historical
resource-key invariant from actual Core transitions. Acquisition is the only
successful step that increments the counter and appends an acquisition event;
all prior acquired keys are smaller. The result applies to finite executions
from `initial`, including the same twelve-step prefix and checked observation
traces. It covers resource activations, not handler, ticket or cleanup owners.
Its target-world freshness corollary still requires world correspondence; the
Core history proof does not supply that premise. Both leaves pass fresh
independent compilation and statement review with standard axioms only.

[CoreTicketHistory.lean](CoreTicketHistory.lean) separately derives the capture
ticket history from actual Core transitions: issued tickets are exactly
`List.range nextOwner`. Successful capture issues the previous counter;
resume, discard and nested closing preserve the history. Therefore a capture
reached from the initial state receives a fresh ticket, even when the same
static handler and owner are used repeatedly. A missing-clause dispatch issues
none. The proof covers historical ticket issuance, not live-owner uniqueness,
target-world correspondence, capacity failures or M4 validity. The leaf is
registered in the grouped check and passes independent warnings-as-errors
compilation and statement review with standard axioms only.

[CoreHandlerPrefix.lean](CoreHandlerPrefix.lean) extends that same linked
execution through the getter and setter bindings, the saved ordinary
continuation and handler41 entry. Twenty actual transitions from `initial`
reach body29 under the handler, ordinary continuation and cell boundaries.
The component relation holds at every intermediate state. The exact target
ledger still creates only `[resource 0]` and discharges nothing. The proof stops
before evaluating body29 or registering its cleanup callback. Scope and answer
annotations are supplied runtime-relation data; their authentication remains
separate from these actual transition equations.

[CoreCleanupFrames.lean](CoreCleanupFrames.lean) relates an armed cleanup
boundary to its actual delayed Core action, saved environment and callback.
The cleanup shape check constructs the delayed invocation's translation;
callback lookup and body interpretation follow from one current lexical
closing derivation. The ordinary stack relation now has this exact armed
constructor and transports it under heap extension.

[CoreCleanupEntry.lean](CoreCleanupEntry.lean) extends the same initial chain
to 24 actual Core transitions. It constructs the callback binding and registers
cleanup, reaching guarded body24 with action27 saved at key0. Every intermediate
state remains related; silent links use the existing strict potential and
registration takes a positive target step. The exact target ledger creates
`[resource 0, cleanup 0]` and discharges nothing. The action has not been entered,
and a missing callback is proved to reject rather than register. Supplied action
scope, answer and request annotations still need authentication. Cleanup
execution, general owner freshness, capture and M4 validity remain open.

[CoreAllocationCorrespondence.lean](CoreAllocationCorrespondence.lean) proves
that current Core acquisition history and the target's historical resource
world remain equal when an actual Core step and target raw segment agree on
their local allocation event. The successor equality is derived, not assumed.
General event matching is still a simulation obligation. For the fixed initial
prefix, all matching, world and freshness premises are discharged: the target
`RunSteps` starts with an empty ledger and ends with resource world `[0]`.
This covers historical resource keys, not live ownership or other owner
families. `RunSteps` checks raw transitions and creation freshness; it is not
M4 validity. Both new leaves pass independent compilation and statement review.

### Closing projection component

[CoreClosing.lean](CoreClosing.lean) models the successful Rust discard
projection with an independent `PopAppend` traversal. Shared `Control` encodes
frame shapes and ghost owner identities; this is not an exported Rust heap or
configuration. `discard_projection_exact` proves the exact ordered retained
cleanup/resource list. `ready_selected_accounting` partitions the selected and
contained tickets from retained owners, and `ready_selected_no_duplicate_owners`
derives uniqueness. `open_closes_projection` connects existing interpreter and
support evidence to the same traversal.

This component assumes successful preparation and disposal checks, and excludes
registrations, native buffers and protected running completions. It does not
simulate callback execution or the conditional Core close-completion marker.
The selected and nested ticket retirement order is related by permutation; only
retained cleanup/resource order is claimed exact. Independent review found no
scope or proof defect. A fresh warnings-as-errors compilation passed with only
`propext` and `Quot.sound` in reported dependencies.

### Callable-support component

[CoreCallableSupport.lean](CoreCallableSupport.lean) constructs a closed
`InitialAdmission.Program` for a pure closure retaining a cell reference under
an unused binding. Its actual latent footprint stays empty. The target request
allowance includes that cell to satisfy the existing lambda capture guard;
`capture_guard_from_cell_support` derives the guard from a finite support bound.
The negative empty-allowance theorem confirms that the original guard cannot
admit the same retained reference without support in the function port.

This admits the isolated closure through conservative annotation refinement.
It does not establish a general Core translation, exact
Core-row equality, arbitrary callable refinement or Rust closure correspondence.
Independent review and warnings-as-errors compilation passed. The Program
construction uses only `propext` and `Quot.sound`; its existing initial-state
wrapper additionally depends on `Classical.choice`.

The [passed pure closure](fixtures/core-cleanup-passed-pure-closure.ash) is a
further D4 admission obligation: validated Rust returns Unit when a user operation
accepts a pure closure retaining a live cell, invokes it and resumes. The declared
operation instance has no resource argument. Adding the cell to the closure's
request allowance alone changes its operation input port, so the isolated support
refinement does not yet establish this case. General admission must justify a
compatible support representation or capture erasure; neither follows from the
successful Rust run. This remains higher-order support within C2.3, not an
additional fragment exclusion or a demonstrated runtime disagreement.

[CoreHigherOrderSupport.lean](CoreHigherOrderSupport.lean) proves the precise
obstruction. Keeping the original pure function port forces its request allowance
to remain empty. The unchanged retaining lambda then fails the current capture
guard and `Auth.value_support`, although its source typing can be constructed.
Adding the cell allowance changes the operation input port. These results rule
out that annotation strategy for this case, not every possible translation.

The [specified resource analysis](../../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
tracks stored dependencies separately from request obligations and checks the
recipient of operation payloads. A separate retention interface must preserve
that receiving-scope check, substitution and resource-exit bounds. A capture
erasure alternative must preserve actual cell and cleanup observations. Neither
obligation is discharged by merely relaxing the lambda guard or deleting pure
calls. C4.1 is reopened for this identified admission repair; the D2, D8 and D9
repairs remain verified.

[CorePayloadRefinement.lean](CorePayloadRefinement.lean) checks a bounded
candidate using one declared pure operation port, actual payload body plans and
independent retained support. Unit and sequenced-Unit closures have distinct
rich refinements at that same port. A cell-retaining closure's support is
computed from its closed code; the executable check accepts an inner handler
receiver and rejects an outer receiver. Both checks use tables and families
realized by the actual stacks and exact handler cuts. The candidate constructs
specialized clause selection, body Source/Auth, Local/Pending and actual
acquisition, installation, capture, call and beta steps. After beta it constructs
source/authentication and canonical support for the substituted body.

This is partial interface evidence, not a selected general repair. The old
retaining-lambda authentication is still refuted, and a single old rich
operation table cannot store both actual refinements by equality. The module
does not assemble an initial `Program`, accounting or general helper, branch
and higher-order result transport. Fresh independent warnings-as-errors
compilation passes with standard axioms; the complete D4 obligation remains open.

[CoreRefinementJoins.lean](CoreRefinementJoins.lean) completes the bounded
helper/branch assessment. Structural inversion proves that the unchanged Unit
and sequenced-Unit lambdas cannot share one old rich value. Consequently, the
current homogeneous branch constructor cannot admit both arms, and two calls
through one stored helper cannot accept both arguments at its fixed rich input.
These are restrictions of the current constructors, not an impossibility result
for every translation.

The same helper code has actual finite traces to Unit for both payloads. Boolean
selection retains the chosen payload's declared port and computed support; an
outside-owner receiver rejects the retaining arm. Per-payload body Source/Auth
and these operational results do not construct common whole-expression
admission. The generalization gate therefore identifies required changes at
ordinary callable inputs/results, branch joins and continuation refinements as
well as operation ports. A shared-interface repair remains undecided. The leaf
passes fresh independent compilation with eleven standard-axiom reports.

[CoreCallablePlanRefinement.lean](CoreCallablePlanRefinement.lean) supplies the
next static prerequisite. An actual `PurePlan` body receives M4's
`SourceAdmission.Code` certificate and `CodeChecked` evidence at any current
context. Existing silent-plan accounting transports between its actual rows
and the pure contract with exactly the same root requirements. This is an
equivalence of accounting judgments, not unconditional continuation admission.
Unit, sequenced-Unit and cell-retaining payloads instantiate that contract with
unchanged bodies and ports; computed support still accepts the inner receiver
and rejects the outer receiver. Independent compilation and review pass for all
eight named reports. Old lambda/application/result judgments do not yet accept
these private refinements, so whole-program admission and effectful callable
contracts remain open.

[CoreCallableRefinementTransport.lean](CoreCallableRefinementTransport.lean)
constructs contextual transport for the exact `Code` certificate, its
`CodeChecked` proof and unchanged-root accounting. Identity, composition,
pure-plan refinement and a pure prefix before an arbitrary actual suffix are
proved. Authenticated Unit substitution then constructs
`SourceAdmission.Admitted` for each selected payload's actual body after beta,
with the checked certificate, accounting and actual beta step. The two-body and
retaining instances preserve declared ports and computed support. Receiver
support checks remain independent: this result does not establish the complete
M4 resource-access invariant. All eight reports pass fresh independent
warnings-as-errors compilation with standard axioms only; all 436 transitive
dependency source hashes match the verified baseline.

This is still admission of the substituted body, not of the whole application.
The old lambda guard and fixed rich input/result rules remain unchanged.
Moreover, `Accounting.Run.choice` constructs a different requirement tree, so
the identical-root interface does not cover arbitrary branches.

[CoreCallableRootRefinement.lean](CoreCallableRootRefinement.lean) resolves that
accounting restriction. Its refinement constructs an actual normal root with
the same owner-demand index, together with accounting and a transport of
`RowAnnotation`, the disposal-annotated check and the current budget bound.
Identity, composition and embedding of identical-root refinement are proved.
The choice constructor checks both actual alternatives at the same store,
receiver and phases, then bounds their appended footprint by the same budget.
It preserves alternative owner demand rather than consuming both branches.
Unit/sequence and Unit/retaining row choices instantiate the common pure
contract at arbitrary continuations. All eleven reports pass fresh independent
compilation with standard axioms; all 437 dependency source hashes match the
verified baseline. This changes no value-typing rule: common helper,
branch-result, continuation and resource-exit admission remain open.

Four focused Rust regressions in
[core_alignment_cleanup.rs](../../../../tests/core_alignment_cleanup.rs)
retain implementation evidence for this pressure. Independent Core validation
preserves two requests with the same exact operation and `Unit -> Unit` payload
type but distinct Unit/Bind bodies. The
[inside-owner payload](fixtures/core-cleanup-passed-pure-closure.ash) executes,
the [outside-owner payload](fixtures/core-cleanup-passed-pure-closure-outside.ash)
is rejected with `type.resource-escape`, and an
[ordinary helper](fixtures/core-cleanup-helper-closure-branch.ash) executes both
branch choices. All ten cleanup/alignment integration tests pass, as do targeted
clippy and formatting checks. These tests do not repair calculus admission.

### Runtime capacity boundary

The [runtime failure representation](../../../../src/eval/failure.rs)
distinguishes configured capacity, allocator refusal, storage reservation failure
and exhausted work. These are separate from malformed-control, missing-binding
and invalid-location failures. A correspondence theorem must not admit the latter
as progress alternatives for a related validated state.

The successful-step comparison must include every fallible preparation used by
that step: frame and heap storage, environment and instantiation storage, live
owner limits, finite activation keys, work charges and enabled trace storage.
Mathematical freshness does not imply that a representable Rust key is available.
Registration and native-buffer capacities remain outside the declared fragment.

Capture reserves before draining active frames; resume reserves before taking
the captured continuation. Discard additionally checks host disposal while
walking frames after consumption. Thus successful preflight alone does not
justify successful discard projection. The existing
`owned_discard_preflight_is_exact_atomic_and_fresh_retryable` regression checks
preflight refusal, not a theorem that every possible failure is atomic.

Under [cleanup semantics](../../../../spec/dynamic-semantics.md#scoped-cleanup-actions),
internal exhaustion gives no source-callback completion guarantee. Host teardown
does not replay source cleanup or roll back writes. Its separately reported
`CleanupStatus::Complete` means host destruction completed, not that source
callbacks ran. The final Rust claim must distinguish a matching successful run
from a capacity-stopped prefix and account for any observations made within a
failing operation before asserting prefix correspondence. This failure boundary
is identified; its connection to the independent Core machine remains open.

### Core syntax translation component

[CoreSyntax.lean](CoreSyntax.lean) retains a distinct finite Core graph with
postorder child references, original node identities, structural types, effect
rows, binders, clause owners and source spans. Its shape checker rejects cycles,
missing children, duplicate original identities and unsupported local forms.
Stored resume/discard use outcomes must be `Consumed`, as required by the Rust
validator; this field does not describe a runtime owner's current liveness.

[CoreTranslation.lean](CoreTranslation.lean) translates that graph through an
explicit lexical owner map. Request operands remain nested and strict. Resource
translation binds the Core handle to the fresh resource reference. Cleanup
checks its stored callback invocation before translating the callback variable.
Unit matches retain scrutinee evaluation; exhaustive Boolean matches become
branches. A singleton global wrapper becomes an ordinary binding only when its
initializer has no free self-reference.

The checked component proves request/resource/cleanup equations, entry through
the shape check, and fresh administrative-name separation. Concrete reductions
cover the supported constructor transformations and structured rejection cases.
Types, exact rows, declaration signatures, lexical support and source provenance
are retained data, not authenticated static judgments. Fuel exhaustion is an
explicit error; the separate budget proof below rules it out for checked graphs.
No initial admission or execution correspondence follows from this syntax
component alone. Independent warnings-as-errors compilation passed.

### Translation budget and type support

[CoreTranslationFuel.lean](CoreTranslationFuel.lean) proves that successful
translation returns the same code under any larger fuel budget. It extracts
strict postorder directly from the existing `checkShape` implementation and
proves that the public `nodes.length + 1` budget cannot exhaust fuel on a checked
graph. Owner resolution, cleanup shape and recursive-initializer checks may still
reject syntax. This is not a typing or admission theorem.

[CoreTypeSupport.lean](CoreTypeSupport.lean) decorates the supported structural
Core types with finite retained-resource annotations. Erasure recovers the exact
Core type, including every nested function's unchanged request row. Decoration
adds only the supplied retention lists. Lexical resource realization reuses
`Instantiation.TypeRealizes` and its existing resource lemmas. Examples include
a pure function retaining a cell, nested functions/products, resource shadowing,
and malformed or unsupported input rejection. Authenticating retention against
actual captures, typing Core expressions and constructing source admission remain
open. Both modules passed fresh independent compilation and review with standard
axioms only.

[CoreOperationSignatures.lean](CoreOperationSignatures.lean) builds declaration
ports from supplied Core metadata using the existing lexical realization
relations. Accepted lookup is equivalent to a realized source declaration;
every accepted entry remains represented. Keys retain the entire effect argument
tree. Aliased keys must have equal ports, and conflicting aliases are rejected.
Callable retention annotations do not affect the resulting declared port, while
reference identities and nested function request rows remain exact. Independent
compilation and review pass. Authenticating these inputs against the Rust
registry and constructing enriched callable operations remain open; a supplied
declaration table is not validated Core evidence.

[CoreBuiltinSignatures.lean](CoreBuiltinSignatures.lean) checks every cell entry
against the actual read and write signatures, including the cell reference in
the ordinary operand. It retains the complete finite table and rejects malformed
entries even behind earlier duplicates. For primitive, product and reference
ports, checked enrichment constructs `SourcePlannedTyping.Operations`; erasing
it gives exactly the accepted port lookup, and the existing builtin compatibility
judgment follows. A comparison with `CoreInitialExample` proves equality on an
explicit finite domain, without adding signatures for other activations.

Functional ports remain part of the wider target fragment. This partial helper
rejects them because their dependency, footprint and plan evidence is not present
in a declaration port. The builtin checker itself preserves user functional ports.
Fresh independent compilation, positive/negative cases and statement review pass
with standard axioms only.

### Actual Core export

The [test-only exporter](../../../../src/core/alignment_export_tests.rs)
compiles and independently validates the restored-clause-suffix fixture before
exporting its 55 reachable nodes to [CoreExportedFixture.lean](CoreExportedFixture.lean).
Ordinary cell helper functions remain in the graph. A separate manifest retains
qualified identities, instantiated operation signatures and provenance.
The current exporter accepts nullary and resource user-effect arguments;
other closed arguments remain an explicit exporter limitation.

Seven focused Rust checks pass, including golden equality, deterministic export
across independent compilation, actual node counts, sealed handle identity and
unsupported-input rejection. The regeneration test is intentionally ignored by
normal tests. Lean checks the exported count, graph shape and successful syntax
translation with kernel reduction. The manifest is retained data, not a Lean
authentication theorem, and the exported example does not prove a general
translation or execution correspondence.

[CoreExportedAdmission.lean](CoreExportedAdmission.lean) directly constructs
source and row authentication for the actual exported getter closure at node 4
and its application at node 44. Translation equations retain resource-name
instantiation; typed lexical environments retain resource handle 4 and getter 11
over an arbitrary existing environment. The getter's request allowance, latent
read footprint and body rows are explicit. A reusable administrative row wrapper
constructs the application's current structural `Code`/`CodeChecked` evidence at
the actual cell receiver; independent accounting discharges the read there.

Fresh independent compilation and statement review pass with standard axioms.
This local construction assumes the issued cell and typed lexical environment;
it does not construct the whole exported resource/binding chain or an initial
`Program` for the graph. The following static derivation generalizes its ordinary
constructors; constructing that derivation from validated metadata remains a C2
obligation.

[CoreGraphAdmission.lean](CoreGraphAdmission.lean) supplies a separate graph-indexed
static derivation and constructs source typing and row authentication from it.
The ordinary rules cover literals, variables, lambdas, application, binding,
binary pairs, Boolean branches, Unit matches and singleton nonrecursive entry
wrappers; exact operation requests, resume, discard, cleanup and handlers are
also covered.
The resource environment, owner contracts, issued world and lexical owner map are
recursive indices. Resume/discard check the actual Core owner mapping, resolved
source ticket, permission and contract allowances; discard retains the existing
unprotected-contract requirement. The translation theorem
synchronizes that construction with actual fuel-bounded graph translation and
resource instantiation. Core rows are compared as sets; function bodies may use
a subset of their original declared allowance. Source/Auth judgments and future
execution are not inputs to this compiler.

Concrete derivations construct the exported getter, setter and write applications
for 7, 99 and 11 using actual graph indices and typed lexical environments.
`Clause.compiled` constructs actual clause40: condition30, resume32 with Unit31,
the write11 application under binder10, bind38 and discard39. It preserves the
fresh contract's demands and rows, and requires the existing branch-demand
balance. Its ordinary unprotected mode does not impose that mode on every
handler offer. Fresh independent compilation passes with standard axioms.

The cleanup rule checks the original callback binder type, callback variable,
actual delayed application and body recursively. It retains the translator's
cleanup-shape check and records registration separately from delayed execution.
`Guarded.checked` constructs body29 with callback13/write7, cleanup28/action27,
both requests and the write99 suffix. The
[finite capability checker](CoreGraphCapabilities.lean) constructs existing
one-shot usage derivations from actual syntax, including branch agreement,
callable barriers and nested clauses. `Clause.capability` applies it to the
translated clause40; duplicate resume and callable ticket escape are rejected.

The handler rule constructs both declaration modes from recursively checked
clause bodies. Each declaration also checks one finite fresh-contract body
independently of mode availability, so unavailable offers cannot make port
typing or clause translation vacuous. Exact operation lookup, argument type,
owner-map extension, duplicate-owner exclusion, clause shapes, coverage and
uniqueness remain explicit checks. Usage comes from the same finite capability
checker. The compiler builds the source/authentication judgments and actual
translated clause list; none is an opaque input leaf.

`Handler.checked` constructs handler41 with its ordinary offer and unavailable
protected offer. Its row-admission proofs retain the actual resume/write suffix
and discard alternative. `Spine.closedCompiled` then constructs resource body47
with getter/setter bindings, handler-result binding and final read, discharging
the empty-registry and lexical-map witnesses. It has no supplied handler proof.
The resource constructor now recursively checks the actual initializer and
fresh-activation body, including its handle binding. It retains the original
Core type/row checks, masked raw template translation, lexical opening equation
and resource hiding evidence for the actual body requirements. The compiler
constructs source and authentication evidence using the existing resource
opening lemma; neither judgment is a supplied semantic leaf.

`Resource.hidden`, `Resource.checked` and `Resource.compiled` instantiate this
rule for resource48. The fixture-local requirement transformation is justified
by its explicit hiding derivation, not assumed valid for arbitrary trees.
`Main.rootCompiled` then constructs translation and source/authentication for
the actual exported root54, including Unit match49, main50 and application53.
It takes no handler or resource certificate. The static derivation still needs
to be derived from validated Core metadata in general.

[CoreGraphProgram.lean](CoreGraphProgram.lean) now assembles a complete initial
`Program` for that actual exported root. Its declaration certificate retains
clause40's resume/write suffix and discard branch. A structural builtin-row
grammar and receiving-tail judgment construct the contextual code and resource
checks through both captures, protected cleanup and the final read. Independent
accounting interprets those same actual rows and constructs the checked root.
No execution, desired invariant or external source certificate is an input.

`closed_initial_state` constructs the M4 invariant, and `initial_target`
identifies its machine with the runtime relation's actual root target.
`finite_prefix` applies existing M4 progress to this admitted source. It does
not identify the resulting trace with the fixed Core execution: source-selected
successor metadata must still be connected at resource entry, handler
installation, cleanup registration and capture. All 23 dependency reports pass
fresh independent compilation with standard axioms; 475 dependency sources
match the integrated baseline. General metadata authentication and higher-order
admission remain open.

### Initial-admission interface repair

[CoreInitialExample.lean](CoreInitialExample.lean) retains the complete intended
normalized fixture and constructs source/authentication components for its cell
operations, user requests and cleanup around the complete protected body. Its
`clauseRows` and `clauseProtectedRows` now certify the full Boolean choice between
resume followed by a cell write and discard, over any cell identity. It does not
itself construct a complete `Program`; `CoreKernelProgram` below completes that
construction.

The original failed certificate allowed a source store with owner 9 unprotected
and an independently supplied receiving tail with owner 9 protected. Resuming
owner 8 consumes owner 9; a subsequent cell write exports an unprotected demand,
outside the earlier protected advertisement. Exact effect coverage retains the
protection bit. The current `InterfaceObstruction.interface_rejected` theorem
proves that this sourced witness cannot satisfy the strengthened interface.

The conditional field `Interface.closingSeparate` requires a disposing capture's
closing demand to be absent from live owners in its receiving tail. Actual
capture constructors derive this fact from existing closing ownership and
uniqueness. Resume-only interfaces acquire no restriction: their pending code
may use an outside owner. The repair does not weaken protection-bit coverage or
introduce a future-execution premise.

[CoreClauseCoherence.lean](CoreClauseCoherence.lean) connects the repaired
interface to its component obligations. `unwind_closing_demand_separate` derives
separation from
the existing unwind template and unique physical ownership.
`disposing_resume_then_suffix_checked` preserves the exact ordered
interpretation and effect bound after consuming the selected continuation and
its separated demand. The earlier witness fails precisely this separation
condition. Shared lemmas live in `OwnerPhaseTransitions` and `ClauseRowContracts`;
the comparison module reuses them.

Focused dependency builds passed for the fixture, coherence module and M4
endpoints (449 modules), and for the remaining changed historical/runtime
constructors (469 modules). Fresh independent compilation of the fixture,
coherence module and `SourceScheduledM4` also passed, with only `propext`,
`Quot.sound` and `Classical.choice` in the reports. These counts overlap and are
not a substitute for the final registered audit.

This changes experimental admission evidence under DN-0033, not Ash's specified
runtime behavior.

[CoreKernelAdmission.lean](CoreKernelAdmission.lean) now constructs source and
authentication evidence for the complete normalized resource, handler, cleanup,
both requests, both clause branches and final read. Its resource-discharge proof
retains the cell-dependent request requirements inside the resource. Fresh
independent compilation passes with standard axioms only.

The D9 declaration gap is repaired by `ClauseRecipe.suffix`. The constructor
retains the consuming prefix and its actual suffix, and adds the suffix's external
request requirements. Its compiler derives the receiving-tail checks using the
structural transport below. `clauseRecipe` and `resourceCertified` construct the
exact normalized plan's declaration evidence. `effectfulPlainResume` checks a
resumed prefix with the write still pending; `suffixMissingReceiver` rejects a
missing receiver. The previous rejection proofs are retained in commit `f44ff78`.

Fresh independent compilation of the kernel fixture and affected M4 endpoints
passed across 450 dependency modules with standard axioms only. This is an
experimental evidence extension under DN-0033, not a change to specified Ash
behavior.

[SourcePlainSuffixTransport.lean](SourcePlainSuffixTransport.lean) supplies the
standalone transport needed by D9. `plain_suffix_admission` constructs checking
for a consuming prefix followed by a suffix from the prefix's current check,
the suffix's structural request footprint and finite operation checks at the
actual receiver. It transports selected handlers and owners, retained captures,
resume restoration and discard waiting contexts while retaining the actual plain
frame. The inserted suffix executes during ordinary return and is skipped during
unwind. No constructor takes successful future execution or a future `Pending`
proof. Fresh independent compilation and review pass with standard axioms only.
Declaration-recipe integration is verified.

[CoreKernelProgram.lean](CoreKernelProgram.lean) constructs every field of
`Program` for the complete normalized fixture: source and row authentication,
declaration evidence, structural code and receiving-tail checks, independent
root accounting and checked empty root demand. Both requests, cleanup write 7,
resume followed by write 11, discard, pending write 99 and the final read remain
in the source. No external certificate or successful future execution is a
premise. Its initial-state and finite-prefix theorems apply the existing M4
endpoint. Fresh independent warnings-as-errors compilation and statement review
pass, with standard axioms only.

This completes the normalized admission checkpoint for D8/D9. It does not connect
the exported 55-node graph to that normalized source: helper closures, handle and
callback bindings, and the entry wrapper still require authenticated static
transport or direct admission. General Core admission and simulation remain open.
