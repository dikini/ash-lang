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

[CoreRequestFrames.lean](CoreRequestFrames.lean) derives request effects and
selected clause bodies from the same saved environment interpretation. The
selected body remains under its parameter binder until argument substitution,
so an outer binding with the same name cannot replace the clause parameter.
Live owner frames recursively retain the full captured stack; spent frames
retain their selected handler identity and outside stack.

[CoreCaptureEntry.lean](CoreCaptureEntry.lean) proves simultaneous Core and
calculus nearest-handler selection, including matching-cell barriers and
search past live or spent clauses without searching their dormant captures.
The generic capture theorem constructs the clause environment and successor
relation from the actual selected handler. Non-value request operands take a
positive focus step; value-ready operand traversal uses the strict potential.

The connected exported prefix now reaches clause body40 after 28 actual Core
transitions. It retains the second request, cleanup action27 and selected
handler inside ticket0, with the resource and handler-result continuation
outside. The exact target ledger is `[resource 0, cleanup 0, ticket 0]`, with
nothing discharged. A matching-cell selection and an unchanged-source silent
step provide negative checks. Independent compilation of all 14 affected
modules passes with standard axioms. Supplied annotations, reachable owner-map
coherence, live-owner uniqueness and M4 capture validity remain obligations;
this prefix does not prove resume, discard or cleanup execution.

[CoreResumeFrames.lean](CoreResumeFrames.lean) derives resume operands and
static owner resolution from the same translated expression and saved
environment. Value-ready operand traversal decreases the existing strict
potential; non-value operands take a positive target focus step.

[CoreResumeEntry.lean](CoreResumeEntry.lean) relates the exact Core owner lookup
to the target stack cut. A successful resume restores the captured prefix,
then the caller's active frames, then the consumed owner marker and its outside
frames. Captured owner maps are retained recursively. The successor relation
is constructed from this cut and the returned value; its scope must resolve the
resume binder to the selected dynamic ticket. A matching spent owner stops
lookup, including when an older live occurrence exists. Dormant captures are
not searched for a different owner.

The same initial chain now reaches the first resume completion after 35 actual
Core transitions. Its restored frames retain the pending second request,
cleanup action27, handler41, post-resume write11, spent ticket0 and the outside
getter/cell. The target ledger creates `[resource 0, cleanup 0, ticket 0]` and
discharges `[ticket 0]`. Reusing ticket0 and unchanged-state silent matching are
proved to reject. All 16 affected modules pass fresh independent compilation
with standard axioms. Generic scope coherence and annotation authentication
remain obligations; this extension does not establish M4 validity, the second
capture, discard or cleanup execution.

[CoreSecondCapture.lean](CoreSecondCapture.lean) continues the same reached
resume state through five more actual Core transitions, reaching the second
clause with argument false after 40 transitions from the initial graph. It
recovers the pending bind's saved code from the preceding relation, restores
its empty owner map and scope, then reuses exact request and capture proofs.
Ticket1 captures pending write99, armed cleanup27 and handler41; post-resume
write11, spent ticket0, the getter and cell remain outside. The target ledger
creates `[resource 0, cleanup 0, ticket 0, ticket 1]` and discharges `[ticket 0]`.
Nearest-owner lookup selects ticket1; outside lookup still rejects spent0.
The observations show that callback27 has not entered. All 11 reports pass
fresh independent compilation with standard axioms.

[CoreUnwindRelation.lean](CoreUnwindRelation.lean) relates ordinary execution,
pending Core discard control and the nonempty closing projection to the current
lexical unwind machine. The projection retains the exact `closeFuel` equation,
captured and outside stack evidence, close marker and successor counter. The
named evaluate-to-discard administrative step preserves the same target and
strictly decreases the existing potential.

[CoreDiscardPrefix.lean](CoreDiscardPrefix.lean) extends the same initial chain
to 45 actual Core transitions, through false-branch selection and discard of
ticket1. One current-machine chain includes every inherited related point.
`CoreInitialPrefix.Positive` now requires the lexical ordinary guard for every
raw step; direct induction lifts the earlier prefixes, and a negative theorem
rejects legacy raw discard. A separate no-close ledger induction supplies the
same guards for the earlier target trace.

The combined target ledger creates
`[resource 0, cleanup 0, ticket 0, ticket 1, close 0]` and discharges
`[ticket 1, ticket 0]`. This fixture's projection consumes no nested tickets.
Core retains cleanup27, close completion and the spent/outside frames; the
target also retains the captured plain frame and handler41 for lexical unwind.
The actual callback's cell0 request resolves to the same builtin interpreter
on both sides. An explicit negative check shows that unrelated user0 dispatch
does differ, so this is not all-effect dispatch equality. Cleanup has not
started. All 15 affected modules pass fresh independent compilation with
standard axioms. The completion proofs below extend callback execution and
admission; general dispatch and close-identity evidence remain open.

[CoreCleanupRunFrames.lean](CoreCleanupRunFrames.lean) and
[CoreCleanupRunPrefix.lean](CoreCleanupRunPrefix.lean) extend that same chain to
51 actual Core transitions. The delayed callback and its saved environment come
from the existing captured-stack relation. Cleanup starts once, then ordinary
application and beta enter body12 with its original environment and Unit
argument. The physical tail contains cleanup completion with saved Unit, close
completion and the spent/outside frames. The corresponding lexical tail retains
the original handler, unwinding action and closing scope.

Ordinary administrative steps use the existing isolated-prefix witnesses,
an exact common tail and actual full-state `CoreMachine.next` equations. Their
strict potential decrease follows by adding the unchanged tail weight. An
unchanged administrative step is rejected. The full target ledger is unchanged
from discard; neither cleanup nor close has completed. Cell0 dispatch agrees
for the callback's actual request. All four affected modules pass fresh
independent compilation with standard axioms. Callback cell write and completion,
general dispatch authentication and M4 admission remain open.

[CoreCellWriteFrames.lean](CoreCellWriteFrames.lean) and
[CoreCleanupWritePrefix.lean](CoreCleanupWritePrefix.lean) extend the same chain
to 63 actual Core transitions. The reached callback body determines its setter,
pair operands and exact cell request. Tuple allocation supplies a proved heap
extension; the retained running tail transports through that extension. Each
administrative step still has a strict decrease and an actual full Core step.

The selected update reconstructs the outside stack from its existing frame
interpretations. It preserves the captured cleanup, lexical handler, spent
tickets and both pending suffixes while changing cell0 from 0 to 7. The actual
Core nearest-interpreter equation and target cell update agree for this request.
A negative actual-step equation rejects a mismatched handle. This does not
establish general cleanup dispatch correspondence.

The same initial chain proves one write of 7 and one cleanup start, with neither
cleanup nor close completed. Its target ledger remains unchanged from discard.
All six affected modules pass fresh independent warnings-as-errors compilation;
the combined audit covers 834 registered modules and 11,348 exact dependency
reports using standard axioms. Cleanup/close completion, general close-name and
nested-ticket correspondence, and admission for these later states remain open.

[CoreCleanupFinishPrefix.lean](CoreCleanupFinishPrefix.lean) and
[CoreFinalPrefix.lean](CoreFinalPrefix.lean) extend the same initial chain through
all 90 actual Core transitions. Cleanup completion matches a target cleanup
finish followed by an explicit advance past the retained handler. The new
`awaitingClose` relation requires returned Unit, the actual close-completion
frame and its recursively related mapped tail. Close completion and both spent
clause returns restore the saved callers from those same frame relations.

The final caller writes 11, reads 11 and releases resource0. The proof derives
both saved callable bodies from their reached environments, transports them
through the second tuple allocation and proves each actual Core successor.
Final observations are close start, cleanup start, write7, cleanup finish,
close finish, write11, read11 and resource release. Both endpoints return integer
11 with empty stacks. The target ledger creates resource0, cleanup0, tickets0/1
and close0, and discharges all five; discharge order is recorded explicitly.
A terminal negative theorem excludes an extra successful Core step.

All eight affected modules pass independent warnings-as-errors compilation,
including the admitted-discard consumer. The combined audit covers 838 modules
and 11,395 exact standard-axiom reports, retaining 830 unchanged verified pairs.
This completes the runtime relation for this finite example. General transition
coverage, cleanup dispatch, close-name and nested-ticket correspondence remain
separate obligations.

[CoreAdmittedCompletionPrefix.lean](CoreAdmittedCompletionPrefix.lean) connects
that same exported execution to admission through all 90 Core transitions and
41 target events. `admittedFinalCompletion` consumes the admitted discard's
selected annotations, derives the actual callback and saved caller code from
the reached environments, and retains the selected handler answers, scopes and
resource answer until their boundaries return. The supporting
[CoreValueUniqueness.lean](CoreValueUniqueness.lean) proves uniqueness of closed
code for the same finite physical value/environment; it does not identify
selectable type or row annotations.

Every Core point has both its runtime relation and an admitted target snapshot.
Additional target-only cleanup/handler and bind-plug intermediates are admitted
explicitly. The endpoint returns integer 11 with an empty target stack, historical
resource world `[0]`, and all five issued owners discharged: resource0, cleanup0,
tickets0/1 and close0. The completed list records resource0, close0, cleanup0,
ticket1 and ticket0 in reverse completion order. Existing runtime-final results
supply the exact Core observations and terminality for the same endpoint.

Both leaves pass independent warnings-as-errors compilation against the current
baseline, with seven exact standard-axiom reports. This finishes the bounded
admitted example; no further variants or trace extensions
are planned. General higher-order admission, simulation and the integrated
fragment theorem remain open.

[CoreNormalCleanupSteps.lean](CoreNormalCleanupSteps.lean) proves normal
cleanup start and finish for arbitrary states and saved values. The normal
`RunningTail` constructor retains the same delayed action relation, saved-value
relation and mapped outside stack. Start derives both current interpretation
and the actual callback-entry successor. Unit completion restores the exact
saved value, its caller map and the action's saved scope, discharging precisely
that cleanup identity. Heap extension transports all three retained witnesses.

These are general transition lemmas, with current structural evidence as
premises. They assume neither callback success nor a future related or valid
state. A non-Unit callback result is proved rejected and cannot supply a
successful Core step. The outside stack must have an ordinary mapped
interpretation; nested running cleanup, arbitrary callback execution and general
cleanup dispatch still need their correspondence proofs. The relation
`Related` alone is not a general preservation theorem; `Link.positive` requires
both endpoint relations, which these two lemmas construct.

All ten affected modules pass independent warnings-as-errors compilation,
including the existing discarded-cleanup and admitted-discard consumers. The
combined audit covers 839 modules and 11,400 exact standard-axiom reports,
retaining 829 unchanged verified pairs. This closes the two normal-cleanup
transition components of C3.2, not its complete simulation obligation.

[CoreCellSteps.lean](CoreCellSteps.lean) proves actual cell read/write completion
from the current request, operand and mapped nearest-cell cut. The cut derives
Core selection and the exact physical stack update, including active clause
frames whose dormant captures remain unchanged. Operand decoding follows from
the same value relation; reads preserve both stacks, and writes update only the
selected cell. Each theorem constructs the actual Core successor, a positive
lexical transition and both endpoint interpretations.

Immediate requests above a normal cleanup completion frame also preserve the
same arbitrary saved value and delayed action. These corollaries require an
ordinary mapped outside stack. Arbitrary callback prefixes, nested running
cleanup and projected-handler dispatch remain open, as does deriving the current
structural witnesses from general static admission. No future relation, selector
equation or operand equation is assumed.

Five affected modules pass independent warnings-as-errors compilation. The
combined audit covers 840 modules and 11,412 exact standard-axiom reports,
retaining 835 unchanged verified pairs. These are general C3.2 components;
they do not complete admission or the full simulation theorem.

[CoreCompletionSteps.lean](CoreCompletionSteps.lean) proves generic consumed-clause
return and Unit close completion. Clause return retains the same related value,
restores the saved handler scope and caller map, and records the actual Core
clause-return observation. Close completion uses the current lexical
`finishClose` transition and discharges its close owner. Both construct the
actual Core successor and its interpretation from current frame evidence.

These rules require an ordinary mapped outside stack. Close completion uses
one locally matching Core/target identity, as required by `Related.awaitingClose`;
it does not establish the general close-name mapping or empty-discard case.
Returning across a live clause and finishing a close with a non-Unit value are
proved rejected and cannot count as successful Core steps. Nested retirement
and reachable annotation authentication remain separate obligations.

The new leaf passes independent warnings-as-errors compilation with six exact
standard-axiom reports. The combined audit covers 841 modules and 11,418 reports,
retaining 840 unchanged verified pairs. This adds two C3.2 transition components;
it does not complete the general simulation obligation.

[CoreEmptyDiscard.lean](CoreEmptyDiscard.lean) proves general empty-projection
discard, including nested live and spent captures. The same mapped capture and
successful empty `closeFuel` result construct a finite lexical unwind. Core
consumes nested tickets before their children; lexical unwind retires parents
after children. The proof gives both exact orders and their permutation, without
confusing those ghost events with observable callback order. Retained resource
or cleanup frames contradict the empty-projection hypothesis.

`discard_empty` derives actual Core next and both related endpoints from the
same current owner cut. Core's close counter stays unchanged. The positive
target segment explicitly discards, advances and retires scopes, then finishes a close
whose label is chosen independently of that counter. Its created close is also
discharged within the segment. Freshness of that label remains a current-history
obligation for admission; the raw transition theorem does not assert it.
Nonempty projected callbacks and general annotation authentication remain open.

The new leaf passes independent warnings-as-errors compilation with three exact
standard-axiom reports. Grouped integration with the admitted-completion leaves
covers 844 modules and 11,428 reports, retaining 841 unchanged verified pairs.
No Rust behavior, relation representation or finite example was added for this
general empty-discard proof.

[CoreResourceProjection.lean](CoreResourceProjection.lean) derives a residual
resource cursor from the same mapped capture and successful `closeFuel` result.
It retains exact resource nodes, keys and payloads, skipped lexical frames and
nested live/spent captures. Live expansion introduces the corresponding
retirement marker. The existing `PopAppend` traversal agrees with this actual
projection; it does not replace the Core evaluator.

[CoreResourceUnwind.lean](CoreResourceUnwind.lean) connects actual nonempty
resource-only discard through every release and close completion.
`discard_resource_segment` constructs one `AccountedChain` of
`closing.length + 2` Core transitions. Each link derives its related endpoints;
the same positive transition witness supplies the target trace and ownership
accounting. Finite lexical advances and retirements precede the matching Core
resource pop or final close pop. The result preserves exact resource-release
order and completed-ticket order, and proves ownership multiplicities by
permutation.

Core and target close labels are independent local parameters. This covers a
nonempty resource projection after empty discards have separated their counters.
The physical counter advances once at discard; the target close is created and
completed within the segment. Current-history freshness and admission do not
follow from the cursor. Cleanup-bearing projections and general callback
dispatch remain required coverage, outside this resource-only component.

[CoreStrictFocus.lean](CoreStrictFocus.lean) adds eight general operational rules
for tuple and application entry/return, bind and Unit-match initialization,
Boolean condition evaluation and resource initialization. Current translation,
closing and mapped-tail witnesses construct both related endpoints, actual
Core next and an assembled positive link. Tuple/function return restores the
saved owner map and scope through plug followed by focus. Unit match retains
both dummy-absence facts; Boolean focus covers both actual arm orders.

Existing request/resume and value-ready traversal rules are reused. The tenth
target focus position, non-value cleanup registration, is unreachable for Core's
authenticated closed callback. Together these account for all strict-focus
positions at the current-witness boundary. Deriving those witnesses from general
admission, and lifting the full transition relation through running callbacks,
remain open.

The three new leaves report 26 standard-only axiom dependencies. Independent
verification rebuilds 16 affected modules and retains 831 unchanged verified
pairs: 847 registered modules and 11,454 exact reports in total. The additive
unwind relation requires three impossible-case compatibility branches in
existing consumers. No Rust change or new finite example accompanies this batch.

[CoreCleanupProjection.lean](CoreCleanupProjection.lean) extends the residual
cursor to retain authenticated delayed cleanups. Its construction uses the same
captured frame relation and actual successful Core projection, including nested
live and consumed captures. Finite normalization exposes the corresponding
resource, armed cleanup or empty target head.

[CoreProjectedCleanupSteps.lean](CoreProjectedCleanupSteps.lean) connects actual
nonempty discard to selected cleanup start in one accounted chain. It also
matches current Unit callback completion, resource release with later cleanups,
and final close completion. Each case uses the same positive transition witness
for execution and ownership accounting; physical and target close labels remain
independent. No callback-success premise is supplied. General callback-body
lifting, exact user-effect dispatch, freshness and admission remain open.

The cleanup batch independently rebuilds 18 affected modules and retains 831
unchanged verified pairs: 849 registered modules and 11,467 exact reports. The
two new leaves add 13 standard-only reports. Existing consumers receive only
the additive carrier cases; the completed finite example is unchanged.

[CoreSuffixSplice](CoreSuffixSplice.lean) proves that every successful Core
transition extends by the same physical stack suffix, and derives heap extension
from that transition. Target raw and guarded lexical transitions extend by the
same lexical suffix with identical created and discharged event lists.
[CoreRunningSplice](CoreRunningSplice.lean) uses these laws to construct both
running-cleanup endpoints from existing isolated component witnesses. Its
`beta_running` theorem derives the isolated application witnesses from current
closure, argument, saved-frame and prefix relations under an arbitrary retained
cleanup tail. Accounting uses the same transition witness. Neither theorem
assumes callback success or a future related state.

The two leaves pass independent pinned compilation with 20 standard-only reports.
The grouped result contains 851 registered modules and 11,487 exact reports,
including 849 unchanged verified pairs. Dispatch selecting into the appended
tail, nested callback/unwind coverage, general readiness and creation freshness
remain open. This batch establishes reuse for covered evaluation transitions;
it does not close general simulation or admission.

[CoreProjectedCellDispatch](CoreProjectedCellDispatch.lean) connects builtin
cell reads and writes through a retained cleanup projection. Current scope
selection, realization of that scope by the same target stack, and its ownership
ledger determine the actual physical cell cut. Uniqueness prevents a saved cell
from intercepting the selected operation. The dispatch theorems construct actual
Core execution, a positive target transition, both related endpoints and the
exact read or write observation. Accounting uses that same transition witness.
No additional transparency checker or future-state premise is required.

The new leaf passes independent pinned compilation with nine standard-only
reports. The grouped result contains 852 registered modules and 11,496 exact
reports, including 851 unchanged verified pairs. User-handler capture into the
retained tail, nested running completions, general admission and creation
freshness remain open.

[CoreCallbackRequestRoutes](CoreCallbackRequestRoutes.lean) connects a stored
callback's static request allowance to actual callback execution and projected
cell dispatch. `StoredCallback` authenticates the same closed action at its full
private plan and rows, then constructs its initial application source and
authentication. `CallbackCurrent` retains that exact origin through an actual
past trace and the same outgoing allowance. Beta, bind, focus, handler entry,
closed-value steps and selected handler capture construct their actual steps
and preserve this evidence at their stated local prefixes.

A current request that misses those prefixes belongs to the same action's
request list. Closing evidence derives the original and surviving route pair;
current scope realization and a nonexported cell route determine the same
builtin selector used by `CoreProjectedCellDispatch.read_dispatch`. The public
consumer constructs actual Core execution and its exact read observation.
It does not assume a chosen future dispatch or successor. The callback root
scope producer uses the existing recursive scope realization and outside scope.

Independent parent compilation passes with 20 standard-only reports and checks
all 465 selected dependency source/artifact pairs under Lean 4.33.1. This is a
bounded component, not general callback admission or preservation. Core cleanup
translation still needs to construct `StoredCallback` from validated static
metadata; runtime cleanup correspondence alone does not constrain its request
list. Arbitrary callback resource entry, resume, discard and termination remain
outside these local preservation factories.

The callback increment's grouped audit covers 876 registered modules and 11,643
exact dependency reports, reusing the unchanged 875-module baseline. All 2,064
local links and anchors, import order, trust, whitespace and artifact scans pass.
Concurrent restoration components have separate compilation evidence and are
not included in this increment's registered-module count.

[CoreCallbackAdmissionProducer](CoreCallbackAdmissionProducer.lean) constructs
the source-owned part of that stored callback from an existing `Checked` graph
derivation for the same closed action. The stronger private-plan endpoint first
inverts the actual lambda constructor, then retains its private plan and complete
rows. Equality of erased signatures alone does not identify a literal plan.
The producer also derives agreement with the same node's declared request row,
exact translation and resource instantiation, and initial application source,
authentication and typing. Declaration certification is not assumed in its
annotation and is not yet constructed.

Independent compilation reproduces all 11 reports and the exact frozen artifact
and log, checking 495 selected dependency pairs under Lean 4.33.1. This is a
C2 component. Shape validation does not yet construct the stronger `Checked`
derivation; captured runtime environments do not yet supply static substitution
evidence; declaration-required-action metadata still needs to construct the
certificate required by `StoredCallback`. General static admission remains open.

Registration detected three older dependency sources in that frozen graph.
The coherent integration build recompiles those modules and their affected
consumers against the current registered baseline: ten modules and 93 reports,
including the unchanged producer source. All 495 dependency pairs are checked
before and after compilation. The earlier artifact reproduction remains evidence
for its frozen predecessor graph, rather than the integrated dependency graph.

[CoreNestedCleanupSteps](CoreNestedCleanupSteps.lean) reuses normal cleanup start
and finish under an enclosing running tail. `RunningTail.append` retains both
authenticated physical tails and their lexical stacks. Start saves an arbitrary
related value; actual Unit completion restores that value and its recorded scope.
Both theorems derive actual Core execution, a positive target step and both full
related endpoints. Observations record exactly the corresponding start or finish;
completion accounting uses the same witness and discharges that cleanup once.
Existing callback beta correspondence applies to the composed tail unchanged.

Independent pinned compilation passes for all 20 affected modules. The grouped
result contains 853 registered modules and 11,503 exact reports, retaining 833
unchanged verified pairs. Two existing empty-tail eliminations now use the proved
nonempty property. User-handler capture, dispatch selecting into nested tails,
and projected inner completion into unwind remain open.

[CoreGeneralStack.lean](CoreGeneralStack.lean) retains arbitrary authenticated
physical and lexical segments, including running cleanup with an arbitrary
saved value, unfinished close, nested live and consumed owners, and retained
cleanup projections. Physical live owners save the same segment. A projected
lexical owner does not become a physical resumable owner. Recursive protection
evidence proves that an obligation to finish cleanup or close prevents successful
disposal even behind ordinary prefixes or nested saved owners.

[CoreGeneralCaptureResume.lean](CoreGeneralCaptureResume.lean) embeds the old
configuration relation and step witnesses unchanged. `handler_split` and
`owner_split` derive authenticated segment decompositions from actual Core
lookup. Handler cut extraction also uses current source scope and outward-route
evidence for that exact prefix, preserving selector agreement across erased
lexical handlers. Resume extraction follows the actual selected physical owner,
retains the same saved segment, and requires current binder resolution to that
dynamic ticket.

`capture_general` and `resume_from_lookup` construct actual Core transitions,
positive target transitions and both full related endpoints. The connected
`capture_immediate_resume` chain covers an immediate Unit-resume clause on an
arbitrary captured segment: capture, two decreasing operand-administration
steps, and resume. It restores the entire saved segment before the consumed
owner and outside stack. The same chain proves exact capture/entry/resume
observations and ownership accounting. This clause connection does not simulate
arbitrary clause programs. Protected captured obligations admit no successful
discard step.

The two leaves pass independent pinned compilation and review with 45
standard-only reports. The grouped audit covers 855 registered modules and
11,548 exact reports, retaining 853 unchanged verified pairs; 2,054 local links
and anchors pass. Current
callback request authentication was still required at this checkpoint.
`CoreCallbackRequestRoutes`, recorded above, now derives exact membership and
closing routes from the same authenticated stored callback; its producer from
validated Core static metadata remains open. Admitted
ticket validity, ledger uniqueness, generalized completion/unwind after restored
segments and callback-local discard correspondence remain open. These are
experimental runtime results; they do not establish general admission, M4
validity or Rust execution correspondence.

[CoreResumeReadiness](CoreResumeReadiness.lean) derives handler definition
readiness from the same active physical segment. Actual owner lookup identifies
the saved segment inspected during ordinary resume; `resume_ready_from_lookup`
combines its readiness with the existing actual Core and positive target
transition witness. The entire saved prefix is restored before caller work,
the consumed owner and the outside tail. Dormant saved frames are checked when
they become that selected segment, rather than treated as currently active.

Independent review and fresh compilation reproduce the artifact and six reports,
checking 283 selected dependency pairs under Lean 4.33.1. The result discharges
the experimental graph counterpart of Rust's post-consumption handler lookup.
It does not establish allocation, storage or control-work success, disposal or
registration preparation, or the general Rust-to-model relation. These remain
within C3.4 and the full simulation obligations.

The combined static-producer and readiness increment's grouped audit covers
878 registered modules and 11,660 exact dependency reports, reusing the unchanged
876-module callback baseline. Concurrent restoration components retain separate
evidence and are excluded from this registered subset.

[CoreGeneralRestoration.lean](CoreGeneralRestoration.lean) connects normal
cleanup start and current Unit completion, consumed-clause return and evaluation
mode close completion over an arbitrary restored segment. Saved return values
retain the same `ValueRel`; completion restores their recorded scope and every
outside obligation. `resume_then_normal_finish` connects actual resume to
cleanup completion using the same saved segment, caller prefix, consumed marker
and outside stack.

[CoreGeneralUnwind.lean](CoreGeneralUnwind.lean) reuses retained-cursor
normalization and cleanup selection for resource release, cleanup start and
current completion, and final close completion. Finite lexical advances precede
the matching physical step. The same positive transition witness determines
observations and discharge accounting, with separate Core and target close
labels. `cleanup_finish_then_close` connects completion to the same empty
retained cursor and actual physical close pop.

[CoreGeneralProjection.lean](CoreGeneralProjection.lean) connects callback-local
discard of an ordinary mapped saved capture while retaining an arbitrary caller
prefix and outside segment, including protected running and closing obligations.
It derives the selected capture's unprotected guard and the retained cursor from
that capture and its current successful projection preflight. Empty projection
creates no physical close or counter increment; nonempty projection increments
the physical close counter once and preserves the exact nested-consumption
observations. `discard_then_resource` connects discard to the same projection's
inner-first release. Protection of a selected saved capture still excludes
successful disposal; protection outside that capture remains intact.

All four affected leaves pass independent pinned compilation and both stages of
review with 53 standard-only reports. The grouped audit covers 858 registered
modules and 11,572 exact reports, retaining 854 unchanged verified pairs; all
2,057 local links and anchors pass. Current Unit return is a completion redex,
not a claim that arbitrary callbacks terminate. Current `closeFuel` preflight
remains explicit. This local-discard batch does not project arbitrary selected
`GeneralSegment` captures. General admitted-state closure, route production,
ticket validity and restored higher-order support remain open.

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

The general close-identity relation must also cover empty projection.
`CoreMachine.discardOwner` allocates a close marker and increments `nextClose`
only when the projected closing list is nonempty. The current
[lexical unwind machine](SourceResourceRoutes.lean) creates a fresh close owner
on every discard and later completes it, including when only non-owning frames
were captured. After an empty discard, using Core's unchanged counter as the
next target close identity would reuse an issued target identity. The general
relation therefore needs an explicit correspondence for close identities or a
proved treatment of these administrative close events. Equality in the
nonempty fixture does not establish that relation. The empty-discard and
resource-only nonempty components above now use independent local labels;
cleanup-bearing projection still needs that treatment. This is a C3
representation obligation, not a demonstrated change to source-visible cleanup
behavior.

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

[CoreCallableContractSource.lean](CoreCallableContractSource.lean) now supplies
a separate recursive value judgment. A function has a public checking contract
and retains its own private body derivation and row refinement. Closed
substitution preserves that private evidence through variables, products,
application, binding and branch results. Actual lexical support is bounded
independently of the public function port. Beta recovers the selected body and
transports its current code certificate, resource check and accounting root.

[CoreCallableContractExamples.lean](CoreCallableContractExamples.lean) checks
one helper bound once and called with two unchanged implementations under the
same contract. The retaining instance computes the captured cell support and
accepts receipt inside its owner while rejecting the actual outside receiver.
Common-contract branches and returned callables retain their private bodies.
A connected trace follows the producer, branch selection, caller binding and
returned-function invocation; the sequenced implementation executes its extra
Unit bind. Current checks follow the same source derivations, and ordinary
actual-plan certification is derived structurally. All 34 reports across both
modules pass fresh independent warnings-as-errors compilation.

This completes the bounded ordinary prototype gate. It does not construct
legacy `Auth`, `ExecutionSite` or general M4 admission. Effectful extension must
retain exact global operation and owner contracts, execution scope, scalar
source requirements and certification of private bodies containing handlers.
The [migration boundary](../../DN-0033-direct-effects-and-continuation-capabilities.md#m4-migration-boundary)
records the required current, pending and coherent interfaces. Higher-order
functions remain in the intended comparison fragment.

[CoreCallableContractAdmission.lean](CoreCallableContractAdmission.lean)
extends the separate source judgment with a fixed exact operation registry,
execution scope, scalar source requirements and actual declaration plans.
Each lambda retains recursive private-body evidence and its scalar outward
bound. Public declaration certification is checked explicitly; actual-plan
certification follows from the source derivation. Closed substitution preserves
these witnesses, and independent support bounds compose through substitution.
Request inversion authenticates both input and result from the same global key.

[CoreCallableContractAdmissionExamples.lean](CoreCallableContractAdmissionExamples.lean)
constructs one bound helper used with two same-contract bodies containing the
same exact request, one with an additional Unit bind. Actual bind/beta steps and
private certification are proved for these derivations. Current code/resource
certificates and checked accounting roots transport under supplied current
checks. Wrong input, result and operation keys are rejected, as is a false empty
support bound for an effectful closure retaining a cell. All 25 reports pass
fresh independent compilation with only `propext` and `Quot.sound`.

This indexed source checkpoint does not establish enclosing handler admission
or operation-response preservation. The subsequent owner-source extension below
adds resume/discard typing; handler, resource and cleanup constructors still
need extension. Common callable input/answer contracts must also reach live/spent
pending continuations. The experimental modules import existing M4 machinery,
so direct import back into that machinery would form a cycle. The companion
interface must connect current and saved-source evidence to M4's guarantees;
conditional beta transport alone does not replace the M4 invariant.

[CoreCallableContractExecution.lean](CoreCallableContractExecution.lean) now
connects current recursive source, saved plain/cell frames and the same existing
contextual checking/accounting structures in a bounded companion `Site`. Source
projection into `SourceTemplates.Expression` is constructive. Focus builds a
saved frame whose input bound contains the receiving scope's visible resources
that are in the current world. Plug preserves the returned value's actual
support and the saved suffix's private body evidence. The exact cell-read reply
derives its integer result contract from the same global operation key and its
contextual builtin receiver from the actual physical cell update.

[CoreCallableContractExecutionExamples.lean](CoreCallableContractExecutionExamples.lean)
constructs the predecessor's source, current checks, saved-frame checks and
accounting with live cell0. One helper accepts two cell-reading bodies with
different sequencing and actual retained support `[0]`. Its `transported_segment`
applies generic focus, cell reply, plug and bind in one actual raw trace, deriving
the endpoint `Site` from that predecessor. Both modules pass fresh independent
warnings-as-errors compilation; all 18 reports use only `propext` and
`Quot.sound`. This fixed-world plain/cell companion leaves full M4 validity,
user-handler replies, capture/resume/discard execution, cleanup and resource-exit
preservation open.

[CoreCallableContractRegistries.lean](CoreCallableContractRegistries.lean) now
separates immutable operation contracts and ticket policy from common owner
contracts. Both continuation endpoints retain common callable contracts. Owner
insertion preserves the immutable registry and commutes with legacy erasure.
The same `Source` judgment is indexed by owner tables and resource worlds;
resume/discard constructors and the structural source inductions use those
indices. Substitution preserves the actual private bodies and their plans.

Scoped erasure now requires the actual `EffectScope`; the empty-scope wrapper
remains available. The old all-expression empty-demand statement is replaced by
`value_demand`, requiring an actual value. The lower source projection covers
both owner operations. Existing example theorem statements are unchanged.
Five affected modules pass independent warnings-as-errors compilation with 50
standard-axiom reports. The combined audit covers 835 registered modules and
11,355 exact reports, retaining 830 unchanged verified source/report pairs.
Handler declaration/capture transport and changed-world saved-frame transport
remain open; this checkpoint does not prove full M4 validity.

Handler extension requires a different substitution statement. Substitution
changes literal clause syntax, so it cannot preserve a handler plan indexed by
the original clauses. The next proof must construct the substituted actual plan
and rows, preserve the public contract and signature, and derive certification
under the declaration policy's signature-congruence law. Existing substitution
proofs cover the constructors present at this checkpoint; they do not establish
that handler extension. This is an open C2/C4 proof obligation, not a failure of
the established M4 theorems.

The [clause-cell result fixture](fixtures/core-resume-clause-cell-closure.ash)
adds a concrete receiving-context obligation. A request captures its caller
before cell acquisition. Its clause then creates a cell-retaining callback and
resumes with it; the caller invokes it while the clause's cell frame remains
live below the restored capture. A fresh CLI run from the alignment worktree
returns `() : Unit`. The [outside variant](fixtures/core-resume-clause-cell-closure-outside.ash)
returns that closure beyond the resource body and is rejected with
`type.resource-escape`. These fixtures retain CLI evidence, separate from the
automated regressions below. Full higher-order resume preservation must update
saved support bounds under the restored world and receiving context; copying
the pre-capture bounds is insufficient.

This requirement also reaches handlers inside private callable bodies. Review
found that aggregate expression support and plan certification do not validate
each stored clause support bound. A bound selected before a resource is acquired
cannot be preserved by equality when substitution inserts a callable retaining
that resource. Fixed-bound substitution remains valid when its explicit support
hypotheses hold; general restoration must authenticate new bounds against the
actual receiver. Review established that the lambda refinement's universal
checking premise is too strong for this transport: public pure rows can be
checked at an empty receiver, while private handler rows retaining a resource
cannot. Reannotating the rows alone cannot repair that premise.

The approved experimental repair selects private rows from open body evidence
indexed by the call world, receiving support bound and actual argument support.
A hereditary companion authenticates each clause bound using the same source
derivation and support environment. Private checking consumes evidence for the
actual receiver. Further review disproved unconditional private-code refinement:
public pure rows admit an unchecked caller tail, whereas an internally handled
request must check that tail. The refinement must therefore also consume the
current retained-stack certificate and its support check, already carried by
the execution site. Existing return-mode and installation-history lemmas provide
the required transport. Accounting remains unchanged, and universal refinements
embed into the conditional interface. The connected fixed-world gate below now
implements this interface through substitution, supported source, saved frames,
the current execution site and actual handler capture. General restored-world
transport and full handler admission remain open.

Operation payload transfer also needs current request-flow evidence. Rust's
capture analysis checks hidden value dependencies against each acquisition in
the selected prefix, but its transient check result is not a retained Core
request annotation. A locally verified finite-certificate bridge now derives
post-cut support from checked origin separation, one current activation-origin
map and the actual handler cut. It does not authenticate the current request's
table index or construct the operand/prefix realization. C2 must derive those
facts from validated Core; the connected C4 admission gate must preserve them.
Public callable ports and aggregate receiver bounds do not supply them.

The connected higher-order gate promotes
[CoreCallableSourceSubstitution.lean](CoreCallableSourceSubstitution.lean) and
[CoreCallableSupportedSubstitution.lean](CoreCallableSupportedSubstitution.lean)
with their hereditary authentication dependencies. Substitution constructs the
deterministic transformed plan and preserves its signature and complete rows.
The concrete declaration policy supplies signature stability. The admission
companion retains request inversion; its former Source-only beta wrappers are
replaced by receiver-aware Supported substitution.

[CoreCallableContractExecution.lean](CoreCallableContractExecution.lean) carries
the full issued receiver through current code, saved bind suffixes and installed
handler declarations. Aggregate result bounds remain separate. Its local
`SelectedPending` witness jointly retains the predecessor, exact installed
private source family and active outside continuation. Owner insertion
transports that joint evidence. Cell updates rebuild the same predecessor path
and physical cut around the updated active outside stack, preserving dormant
saved prefixes. Existing focus, bind, plug, builtin selection and cell reply
methods remain available.

The `capture` theorem in
[CoreCallableContractCaptureConnection.lean](CoreCallableContractCaptureConnection.lean)
inverts the current pending stack and actual cut to select the same declaration,
full answer contract, owner-indexed private plan family and complete rows.
Actual operand support and current origin separation derive its post-cut
receiver. Authentication and substitution then construct the successor `Site`,
guarded calculus capture and actual Core `RawStep`, with exact transformed plan,
signature and row equalities. A desired successor or chosen private source is
not a premise. Readiness, current owner/action freshness, finite request-flow
evidence and policy stability remain explicit current assumptions.

That checkpoint is a fixed-world formal companion gate. C2 still must authenticate the
request index and produce operand/prefix realization from validated Core.
Higher-order resume after the clause acquires resources still requires saved
support transport under the restored world. General M4 admission, Rust execution
correspondence and runtime capacity success do not follow from this result.
Independent pinned compilation covers 21 affected modules with 96 standard-only
reports; the existing twelve admission and five execution example reports and
negative cases are retained. No Rust or M4 behavior changes accompany this gate.

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

### Checked higher-order restoration and actual Core resume

The restoration consumer now derives the successor from the same current
installation and full owner contract. [CoreCallableRestoredSupport.lean](CoreCallableRestoredSupport.lean)
reconstructs support bounds under the actual receiving world and context while
retaining literal private plans, complete row structure and non-support data,
and owner-indexed families. Support leaves are deterministically reannotated.
[CoreCallableRestoredAccounting.lean](CoreCallableRestoredAccounting.lean)
reconstructs the raw certificate with the same demand and root.
[CoreCallableRestoredChecking.lean](CoreCallableRestoredChecking.lean) checks
that certificate in all 23 code and pending constructor cases. Its complete
exports derive their receipts from original source/authentication evidence;
the standalone recursive handler helper has an explicit inner checking premise.

[CoreCallableRestoredResume.lean](CoreCallableRestoredResume.lean) connects these
constructions to `Site.resume`. It derives the exact entry allowance from the
selected installation, transports the current front using
[CoreCallableAllowedTransport.lean](CoreCallableAllowedTransport.lean), and
retains the private handler residual. The resulting stack contains the complete
saved prefix, current front, spent owner and outside tail in that order. The
operand is reauthenticated against the actual receiving support, the root
consumes that owner, and its phase becomes spent. No desired successor source,
checking certificate, accounting root or `Site` is supplied. `Site.resume_plug`
then uses the actual restored plain head and the existing bind consumer.

[CoreCallableResumeCorrespondence.lean](CoreCallableResumeCorrespondence.lean)
connects this successor to the actual Core owner lookup and positive resume
witness. Current dynamic-name uniqueness and scope-resolution agreement align
the entire cut, including dormant saved frames and caller metadata. The theorem
returns the rich successor at the exact Core endpoint, the full owner contract,
root consumption, spent phase, resumed observation and ownership permutation.
Deriving those current name and scope premises from general reachable Core
configurations remains a C3 obligation. This is one connected transition family,
not a complete configuration simulation or a Rust capacity theorem.

The independent callback lane also closes a bounded C2 certification gap.
[CoreCallbackRecipeProducer.lean](CoreCallbackRecipeProducer.lean) certifies
retained structural recipes and the existing consuming clause's effectful
suffix for every owner, including occupied owner components. `callback_lambda`
constructs the same graph lambda and stored callback from a checked body at its
literal plan and complete rows, ordinary metadata and a structural recipe.
Exact translation, resource instantiation, initial typing and callback start
follow from that construction. Exported validated Core must still produce or
validate the body and recipe annotations; captured-environment static admission
also remains open. `CleanupRel` alone does not constrain `ActionData.requests`.

This factory exposed an unintended auto-implicit declaration-policy parameter
in `StoredCallback.certified`. Qualifying the existing cleanup policy removes
that accidental universal parameter and retains the intended private and
all-owner checks. This changes an experimental proof interface, not Ash or M4
semantics. Independent reviews pass for restoration, the callback factory and
the Core connection. The registered grouped audit covers 885 modules and 11,760
exact dependency reports. All 12 modules in the changed sources' reverse
dependency closure were freshly compiled with 174 reports; 873 unchanged
modules retain exact baseline source and report provenance. The final three
consumers pass 49 fresh parent reports against 534 exact selected dependency
pairs. The audit checks 2,083 local links and anchors, import order, standard
axioms, trust boundaries, whitespace and artifact exclusion. No Rust source
changed in this increment.

### Static annotation gates and reachable ownership receipts

[CoreCallableGraphAnnotationChecks.lean](CoreCallableGraphAnnotationChecks.lean)
checks finite function and binding annotation data against the same graph site,
parameter and translated body. Successful checks construct exact type/effect,
lexical knownness, receiver-support and world-formation guards. Its annotation
data contain no desired Source or Auth proof. `receiver_lambda` consumes those
guards at the same literal full contract, but still receives recursive private
body source, authentication and refinement. Actual bound-value authentication,
private-plan origin and the general recursive static producer remain open.

The test-only Rust exporter now emits structured operation declarations from the
same validated registry traversal, identity maps and full type substitution as
the graph export. The existing graph golden is unchanged.
[CoreExportedOperationMetadata.lean](CoreExportedOperationMetadata.lean) retains
the exact declarations and the same origin manifest.
[CoreExportedOperationChecks.lean](CoreExportedOperationChecks.lean) builds those
entries for any activation of the exported resource binder, realizes every raw
entry and connects its accepted ports to the current builtin signature overlay.
Read retains the reference input; write retains the reference/integer pair.
Unresolved resource binders, conflicting ports, absent operations and unrelated
cell entries are rejected. Agreement covers the generated cell and all user
instances, not a fabricated finite entry for every unrelated cell. Manifest
equality pairs the exports; it does not prove general Rust compiler soundness or
rich private callable admission.

[CoreCallableInitialAdmission.lean](CoreCallableInitialAdmission.lean) constructs
the rich initial Site from the same supplied static source/authentication,
literal plan, complete rows, full contract, support and accounting. Its lower
projection supplies initial typing, joint validity and an actual first progress
step under the existing usage and builtin-signature assumptions. It does not
construct that static Program from validated Core, establish rich successor
preservation, or supply the legacy M4 authentication refuted by D4.

[CoreCallableReachableResume.lean](CoreCallableReachableResume.lean) constructs
current and saved owner-map/scope receipts through actual capture, beta, bind
and resume operand transitions. The canonical static binder map and first
matching physical owner path derive the current resolution agreement. Ticket
counting and actual initial Core history derive current dynamic-name uniqueness.
The consumer uses these produced facts to obtain the same current Site's actual
Core resume endpoint and rich successor; caller-supplied desired resolution or
Nodup is unnecessary. Older map entries and each saved frame's own scope remain
available; the fragment is not restricted to an otherwise empty map.

[CoreCallableCleanupOrigins.lean](CoreCallableCleanupOrigins.lean) derives the
saved cleanup receipt from actual registration's current scope and callback
lookup. Normal callback entry retains the entire ActionData and saved caller
receipt while clearing current scope. Unit return restores the same saved
value, installation map and scope over an arbitrary outside general segment.
CleanupRel alone does not supply scope provenance. The running-cleanup transport below extends these receipts through actual
capture and inside-anchored restoration. Outside-anchored restoration, armed
projection, disposal history and the combined reachable invariant remain open;
these factories do not prove callback termination.

Independent reviews pass for these bounded components. Integration additionally
detected historical source/artifact association errors in the saved frame and
unwind dependency caches. Frozen worker reviews retain their recorded graph
scope. The current registered integration freshly compiles all 891 modules
from every registered current source, recording each command, direct imported
artifact, log and output hash. The 11,814 exact reports use standard axioms only;
the independent packaging audit also verifies the compilation source association.
Full `cargo xtask verify` passes: 2,902 tests, no failures and two intentionally
ignored tests. General admission, the rich resource/cleanup constructor extension,
whole-fragment simulation and Rust preparation remain separate acceptance
obligations. The task's current phase board records locally verified producer
and cleanup-extension work separately from this retained integration.

### Recursive source production and rich cleanup construction

[CoreCallableStaticProducer.lean](CoreCallableStaticProducer.lean) constructs
same-code IndexedSource and authentication for fourteen constructor forms: scalar
values, activation references, variables, pairs, bind, application, requests,
branch, receiver-aware lambda, cleanup, resume and discard. Typed annotation indices preserve the
literal full contracts, actual private body plans and complete rows. Structural
lookup, recipe, refinement and permutation tags derive their corresponding
judgments; annotations do not contain Source/Auth/Certified proofs. Recursive
body evidence is now produced for the accepted templates. `checkGraph` additionally
checks whole graph shape, root metadata and the exact translated/instantiated
literal Code. Interior metadata, actual bound/captured values, registry/owner
origin and arbitrary full contract/private-family origin remain unproved.
Supported constructor forms do not imply completeness for every composition:
the instruction and recipe grammars remain bounded.

The rich source grammar now has cleanup. Its full Unit→Unit callback contract,
requests, latent row, public plan and complete public rows remain fixed; callback
and body Source/Auth are recursively supplied by the producer. Actual execution
plans retain `sequence callbackPlan (cleanup publicPlan bodyPlan)` and the matching
complete rows. Environment, owner, scope, world, allowance, substitution and
restored-support transports derive the same target children and keep the immutable
public callback suffix. Resource construction remains absent until actual
returned-storage evidence and its exact substitution contract are available.
Source/transport coverage does not establish general cleanup execution preservation.

[CoreCallableReturnStorageProducer.lean](CoreCallableReturnStorageProducer.lean)
constructs the independent CallableContracts storage/domain/result derivation for
its bounded ordinary and higher-order forms. Checked actual bind initializers
build the nearest environment from empty; `BindingAt` fixes open entries to the
same literal enclosing binds. Application and substitution check the same actual
argument/replacement at the exact domain. Returned bounds reject the existing
closure retaining the fresh resource. This companion judgment does not establish
full typing or runtime origins; control/resource/cleanup remain open there.

Independent reviews reproduce the cleanup closure and checker. All 29 changed
reverse consumers occur in the 38-module cleanup replay with 299 standard reports.
The new checker compiles against a sole coherent current-source cache with twelve
standard reports. The complete audited assembly contains 893 modules and 11,842
exact reports; 862 unchanged modules retain the preceding fresh source/artifact
association and identical direct-import hashes. This is an assembly of verified
current-source results, not a second fresh build of every unchanged module.
The returned-storage producer adds sixteen standard reports and checked actual
initializer/domain/substitution origins; control/resource/cleanup and runtime
origins remain open. The following bounded running-cleanup and literal-site components are retained
by the next checkpoint. General admission, reachability, simulation,
preparation and the integrated theorem remain open.

### Running cleanup transport and literal-site ancestry

[CoreCallableCleanupReachableTransport.lean](CoreCallableCleanupReachableTransport.lean)
keeps the same running callback, full ActionData, saved value and original
registration map/scope through actual capture. A physical captured running
completion is protected: `closeFuel` cannot successfully project it, including
nested captures. `resume_then_finish_inside` constructs the actual full-prefix
resume and Unit-completion chain, its positive target steps and restored
CurrentOwnership. The original first matching owner must lie inside the retained
captured suffix. New front frames and the spent marker then occur below that
same first match. Actual current cuts, frame/context/resolve and TicketBound
remain premises; a desired future scope or ownership proof is not an input.

[CoreCallableSiteLineage.lean](CoreCallableSiteLineage.lean) checks unique literal
handler sites for the same finite graph. The existing exported fixture passes;
the checker does not establish general Rust validator/export correspondence or
dynamic activation uniqueness. Initial, selected-clause and ordinary-child receipts retain enclosing-handler
metadata and a strict postorder site bound. They are paired with actual capture,
beta, bind entry and bind return; they do not record a whole execution ancestry
trace. Beta clears the current owner map; saved bind continuations
retain their own literal site, map and scope. Literal descent cannot reinstall
its own enclosing handler without crossing a reset or saved-site boundary.

Neither leaf proves that an arbitrary inserted resume front misses the original
outside owner. Existing general segments do not retain the past installation
site of every moved handler frame. A generic static-pair shadow obstruction
identifies this missing premise without claiming a reachable counterexample.
Outside-anchored restoration, armed projection, disposal history, general
reachability and whole-fragment simulation remain open.

Independent leaf/interface reviews pass for both components. Fresh integration
compilation reproduces their same reviewed sources, artifacts and 25 reports.
All 893 unchanged modules retain exact parent source/log/artifact associations
and identical direct-import hashes in one current-source cache. The preceding cleanup/site checkpoint `3fad8e8` assembled 895 modules and
11,867 ordered standard-only reports;
this is not another uncached build of every unchanged module. No Rust sources
change in this increment.

### Paired initializer origins and past frame installations

[CoreCallablePairedOrigin.lean](CoreCallablePairedOrigin.lean) selects actual bind
initializers and bodies from the same original rich annotation. Both nearest
binding environments advance and shadow together. Each initializer is checked
at its original full rich contract and exact storage contract; lexical storage
support must fit the actual receiver. The root/path/body successful-check
equations retain the original literal private data and complete rows.
`substitute_current` checks the actual replacement at both exact inputs, then
constructs actual substituted Source/Auth, the computed plan and full-row
transport, and CallableContracts.Derives on that same substituted Code.
`apply_current` constructs the full public-suffix application and exact storage
result. Returned bounds stay fixed and are checked within the receiver/world.
ClosedValue and substitution policy stability remain ordinary current premises.
This is static same-code pairing; runtime bound/captured values, universal call
storage recipes, owner/declaration control contracts and resource/cleanup
storage cases remain open. It does not add rich resource authentication.

[CoreCallableFrameInstallations.lean](CoreCallableFrameInstallations.lean) pairs
actual mapped frames with past literal handler/clause installations. HandlerPast
keeps the original predecessor, mapped suffix, full HandlerData, site/environment,
caller map/scope and actual handler-entry equation. ClausePast keeps that same
installation, full selected Clause and original inside/outside/captured maps.
Ordinary frames require actual PushCarrier. Joint handler/owner selection walks
these same records; it does not infer full private-data equality from a separately
chosen cut with matching answer/scope. A matching spent owner stops selection.
Actual capture and resume expose deterministic successor receipts, selected
Clause/installation equations and the physical full-prefix endpoint. Dynamic
activations are not constrained to globally unique static handler/owner pairs.
These receipts cover mapped frames. General completion/retained cursors, heap
extension, ordinary/callback history evolution and saved-caller outside misses
remain open. No arbitrary GeneralChain is authenticated by this component.

Both leaves pass independent source/interface review and fresh integration.
Their 24 reports reproduce the same reviewed sources and artifact bytes. The
preceding paired checkpoint `b04701b` assembled 897 registered modules and 11,891 ordered
standard-only reports; all 895 unchanged modules retain exact preceding
source/log/artifact associations and direct-import hashes. Retaining-value and
retaining-template negatives pass unchanged in the paired consumer's review.
Whole admission, general reachability, simulation and C4/C5 acceptance remain open.

### General completion history and parameterized storage recipes

[CoreCallableGeneralHistory.lean](CoreCallableGeneralHistory.lean) extends the
same original handler/clause installations to general physical history. Mapped
adapters retain the original maps and predecessors. Heap weakening changes only
current relations; past installations remain fixed. Running cleanup receipts,
dormant captures and retained logical cursors have separate constructors.
Actual handler entry and normal cleanup start/Unit finish construct history and
positive transition witnesses. Finish requires the original saved suffix to be
current; it does not prove callback termination or moved outside origins.

A finite physical-handler inventory carries each original installation, current
full header, prefix/outside histories and exact decomposition. It omits dormant
captures and physically removed retained handlers. `capture_history` consumes a
candidate from that same inventory and constructs the actual selected-clause
receipt and deterministic live history, including captured running completions.
Current route/effect, inventory-index and first physical lookup guards remain
inputs. At the preceding history17 checkpoint, owner selection/resume remained open.
Outside-caller misses, retained
projection, disposal and whole-chain reachability remain open.

[CoreCallableStorageRecipes.lean](CoreCallableStorageRecipes.lean) specializes
finite storage templates at the same actual binding and resource-opening
environments as Code. A formal slot retains the entire actual storage contract,
including higher-order captures, input and output. `pair_argument` constructs the
argument receipt from both actual checks. `formal_opening_receipt` and
`formal_resource_storage` prove a generic fresh scope returning that existing
formal argument preserves its contract and excludes the fresh resource identity.
A generic retaining-opened-value rejection remains explicit. No empty environment
or resource-free public port substitutes for actual storage support.

These are reviewed bounded producers. An arbitrary recipe's computed acceptance
is not universal body acceptance. Rich resource Source/Auth, captured-callee
origins after substitution, owner/control storage and actual-return observer
transport remain open. Both leaves pass fresh current-source integration with the same reviewed source
and artifact bytes and 27 standard-only reports. The current audited assembly
at checkpoint `bfc72e1` contained 899 registered modules and 11,918 ordered reports. All 897 unchanged
modules retain exact preceding source/log/artifact and direct-import associations;
this is not a fresh uncached build of every module. No Rust sources change.
Whole admission, general reachability, simulation and C4/C5 acceptance remain open.

### Same-history owner selection and actual general resume

The reviewed extension to [CoreCallableGeneralHistory.lean](CoreCallableGeneralHistory.lean)
adds `owner_search` with found, missing and blocked results. Found retains the
same installed full GeneralClausePast/header and captured/front/outside histories.
Missing constructs a physical prefix traversal law from ordinary, completion and
retained-cursor relations. A matching spent marker blocks search and append
fallthrough. Dormant captures and retained logical owners are not physical lookup
candidates. The current first lookup and GeneralOwnerCut are derived from this
same history, rather than supplied as independent cuts or signature matches.

`resume_history` consumes the computed found result, current ResumeRel, operand
relation and scope resolution. It constructs an actual Core step, positive target
execution and deterministic successor history at captured ++ front ++
spent(the same selected receipt) :: outside. Original installation, full selected
Clause, suffix/maps and running saved completions remain fixed. No future origin,
Source/Auth or ownership certificate is an input. The extension passed fresh
independent replay with 25 reports and 32 public probes against the exact current
899-module dependency cache. Fresh integration reproduces its exact reviewed
source/artifact bytes and all 25 reports. Checkpoint `a336e3b` assembled 899 modules
and 11,926 ordered standard-only reports; all 898 unchanged modules retain exact
preceding source/log/artifact/direct-import associations. Outside
caller misses, retained projection, disposal and whole reachability remain open.

### Literal captured-callee ordinary-call storage

[CoreCallablePairedCall.lean](CoreCallablePairedCall.lean) is indexed by the same
original literal rich lambda/body annotation and paired initializer Admission.
`lambda_origin` extracts the original storage lambda body annotation and full
function contract, then checks exact agreement with the finite body Recipe
specialized at the callee's captured bindings and original instantiation map.
The actual argument separately retains its caller bindings/map and produced
rich/storage receipt. No desired Source or storage derivation is annotation data.

`call_body_check` checks nearest dependency-relevant captured slots against the
actual receiver, extends the callee storage environment with the exact actual
argument contract, and specializes the same original body recipe. Existing
closed-value environment transport and substitution derive storage for the same
body.subst formal actualValue. `paired_call` enforces full agreement with the
original stored function domain/result and derives receiver-to-world bounds.
Generic formal-return and captured-variable specialization equations are proved.

This is static literal ordinary-call storage, not runtime closure origins,
closed-callee finite recipe provenance or universal body success. A concrete
original storage function contract cannot stand for every varying higher-order
argument storage tree. The universal scheme must structurally generate that
family from actual slots while retaining the original rich private families.
Callee map graph origin, captured substitution lineage, rich resource Source/Auth,
control storage and actual-return observer transport remain open.

Independent same-cwd replay passes seven reports, sixteen public probes and both
existing retaining negatives. Fresh integration reproduces exact reviewed
source/artifact bytes and reports. The current assembly contains 900 registered
modules and 11,933 ordered standard-only reports; all 899 unchanged modules retain
exact preceding source/log/artifact/direct-import associations. No Rust sources
change. Whole-fragment admission and simulation remain open.

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
not identify the resulting trace with the fixed Core execution. The following
prefix modules connect source-selected successor metadata incrementally;
capture and subsequent execution still need this admitted-state connection. All 23 dependency reports pass
fresh independent compilation with standard axioms; 475 dependency sources
match the integrated baseline. General metadata authentication and higher-order
admission remain open.

[CoreAdmittedPrefix.lean](CoreAdmittedPrefix.lean) connects that constructed
initial state to the first 12 actual Core transitions, through resource entry
and the generated handle binding. The target trace has five positive steps.
Every intermediate Core point relates to a constructed valid target snapshot;
resource entry uses the answer annotation chosen by the source preservation
proof throughout the relation. No successor validity is an input. The endpoint
has resource world `[0]`, empty handler history, issued ledger `[resource 0]`
and nothing completed. Initial public translation is tied to the same exported
root. All seven reports pass independent compilation with standard axioms.
The following modules supply handler installation, cleanup registration and
first capture with the same admitted-state evidence.

[CoreAdmittedHandlerPrefix.lean](CoreAdmittedHandlerPrefix.lean) extends that
same admitted prefix to actual handler41/body29 after 20 Core transitions and
nine target events. Both method bindings preserve the chosen resource answer.
Focus obtains its actual `PlainData` from source preservation; installation
retains the selected `HandlerData` and updated registries. The supplied-identity
`install_handler_at` endpoint uses Core occurrence0, whose freshness follows
from the empty handler history. The previous existential installation endpoint
remains a wrapper around this proof.

Every intermediate Core point has a related, constructed valid target snapshot.
The final resource world and handler history are both `[0]`; the issued ledger
is `[resource 0]` and nothing is completed. No future validity or successful
execution is assumed. Fresh independent compilation passes for all 169 modules
affected by the shared endpoint factor and for this new leaf. The proof stops
before callback binding and cleanup registration.

[CoreAdmittedCleanupPrefix.lean](CoreAdmittedCleanupPrefix.lean) extends the
same admitted handler prefix through callback binding and cleanup registration,
reaching actual s24 after 24 Core transitions and 11 target events. It preserves
the same source-selected resource answer, handler and result frame. Registration
obtains its `ActionData` from the admitted allocating transition; identity0 is
fresh in the current issued ledger `[resource 0]`. Only the resulting identity,
callback and scope equations synchronize Core's cleanup boundary. The callback
remains delayed.

Every intermediate Core point again relates to a constructed valid snapshot.
The final world/history are `[0]`, issued owners are `[resource 0, cleanup 0]`
and no owner is completed. Source preservation supplies action ports and effects;
no fixed handler answer or desired successor invariant is assumed.
[CoreReadyBindings.lean](CoreReadyBindings.lean) shares the three-step lambda
binding proof across handler and callback setup, with arbitrary mapped tails.
All six affected modules pass fresh independent compilation with standard
axioms. The following capture construction extends this same admitted prefix.

[CoreAdmittedCapturePrefix.lean](CoreAdmittedCapturePrefix.lean) reaches actual
s28 after 28 Core transitions and 13 target events. Focus retains the frame
selected by source preservation. The actual handler cut includes that frame,
the armed action and the selected handler; physical-cut and clause uniqueness
identify the same witnesses used by M4 preservation. Ticket0 freshness follows
from the issued resource0/cleanup0 ledger.

The metadata endpoint in
[SourceScheduledCapture.lean](SourceScheduledCapture.lean) exposes the allocated
input contract, selected clause, derived rights and exact successor shape from
its existing preservation proof. The original endpoint remains a wrapper with
the same statement. Resume and close footprints are explicit chosen annotations;
this construction does not claim that those rows describe runtime work.

Every intermediate Core point relates to a constructed admitted snapshot. The
final world/history are `[0]`, issued owners are
`[resource 0, cleanup 0, ticket 0]`, and nothing is completed. The ticket rights
are the actual clause's required actions. All 25 affected modules pass fresh
independent compilation with standard axioms. The following construction extends
the same admitted prefix through first resume.

[CoreAdmittedResumePrefix.lean](CoreAdmittedResumePrefix.lean) reaches actual s35
after 35 Core transitions and 16 target events. Branch selection retains the
capture-selected data and symbolic resume/close rows. Source focus supplies the
post-resume frame; the current resume event determines owner0 and the complete
restored capture, caller frame, spent marker and outside spine. Saved owner maps
come from the existing relation, with an exact physical-frame equality; physical
frames alone do not determine those maps.

Every intermediate Core point relates to a constructed admitted snapshot. The
world/history and issued ledger remain unchanged, completed owners become
`[ticket 0]`, and the resume, disposal and annotated stores remove owner0. Ticket
rights remain unchanged. Fresh independent warnings-as-errors compilation and
all seven dependency reports pass with standard axioms. Its metadata endpoint
retains the already-derived focus context/scope and handler identity/clauses;
the original theorem remains a wrapper with the same statement.

[CoreAdmittedSecondCapturePrefix.lean](CoreAdmittedSecondCapturePrefix.lean)
extends that same admitted execution to actual s40 after 40 Core transitions
and 20 target events. It splits the saved annotations while retaining their
owner maps. Source preservation supplies the second focused frame; the actual
handler cut, exact effect identity and selected clause determine the same second
capture on both sides. The first and second captures keep separate chosen
resume/close rows and source-selected input contracts.

Every Core point relates to an admitted snapshot. The intermediate calculus
state between plug and bind is also admitted, even though those two target
events match one Core return-bind transition. The final world/history are `[0]`,
issued owners are `[resource 0, cleanup 0, ticket 0, ticket 1]` and completed owners
are `[ticket 0]`. The post-resume frame and spent ticket0 remain outside the new
capture, which retains the armed cleanup and handler. All three affected modules
pass fresh independent compilation with standard axioms. The following endpoint
connects that same admitted state through discard.

[CoreAdmittedDiscardPrefix.lean](CoreAdmittedDiscardPrefix.lean) extends the
same source-selected second capture to actual s45: 45 Core transitions and 22
calculus events. It retains both capture epochs' symbolic rows, selected ports,
authenticated saved owner maps, cleanup, handler and pending frames. The current
false branch is preserved before constructing `Allocating.Request.discard`.
Fresh close0 follows from the actual issued ledger. Event inversion determines
owner1 and the exact retained lexical unwind stack; the physical projection
comes from the same mapped owner cut.

Every intermediate Core point remains related to an admitted snapshot. The
final world/history stay `[0]`; issued owners are
`[resource 0, cleanup 0, ticket 0, ticket 1, close 0]` and completed owners are
`[ticket 1, ticket 0]`. All three stores remove owner1, with ticket rights
unchanged. The existing owner-head decomposition is public and reused without
changing its statement. Three affected modules pass independent compilation;
the combined audit covers 836 registered modules and 11,359 exact standard-axiom
reports. The admitted-completion proof above extends this same prefix through
final release. General metadata authentication and higher-order admission remain
open.

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
the exported 55-node graph to that normalized source. `CoreGraphProgram` above
instead constructs direct admission for the actual exported root, including its
helper closures, bindings and entry wrapper. General Core admission and
simulation remain open.
