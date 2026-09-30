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
| D8 | Admission-interface gap | A sourced store and a row-checking context could disagree about a nested owner's protection. The earlier interface refuted the chosen post-resume suffix certificate. | The conditional `Interface.closingSeparate` field now excludes that mismatch; actual capture constructors derive it from ownership and uniqueness. Full kernel initial admission remains open. This is not a coherent Rust runtime counterexample. |
| D9 | Declaration-recipe gap | The current `ClauseRecipe` grammar puts the consuming invocation at the end of its branch; it cannot directly describe the normalized clause's resume followed by a cell write. | Preserve a finite rejection witness, then derive a structural suffix extension from existing request footprints and receiving-tail checks. The consuming prefix must remain valid with the suffix pending. This is separate from D8's row-certificate repair and does not justify weakening the fixture. |

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
are not Rust's dispatch trace, which omits cleanup registration entries.

### Actual Rust configurations

The test-only [alignment observer](../../../../src/eval/machine/alignment_trace.rs)
records pre-step configurations in the actual `Machine::run_loop`. It retains
structured controls, lexical environment entries and recursive function
templates, resource instantiations, heap contents, active and captured frame
vectors, live/consumed clauses, counters, limits, work accounting and traces.
Raw snapshots retain identity tokens. A separate comparison view renumbers
environment references and uses a consistent module map across the observed
run; it preserves distinct modules and rejects foreign closure arenas.

Ten focused tests pass, including a fresh independent run. They check result
and trace agreement with observation disabled, result 11 and cell writes 7 then
11, nearest exact owner selection and full-prefix restoration, lexical cell
capture, deterministic comparison across independent compilation, and an
unchanged resource-capacity failure with its observed prefix. Clippy with
warnings denied and formatting checks also pass.

The observer explicitly rejects arithmetic frames, general data, polymorphism,
hooks and native buffers. Such a rejection stops observation while evaluation
continues; two arithmetic cleanup fixtures exercise this distinction. Tests of
native/hook/polymorphic rejection use constructed states. These exclusions are
observer coverage limits, not new exclusions from Ash or changes to the declared
Core fragment. Snapshot-to-model conversion and step correspondence remain
unproved. The capacity test concerns a failed acquisition; it does not establish
discard atomicity or observation accounting inside every failing step.

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

This resolves the concrete D4 representation example through conservative
annotation refinement. It does not establish a general Core translation, exact
Core-row equality, arbitrary callable refinement or Rust closure correspondence.
Independent review and warnings-as-errors compilation passed. The Program
construction uses only `propext` and `Quot.sound`; its existing initial-state
wrapper additionally depends on `Classical.choice`.

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
explicit error; shape checking has not yet been proved to supply sufficient
fuel. No initial admission or execution correspondence follows from this syntax
component alone. Independent warnings-as-errors compilation passed.

### Actual Core export

The [test-only exporter](../../../../src/core/alignment_export.rs) compiles and
independently validates the restored-clause-suffix fixture before exporting its
55 reachable nodes to [CoreExportedFixture.lean](CoreExportedFixture.lean).
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

### Initial-admission interface repair

[CoreInitialExample.lean](CoreInitialExample.lean) retains the complete intended
normalized fixture and constructs source/authentication components for its cell
operations, user requests and cleanup around the complete protected body. Its
`clauseRows` and `clauseProtectedRows` now certify the full Boolean choice between
resume followed by a cell write and discard, over any cell identity. It does not
construct a complete `Program`.

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

The remaining declaration certificate exposes D9. The existing consuming recipe
grammar ends each branch in an invocation; the actual resume branch ends in the
cell write. `effectfulSuffixRecipeRejected` proves rejection of that dependency
family, and `resourcePlanCertificateRejected` lifts it to this exact plan. These
theorems do not refute every possible decoration of the source expression.
The next extension must transport a consuming prefix across a pending plain
suffix using static request footprints and receiver checks. Full `Program`
construction, the actual graph-translation bridge and general admission remain
open.

[SourcePlainSuffixTransport.lean](SourcePlainSuffixTransport.lean) supplies the
standalone transport needed by D9. `plain_suffix_admission` constructs checking
for a consuming prefix followed by a suffix from the prefix's current check,
the suffix's structural request footprint and finite operation checks at the
actual receiver. It transports selected handlers and owners, retained captures,
resume restoration and discard waiting contexts while retaining the actual plain
frame. The inserted suffix executes during ordinary return and is skipped during
unwind. No constructor takes successful future execution or a future `Pending`
proof. Fresh independent compilation and review pass with standard axioms only;
declaration-recipe integration and full initial admission remain open.
