# Provider experiment execution record

> Active experiment tracking for [the plan](plan.md), governed by
> [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md).
> Candidate P-1 is specified in [semantics](semantics.md#selected-first-execution-contract).
> This record assigns work and evidence. It has no independent semantic or
> architectural authority and leaves the current tree when this work finishes.

## Current checkpoint

As of 2026-10-02, the corrected B3 private checkpoint is independently reviewed.
Local-call correspondence is the next active slice. The completed slices below
are experimental components, not current language behavior or completed source
cases.

| Boundary | Verified state |
| --- | --- |
| Native SQLite and physical arena backing | Independently reviewed safe APIs; 37 native tests pass. |
| Declaration/instance front end and foreign registration | Independently reviewed parsing, resolution and canonical registration; public checking guards remain. |
| Private lifecycle templates with imported helpers | Independently reviewed Connection acquisition/finish and Statement acquisition with its enclosing Connection association. The last frozen batch passes 1,397 library and 566 integration tests; scoped Clippy passes. |
| B3 source data, prerequisite dictionaries and method-local parameters | Independent contract and quality review approve the corrected frozen checkpoint, including the interim local-call guard. It passes 1,413 library and 593 integration tests across 31 targets, scoped Clippy, formatting and diff checks. |
| Lawful local imported forwarding | Active; retained source occurrences and actual call/capture correspondence must replace the interim refusal. |
| Handler templates, atomic module publication, instances and complete control validation | Pending; private lifecycle checks do not discharge these boundaries. |
| Public runtime and S/M/X cases | Pending; S-01 is prepared but has not executed through the public driver. |
| Results, blueprint, tooling and product adoption | Pending; successful evidence precedes adoption and normative specification changes. |

The starting evidence and observations below retain the sequence of discoveries.
Later reviewed checkpoints supersede earlier pending statements within their
explicit scope. The case ledger changes only after actual source observations.

## Starting evidence

### Completed native checkpoint

N0's copying adapter is implemented in the root workspace's
[foreign-adapter](../../../foreign-adapter/README.md) crate. Its 21 tests,
warnings-denied Clippy and rustdoc checks, formatting and diff checks passed.
Independent review confirmed the pinned header and runtime provenance and the
safe API's consumption, refusal, partial-owner and copying contracts. Recorded
inputs and limits are in [environment.json](environment.json).

Physical arena backing is also implemented in the same crate and independently
reviewed for contract conformance and Rust safety. Its 16 tests cover real
bounded storage, alignment, non-owning keys, immutable publication, rollback and
cleanup. The combined native package passed 37 tests, warnings-denied Clippy and
rustdoc, formatting and diff checks. This supplies host storage primitives only;
checked Ash layouts, encoding, lifetime/dependency checking and the evaluator
bridge remain pending. Native tests do not complete any M case.

Independent review also found P-1 ready for implementation within its selected
synchronous copying profile. Review corrections made source/native error
mapping, callable authority boundaries, lifecycle rows, state lineage, template
validation and body-free public facts explicit. This is an experimental contract
checkpoint, not a claim about implemented Ash behavior.

These checkpoints do not complete an Ash-source case. F0/F1 declaration and
instance parsing/resolution is implemented and independently reviewed. Thirteen
provider tests and one internal imported-origin fixture passed. Independent
review also passed 258 existing integration tests, all-target Clippy with
warnings denied, formatting and diff checks. A 256 KiB probe resolved and
disposed 128 nested instances; the retained regression covers success and late
rejection. Review corrections fixed iterative scheduling, frame size, grammar
diagnostics and exhaustive test walkers.

F0/F1 retains explicit checker, evidence and export-authentication guards.
The imported-origin fixture bypasses checked-summary admission for its isolated
resolver test; it does not establish admitted client use. T0 foreign registration
and admission is implemented and independently reviewed. Its final checks passed
1,306 library tests and 124 affected integration tests, warnings-denied
all-target Clippy, formatting and diff checks. Independent review reran 1,369
unique tests and verified the original malformed-state probes now reject.

T0 retains canonical signatures, operation roles, complete state operand paths,
owned and retained lineage, result constructors and sealed StateAccess identities.
Summary admission and linking independently authenticate its immutable
certificates. Ordinary native calls and source handlers remain unavailable;
passive registered imports and ordinary configuration construction work.
T1a declaration checking and retained typed templates is active. T1b instances,
T1c dependency/control validation and R1 execution follow the agreed descriptor
seam. The source S/M/X ledger remains unimplemented until actual fixtures cross
those boundaries. A-0's bounded arena contract also passed independent design
review; Ash typing, runtime integration and source evidence remain pending.

T1a's structural Core checkpoint passed independent review and 1,318 library
tests. Its private entry compares contextual metadata with independently
reconstructed registrations and authenticates native certificates before
allowing sparse imported identities. Final dense linked validation is unchanged.
The entry returns unvalidated Core: it grants no lifecycle, publication or
execution authority. Independent phase/ownership flow analysis is active;
authenticated external environments, handler templates and retained typed
template publication remain pending.

Structural quality review found an omitted operation annotation origin in the
canonical comparison. The correction uses the existing cumulative, iterative
origin comparison. An annotation-origin-only regression first failed and then
passed for changed and absent source origins. Independent re-review resolved
that finding; phase/ownership flow remains outside this structural approval.

The unpublished Current-state ownership analysis passed eight focused tests and
independent conformance and Rust/API quality review. Evidence covers native
outcome branching, duplicate completion, guard loss, aliases, phase boundaries
and bounded cleanup. The implementation owner passed 1,326 library tests before
StateAccess landed. Review found uncharged global native-fact scans: adding one
canonical state and 64 operations initially left the measured cost unchanged.
The corrected immutable local index charges every module, record and lookup,
reserves fallibly and rejects duplicate defining IDs. The new regression passed
exact and one-short work limits; independent re-review resolved the finding.
This approval establishes ownership classification only. Complete report-role/
error fidelity, independent mapped payloads, Enclosing-state access and
authenticated template-entry capabilities remain required before executable
template admission.

The unary `ProviderStateAccess` Core substrate is implemented in
[effect.rs](../../../src/core/effect.rs) and
[transform.rs](../../../src/core/transform.rs), and passed independent scope
and Rust/API quality review. Six new tests passed; the affected effect and
transform suites passed 25 tests. Evidence covers ordered type metadata,
substitution, one operand, operand-row replay, identity/origin preservation,
exact work boundaries and iterative partial-failure disposal. Clippy passed
with warnings denied and an explicit dead-code allowance for active T1 code;
scoped formatting and diff checks passed. This approval covers representation
and rebuilding only. Descriptor, phase, Enclosing-lineage, capture and runtime
admission remain closed.

Direct source StateAccess now emits unpublished typed draft Core from checked
local header associations. Five tests passed: Statement acquisition selects
Connection's association despite their distinct native effects, targeted
renaming preserves the canonical method identity, and first-class/callable,
wrong-operand and missing-association paths reject. Independent conformance
review approved that source slice. Rust/budget review found two gaps: separately
retained argument carriers lacked distinct precharges, and a cloned/displaced
type could lose iterative ownership across a later failure. Both regressions
first failed, including an isolated small-stack overflow, and then passed after
separate precharges and guarded cloning/duplicate-formal rejection. Independent
re-review approved the correction; exact/one-short work and iterative cleanup
tests passed. Imported raw resource facts, ordinary evidence,
independent Core association/Enclosing validation, capture and runtime still
provide no admission authority.

The unpublished independent Core association check now validates the exact
defining relation, ordered resource arguments, associated state type and operand
row. Its three tests also check enclosing-state coordinates, callable barriers,
coherent wrong-owner mutations and deep untrusted metadata disposal. Independent
contract review approved this slice. Rust/budget review found that shared source
and Core state scans visited nullary effect labels without charging for each
label. Paired regressions observed cost 3 for both empty and 64-label rows; after
precharging the labels, the wide rows cost 67. Exact, one-short, prefix and fresh
retry checks passed. Re-review approved the correction and association slice.
Header associations still provide no descriptor certificate or runtime authority.

Before the next lifecycle-entry review corrections, one combined command passed
1,355 library tests and 37 integration tests: foreign admission (20), SQLite
preparation (4), provider resolution (7) and provider syntax (6). The direct
StateAccess import tests now assert the source diagnostic produced by controlled
phase checking; a separate method-value test retains the closed generic-method
guard. Their correction passed independent review. Lifecycle-entry and report
proofs are under review; template publication, capture and execution remain
pending. This is a batched regression checkpoint, not whole-worktree verification
or an executed S-01 case.

The private [lifecycle-entry proof](../../../src/core/provider/entry.rs) and
composed flow now passed independent contract and Rust/API quality review.
They compare canonical local declaration/template identities, ordered source
and generated formals, separate answer/row binders, exact input and state types,
wrapper types/rows/origins, source report constructor roles and registered error
monotypes. Native consumed-success and consumed-error outcomes remain distinct
through source mapping; independent pure error mapping is permitted. Review
mutations exposed four incomplete metadata relations and an aliased source
answer binder. All reject after correction. Connection and Statement acquisition
and finish, two-formal relations and cumulative failure/retry checks passed.

The corrected entry batch passed 1,358 library tests and the same 37 integration
tests. A later focused batch passed 59 provider tests after the final answer
guard and constructor cleanup repairs. Rust review found that the existing
draft compiler dropped deep input/result/function types recursively if a later
clone failed. Two shared production assembly helpers now retain iterative
guards through sibling type/row and parameter cloning. Isolated 256 KiB tests
reproduced three late stack-overflow paths before repair, then passed with
32,000-level untrusted metadata, prefix/exact/one-short budgets and fresh retries.
The fixtures test assembly and disposal, not accepted source or deep admitted
Core. This approval authenticates unpublished local entry and lifecycle flow;
the caller supplies canonical local provenance. Imported helper authentication,
final dictionary ABI lowering, handlers, atomic publication, instance validation
and execution remain pending.

The subsequent plain imported-helper checkpoint now passes 73 focused
provider/capture tests and one combined run of 1,375 library tests plus 111
integration tests. The latter includes module and provider suites and the five
existing resource/control targets used at baseline. Canonical actual imports
determine full normalized `Forall` types and kinds. Actual helper applications
retain their defining binder and inferred type application through aliases;
flow combines independent operands/results with selected callable results,
control and stored captures. Two regressions reproduced the old query accepting
unknown lexical captures and unmatched metadata. The correction distinguishes
metadata slots and permits only the actual canonical application parameters.
An unrelated noisy helper does not poison the selected call.

Statement acquisition now composes that helper context with an enclosing
Connection state association. A proof tied to the immutable program and exact
StateAccess nodes checks method, definition, arguments, operand/result types and
rows before contextual structural acceptance; existing phase/lineage flow then
runs. The contextual registry compares exact independent canonical metadata
before accepting sparse IDs whose allocation order differs from textual order.
Field/row mutants, changed origins and coherently changed identities reject.
Ordinary final validation remains closed. Cumulative exact/prefix/one-short and
fresh-retry tests measure 3,538 work units for external acquisition and 13 for
the selected-capture fixture. Independent contract and Rust/API reviews approved
the exact private bounded slice. The Rust review checked ownership guards,
iterative failure cleanup, borrowed proof lifetimes, metadata relocation and
normalization equivalence. Scoped formatting passed after mechanical correction.

Contract review requested a concrete transitive generic counterexample:
`prepare<B> : B -> B` calls `identity<A> : A -> A`. Both the dependency and each
lifecycle source compile, but contextual checking refuses configuration and
close-error calls with `ResourceEscape`. The outer metadata allowance does not
substitute the nested callee's formal context. A test-only addition reproduces
both phases; its provider/capture batch passed 74 tests after the combined run,
with no further production change. This is a valid P-1 support obligation, not a
source safety rejection. The constrained-helper owner now continues from this
reviewed checkpoint with staged evidence and actual call-context substitution.

The next helper fixture retains generic `normalize<A> : A -> A` with ordered
`Pass<A>` and `Stamp<A>` requirements. `Pass` declares two equal-typed methods;
`Stamp` declares a third. An initial blanket `impl<A> Pass<A>` fixture failed
ordinary dependency checking because its selection key contains only a bare
variable. That failure is fixture evidence, not the missing lifecycle bridge.
Concrete implementations for registered `OpenConfig` and `CloseError` repair
the fixture without changing current implementation rules. The dependency then
checks normally. The closed lifecycle entry reports `Internal(InvalidState)`,
but installing the real selector exposes another fixture issue: the alias-only
import brings names into scope and selects no implementations. It correctly
reports `Unsatisfied` when closing this call's obligations. The positive trial
adds `import helper (impl Pass, impl Stamp)`; the alias-only form becomes an
authority negative. Neither fixture failure is successful lifecycle admission.
Typed Core rewriting and independent admission remain under implementation.

The repaired positive now retains exact unpublished slots, lowers dictionary
Core and passes the private contextual check. A combined external-helper batch
passes 17 tests, including both lifecycle phases with concrete producers and
generic tuple-head producers for Connection, without enclosing state-access
associations. The former transitive generic frontier is now a
positive: actual nested source-call contexts pass through reconstruction from
canonical imported summaries. Capture correction prunes the obsolete source
method placeholder after its authenticated route replaces it, while retaining
the selected binder and evidence dependencies. Coherent ABI mutations, failure
and budget cases, broader regressions and independent reviews remain pending.
Evidence slots, descriptors and templates remain unpublished; this is an
intermediate B2 result.

The reviewed plain helper bridge accepts primitives, tuples and zero-parameter
native ordinary data, recursively inspecting canonical constructor payloads.
Its constrained and transitive-generic restrictions are the subject of B2's
connected positive tests above. B2 still excludes prerequisite dictionaries,
method-local polymorphism, higher kinds, source nominal and parameterized data,
and selected internally handled/resource control. Resource and provider-state
transport remain prohibited by P-1. Complete lawful helper contexts, handlers
and transactional template publication remain required. No S-01 case or public
provider admission follows from these private checks.

Read-only inspection also found an API-level capture gap: the typed query checked
nested callees' stored dependencies but could omit those of its initial target.
A direct regression exercises ignored unknown values and unresolved metadata.
The general query must check that target. Only the synthetic source wrapper
rebuilt from canonical imported facts needs a separate entry, because its
unapplied helper ports become bound at the nested call. Every actual helper and
producer target still requires capture checking. B2's final independent review
checks this boundary: the query accepts an opaque proof whose fields and
constructor belong to canonical reconstruction, rather than an arbitrary
capture summary. This finding does not show a public provider-admission
counterexample.

Constrained helper composition with Statement acquisition is still pending.
The earlier plain-helper test retains its authenticated enclosing Connection
association. B2's convenience compiler and checker currently supply no such
association, although the independent staged authenticator already accepts it.
The next composition case must carry that same checked relation through the
staged path and combine independent SQL normalization with Connection state
access. Missing and wrong associations must reject. This is an unwired support
seam, not a regression of the reviewed plain-helper path.

Following the user's batching instruction, one implementation owner runs Cargo
for related provider, capture and evidence changes. Focused regressions establish
the relevant failure, then combined library and affected integration suites
verify the shared boundaries. Root reads the receipts and maintains this record;
it does not run competing builds.

The correction batch passes 90 provider tests and 119 capture tests. It includes
direct constrained-path ABI and authority mutations, initial-target stored
capture checks, charged target lookups and cumulative output-builder work.
Compilation and independent checking pass exact, one-short and prefixed work
tests in both Connection phases. The new deep-refusal probe passes shallow
checking, bounded and unlimited rejection, and complete draft/fixture teardown
with 8,192-level metadata at 256 KiB. Its earlier 64 KiB failure occurred even
for shallow input and supplies no deep-disposal evidence. The existing cleanup
regression now also passes at its unchanged 256 KiB bound after extracting the
global-occurrence branch from the large expression dispatcher.

The final frozen B2 batch passes 1,394 library tests and 460 integration tests
across 20 targets. Isolated preparation/rebuild proofs verify width-sensitive
work, prefix/exact/one-short refusal and fresh retry. The shared transform's
existing exact accounting test includes the newly charged fallible carriers;
its one-short refusal, exact success and Arc lifecycle checks remain intact.
Independent contract and Rust/API/budget/ownership reviews both approve the
frozen 15-file slice after reading the actual receipts and checking its hashes.
Their lookup, rebuild-accounting, carrier and evidence-attribution findings are
resolved. Approval covers private Connection acquisition and finish with no
enclosing state-access association, within the data and producer limits above.
Whole-worktree Clippy/`xtask`, constrained Statement composition, complete P-1,
template publication and source execution remain pending.

Constrained Statement composition is now active. Its dependency and both local
headers check normally. The actual SQL operand is registered `Native.Bytes`;
the native manifest defines no `Native.SqlText` family. The first staged source
trial fails at `Provider.state_of db` because the compiler supplies no exact
checked local header association. This is the missing wiring to replace, rather
than an invalid helper or a changed native ABI. The owner now carries the same
canonical association through the staged compiler, independent authenticator
and flow entry. Missing/wrong associations, exact work limits and unpublished
failure/retry remain required evidence.

That composition now passes independent contract and Rust/API/budget/ownership
review. Its unfiltered frozen batch passes 1,397 library tests and 566
integration tests across 26 targets, including all 53 baseline runtime/native
resource cases and 53 scoped-evidence interactions. Scoped Clippy passes with
warnings denied and only the active T1 dead-code allowance. Formatting and
whitespace checks pass. Exact work is 2,229 units for association cloning and
source compilation, and 9,813 for independent checking; exact, prefixed,
one-short and fresh-retry cases pass with source slots empty.

Evidence includes renamed imports and helper-file deletion; missing, duplicate
and changed association state/definition/family/formals; changed Core method,
owner, arguments, operand/result types, rows and enclosing identity; wrong
lifecycle phase; and helper transport of native state or an enclosing owner.
The compiler and checker forward the existing checked relations through thin
entries, with no new certificate or native ABI. This adds private Statement
acquisition to the reviewed constrained helper fragment. Prerequisites,
method-local polymorphism, canonical source data, internally handled control,
handlers, publication and execution remain pending. Full `xtask` verification
is not claimed.

B3's dependency now checks normally with transparent `Box<A>` data, decreasing
`Pass<Box<A>>` and `Stamp<Box<A>>` prerequisites, and `first<B>` called at
`Bool` and `Unit`. Concrete registered configuration, error and byte data
terminate the selections. The first trial had an invalid nested constructor
pattern; correcting it establishes a genuine source-positive fixture. The
retained lifecycle draft then fails with `Internal(Core(InvalidPayload))`.
This is missing bridge evidence, not a rejection of the helper's source types.

The ordinary lowerer emits prerequisite and polymorphic method anchors, but
the draft has no canonical method-evidence catalog installed. B3 factors the
existing catalog's checked fact inputs and authenticates imported owners
without claiming they have local definitions. Independent checking must also
authenticate every prerequisite route and compare the complete canonical
catalog; agreement between emitted anchors and supplied rows is insufficient.

Transparent instantiated data has existing canonical payload facts. Opaque
ordinary data remains unsupported by this private checkpoint because the
imported view does not supply its hidden payload family. Current linking rules
already retain hidden defining facts without granting source access; later
support needs an authenticated storage-fact input, not exposed constructors.
No B3 production admission or verification pass is claimed yet. Complete lawful
helper contexts remain a P-1 obligation.

The next connected batch passes the 94 incumbent provider tests, while B3
remains red. An ordinary linked counterpart now reproduces the same failure;
29 incumbent external-helper tests pass alongside both failing B3 cases.
The mismatch is a polymorphic prerequisite dictionary under a monomorphic
implementation method. Its emitted application targets the parent's requirement,
while the existing root application expectation targets the helper's different
requirement. Correcting this shared lowering/catalog relation precedes any
contextual admission claim. The supplied global row cannot authenticate the
nested application merely because its method and type agree.

Both new positives now pass: ordinary linked synthesis/validation and private
retained acquisition/finish with nested source data, prerequisites and distinct
method-local applications. Shared lowering retains canonical passive parent
rows and checks their actual prerequisite edges without requiring nonexistent
abstraction nodes. Carrier validation follows the independently authenticated
parent relation. Contextual checking reconstructs the imported catalog rather
than trusting its emitted anchors. No slot or public resource is published.

The first completed library batch reports 1,392 passing tests and seven
failures, all at existing exact-cost assertions in the catalog, validator,
transform and driver boundaries. The new checks change accounting; independently
derived cost corrections and exact/one-short/prefix/retry evidence are still
required. Review distinguishes restoration of pre-existing linked scan charges
lost during factoring from additional carrier and field-check work. The imported
lookup width regression confirms an undercharge: zero units versus 192 for
three 64-wide searches. Complete catalog/retry evidence remains pending.
The initial authority pass already authenticates polymorphic producer-node
metadata; a contrary preliminary claim was retracted. The added detailed check
is consistency checking. This is an intermediate positive, not a frozen B3
approval or whole-worktree verification.

The later library batch passes 1,407 tests. The provider/storage batch covers
actual imported catalog width, both lifecycle phases, Statement associations,
exact/prefix/one-short/retry limits and 8,192-level storage refusal/disposal on
a 256 KiB stack. Scoped Clippy passes. The broader integration run stops at an
outdated source-text cost formula; its correction and completed receipt remain
pending. These receipts precede the new authority probe below.

That coherent mutation keeps the original helper invocation and every dictionary
ABI node live, then directly calls an installed method that the helper does not
invoke. The selected method contains control outside the admitted private
profile. The checker accepts the mutation because a dictionary producer becomes
an ordinary callable flow fact, whose fallback checks state-free types without
the selected method's call relation. The correction distinguishes dictionary
carriers and permits their applications only at independently authenticated
prerequisite installation nodes. Global ABI staging and the actual helper call
remain separate. Correction and frozen review are pending; no public admission
or new helper-control support follows from this finding.

The corrected source is now frozen across 18 files. All 1,409 library tests
and 593 outer integration tests across 31 targets pass; child-process summaries
are excluded from that integration count. Scoped Clippy with warnings denied
and the active-code dead-code allowance, formatting and diff checks pass.
Independent contract and quality review follow sequentially.

Dictionary facts now remain distinct through direct reuse, aliases, type
application, tuples, branches, identity calls and captured local callables.
Only exact prerequisite installation nodes obtain the carrier application
permission, after independent canonical catalog/Core checking succeeds.
Ordinary fallback rejects nested carrier arguments. The unused noisy selected
method remains a positive; broader lawful callable/control contexts remain
unfinished.

Measured cumulative fixture work is 68,433 check / 12,891 compile units for
Connection acquisition, 144,266 / 33,484 for Connection finish and
69,561 / 13,907 for Statement acquisition. Exact/prefix/one-short/retry checks
retain the same staged prefix. These are compiler work units, not native cost
or elapsed-time measurements. Opaque ordinary data, generic evidence scopes,
handlers, atomic publication, instances, public execution and full product
verification remain outside this frozen slice.

Fresh contract review reproduced an inherited plain-import entry gap. With
valid line-based source syntax and explicit native config/error arrows, direct
control-bearing helper calls reject, but local functions forwarding to that
helper pass the raw plain entry in both acquisition and finish. Pure direct and
forwarded counterparts also pass that entry. The local function's ordinary
callable classification omits its imported callee relation; fallback application
therefore returns independent data without checking the actual helper call.
This demonstrates inconsistent private admission, not public execution or a
native memory failure.

The canonical staged entry rejects both pure and control-bearing forwarders
with `InvalidEntry`. Its source traversal finds one imported occurrence in
acquisition and two in finish, while retained occurrence counts are zero.
That is a missing lawful local-call correspondence bridge, not control-specific
rejection. Only the test file was reopened for this probe; the other 17 frozen
source hashes matched.

The interim correction retains unproved imported-call dependencies through
local functions, aliases, aggregate captures, recursive groups and argument/
return laundering. Direct authenticated calls and ordinary pure local data
computation remain distinct. This closes the unchecked raw entry without
claiming support for the rejected useful forwarders. The next connected
implementation must retain their source occurrences across callable phase
barriers and establish canonical call/capture correspondence before handler
drafts and publication. Lawful higher-order and internally handled helper
support remains required by the full experiment.

The corrected 18-file snapshot passes 1,413 library tests and 593 outer
integration tests across 31 targets. Scoped Clippy, formatting, diff checks and
all recorded source hashes pass. Seven source dependency/laundering variants
cover both lifecycle phases and exact/prefix/one-short/retry budgets. Direct
authenticated aliases and pure local arithmetic/data remain positive. Both
pure and control-bearing local imported forwarders now reject at the raw entry;
the staged occurrence-ledger mismatch remains. The original paired failing
probe is preserved. Fresh contract and quality review approve this corrected
snapshot with no blocking findings. All 18 source hashes match before and after
review; the coordinator preserved their exact snapshot as the next comparison
baseline. The useful local-forwarding bridge remains pending.

The corrected Connection finish check costs 144,279 work units; its compile
cost remains 33,484. Acquisition and Statement costs are unchanged from the
preceding frozen dictionary checkpoint. These measurements describe the private
checked fixtures only.

After the source and external-global cleanup corrections, the coordinator ran
`cargo test --locked --lib --quiet`: all 1,348 library tests passed. The
remaining library-test warnings concern active T1 handler/template fields.
This is a regression checkpoint for the compiled private components; independent
Core association/Enclosing validation and the complete executable provider path
remain unfinished.

After the new Core operation landed, the coordinator reran the five affected
builtin resource/effect suites used at baseline: all 53 tests passed, including
capture/resume/discard, structural completion and both Core transforms. This
checks existing behavior across the new representation; it does not establish
experimental source admission or whole-worktree verification.

The concrete S-01 library/client bundle and its
[preparation tests](../../../tests/provider_sqlite_source.rs) now exist. Four
tests passed: shallow source parsing/projection, preservation of the original
frontend depth failure, and SQLite resolution against normally checked
registered dependencies, plus the concrete client's public-driver failure at
the pending resource admission guard. The last pins typing's internal invalid
state and `type.internal`; it must become successful runtime evidence after
T1/R1. Independent review confirmed the ordinary modular path and all four
tests. SQLite declaration checking, importing client checking and execution
remain pending. These preparation tests do not complete S-01.

### Baseline and scope

The experiment worktree is `.worktree/provider-experiments`, on
`codex/provider-experiments`, based on
`124e164094a9a338fd5ce6a58f979da463285f28`. The carried design package is not
baseline implementation. All changes use the root workspace; `main` remains
untouched. No second parser, checker, runtime or probe workspace is admitted.
Useful experimental code may be retained. Unsuccessful or unresolved behavior
does not merge.

No commits have been made. Any future commit uses
`git -c commit.gpgsign=false commit`, without `-S`, following the user's explicit
request. Do not change global Git configuration.

Current Ash provides scoped builtin cell/native-buffer authority, fresh rigid
identities, stored dependency analysis and structural capture/completion. It
does not provide source resource declarations or general foreign interpretation.
The implementation derives `ResourceApi` from builtin module IDs, uses fixed
`ResourceMethods` arrays, checks integer initializers and stores builtin runtime
payload alternatives. Those facts identify extension seams; they do not define
the experimental resource contract. The affected current contracts are
[resource typing](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies),
[native-buffer execution](../../../spec/dynamic-semantics.md#scoped-native-buffer-execution),
[source grammar](../../../spec/syntax.md) and
[entry checking](../../../spec/static-semantics.md#globals-and-modules).

The transferable evidence is exact lexical selection and hidden capture
tracking, rather than builtin identity numbers. Arena allocation needs a
relational payload summary to admit safe outer projection. Retention and views
need a shorter access interval than owner liveness. Handler clauses depend on
the client's answer type and continuation row, so declaration templates must
instantiate ordinary Core handlers rather than pretend to be ordinary rank-2
source functions. Existing cleanup/control nodes can carry completion policy;
only the resource carrier owns guarded publication and native state. Global
resources, ownership transport, callbacks, processes, tracing and reference
counting remain excluded.

## Shared descriptor seam

Land the declaration registry before splitting callers. The following is an
implementation interface sketch; the checked relations in `semantics.md` govern
its meaning. IDs use existing module/ordinal conventions, and collections remain
budgeted and iteratively disposable.

```text
ResourceDefinitionId = (ModuleId, declaration ordinal)
ResourceDefinition {
  id, origin, family: NominalTypeId,
  parameters: [ResolvedTypeVariable], identity_position: 0,
  input: TypeTemplate, state: TypeTemplate,
  provider: InterfaceId, forwarding_methods: [MethodId],
  state_access: CheckedStateAccessRelation,
  provided: [EffectInstanceTemplate],
  interpreted: [RegisteredForeignInstanceTemplate],
  acquire: ControlledAcquireTemplate,
  handlers: [HandlerTemplate], finish: ControlledFinishTemplate,
  result: ScopeResultTemplate,
  retained_state: ValueRelation, completion: ControlRelation
}
ResourceInstance {
  definition: ResourceDefinitionId, outer_arguments: [Type],
  identity: TypeVariableId, handle: TypedBinder,
  provider_evidence: LexicalEvidenceId,
  provided_instances: [EffectInstance],
  initializer: expression/node, body: expression/node, origin
}
ForeignRegistration {
  library_id, manifest_origin, type/effect/operation identities,
  operation_schemes, roles: Acquire | Borrow | Finish,
  state/dependency/access/postcondition relations,
  constructor identities, safe adapter dispatch
}
```

The concrete source carrier is `SurfaceResourceDefinition`: visibility/name,
ordered parameters, `input`/`state` surface types, `result` type plus one answer
parameter, `provider` interface application, `effect` and `interpret` instances,
acquire binder/body, finish binder/body, handlers state binder/clauses and spans.
`ResolvedResourceDefinition` preserves these as resolved identities and templates;
checking admits `ResourceDefinition` above. Resolution predeclares the opaque
nominal family, resolves the initializer before the fresh instance binders, and
defers outer parameter inference to initializer type unification in elaboration.
Native signatures use canonical native data and state families; controlled
`Provider.state_of` follows a descriptor's sealed state-access relation without
import cycles or nominal spelling tests.

A registry-backed generic descriptor replaces fixed builtin assumptions for new
definitions. Existing builtin descriptors may retain their current optimized
execution. The native library ID selects a registered safe operation; it never
selects a compiler-defined SQLite resource type. No state token or completion
report constructor is sufficient proof of lifecycle authority by itself.

Current module checking retains checked resolved body wrappers; final synthesis
elaborates those bodies again. Provider templates need a separate retained typed
Core table carried from `CheckedModule` through linking, with checked relocation
of references into the final Core environment. The public descriptor remains
body-free. Reusing an ordinary checked body wrapper would not meet P-1's
compile-once contract.

Existing `CheckedGlobalScheme` and `ImportedGlobalScheme` already retain the
defining binder, full constrained scheme, origin and immutable capture/control
summary. Import retention authenticates those facts across routes, and template
capture checking can consume the completed summaries without checking helper
source again. Canonical Core lowering must retain outer type quantification and
the ordered method-dictionary domains of every requirement; the scheme's value
type alone omits those domains.

The private [external-global catalog](../../../src/elaborate/provider_globals.rs)
now projects completed checked modules and admitted imports into those full
Core schemes. It retains defining binders, checked constrained schemes, origins
and shared capture/control summaries, and rejects conflicting duplicate
identities. Nine tests passed, including parity with existing final lowering,
ordered requirements/methods, aliases/re-exports, coherent-fact conflicts,
cumulative work refusal and iterative deep-metadata cleanup. Review during
implementation found missing independent charges for retained interface indexes;
a pre-copy refusal regression failed before the correction and then passed.
Independent conformance review approved the catalog. Rust/API quality review
found a failure path in its reused parent lowering: a substituted method type
lost iterative ownership before fallible application cloning. A constrained
deep-type regression reproduced the precise late-clone stack overflow in an
isolated small-stack process, then passed after retaining the guard through
application cloning and complete method installation. Independent re-review
approved that correction and the catalog's Rust/API quality. Two existing
lowering-budget tests also passed. These checks make no whole-worktree Clippy
claim while Core association work is active. The catalog creates no
graph nodes, admits no occurrences and authenticates no template entry or
publication.

Module-checking drafts currently emit source-scheme global variables and
provisional method occurrences. Final synthesis selects evidence and lowers
global calls to their dictionary ABI. A retained provider template must bridge
that distinction. The active checkpoint selects rewriting typed Core after
authenticated selections, using the complete final lowering environment.
Merely accepting external binder IDs would retain the wrong ABI. Template
publication stays closed until independent checking establishes that lowering
and relocation preserve P-1's compile-once contract.

The next constrained-helper checkpoint will rewrite retained typed draft
occurrences through the existing final dictionary-lowering chain. It must retain
exact occurrence roots, actual type/row arguments, slot identities and origins;
borrow checked selections from pending evidence publication; and rebuild the
graph without retaining obsolete source-scheme children. The lowering
environment needs both admitted globals and separately authenticated
implementation-method producers. Those producers are not ordinary imported
globals. Independent Core checking must derive dictionary order, producer
authorization and occurrence relations from the completed facts and selections.
Dictionary applications stage the ABI; the actual source argument invokes the
helper's capture/control relation once. No provider source replay or early slot
publication supplies that proof.

The proposed regression dependency has `Pass<A>` methods `first` and `second`,
then `Stamp<A>.stamp : (A, Int) -> A`. Its generic `normalize<A>` helper uses all
three methods and is called with native configuration and close-error data.
The final ABI has those three method domains before `A -> A`, in requirement
and declaration-method order. Swapping the equal-typed `first` and `second`
dictionaries must reject even though ordinary arrow types still agree. Batch
evidence also covers exact producers and slots, missing imports, type relocation,
pending-slot failure, cumulative work refusal and checking without helper source
bodies. This pure fixture does not establish hidden continuation-row relocation.
Handler drafts and broader lawful helper control remain subsequent requirements.

After B2's independent reviews, the next connected helper fixture combines
source `Box<A>` data, decreasing prerequisite selections through two `Box`
levels, and a method with its own type parameter. Concrete native configuration
and close-error implementations terminate the selection tree. The helper calls
the polymorphic method at distinct actual types; lifecycle calls wrap and then
project ordinary payloads before native acquisition or completion. This tests
existing language obligations rather than extending implementation selection.

Use the ordinary method-evidence catalog and independent producer expectations
for this slice. The existing lowerer and capture adapters already represent
prerequisite graphs and method-local parameters. Factor their canonical inputs
for imported contextual references; do not fabricate a validated module or
derive producer expectations from emitted anchors. Source data checking must
substitute canonical payloads and newtype representations, respect opaque
source access, and distinguish differently instantiated recursive relations.
A nominal head alone cannot prove independent data. Budget/failure tests and
coherent prerequisite, adapter and payload mutations precede admission.

The ordinary Core variable and scope checks accept graph binders only. T1's
contextual entry therefore needs authenticated checked-global lookup and the
relevant requirement, method, occurrence and authorization facts for evidence
validation. Local scheme headers precede completed body/capture facts, so they
cannot authenticate a published template on their own. Stage those facts until
whole-module publication succeeds. Regression evidence must reject coherently
changed external annotations or dictionary order against unchanged checked
schemes, and must publish no evidence slots or templates after failure.

T1 has three sequential review checkpoints: declaration and template admission;
initializer inference, exact evidence and Core specialization; then actual value
dependencies, completion/control and complete validation/transform coverage.
One implementation owner keeps the shared catalogs coherent. Replace each
pending guard only after its independent replacement proof exists. Runtime
implementation receives the validated interface after all three checkpoints.

### Local-call correspondence before handler drafts

Current function checking saves and clears `provider_context` before the
body, then restores it at function completion. Imported globals still record
ordinary obligations and capture uses, but `retain_provider_global_occurrence`
uses that same context as its recording condition. The source walker traverses
function bodies and recursive initializers, so independent occurrence comparison
detects the missing records.

Give template occurrence retention a lifetime separate from controlled native
phase authority. Retain exact source slots, kinds, type/row arguments, roots and
origins through the existing selection and lowering path. Callable barriers
must continue to clear native phase and StateAccess permission.

Local invocation needs its actual graph and lexical environment, not an invented
global scheme. Reconstruct capture/control facts from draft nodes, canonical
imported summaries and exact selected-method/adapter routes. Reuse the existing
independent typed-call analysis, which tracks actual code, type and value
contexts. Its generated source-wrapper exception cannot authenticate arbitrary
local functions. Unknown captures remain closed until their actual environment
is established.

First evidence admits ordinary pure local forwarders in both lifecycle phases,
then independent captures, aliases and nested calls. Pair them with the same
typed control-bearing helper and coherent target, capture, source-slot and
metadata changes. Preserve exact/prefix/one-short/retry and iterative failure
cleanup. Broader generic/higher-order and internally handled helper contexts
remain subsequent obligations. This map records an implementation target;
the interim unproved-call guard does not complete it.

### Handler draft boundary after B3

After the local-call correspondence checkpoint, the connected source case
checks the existing Connection read clause,
then the Statement tuple/column clause, as unpublished generic templates.
Allocate distinct hidden rigid answer and continuation-row binders before
checking their bodies. Reuse ordinary operation substitution, irrefutable
pattern checking, resume-use checking and clause suffix-row replay from
`finish_handler`. A declaration has no handled client body, so factor the
clause inputs rather than fabricate a handler expression or body value.

Independent resume validation currently obtains its result and row from an
actual handler node. A private draft entry must reconstruct the corresponding
clause contract from the canonical declaration, operation, operand pattern,
state lineage, hidden binders and owned resume. Specialization later produces
an ordinary exact handler and runs ordinary validation. The lifecycle
tail-free row check does not establish handler validity; direct clause demands
and the continuation row need their actual relationship.

Positive evidence starts with those real clauses and checked helper/error
mapping. Nearby source and coherent Core negatives cover operation/result
types, coverage, patterns, resume identity/use, hidden type/row binders,
operand paths, authority laundering and state/owner escape. Late failure and
work-limit refusal must leave source slots, templates and descriptors
unpublished. This is a read-only implementation map, not completed handler
support or a new semantic decision.

### Whole-module publication boundary

The existing module checker stages body evidence and freezes public exports,
then reserves the remaining checked-body storage before publishing slots.
Provider checking must prepare and authenticate every descriptor, executable
template, public hidden closure and retained carrier before that same commit.
A later unrelated body failure or allocation/work refusal returns no checked
module or summary and leaves every source slot empty. Work already consumed
is not reset on refusal.

`CheckedModule` currently retains ordinary checked resolved bodies, which final
synthesis elaborates again. P-1 needs a separate privately retained typed Core
table through checked module grouping, evidence validation and final
relocation/specialization. The defining module supplies code; imports and
re-exports preserve body-free contracts and defining template references.
Required imported facts must survive preparation before `CheckedModule::new`
consumes them. Project completed pending global facts without manufacturing a
checked module or committing evidence early.

The front-end `ResourceTypeFact` carries no lifecycle authority and remains
rejected by public-summary authentication. Its replacement proof must cover
the complete descriptor and hidden closure before opening that guard. Evidence
includes helpers declared after their resource, aliases/re-exports/diamonds,
client checking without dependency source, and separate failure for missing
executable code. Removing or poisoning retained provider resolved bodies after
checking must not trigger source replay. Coherent descriptor/template, hidden
binder, native lineage, capture/control and dictionary mutations must reject.
Private acquisition/finish drafts and local header associations do not prove
this publication boundary.

Read-only lifetime inspection adds a retention/relocation obligation.
`EvidenceSlot::storage_id` is derived from its Arc allocation. Pending handles
and retained source occurrences currently pin it; Core catalogs retain only
the numeric ID. Ordinary linking keeps checked resolved bodies through final
synthesis, and ordinary transforms remap graph nodes without renaming those
occurrence IDs. A body-free owner can preserve distinct original allocations
after provider bodies are removed. It does not give repeated specializations
of one template distinct occurrence identities or substituted facts.
Independent design review supports the explicit relocation direction now
recorded in [semantics](semantics.md#evidence-occurrence-retention-and-specialization):
retain source provenance, create separately owned final identities for copies,
and validate each specialization against the recorded selections and admitted
defining context. Final catalog preparation precedes builder sizing.
Same-argument copies, generic dictionary scopes, complete index relocation and
acyclic retention remain required evidence. This approves the experimental
direction, not its implementation; current pinned B3 drafts are unaffected.

### Runtime boundary after validated T1

R1 receives admitted descriptors and executable templates, exact provided and
interpreted instances, operand paths, native operation registrations, owned and
retained identity coordinates, capabilities, report roles and complete control
contracts. Resolved headers or private drafts cannot supply runtime authority.
The current evaluator has builtin resource owners and structural capture,
resume, discard and disposal, but no registered provider execution or native
state access. Its singleton activation lookup also cannot identify both
Statement parameters. Extend the generic resource path from the validated
coordinates; SQLite-specific operation code belongs in the safe adapter.

Preflight and reserve storage before native acquisition. Move a successful
guard into the owner frame only after publication succeeds; late failure
destroys unpublished state once and never enters the body. Completion preserves
the body value while running the checked finish template. A retained finish
report removes source access and quarantines the owner with its native
dependencies; its storage and host teardown require accounting. Capture and
resume move ownership without reacquisition, and admitted discard uses the
existing structural completion order.

The safe adapter already covers the first SQLite path, except that the
registered Connection diagnostic has no public safe adapter method. S-01 must
run the retained source bundle through the public driver, independently validate
generated/transformed Core and observe native statement-before-connection
release. Repeated and simultaneous instances, real acquisition failures,
empty SQL, preflight/late-publication refusal and consumed/retained completion
are required observations. This map records dependencies, not runtime support.

## First source fixture

The [source library](../../../tests/fixtures/provider-experiments/sqlite-copying/sqlite.ash)
declares and exports the resource assemblies and effects in `semantics.md`.
It re-exports native configuration and lifecycle error families,
defines its own operation result and error families, and provides pure functions
`memory : Unit -> OpenConfig` and `select_parameter : Unit -> SqlText`. The
latter constructs actual UTF-8 bytes for `SELECT ?1`. Current equational globals
require a positive pattern count; these are functions called with `()`, rather
than unimplemented global value definitions. The client fixture has no direct
native calls. The [client](../../../tests/fixtures/provider-experiments/sqlite-copying/entry.ash)
uses an ordinary generic helper with explicit argument, row and provider
requirement. The originally planned four nested matches exceed the existing
frontend depth budget; that source is retained in
[entry-deep.ash](../../../tests/fixtures/provider-experiments/sqlite-copying/entry-deep.ash)
as a frontend failure, not a resource-safety rejection. Factoring preserves the
query, call order and nested result:

```text
import provider as Provider
import sqlite as Sqlite

main : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Provider.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Int>>>
main () = resource Sqlite.Connection<C> db = (Sqlite.memory ()) {
resource Sqlite.Statement<S> stmt = (db, (Sqlite.select_parameter ())) {
match Sqlite.bind_int (stmt, 1, 42) {
Sqlite.Ok(()) => after_bind stmt
Sqlite.Err(error) => Sqlite.Err error
}
}
}

after_bind<S, C> : Sqlite.Statement<S, C> -> Sqlite.Result<Int> ! {Sqlite.StatementOps<S, C>} where Sqlite.StatementProvider<S, C>
after_bind stmt = match Sqlite.step stmt {
Sqlite.Row => match Sqlite.column_int (stmt, 0) {
Sqlite.Ok(value) => match Sqlite.step stmt {
Sqlite.Done => Sqlite.Ok value
Sqlite.Row => Sqlite.Err Sqlite.UnexpectedRow
Sqlite.StepError(error) => Sqlite.Err error
}
Sqlite.Err(error) => Sqlite.Err error
}
Sqlite.Done => Sqlite.Err Sqlite.MissingRow
Sqlite.StepError(error) => Sqlite.Err error
}
```

Expected normal observation is
`Completed(Completed(Ok(42), Closed), Closed)`, with statement finalize preceding
connection close. Do not assert a display string until actual constructor display
has been checked. S-01 still requires the source to pass through
`driver::run_path` and its generated and transformed linked Core to pass
independent validation. Parser or resolver preparation does not establish those
obligations. The initial execution test must fail because P-1 support is
missing, after native smoke setup passes.

Pair this fixture with wrong initializer type, wrong connection parameter,
escaping statement, hidden capturing closure, forged provider evidence,
duplicated finisher and fabricated state/publication. Repeat with two live
connections and repeated activation at one source site. Native counters observe
actual acquisition/release, not a manually constructed trace pretending to call
SQLite.

## Work ownership and dependency order

Owners are roles assigned by the coordinating task. One writer owns each shared
file at a time. A listed seam transfers only after its current owner reports the
interface and verification. Tests are partitioned by suite to avoid shared edits.

Batch related edits and focused suites at meaningful checkpoints, following the
user's 2026-10-02 instruction. Coordinate Cargo runs so agents do not queue
duplicate compilations of the same workspace. A regression checkpoint may batch
several tests before the corresponding fixes; retain the observed failing causes
and rerun the affected batch after correction. Run broader checks when a shared
compiler boundary changes or a failure requires them. Batching changes the
schedule, not the contract, independent reviews or required exit evidence.

| Work | File ownership | Depends on | Exit evidence |
| --- | --- | --- | --- |
| P0: candidate contract and registry schema | Design owner: `semantics.md`, this record; coordinating task owns plan updates. | Context and independent seam review. | Typed declaration/instance/report/native authority contract; no compiler spelling with an unstated type. |
| N0: native setup and safe adapter | Native owner: `foreign-adapter/`, root Cargo membership/lockfile, native environment report. | Recorded ABI inputs and native contracts. | Matching headers/library, smoke calls; partial-owner guards, consumed finalize and retained close tests. |
| F0: declaration/registration descriptor | Front-end owner: `surface.rs`, `resolved.rs`, registry/module structures. | P0. | Generic identities, templates and imports; no third SQLite resource kind. |
| F1: parse and resolve declarations/instances | Front-end owner: lexer/parser, `resolve.rs`, `module.rs`; syntax/module suites. | F0 and registration interface agreed with native owner. | New source positions resolve with input-before-binder scope and preserved defining origins. |
| T0: authenticated foreign registration | Registration owner: foreign manifest modules, loader/driver configuration and resolved registration facts; foreign module suite. | P-1 admission contract and F0/F1 schema. | Generic registered imports, canonical signatures/roles/state/result facts and defining identities; no source spelling grants privilege. |
| T1: check and elaborate P-1 | Typed/Core owner: `kind.rs`, `types.rs`, `elaborate.rs`, evidence validation, Core effect/dialect/validation/transform and capture analyses; typing/Core suites. | F0/F1 fixtures and T0 authenticated facts. | Controlled lifecycle roles, exact handler types/rows, independent descriptor/instance validation and mutation rejection. |
| R1: execute P-1 | Runtime owner: evaluator machine/value/disposal and driver; runtime suites. | N0, T1 Core interface. | S-01 source-to-native path, guarded publication, reports, structural completion/capture and safe failure teardown. |
| S2: copying SQLite library | Library/runtime owner: Ash library fixtures and runtime/module suites; checker changes return to current seam owner. | S-01 complete. | S-02..S-05, actual bytes/null/empty distinction, temporary-file persistence, authenticated generic importing helpers. |
| A0: quantified coverage/layout contract | Design/Core owners: selected arena contract and descriptor extensions. | S-01 plus review. | Handler template coverage, sealed layout dictionaries, relational allocate/load summaries and failure policy. |
| A1: arena implementation/library | Native owner: backing storage; typed/Core owner: layout and relations; runtime owner: arena execution; separate arena suites. | A0, stable generic resource path. | M-01..M-05 with real payload storage, sharing, safe projection, deep-copy costs and rejected owner transport. |
| C1: completion/control composition | Typed/Core/runtime owners in their files; `provider_control.rs`. | P-1 completion and arena ownership. | M-06 and compatible SQLite capture/resume/discard, independent validation, required action-before-release order. |
| X0: retained/view contract review | Design owner: `semantics.md` only. | Copying and arena observations. | Release points, invalidation, branch joins and captured access specified before code. |
| X1: retained/view implementation | Existing seam owners; `foreign_memory_interactions.rs`, composed control suite. | X0, A1, C1. | X-01..X-04 positive and rejection cases; no silent copy in the borrowing candidate. |
| E1: compare assembly and authoring tools | Coordinating/library owners: `results.md`, `blueprint.md`, `tooling.md`; one small root-workspace tool if evidence warrants it. | All cases observed or explicit counterexamples retained. | Measured costs, useful API/friction comparison, native-build/contract report compared with manual workflow. |
| D1: adoption artifacts | Coordinating/design owners: adoption report and proposed semantic/architectural artifacts. | Successful evidence or clearly bounded partial result. | Current behavior/delta, trust assumptions, compatibility, target support and coherent proposed product checkpoints. |

Do not parallelize a caller change with an unagreed descriptor rewrite. The
front-end and typed/Core owners coordinate `resolved.rs` schema changes through
the front-end owner. Runtime changes begin against the validated Core interface.
Native safe APIs may proceed independently while their signatures are recorded.

Preparation of A1's physical arena block/table completed independently in
the existing adapter crate against the reviewed A-0 capacity, alignment and
publication contract. This slice stores opaque encoded bytes and checks
allocation keys; it supplies no authenticated Ash layout or lifetime facts.
Layout codecs, registration, family evidence, source checking and execution
retain A1's dependencies on the validated generic resource path. Native backing
tests cannot complete an M case.

## Case and evidence ledger

At creation, all Ash-source cases remain unimplemented. Native helper tests do
not change that status. The coordinating task updates case status only from
actual source fixtures and observations, with commands and outcomes.

| Cases | Required semantic evidence | Required observation |
| --- | --- | --- |
| S-01 | Input inference, two identities, exact operations, non-escape, controlled publication/completion. | 42, statement-before-connection release, distinct/repeated activations. |
| S-02 | No body after failure/empty input; guarded partial state. | Real open/prepare errors separately from injected failures. |
| S-03 | Independent copied bytes versus aliases. | 1/2/3 and empty/null distinctions; bytes copied. |
| S-04 | Body/finish report nesting, consumed versus retained authority, protocol checks. | Native finalization/close refusal separately from report fault injection. |
| S-05 | Public contracts, defining origins and helper relationships. | Temporary-file persistence after close/reopen; owned file cleanup. |
| M-01 | Layout evidence, checked arithmetic, complete publication and rollback. | Exact capacity, prior objects survive failure, payload/metadata measured separately. |
| M-02 | Alias and hidden closure capture relationships. | One node payload, repeated reads, no alias payload copy. |
| M-03 | Relational payload/load summaries, selected outer projection. | A reference usable after B; whole tuple and B reference rejected. |
| M-04 | Deep-copy relation, recipient dependencies. | Independent result after A closes, sharing duplicated or preserved as declared. |
| M-05 | No owner transport; repeated scope identity and completion. | Reusable scratch capacity, peak payload and metadata. |
| M-06 | Completion captures and interpreter/storage requirements. | Actions read live arena data before release on return/resume/discard. |
| X-01 | Retention creation/release and incompatible mutation. | Stable retained input; reset alone preserves retention; copy comparison. |
| X-02 | View interval and invalidating-operation conflict. | Live owner does not authorize stale view; copied output survives. |
| X-03 | Captured access obligation visible to surrounding handlers. | Resuming compatible handler succeeds; conflicting alias access rejects. |
| X-04 | Combined owned completion and consumed/retained reports. | Statement, connection, arena-using actions, arena release in checked order. |

For every case record candidate, fixture, parse/resolution/type/Core/runtime phase,
positive and negative outcome, causal diagnostic, explicit and inferred facts,
Core/native event agreement, completion, assumptions and measured cost. A
rejection due to an unsupported layout is not evidence of correct borrow or
escape checking. An unimplemented case is not a passing negative test.

## Verification and completion gates

Run affected suites per coherent slice and the existing resource/native-buffer,
module, evidence and Core suites for crossed invariants. Run `cargo xtask verify`
at coherent compiler/runtime checkpoints. Adapter unit tests verify only its
safe API/ABI boundary; public modular driver execution verifies the Ash path.
Check documentation links, authority labels and formal notation manually under
the [documentation policy](../../project/documentation.md).

Results, blueprint and tooling are written from observations. If a required
useful case fails, retain its counterexample and revise the design explicitly.
Report supported fragments and unresolved cases without narrowing success to
S-01. Product proposals and tasks precede normative specification changes.
Adoption requires the accepted contract, retained implementation, library APIs,
tests and specification to agree; integration into `main` is a separate gate.
No commit, merge or completion claim follows merely from this record.
