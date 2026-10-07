# Provider authoring observations

> This log records design and implementation observations under
> [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md).
> Observations motivate comparisons and tools; they do not establish language
> semantics or imply that the experimental cases have passed.

## 2026-10-01: declaration and instance types

The initial acquisition examples named configuration values without showing
their bindings or types. Introducing parameters made the names resolvable but
did not define the provider's input-to-state-to-access relationship. The revised
[typing study](semantics.md) makes that relationship a prerequisite for syntax.

The acquisition explanation also treated `Sqlite.Connection` as a provider
designator. The intended role is a resource type definition associating its
provider, formal identity, effect interface, and handlers. The instance refers
to that type definition and introduces a fresh lexical identity. Type and
provider roles must remain distinct in resolution and diagnostics.

Generic arena allocation exposes an existing boundary: effect operations have
no operation-local type parameters, and an ordinary handler covers one exact
effect instance. A generic allocation method needs a specified interface and
handler coverage; shorter source syntax cannot supply them implicitly.

Candidate assistance to evaluate after implementation: show a declared resource
family's initializer type, instantiated access type, provided effects, outward
effects, and result type in one diagnostic or inspection view. Compare this
with reading the declaration and inferred client errors manually.

## 2026-10-01: native setup

The recorded SQLite runtime exists while its development header and `pkg-config`
metadata are absent. A runtime version alone cannot establish build readiness.
The adapter implementation must record matching headers, ABI checks, linked
library, and source/version observations in [environment.json](environment.json).

Candidate assistance: a reproducible build-input report that distinguishes
missing development inputs from native acquisition failure and Ash typing
failure. Evaluate its value against the actual adapter setup rather than adding
a command solely because it appears useful.

## 2026-10-01: existing implementation boundaries

The inspected compiler represents only the two current builtins in its surface
resource designator, resolved API relation, generated method sets, initializer
checking, and runtime payload. A third library-specific resource variant would
preserve that closed model. The experiment therefore needs a declaration-driven
contract that crosses resolution, typing, Core validation, and execution.

Before implementation changes, the following affected baseline passed from the
experiment worktree at `124e164094a9a338fd5ce6a58f979da463285f28`:

```bash
cargo test --locked --test resource_scope_runtime --test native_buffer_runtime --test native_buffer_core --test effect_runtime --test resource_scope_core
```

The suites passed 14, 9, 3, 26, and 1 tests respectively: 53 tests. This confirms
the selected existing resource, handler, transform, and runtime behavior before
extension. It is not evidence for experimental foreign-library or arena cases.

## 2026-10-01: copying adapter evidence

The [native adapter](../../../foreign-adapter/README.md) now builds against the
recorded SQLite 3.46.1 header and installed runtime. Twenty-one adapter tests
passed, with independent contract and Rust safety review. The tests cover real
acquisition, partial failure, copied BLOB input/output, empty BLOB versus null,
statement consumption on finalization error, close refusal, and persistence.
Private publication and native-result injections are labeled separately from
actual native failures.

Review found that a suspect BLOB result needed an immediate SQLite error check
before another API call. A regression test first failed on the previous call
order and then passed after correction. This is a foreign API sequencing
obligation that a value-level signature alone does not express. The authoring
blueprint must include such obligations and identify their trusted adapter
boundary.

These observations support the native copying baseline only. They do not prove
Ash source admission, provider authenticity, lifetime checking, or completion
under captured control. Those require the source-to-Core-to-runtime experiments.

## 2026-10-01: physical arena publication

The native arena now allocates actual bounded payload storage and an object
table. Its 16 tests passed, with independent contract and Rust safety review.
Reservation failure happens before initialization; initializer failure or panic
preserves earlier publications and rolls back the unpublished bytes and cursor.
Object keys keep no owner alive and layout tags supply no Ash type authority.

The Rust initializer's successful return commits publication. The later Ash
bridge must prepare its result and access authority before returning success;
it cannot first publish and then rely on a native removal operation to recover
from failed admission. This requirement crosses the native/compiler boundary
and must be included in the blueprint.

Counters distinguish logical payload and slots from requested physical backing
and metadata. They exclude allocator overhead, codec scratch space and resident
memory. Allocation-failure and identity-exhaustion probes use explicit private
injection; they do not demonstrate actual host exhaustion. These observations
establish physical storage behavior, not Ash layout or lifetime checking.

## 2026-10-01: source fixture conventions

The first client fixture initially assumed exported global values
`memory : OpenConfig` and `select_parameter : SqlText`. Current
[global syntax](../../../spec/syntax.md) requires at least one equation pattern.
The fixture now uses pure `Unit` functions and calls them in the initializer,
following their arrow types. This correction adds no global value or
program-lifetime resource rule.

The source library also needs its own protocol error type: an ordinary native
nominal error cannot acquire additional source constructors through re-export.
P-1 therefore maps native operation outcomes into source-defined result/error
families in its handlers. Configuration and lifecycle error families can retain
their native identities.

## 2026-10-01: effect facade closure

T0 registration tests exposed a failure when a facade re-exported an effect
whose operation signatures referred to unselected type names. An ordinary
source reproduction showed that this was not specific to foreign admission:
summary construction omitted effect signatures from its hidden nominal closure.

Current [module checking](../../../spec/static-semantics.md#globals-and-modules)
requires those hidden kind and identity facts. The repair traverses selected
effect signatures while keeping source name selection separate. The ordinary
and native facade regressions passed, including hidden-name rejection. Both
import selection and summary freezing needed the closure repair. S-05 needs
checked resource/helper contracts; this closure repair does not establish that
case on its own.

## 2026-10-01: foreign manifest completeness

Independent T0 review admitted two malformed registrations: a native state with
no owner parameter, and an operation whose metadata omitted a second state
operand. Another regression exposed an omitted retained connection coordinate.
Admission now rejects all three. Canonical certificate checks also reject
mutated StateAccess declarations and checked mirrors during linking.

These checks establish manifest consistency, not arbitrary native conformance.
They show why a library author needs the complete owner, operand and result
relations alongside an arrow type. A contract-report tool should expose those
relations and their validation rather than merely list foreign symbols.

## 2026-10-01: report roles and generic types

The proposed completion report has two constructors with the same error
payload type. Their types cannot distinguish consumed ownership from retained
ownership. P-1 now selects an explicit
[positional codec](semantics.md#report-algebra-and-failure-order), using defining
constructor identities and order. It checks the generic payload templates
before substitution, because distinct formal parameters may instantiate to the
same type.

This is a reviewed design choice, not executed source evidence. Native calls,
guard lineage and controlled capabilities must establish the lifecycle outcome
before the runtime constructs its ordinary source report. A report constructor
alone supplies no ownership postcondition.

The registration permits several acquiring or finishing operations for one
state. Declaration checking must therefore follow the selected template's
actual result type and authenticated operation facts. Choosing the first
registered operation would introduce a restriction absent from the contract.
Candidate assistance: show the source report's constructor-role mapping and
the actual native lifecycle operations beside their types. Evaluate whether
the positional convention creates enough authoring friction to justify
explicit role associations.

## 2026-10-01: concrete source depth and helpers

The concrete S-01 bundle exposed two existing frontend limits before provider
checking. Nine nested byte constructors exceeded the structural depth budget;
equivalent local bindings construct the same `SELECT ?1` bytes. The planned
client's four nested matches also exhausted that budget: each match has weight
32 and the limit is 128. The exact client is retained in
[entry-deep.ash](../../../tests/fixtures/provider-experiments/sqlite-copying/entry-deep.ash)
with a precise frontend failure regression.

The candidate client source in
[entry.ash](../../../tests/fixtures/provider-experiments/sqlite-copying/entry.ash)
factors the post-bind computation through one ordinary `after_bind<S,C>` helper.
Its argument is `Statement<S,C>`, its result is `Result<Int>`, and its declared
row and requirement are `StatementOps<S,C>` and `StatementProvider<S,C>`.
The query, operation order and nested Scope report are unchanged. This adds an
explicit generic forwarding obligation to the checker evidence; raising a
frontend limit is not needed for that experiment.

All three preparation tests passed: shallow bundle parsing/projection, the
original depth failure, and library resolution against normally checked
registered dependencies. Resource templates remain raw resolver facts in the
last test. None proves client type checking or SQLite execution. The deeper
source rejection records compiler friction, not successful lifetime checking.

Candidate assistance: distinguish syntax recovery, frontend resource exhaustion
and provider-safety errors, and show which source nesting causes a depth failure.
Compare that guidance with the manual helper extraction and its explicit types
before adding a tool.

## 2026-10-01: public driver support boundary

The concrete S-01 client now runs through the ordinary public modular driver
with immutable native registrations. Loading, parsing and dependency admission
succeed before the existing closed resource-declaration guard rejects with
`Typing -> Internal(InvalidState)`, reason `type.internal`, and the text
"typed elaboration state is inconsistent". All four preparation tests passed,
including a regression for that exact temporary failure category.

The internal failure has no owning source span or module field. Identifying
the pending SQLite declaration check required the checked-dependency preparation
test and inspection of the guard. The diagnostic therefore describes compiler
inconsistency where the current experiment actually lacks implementation. It
does not explain the support boundary to a library author. Record this limitation
when evaluating diagnostics; replace the frontier regression with actual S-01
execution after T1/R1. It is not a source safety rejection or a completed case.

## 2026-10-02: declaration-to-Core type relations

Lifecycle-entry review found that comparing nominal heads did not establish an
exact registered error type. A coherently changed `CloseError<Int>` and matching
body metadata retained the head of registered `CloseError`, but registration
requires the latter monotype. Mutation tests also exposed unchecked wrapper
types and rows, discarded source report family/answer roles, and a missing
generated-binder identity check. A final coherent mutation made the source
answer binder alias a resource formal. Each failure was reproduced before its
correction; contract re-review approved the exact relations afterward.

The corrected entry checks whole types, constructor-role payloads, binder roles,
origins and rows. A result answer parameter remains distinct from the resource
identity even when both have kind `Type`. These are implementation requirements
for retained generic templates, not new source annotations or observed SQLite
execution. Rust/API quality review approved the corrected slice after repairing
late clone-failure cleanup in its draft constructor. Complete template admission
remains a separate obligation.

The helper catalog's earlier parity tests also show that a constrained helper's
Core scheme includes ordered method arguments absent from its source value
type. Current module-checking drafts retain source-scheme calls. Keeping the
catalog alone does not lower or authenticate those calls. The remaining bridge
must preserve selected evidence and completed capture/control facts without
compiling the provider source again. An imported helper query must use actual
admitted imports; a dependency's private globals supply no source-call authority.

## 2026-10-02: generic helper context

The first plain helper trial uses a normally checked imported
`identity<A> : A -> A` in acquisition and completion. Its source body compiles,
but contextual Core checking initially rejects the helper occurrence with
`Registry` at its Core node. The template registry retains imported effect
parameters; the helper's `Forall` parameters instead belong to its checked
global scheme. Deriving their kind context from that admitted scheme is a
separate obligation from comparing the occurrence's type annotation.

Capture inspection also found that the existing stored-value graph represents
lexical values and type metadata with the same slot form. A generic function's
captures can therefore contain a type parameter without retaining a runtime
resource value. The helper bridge needs to preserve that distinction and bind
metadata captures to the actual authenticated type application. Ignoring all
captures or treating all slots as resource captures would lose a different
part of the contract. This relation is under implementation; these observations
do not establish successful helper admission or execution.

Two regressions reproduced the old query accepting an unknown lexical capture
and an unmatched metadata binder. The corrected query checks selected stored
captures as well as callable results and control. Its metadata allowance comes
from the actual helper type application, rather than every type variable in the
template registry. Independent contract and Rust/API reviews approved the exact
private bounded bridge after the combined regression batch passed.

Combining Statement acquisition with the helper also exposed resolver pass
ordering. Resource header IDs are allocated after effect/interface IDs, so
sorting the canonical registry by ID can differ from textual parameter order.
The unpublished contextual checker compares exact canonical IDs, kinds, origins
and binder rows before checking the graph. That comparison supplies the ordering
relation for this projection; the ordinary final validator remains separate.
This is compiler bookkeeping pressure, not a new resource lifetime rule.

Contract review identified the remaining nested generic context explicitly.
An imported `prepare<B> : B -> B` calling `identity<A> : A -> A` compiles, but
the first query carries the outer formal metadata allowance into the nested
callee without substitution. A source counterexample reproduces contextual
`ResourceEscape` refusal in both acquisition and completion. The follow-up
provider/capture batch passed 74 tests, including that temporary frontier.
The refusal denotes missing implementation support here, not unsafe source.
The next helper bridge must instantiate each actual call context; allowing all
metadata identities would not supply that relation.

## 2026-10-02: constrained helper fixture and implementation selection

The constrained trial declares `Pass<A>` with two equal-typed methods and
`Stamp<A>` with a third method. Its generic `normalize<A> : A -> A` requires
both interfaces and invokes all three methods. The first trial used blanket
`impl<A> Pass<A>` and `impl<A> Stamp<A>` declarations. Ordinary dependency
checking rejects those heads with `impl.variable-head`, following the current
[implementation selection-key rule](../../../spec/static-semantics.md#implementations).
This is an invalid fixture, rather than a provider implementation failure.

Concrete implementations for registered `OpenConfig` and `CloseError` retain
the generic helper scheme and its ordered dictionaries. This dependency checks
normally. The closed lifecycle entry reports `Internal(InvalidState)` before
selection, but the real selector then exposes a second fixture error: the
alias-only `import helper as Helper` selects names and no implementations,
following the current [import rule](../../../spec/name-resolution.md#imports-and-namespaces).
Closing its obligations correctly reports `Unsatisfied`. Positive trials add
`import helper (impl Pass, impl Stamp)`; the alias-only form remains a negative
for missing implementation authority.

The private compiler must preserve each checked occurrence, actual type
arguments, selected evidence and final dictionary order without publishing
slots or checking helper source again. These fixture corrections test current
rules and create no new author annotations. The bridge remains under
implementation and does not yet establish constrained helper admission.

Staging also exposed an identity-preservation requirement. Ordinary
`EvidenceSlot::clone` intentionally gives an empty clone distinct storage;
filled clones share their immutable selection. A retained source occurrence
therefore cannot use ordinary cloning to refer to its original unpublished
slot. The private transaction needs exact empty-slot retention, with filled-slot
refusal and no publication. This preserves a checked selection relationship;
it does not change the source import rule or ordinary cloning behavior. The
whole-module publication checkpoint must still determine how source facts and
relocated template facts are committed together.

The first connected batch passes 17 external-helper tests. Concrete producers
and lawful generic tuple heads both check in acquisition and completion. A
tuple-head trial separates helper substitution `X -> (OpenConfig, Int)` from
producer substitution `A -> OpenConfig`, with corresponding `CloseError`
contexts in completion. The former nested-generic refusal also becomes a
positive. These are private checks; full ABI mutations, failure checks, broader
regressions and independent review remain pending.

Capture checking exposed an obsolete dependency in normally checked helper
summaries: lexical traversal retained a source method placeholder after the
value graph had replaced it with an authenticated selected route. That
placeholder appeared as an unknown global. The correction stops lexical
traversal at the replaced occurrence and preserves its actual selected binder,
abstract evidence and separately collected type metadata. Canonical imported
summaries and exact pending selections reconstruct the actual source-call
analysis; a compiler-generated capture summary supplies no separate authority.

Read-only inspection of the typed query found a separate API-level gap. Its
initial target's stored dependencies were not checked like nested targets, so
an unused unknown value or unresolved metadata could evade that query. Direct
regressions now cover this distinction. The general entry checks initial
captures; the canonically reconstructed source wrapper needs an entry that
defers its symbolic ports until the nested helper call binds them. That exception
must be confined to the reconstructed wrapper, and all actual helper and
producer captures remain checked. Independent review and the broader regression
batch are pending; no public admission counterexample has been established.

Independent review found two uncharged target scans in the typed query. Adding
64 target records initially changed lookup cost by zero; the retained regression
expects the added scan work. Review also found that the replacement ABI builder
started a fresh work ledger and did not debit its payload-copy work to the caller.
Both are bounded-work requirements for the new bridge. Their corrections,
fallible rebuild carriers and broader verification remain in the active batch.

The new deep-refusal probe initially used 64 KiB. A shallow query already
overflows that stack before any deep metadata is created, so its failure does
not demonstrate recursive disposal. The probe will use the established 256 KiB
bound for its actual deep failure and teardown checks. Separately, the existing
256 KiB cleanup regression fails during source elaboration. Stack traces point
to the enlarged expression task, rather than evaluator cleanup. Moving retained
occurrences into a ledger and factoring the global-occurrence branch addresses
that crossed compiler boundary; the existing test and bound remain unchanged.

Review distinguishes the existing plain Statement helper/Connection-state
association test from B2's constrained Connection trials. The staged
authenticator accepts associations, but its current convenience compiler and
checker pass none. Constrained Statement composition remains a required wiring
case. Existing plain-path ABI mutations also cannot establish constrained-path
mutation coverage; direct staged mutations are being added.

The connected correction batch passes 90 provider tests and 119 capture tests.
Direct staged mutations now cover ABI types/kinds/rows, private or unimported
Core binders and forged retained source identities. Target lookups precharge
their scans; each rebuilt output node uses the caller's remaining allowance
and debits actual builder work on success or failure. Carrier reservations are
fallible and retain iterative owners. Exact, prefixed and one-short compilation
and independent-checking cases pass without publishing slots.

At 256 KiB, the deep-refusal probe completes shallow checking, limited and
unlimited rejection, and both draft and fixture teardown. Factoring the exact
global-occurrence branch restores the existing 256 KiB cleanup regression
without changing its test, bound or evaluator behavior. Both independent
reviewers have checked the corrections statically; frozen broader receipts and
final approval remain pending.

The final frozen batch passes 1,394 library tests and 460 integration tests
across 20 targets. Independent contract and Rust/API/budget/ownership reviewers
verify the same 15 source hashes, read the actual receipts and approve the exact
private Connection acquisition/finish fragment. All their raised findings are
resolved. Source slots and public admission remain closed. The next composition
case is constrained Statement acquisition with its authenticated enclosing
Connection relation; prerequisites, method-local polymorphism and canonical
source data follow. Full P-1, whole-worktree verification and source execution
remain outstanding.

## 2026-10-02: constrained Statement association composition

The next source fixture combines the constrained helper with Statement
acquisition and its enclosing Connection. The native prepare signature takes
`Native.Bytes`; `SqlText` from the surface library must not be mistaken for a
native manifest family. The helper dependency and both resource headers check
normally. The initial staged compiler then rejects `Provider.state_of db` with
the source diagnostic requiring an exact checked local header association.
The staged convenience entry supplies none. Carrying the existing checked
relation through that entry is the active correction; no native ABI change,
provider source replay or new authority mechanism is required.

The corrected association path passes fresh independent contract and
Rust/API/budget/ownership reviews. Its frozen batch passes 1,397 library tests
and 566 integration tests across 26 targets, including the existing native
buffer and resource runtime suites and scoped-evidence interactions. Scoped
Clippy, formatting and whitespace checks pass. Actual measured work is 2,229
units for association clone plus compilation and 9,813 for independent checking;
exact, prefixed, one-short and fresh-retry cases preserve empty source slots.

The same association reaches source checking, canonical staged authentication
and lifecycle flow. Missing, duplicate and changed associations and Core access
fields reject, as do wrong phase and helper state/owner transport. Aliases and
deleted helper source preserve defining identities. Source `SqlText` remains a
newtype over `Native.Bytes`; the native prepare signature is unchanged. This
establishes private Statement acquisition in the constrained helper fragment,
not public admission or SQLite execution.

## 2026-10-02: source data and recursive method evidence

The B3 helper defines transparent `Box<A>`, structural implementations with
decreasing prerequisites, and a method-local parameter `first<B>`. It calls
that method at `Bool` and `Unit`, then calls the remaining monomorphic methods
in declaration order. Two `Box` levels expose recursive prerequisite selection;
concrete native configuration, error and byte implementations terminate it.
The dependency checks under current Ash rules. An invalid nested pattern in
the first trial was a fixture error; the corrected lifecycle draft reaches
`Internal(Core(InvalidPayload))` during retained lowering.

Ordinary final lowering already constructs the required adapters and catalog.
The retained draft needs the same canonical facts before building its anchors.
Imported helper and implementation owners have authenticated metadata but no
local definition envelope. That distinction must be explicit in contextual
validation, while retaining exact selections, prerequisite routes, method
parameters and dictionary order. Emitted anchors cannot authenticate their own
expectations. Source slots remain unpublished during this work.

Storage checking must inspect the payload of each exact instantiated nominal,
rather than infer independence from its head or an absent visible constructor.
Transparent data facts suffice for this fixture. Opaque ordinary data is an
input gap in the current imported storage view, not proof of empty storage.
The [linking rules](../../../spec/elaboration.md#module-linking-and-entry-generation)
retain defining facts needed by Core, while the
[hidden import closure](../../../spec/name-resolution.md) grants no source
constructor access. Later support should retain those authenticated facts
without changing source opacity. B3 is still a red private checkpoint.

The combined provider batch retains 94 passing incumbent tests. A normally
checked ordinary linked counterpart also fails final Core construction, while
29 incumbent external-helper tests pass. This establishes a shared compiler
gap: monomorphic parent methods can receive polymorphic prerequisite
dictionaries, but their application needs the parent's exact requirement and
selected child producer. The helper's root application expectation describes a
different requirement. Reusing that row would grant the wrong authority even
when types agree. The shared lowerer/catalog correction is still in progress.

Preliminary quality review found an imported lookup undercharge. Repeated
method-table searches need a charge for each scan, rather than one charge for
the table. The production lookup's width regression charges zero units for
three 64-wide searches where 192 are required. Integrated catalog and exact
retry evidence remain pending. A second preliminary claim about unchecked
polymorphic producer-node metadata was retracted: the initial authority pass
already compares that field with the actual argument. The added detailed check
and mutation case establish consistency, not a newly repaired admission gap.
No frozen B3 approval follows from the preliminary review.

The first connected library run now passes both B3 positives, including ordinary
linked validation. It reports 1,392 passing tests and seven existing exact-cost
failures. Passive parent rows retain the selected prerequisite relation without
inventing a type abstraction, and independently authenticated edges supply the
rank-2 carrier relationship. The writer is verifying the new accounting against
fixture shape before correcting the assertions. Source publication stays closed;
coherent mutations, complete budget evidence and frozen independent approval
remain pending.

The later library batch passes 1,407 tests, but a new coherent dictionary-reuse
probe exposes a separate authority gap. It preserves the ordinary helper call
and its complete ABI installation, then invokes an installed method that the
helper does not use. That method has internally handled control; its actual
call would reject in this private profile. The producer's generic callable
flow classification accepts the extra invocation without checking that relation.
Dictionary installation authority must remain distinct from source invocation
authority, including when an existing node is reused rather than a new variable
is fabricated. A narrow carrier classification and authenticated installation
edge check are under implementation. This observation neither publishes a
resource nor settles the remaining lawful helper-control obligation.

The correction now passes the frozen batch: 1,409 library tests and 593 outer
integration tests. Direct reuse and laundering through aliases, type arguments,
tuple/branch results, identity calls and captured closures reject; an unused
noisy selected method still admits. A budgeted nested carrier traversal also
passes exact, prefix, one-short and retry checks. Independent approval remains
pending. Refusing unproved local calls is a private checkpoint boundary;
support for lawful higher-order and internally handled helper contexts remains
part of the experiment.

A valid paired local-forwarding probe exposes an inherited raw-entry omission.
The direct pure helper admits and its control-bearing counterpart rejects.
Wrapping either in a normally compiled local function admits through the plain
entry, in both lifecycle phases. Its callable classification does not carry the
imported callee's invocation proof. Staged checking rejects both wrappers because
their retained occurrence ledger is empty despite one/two source occurrences.
An earlier inline-semicolon trial was invalid source setup and supplies no
admission evidence.

Closing the unchecked entry is an interim guard. The useful pure wrapper still
needs retained occurrence and canonical call/capture correspondence; callable
phase barriers must remove native privilege without erasing ordinary helper
facts. That is the next connected case before handler templates. This discovery
does not justify a language restriction on ordinary local functions.

The interim guard now passes 1,413 library tests and 593 outer integration tests.
Seven paired source variants retain imported invocation dependencies through
local callable and argument/return flows; direct authenticated aliases and pure
local computation still admit. Both pure and noisy imported forwarders reject
at the raw entry, while staged checking still lacks their retained occurrences.
Contract and quality review approve the exact corrected snapshot with no
blocking findings. Supporting the useful pure forwarder is the next
implementation boundary; the reviewed interim refusal does not discharge it.

## 2026-10-02: local helper correspondence

The first paired source test now admits a pure local function forwarding its
own parameter to the imported helper, through plain and staged entries in both
lifecycle phases. Retained counts match the one/two actual source occurrences.
A helper with the same type and internally handled control still compiles, then
rejects at the actual invocation with complete occurrence correspondence.

The implementation separates typed template occurrence retention from native
phase permission and derives local-call facts from actual Core analysis roots.
It reuses the generic typed capture/control query with canonical imports, without
the synthetic wrapper's capture exception. Captured aliases, recursive relay,
coherent mutations, budgets and independent review remain pending; this first
pair does not establish complete local-helper support.

Native inspection also confirmed a separate runtime prerequisite: the registered
Connection diagnostic operation has no corresponding public safe adapter query.
A narrow adapter slice will expose copied status data while the owner is live,
including success status, and test independence after later calls and close.
Its source files have a separate owner; one Cargo owner coordinates both slices.
The reviewed 37-test native baseline remains distinct from this change.

The next local-call batch admits captured aliases, nested tuples, a source data
constructor carrying the helper and recursive relay, in both entries and
lifecycle phases. Its lexical relations come from actual checked initializers;
no captured slot becomes independent merely because it is in the environment.
Exact/prefix/one-short/retry checks pass. Higher-order transport and constrained
source-occurrence overlays remain pending, along with paired captured-control
negatives, mutations and independent review.

The native diagnostic slice is now independently approved. Its four new tests
first failed for the missing method, then passed against actual SQLite. The full
adapter passes 41 tests, warnings-denied Clippy and rustdoc, and formatting.
`Diagnostic` copies current status, including OK, separately from `NativeError`
operation failures. Closed owners reject before any query; copies survive later
calls and owner close, and reading status leaves live statements unchanged.
Only the safe adapter source and README changed; the registered signatures and
Ash-source execution boundary remain unchanged.

The constrained local forwarder now passes a focused source test using an
authenticated source projection of lowered dictionary occurrences. The query
needs the instantiated, evidence-bound closure value rather than the generic
header with unsupplied prerequisite slots. Original structure/catalog validation
still checks all nodes before projection; actual local bindings and call targets
retain their node correspondence. Compound Connection cases pass, but Statement
still exposes an unrelated ambient-owner storage refusal before the query.

Preliminary review then reproduced an accepted concrete dictionary producer call
inside a local forwarder. The producer survives outside the source cut, where
capture analysis loses its restricted role. Generic probes had rejected because
of unresolved prerequisites and supplied weaker evidence. Exact surviving raw
dictionary occurrences need their own refusal relation; selected method evidence
must remain available for lawful source calls. A separate cleanup finding
requires cloning origins before releasing guarded recursive types into fallible
builder arguments. Both corrections and frozen review remain outstanding.

The first correction batch passes 46 external-helper tests, including the
concrete dictionary-call refusal. Statement local forwarding still rejects with
`ResourceEscape` at node 16. Leaving unsupported ambient values unseeded removed
the earlier whole-tuple refusal, but did not establish the complete actual-call
relation. The remaining cause must be identified before another correction or
completion claim.

The next diagnostic finds shared capture compilation refusing surrounding
StateAccess before querying the local SQL function. A private program-bound query
now retains that ambient node as unavailable control and unknown data, while
actual reach and ordinary capture admission remain closed. The resulting batch
passes all 47 external-helper tests, including Statement association composition,
dictionary-call mutations and small-stack disposal. Review still asks whether an
unused raw-producer capture preserves its restricted occurrence identity rather
than only its canonical imported binder. That evidence, broader verification
and frozen review remain pending.

The stored-producer extension now confirms an accepting counterexample:
an unused selected producer bound inside the local function resolves its closure
capture through the canonical imported binder, despite the raw occurrence's
unknown expression. Preserve that exact occurrence value as a private capture
port, leaving it unknown while lawful selected adapters keep their canonical
imports. The prior 47-test result covers invocation mutations, not this newly
extended stored-dependency case.

The capture-port correction passes 78 provider/capture tests, excluding the
separate small-stack child receipt. All nine concrete/generic dictionary variants
reject in acquisition and finish after their original drafts admit. Same-typed
noisy target rerouting and independent ledger mutations also reject; a renamed
helper still checks after source deletion. Statement privileged-callable mutations
and exact/short/retry checks for actual unavailable control pass. Final positive
and budget cases, broader verification and frozen review remain outstanding.

The broad library attempt aborts before its summary. Serial execution of the
already-built binary isolates the existing deep capture/type regression, whose
thread retains its 64 KiB stack bound, 4,096 binding chain and 8,192-deep type.
The focused provider disposal case uses 256 KiB and does not discharge that
invariant. No integration counts follow from the aborted command. Diagnosis
must identify the actual graph-checking or retained-type phase before repair;
the test bounds remain unchanged.

Debugger evidence locates overflow in the finite graph-building call chain during
unlimited checking at shallow node 3. The budget-128 refusal completes and
retained deep-type cloning/disposal has not started. The provider slice enlarged
shared frame storage through graph fields and setup carriers. A frame-storage
correction must preserve query meaning, the existing 64 KiB bound and work-limit
behavior, then pass the isolated invariant before broader verification resumes.

The original 64 KiB test now passes after provider-only graph data moved into one
fallible, precharged carrier and setup was factored into small methods. Ordinary
graphs leave the carrier empty; lexical/parameter/capture identities and scan
work remain intact. The crossed capture batch passes 121 tests, including the
small-stack callback invariant. The crossed provider batch passes 78 tests,
excluding its separate small-stack child receipt. Broad verification still
follows.

The broad rerun passes 1,419 library and 593 integration tests across 31
integration targets, excluding child summaries. Existing ordinary 64 KiB and
provider 256 KiB invariants pass together. Scoped Clippy still requires mechanical
borrowed-input type cleanup and removal of an obsolete lint expectation before
freeze. Higher-order argument/return variants remain useful unsupported source
cases; their refusal does not complete the helper experiment.

The local-call source is now frozen for sequential contract and quality reviews.
Its final batch passes 1,419 library and 593 integration tests across 31
integration targets, excluding eight child summaries; scoped Clippy, formatting
and whitespace checks pass. The exact 18-file archive changes eight sources from
the reviewed B3 guard baseline. Constrained local source and mutation cases also
check after helper-file deletion. Public provider admission, higher-order
transport, handler templates and native execution remain outstanding.

Contract review approves the exact local-call snapshot. Quality review withholds
approval for one remaining wrapper cleanup gap: cloned domain/result types and
the released actual type precede fallible origin cloning in four builder calls.
Budget refusal can drop those raw temporaries recursively before builder guards.
The emitter correction does not cover this shared wrapper. Preserve the reviewed
candidate and repair these handoffs with failure-path evidence before corrected
freeze and re-review. The other inspected authority and frame boundaries hold.

The pre-repair probe cannot reach wrapper assembly with an 8,192-deep argument:
the existing emitter payload-depth limit refuses it first. An admitted 128-level
tuple payload safely refuses at the four legacy origin-budget positions on a
256 KiB stack. Exact, one-short and fresh retries pass at prefixes 0 and 17;
the caller cost is 3,540. This supplies admitted refusal-path evidence, not an
overflow counterexample. Repair the source-verified temporary ordering without
relaxing admission or stack limits, and retain that distinction in re-review.

The origin-order correction is now frozen for sequential re-review. Origins are
prepared before recursive types leave their guards. Three files change from the
prior local-call candidate; all 18 manifest and archive hashes match. The
corrected batch passes 1,420 library and 593 integration tests across 31 targets,
excluding eight child summaries. Capture and provider batches pass 63 and 116
outer tests; scoped Clippy, formatting and whitespace checks pass. The focused
probe retains caller cost 3,540, with the builder ledger separate and unbounded.
Neither the earlier deep refusal nor the admitted case demonstrates overflow.
Contract and quality re-review remain pending before handler work.

Both independent re-reviews now approve the exact corrected snapshot, with no
remaining findings. The wrapper cleanup finding is closed; recursive types stay
guarded until builder entry, binders dispose iteratively, and production callers
retain consumed builder work on refusal. Both reviewers verify all 18 hashes
before and after and preserve the evidence limits. A fresh GPT-6.1 Sol agent now
owns source and Cargo work for the real Connection and Statement handler
templates. Publication, instances, runtime and broader helper/control support
remain outstanding; the coordinator owns only the two tracking documents.

Handler reconstruction finds a row-contract gap in P-1. Canonical open rows
assert that the tail lacks their known effects; substituting the whole
continuation row into such a tail rejects useful overlapping effects. The
design does not yet specify a residual interpretation or its derived
instantiation. Source draft work retains direct demands and the hidden row
separately, without authenticating a guessed shared row. A design amendment is
being prepared before Core admission; ordinary clause factoring and source
checks can continue. Native demands remain present until exact interpretation.

Independent design review confirms the residual calculation and identifies two
missing relations: direct discard demands require actual capture/completion
and interpreter context, and nested handlers require separate shared-output
equations for their owned resumes. Keeping nested resumes at provisional rows
would reject a useful case after specialization. The candidate amendment is
being revised before a second review; the governing note remains unchanged.
Closed-demand source checks do not discharge these generic/control obligations.

The revised row contract passes independent design re-review and is now in the
experimental semantics note. It requires actual capture/context inputs and
per-handler output/resume equations, with complete reconstruction and ordinary
least-output checking at specialization. The current specification is unchanged;
the coordinator also owns this reviewed design amendment. Generic recipe,
capture-dependent demand and nested replay implementation remain pending.

The source-only handler draft passes 10 focused tests and a broad batch of
1,430 library plus 593 integration tests across 31 targets, excluding eight child
summaries. Real Connection/Statement clauses retain actual patterns, resumes,
ranges, state binder and hidden identities without a fabricated client body or
Core certificate. All allowance refusals unwind pattern and active-resume
context. Compiler costs 262 and 3,230 exclude the builder's separate ledger.
Two Clippy assertion lints required mechanical `from_ref` fixes after the broad
batch; focused tests, Clippy and formatting pass afterward. The overwritten
failure log is represented by an honestly labeled captured summary and retained
coordinator session output. Contract review approves the exact 19-source freeze;
quality review follows. This does not complete independent handler Core,
publication, instances, runtime or S-01.

Quality review now approves the exact source-only freeze with no findings.
It verifies all 19 hashes before and after and the retained ownership/cleanup
boundaries. The implementer proceeds to independent unpublished Core fragment
admission under the reviewed row contract. Actual clause roots and canonical
scope/type/resume/state-flow facts must authenticate the fragment; an invented
client body cannot substitute for them. All public and full P-1 obligations
remain pending.

The independent Connection entry probe now reaches the actual clause body and
refuses `Scope/UnknownVariableBinder` at its state occurrence. The source draft
passes, but no enclosing ordinary binder node supplies that declaration scope.
The fragment entry must authenticate the real state/pattern/root inventory
without weakening ordinary validation. Owned-resume, row and borrowed-flow
admission remain subsequent obligations.

Canonical multi-root scope reconstruction advances the actual Connection probe
to `Resume/ResumeMissingContract` at node 4. The earlier unknown-state-binder
receipt is preserved separately. Shared clause-contract checking is being
factored for authenticated fragment use, retaining owned resume operand demands
and nested handler distinctions. Structural checking still supplies no
admission witness; native borrowed flow, evidence correspondence and conditional
row/capture equations remain outstanding.

The next focused run passes the 10 source-handler tests and refuses the actual
Connection fragment with `ResourceEscape` at node 4. The later boundary is under
diagnosis; no fragment admission or source execution is claimed. The previous
scope and missing-resume-contract receipts remain intact.

Diagnosis ties the refusal to binder-lowering provenance, not a captured-resource
failure. The fragment now authenticates the exact `BindingLowering` generated
reason and source cause. The focused rerun passes 11 tests, including the real
Connection structural entry; source inventories are precharged and clause
roots indexed. This remains unreviewed structural evidence. Statement and
borrowed flow, external evidence and conditional row/capture admission follow.

The existing native flow evaluator now serves a borrowed handler entry without
replacing lifecycle construction or terminal role checks. The actual Connection
entry reaches the copying-profile flow and the focused batch passes 11 tests.
Borrow roles, state lineage and copied resume arguments are checked. Statement,
local nested-handler lineage, StateAccess and selected external evidence remain
open; this copied-result classification does not define later arena/view
contracts or publish a template witness.

The next batch passes 14 tests: actual Statement's three clause roots,
tuple/newtype lowering and provisional nested-owner checks now cross the private
entry. The Current StateAccess variant still refuses at its actual access node
after source checking. Canonical association and operation-domain operand
provenance are under implementation. Nested row realization and local
nested-state aliases remain separate useful control obligations.

The next batch passes 15 tests after Current StateAccess uses associations from
the defining module and actual clause-domain resource paths. Pattern/local flow
preserves operand provenance before accepting state lineage. Wrong-path/owner
mutations, wrapped inputs, selected helpers, budget boundaries and review still
follow; no public template authority is claimed.

The next batch retains 15 passes and two useful positives refuse. A direct
StateAccess alias fails at the actual clause root with `ResourceEscape`; an
imported pure error mapper fails at its helper occurrence with
`Scope/UnknownVariableBinder`. The receipts preserve these distinct entry gaps.
Source-root lowering and authenticated imports remain implementation work,
rather than new source escape rules.

Exact source-root authentication also exposes the actual `TypeChecking`
wrapper. The extended rerun passes 12 tests and refuses five positives; a
focused diagnostic shows the ordinary Connection body's generated checking
origin relates the body span to the clause span. That cause must be checked
alongside exact block/binding lowering. The prior 15-test pass remains preserved
as an earlier checkpoint, not current verification of this correction.

The corrected batch passes 17 tests. Exact checking/binding causes and source
binder identities admit the direct alias; canonical multi-root plain-import
type, origin and capture reconstruction admits the mapper. The entry returns
no template witness. Local patterns/evidence/nominal wrappers, selected method
evidence and per-owner conditional row/capture equations remain support
obligations before full P-1 admission.

The next mutation and budget batch passes 21 tests. Canonical metadata,
source/Core provenance, resume and row facts, native demands and StateAccess
operand metadata reject their distinct mutations. Cumulative independent
checker work passes exact, one-short, nonzero-prefix and fresh-retry checks.
The Connection fixture cannot distinguish its Current relation from an
identical Enclosing mutation; that attempted mutation is not contrary evidence.

A separate source-helper test exposes an accepted wrong binder: a second
canonical imported mapper with the same type and capture contract can replace
the actual source mapper. The real failing receipt is
`/tmp/ash-h1-handler-wrong-helper-gap-actual.log`; its preceding test-setup
failure does not establish the gap. The correction reconstructs the complete
imported VALUE inventory from actual resolved clauses and requires one-to-one
canonical binder and full occurrence-origin correspondence. The next batch
passes 22 tests, including rejection of the original counterexample.

The wider batch passes 25 tests. Actual Statement StateAccess succeeds through
tuple paths at all three roots; imported aliases and unused stored mapper
values pass while alternate same-typed binder mutations reject. A fixture with
64 actual clause roots and 66 source/module rows measures cumulative independent
cost 23,853 and passes exact, one-short, prefix and fresh-retry checks. The first
wide receipt failed only in test setup. These results are unreviewed private
checks. Pending selected evidence, per-owner conditional rows and captures,
template authority, publication and runtime execution remain outstanding.

Connected provider regressions subsequently pass 141 library tests; separate
ordinary effect Core integration tests pass all six cases. Nested child-process
summaries are excluded from the 141 count. The reviewed eight-file native
manifest is unchanged. These checks cover the connected existing behavior, not
complete conditional template admission or frozen independent review.

The constrained copied-error mapper initially fails because its required
implementation is absent from the ordinary import. With explicit
`import helper (impl Pass)`, normal source checking and builder completion
succeed, while the independent plain entry refuses `ResourceEscape` at root
node 7. The actual gap receipt is
`/tmp/ash-h1-handler-selected-helper-entry-gap.log`; the prior receipt is a
fixture import failure. Selected ABI admission is the next implementation
boundary.

A read-only agent maps reuse of lifecycle pending publication and staged
authentication, with canonical handler VALUE correspondence and no source-slot
installation. It finds that both ABI rebuilding and capture reconstruction
need the actual clause-root forest and reserved off-graph state/pattern binders.
Those observations guide implementation; they are neither H1 approval nor a
replacement for required generic evidence and conditional row/capture support.

A second read-only map identifies the conditional row retention boundary.
Current private checking authenticates provisional operand-only resume rows
and scalar direct demands. Source discard synthesis owns deferred cleanup
equations in the elaborator, but the current handler carriers retain no
equation owner. Those relations need retention or independent reconstruction
against actual code and capture inputs before the elaborator is consumed.

The map also distinguishes single-pair range replay from whole-graph cleanup
replay. Nested specialization must update every affected handler/resume and
descendant; the existing whole-graph owner map expects actual Handler nodes,
which the body-free outer provider entry deliberately lacks. Its iteration and
rollback can inform the implementation without inventing a client body. The
approved conditional contract already requires these relationships. No new
semantic restriction or H1 approval follows from this inspection.

The first selected-forest batch passes 27 focused tests. The actual constrained
copied-error mapper now compiles selected ABI and independently checks; the
original entry refusal remains preserved. Connection, Statement and newtype
forests retain real roots and rebuild state/pattern binders in the new arena
after reserving off-graph identities. The source-only H0 path remains covered,
and pending evidence is not published. Selected helpers in later clause roots,
local forwarding and stored values, authority mutations, exact work limits and
independent review remain the next evidence batch. Conditional row/capture
admission and all public execution obligations remain pending.

The wider selected batch first fails in fixture setup: local forwarding syntax
is invalid, and some catalog variants have no applicable domain/adapter record.
After the syntax correction, the unused stored mapper passes but the called
forwarder refuses at real Apply node 90. The fourth receipt preserves that
useful support gap separately from the remaining catalog setup failure.

Capture compilation requires real handler owners while scanning the complete
forest; the body-free outer provider has no client handler node. Private
provider queries now represent an unmatched resume as unavailable control.
Reaching it still rejects, ordinary capture checking still rejects unmatched
owners, and matched nested resumes retain their exact relation. The corrected
batch passes 32 tests, including all-root ordered selected methods, called and
unused stored values, occurrence/producer mutations, applicable method-scheme
mutation and checking with the helper file removed. Type-work costs are 7,047
for compilation and 28,122 for checking, excluding the separate builder and
constraint ledgers. Actual-graph boundary regressions, pattern ownership,
broader verification and frozen review remain pending. No conditional witness
or public authority is claimed.

The actual-graph provider query boundary regression passes separately. The
first nested/small-stack suite aborts during fixture setup, as confirmed by its
marker receipt before private checking. The corrected probe prepares and
compiles on the normal stack and checks/refuses/retries/disposes actual retained
drafts on 256 KiB. That scope passes without claiming small-stack compilation
or setup. The suite passes 33 tests and preserves one genuine positive refusal:
nested `Box<Error>` prerequisites compile but independent checking reports
`Registry`.

Canonical imported closure retention visits Box before the earlier Completion
declaration. Exact mirroring passes; contextual range checking incorrectly
uses retention order as source order. Independently indexing contextual ranges
by source order preserves the disjointness/identity/provenance requirements
without changing ordinary registry ordering. The nested case subsequently
passes its focused test. Complete charged-work, mutation, broad verification
and frozen review evidence remains pending.

The coherent staged batch passes all 36 focused tests. Selected compilation and
checking cost 7,093 and 29,110 type-work units; the wide root and nominal fixtures
cost 24,637 and 10,267. Exact/one-short resource categories, charged prefixes
and fresh retries pass. Separate low-level tests preserve ordinary registry
order, reject mirror-identical contextual overlap and charge reversed-key
sorting with deep primary origins. The actual query-owner test passes.

Clippy retains the initial seven findings and the following unused-import
finding separately; its third run passes warnings-denied checking with only the
existing active-T1 dead-code allowance. The focused receipt predates these
mechanical corrections. A single final broad batch is running before an exact
20-file source freeze and independent contract then quality review. Conditional
solver ownership is reserved for the subsequent implementation checkpoint.

The broad receipt `/tmp/ash-h1-handler-staged-broad.log` subsequently passes
1,456 library tests and fails three existing exact-work regressions. Integration
targets are not reached. Contextual registry sorting adds work to ordinary
registry validation, and supplemental pattern-origin charging changes an
ordinary linked-method transform allowance. The correction must isolate the
new work to its provider paths while preserving existing ordinary ledgers;
increasing test allowances would not establish that compatibility. Frozen
review remains pending.

The corrected receipt `/tmp/ash-h1-handler-staged-broad-corrected.log` passes
all 1,459 library tests with the original ordinary allowances. The arguments
integration target passes 18 tests; architecture checking then passes 29 and
fails three. One failure identifies an imported-method catalog comparison
outside the closed Core identifier inventory. Two stop the carrier scanner on
an ambiguous `NominalTypeId` reference under a visible glob import. The architecture target
was absent from the earlier 31-target checkpoint. An independent read-only
audit compares the frozen baseline and new source before assigning inventory
updates. No full-suite success or architecture approval is claimed.

The separate all-except-architecture integration batch then finishes with
1,536 passing tests across 93 targets. Three nested child-process summaries are
excluded from that count. Its explicit inventory is
`/tmp/ash-h1-handler-staged-integration-targets.json`, and the receipt is
`/tmp/ash-h1-handler-staged-integrations.log`. This is broader than the earlier
593-test, 31-target checkpoint; the counts must not be interchanged. Together
with the corrected 1,459-library run it establishes regression evidence, while
architecture, final scoped checks and independent frozen review remain open.

Final scoped receipts pass all 36 focused tests, Clippy with the existing
dead-code allowance, formatting, diff and the unchanged eight-file native
manifest. The final selected fixture costs 7,056 compilation and 29,109 checking
type-work units after the ordinary-ledger correction; builder and constraint
ledgers remain separate.

The independent architecture audit identifies a live imported-method catalog
comparison already retained in the frozen H0 source, and an H0 glob-import
ambiguity independently present in the archived elaboration source. Temporary
explicit-import simulation exposes at least 179 unmanifested current fields,
including 38 new H1 keys. Module-path aliases hide further staged carriers, so
the set is not a complete obligation inventory. `Cow<Type>` also needs a Mixed
retention model. The follow-up must preserve ambiguity rejection and complete
inventory checks, repair path and retention modeling with scanner fixtures,
and keep state-access extraction behind its narrow owner API. These findings
do not grant architecture approval or conditional handler authority.

Contract review statically traces a possible native-effect handler bypass.
An ordinary nested Handler could use canonical foreign operation signatures,
evaluate the admitted Current-state diagnostic request, and remove that exact
native demand from the provider's provisional direct row. Source checking
already rejects foreign handler targets, but independent graph admission must
check that boundary itself. An isolated adversarial regression is authorized
with the original 20-file archive preserved. No empirical acceptance, contract
approval or quality review is claimed before that probe completes.

The first probe receipt fails to compile because of a test helper's incorrect
`VariableNode` path. The second reaches source checking and reports
`Internal(InvalidState)` while forming the generic refusal/open-failure resume
input. Neither reaches independent admission. Debugger receipts identify that
separate source setup frontier. The next probe uses the checked real provider
graph and canonical builder types to exercise the independent handler target
rule directly; its result remains pending. The original frozen archive is
retained while the two test/probe files change.

The third receipt `/tmp/ash-h1-native-handler-probe-third.log` reaches the
intended independent boundary. The ordinary source-built handler baseline
passes, and the coherent native-target graph returns `Ok(())`; the negative
assertion therefore fails with exit 101. Unit report payloads avoid the earlier
source setup failure before canonical native-state arguments are substituted
in the retained graph. Contract review rejects the original staged snapshot:
ordinary Handler validation must independently reject registered foreign
targets. Compiled-forest evidence and the minimal shared correction are next;
no revised approval or quality review is claimed yet.

The paired compiled receipt confirms that both original plain and compiled
entries accept the registered-foreign Handler term. The minimal shared
independent Handler check now rejects that target at its actual node. The
corrected focused batch passes 37 cases, including both legal ordinary
baselines and both `ResourceEscape` refusals. Later assertions check exact
refusal work, one-short resource classification, charged prefixes, fresh retries
and empty pending slots. The library run passes 1,460 tests, excluding six
nested child summaries; eight affected integration targets pass 169 tests.
No 93-target rerun is claimed for the correction. Final scoped checks and the
revised snapshot precede independent contract re-review and quality review.

Contract re-review confirms the native-target correction and identifies a
separate accounting gap. The new call to `ResolvedRegistry::foreign_effect`
scans module effect vectors without charging their size. With multiple
canonical registrations and ordinary Handler nodes, that work repeats per
handler; earlier registry authentication pays only its own scan. A measured
exact refusal budget does not cover this missing proportional-work evidence.
The next correction charges membership work and compares deterministic
empty/wide registration cases before another freeze and re-review. No quality
approval is claimed.

The accounted membership helper charges every visited module and the entire
effect-vector scan before comparison. The shared Handler guard and canonical
provider entry both use it. The first batch passes 38 focused tests. Valid
loader/import cases measure lookup costs 0, 3 and 579 for empty, narrow and
wide inventories; the wide case retains 64 additional eight-effect manifests.
Its actual entry costs 61,249 units, with exact/one-short refusal, prefixes,
fresh retries and empty source slots checked. Native-target refusal costs
5,816 units after accounting. Broader verification precedes another snapshot
and contract re-review. The earlier source-based accounting finding remains
the genuine evidence; no synthetic old stderr is claimed.

The accounted 20-file snapshot passes final 38 focused tests, 1,461 library
tests, 169 affected integration tests and scoped checks. Independent contract
re-review approves the declared staged component and closes both findings.
Fresh quality review is active while source and Cargo remain stopped. The
final selected fixture costs 7,056 compilation and 29,117 checking work units.
The context's historical 29,113 value is corrected from the actual final
receipt, with the old context preserved and no source/archive change. The
approval does not complete conditional rows, public execution, architecture
verification or the full plan.

Fresh quality review rejects the accounted snapshot for one remaining new
handler-entry scan: `canonical.foreign_state` visits foreign module/state
inventories without work charges. The existing wide case's exact total omits
that lookup. A charged state query and deterministic late-hit/miss and actual
entry budget evidence are assigned. Other reviewed H1 ownership, disposal,
allocation, forest, source/capture, lineage and evidence paths yield no
additional actionable findings. The staged checkpoint remains unapproved
until the correction passes revised contract and quality review.

The state-query correction returns the borrowed canonical fact and charges
each visited module and its complete state inventory before comparison. The
first focused receipt fails to compile because the test helper's closure
cannot express the returned borrow's lifetime; an explicit borrowed-lifetime
test function resolves that setup error. The second receipt passes all 38
focused cases. State lookup costs are 0, 3 and 131 for empty, narrow and wide
canonical inventories, with late-hit/miss, exact/one-short work, charged
prefixes, fresh retries and canonical pointer identity checked. The wide actual
entry costs 61,380 units; native-target refusal costs 5,819 units. Library
verification passes 1,461 main tests, excluding six nested child summaries;
eight affected integration targets pass 169 tests. Final scoped receipts and a
new freeze precede independent contract and quality re-review. These are
deterministic compiler conformance cases, within the user's exclusion of
cybersecurity work and fuzzing.

The final state-accounted snapshot retains the same 20 source files; three
change from the effect-accounted snapshot. Final focused, library, affected
integration, Clippy, formatting, diff and unchanged native-manifest receipts
pass. The selected fixture costs 7,056 compilation and 29,118 checking units,
parsed from the final focused receipt. The source archive hash is
`40d2f21136bb1b65b74d71d5a4d1d060b100fd10e0c620b1ddbb48fa35e58a42`.
Root independently verifies all live/archive source hashes, metadata and 96
retained receipt hashes. Source and Cargo are stopped for contract delta
re-review, then quality re-review. Architecture and conditional work remain
separate subsequent checkpoints.

Contract delta re-review approves the state-accounted staged snapshot with no
actionable findings. The state lookup pays before traversal and preserves the
borrowed canonical fact and its formal-count, type and ownership checks. The
native-target and effect-membership findings remain closed. Quality delta
re-review is active; source and Cargo remain stopped. Approval is limited to
the staged structural entry and supplies no conditional-template, publication,
runtime or architecture authority.

Quality delta re-review approves the state-accounted staged snapshot and closes
its sole prior finding. Both independent reviews are now complete for this
private structural component. A separate GPT-6.1 Sol writer receives sole
source and Cargo ownership for the architecture checkpoint. Its scope is the
closed method-evidence identifier inventory, faithful carrier scanning through
module aliases and `Cow<Type>`, complete retention/budget/disposal records, and
state-access mutation behind the narrow iterative owner API. The task must
preserve ambiguity rejection, bidirectional inventories, cumulative budgets
and current semantic guards. Conditional handler equations remain subsequent
work, and no public source case is completed by this approval.

The architecture writer reproduces the unchanged checkpoint's three failures
in `/tmp/ash-h1-architecture-unmodified.log`: 29 tests pass, the closed Core
identifier inventory rejects the live catalog comparison, and two scanner
checks stop at the ambiguous `NominalTypeId` reference. The receipt exits 101.
The planned correction touches the architecture test and explicit imports in
the affected provider modules, plus a narrow state-access argument admission
method. It preserves compile-time catalog authentication, closed inventories,
lexical ambiguity rejection and the existing failure/disposal ledgers.

Focused scanner fixtures reproduce three additional failures in the same
architecture target: qualified `Cow<Type>` is classified Owned instead of
Mixed, a carrier reached through a `#[path]` module/reexport cannot resolve,
and the catalog helper lacks its exact inventory entry. The retained red
receipt passes 28 tests and fails six, including the original three. The
coherent scanner/import/owner correction precedes the next Cargo batch; no
passing architecture result is claimed.

The next scanner batch passes the `Cow` case and still fails five architecture
checks. It exposes inherited import anchoring and further exact compile-time
authentication identifiers. A diagnostic-iterator lifetime compile failure is
retained separately before its correction. The scanner now derives module
identity from actual `mod`/`#[path]` relationships; an empty-prefix join bug is
also corrected. Newly reached glob consumers require explicit type and Core
imports in six provider modules, including `core/provider/entry.rs` outside
the prior 20-file manifest. That representation-only scope expansion is
authorized and must be included in the revised manifest. Complete inventory
records follow verified reachability, with no ambiguity or ownership exemption.

Exact import replacement reaches a helper file beneath an actual `#[cfg(test)]`
module that the old filename scan treated as production. The scanner correction
therefore tracks test-only module edges and module-level private import/reexport
bindings. Nested and placement fixtures must prove that exclusion follows
declarations, preserves any production route to a shared physical source, and
never relies on a provider filename or test-name convention. Field identities
remain attached to their physical sources; complete production inventory and
no-stale checks remain required.

A separate GPT-6.1 Sol read-only agent prepares the next conditional-handler
implementation plan from the approved row contract and actual typed code.
It must specify recipe ownership and correspondence, per-handler unknowns,
capture-dependent cleanup inputs, specialization and final ordinary validation,
with deterministic evidence and cumulative-budget/disposal obligations. The
architecture writer retains sole source and Cargo ownership. Planning grants
no conditional admission and does not bypass the architecture/review gate.

Read-only planning confirms that lowered forest correspondence can relocate
cleanup equations without raw provider-body replay. The existing discard
equation stores a builder ordinal (`usize`), so transfer must qualify the
original arena and map that ordinal through the correspondence. Body-free
capture queries intentionally mark absent outer resumes unavailable; actual
discard checking still requires its owner. A conditional recipe therefore
needs an independently authenticated continuation/capture port. Neither an
invented client Handler nor an empty capture assumption answers that boundary.

The corrected standalone scanner reaches 186 missing production-field records,
compared with the earlier 179 minimum. It includes the three staged carriers as
Mixed and four shared evaluator instantiation fields hidden by a source alias.
`BorrowedClauseContract.answer` is also correctly Mixed. Seven provider glob
imports now have explicit bindings. Complete profiles are assigned from the
actual source owners and disposal paths; the shared evaluator fields require
inventory records, with no evaluator code change. Standalone discovery remains
diagnostic evidence until the authoritative Cargo architecture batch passes.

The read-only conditional-handler plan is complete and recorded under the
execution record's conditional row/capture boundary. It specifies actual
equation/root ownership, a typed continuation input, owned checked-template
admission, transactional specialization and final ordinary validation, followed
by checked publication/linkage. Implementation and both reviews remain pending;
the architecture gate still precedes those changes.

The authoritative inventory batch passes 33 architecture cases and fails two,
with no missing production fields. Three stale records belong to the test-only
pattern rebuilding helper; current production rebuilding records remain.
The remaining owner API correction moves argument transfer through a private
consuming state-access method, preserving the existing admission ledger and
iterative argument owner. The next batch passes 34 cases and fails one: the
now-complete owner scan reaches an older substitution-map insertion that can
drop a displaced recursive Type through the raw map. A narrow insertion API
must dispose displaced values iteratively, preserving reservations, charges
and overwrite behavior. The corresponding source substitution owner receives
the same correction if independently reached. These paths are within the
prior 20-file source scope; no owner-check exemption is introduced.

Further complete owner scans reach argument-vector transfer in the provider
external builder and pattern suffix transfer in Core rebuilding. Both receive
private consuming/narrow buffer operations within the approved source scope.
The next complete owner scan exits 101 after 254.07 seconds, with 34 tests
passing and one failing at two older evidence-argument transfers. The writer
collects remaining sites through a temporary diagnostic before the next
coherent authoritative batch, retaining the product guard unchanged. A
briefly overlapping library attempt was stopped and exits 143; it supplies no
semantic test outcome. Cargo runs remain sequential thereafter.

Source-selection review also identifies the old `*_tests.rs` filename filter.
After the current actor terminates, actual module-route classification replaces
that filter. Fixtures must preserve production files with that suffix and
exclude test-only files regardless of spelling. This extends the same source
fidelity correction and supplies no filename-based exception.

The temporary collector completes and identifies the remaining shared-owner
gap at final-reference disposal of `ForeignModuleFact`. The scope expands to
25 files with `foreign.rs`; resolved map behavior and Arc retention stay
unchanged. The destructor uses existing iterative gates for canonical
interfaces, operation types/origins, state/state-access origins and admission
origins. A deterministic fixture constructs a 65,537-cell type and six deep
origins on the normal stack, then drops shared references on 256 KiB: the first
drop disposes no type cells and the final drop disposes all 65,537. No origin
counter exists, so constrained-stack completion supplies that evidence rather
than an invented count. A collector rerun and authoritative Cargo verification
remain pending; the diagnostic's caught failures are not a passing product
guard result.

The final temporary sweep reports no remaining owner failures. The first
full library attempt then fails compilation on four missing test-only parent
imports after glob replacement; its eight diagnostics are retained and provide
no semantic outcome. The corrected library receipt passes all 1,464 main
tests, excluding six nested child summaries. All three new deep-disposal
fixtures and the existing state-access/rebuilding ledger cases pass. The eight
native source hashes remain unchanged. Scoped Clippy precedes the long final
architecture batch, followed by handler and affected integration checks; no
architecture or independent review approval is claimed yet.

Final sequential verification passes all 36 architecture cases, 38 handler
cases and 169 affected integration tests across eight targets. Scoped Clippy,
formatting of 25 sources, diff and native-manifest checks also pass. The complete
architecture test takes 319.36 seconds. The prepared source archive is
`e32bca6b92888a4146c866b9d2687442ce2573eafdbb38d21f4f818459545f6a`;
seven prior-checkpoint files change, 13 stay identical, and five existing branch
paths join the scope. Root independently verifies all 25 live/archive source
hashes and 23 recorded receipt hashes/exits. A one-unit selected check-cost
change (29,119 versus 29,118; compilation remains 7,056) receives an isolated
diagnosis before final metadata and independent review. No source or budget
change is made to explain it. Wide costs and refusal categories stay unchanged.

Isolated repeats on byte-identical sources pass twice with 7,056 compilation
and 29,116 checking units; the serial 38-case batch passes with 29,115 checking
units, versus 29,119 in the concurrent batch. Every actual fixture context
still passes its exact/one-short cumulative allowances, prefixes, fresh retries
and empty-slot assertions. The totals vary with fixture/process context, so
the observation does not establish an extra fixed ownership charge. Charged
canonical source-order merging is a plausible explanation, explicitly an
inference without a complete charge trace. Final metadata retains each raw
cost and the original context; no source, limit or allowance changes follow.

Root verifies the final context hash
`b376f30e10bb866721226e204a827b69ff4dfd130df400d6ecede5ad5a499ca9`
and all 26 recorded receipt hashes and actual exits. A fresh GPT-6.1 Sol
reviewer begins read-only contract review of the frozen 25-file checkpoint;
quality review follows contract approval. Source and Cargo remain stopped.
The review assignment repeats the user's exclusion of cybersecurity work,
including fuzzing, and confines evidence to deterministic language/compiler
conformance. No implementation, publication or full-experiment completion is
claimed by this review assignment.

Independent architecture contract review approves the frozen checkpoint. The
reviewer verifies live/archive identity, seven changed and 13 unchanged prior
sources, 186 new inventory keys, three removed test-only keys, governing and
Cargo hashes, and all 26 receipt hashes and exits. Inspection finds no contract
blocker in scanner closure, narrow transfers, order/capacity, work accounting
or iterative replacement/final-reference disposal. This read-only approval
covers private H1 representation and ownership only. A fresh GPT-6.1 Sol
reviewer now performs quality review of the same frozen identity; source and
Cargo remain stopped until both reviews approve it.

Quality review reports one verified scanner finding. Flattening attribute
contents makes `has_direct_cfg_test_attribute` treat
`#[cfg_attr(test, cfg(test))]` as an unconditional test-only attribute. In a
non-test Rust build the module remains production, but the scanner omits its
source and Type carrier. The reviewer reproduces the omission with unchanged
frozen scanner functions and separately compiles a non-test Rust fixture;
`/tmp/ash-h1-quality-cfg-receipt.json` records both exit-zero observations and
hashes. Root independently inspects the helper and accepts the finding.

The sole implementation owner resumes with edits confined to
`tests/architecture.rs`: preserve individual attribute boundaries, recognize
root direct `cfg(test)`, and retain unresolved conditional routes. Batched
external-source and inline-module regressions precede the fix. New focused,
architecture and scoped quality receipts precede a separate corrected freeze
and both re-reviews. The 24 unchanged production files can retain their prior
library/handler/integration evidence; this does not claim reruns. Conditional
path selection is an unproven review observation, not a second finding. The
original freeze and unsuccessful quality review remain recorded.

Both new external-source and inline-module regressions fail against the
unchanged helper: the expected Owned production carriers are absent. The
batched Cargo receipt exits 101 with two failures and 36 filtered cases;
root reads the preserved log and actual exit. The correction retains separate
direct attribute slices and compares a complete root `cfg(test)` attribute,
leaving existing path-token handling unchanged. Focused and full architecture
verification follow before any corrected-freeze approval claim.

The first corrected scanner batch passes six cases and fails the inline
fixture. A preserved diagnostic shows its carriers and import aliases survive
parsing, but the retention prefilter checks raw `Payload`/`super::Payload`
against declaration names before calling the existing alias resolver. The
declaration is named `Type`, so the imported renamed carriers are omitted
from the retention fixed point. Root and the writer independently inspect
this causal path. Canonical qualified references isolate the original
`cfg_attr` regression; seven focused cases then pass and the full architecture
actor starts. That green focused result does not resolve the discovered alias
omission. Read-only quality review examines the alias boundary while the
current actor runs without edits or restart. Alias regressions and any bounded
repair follow its terminal result, within the same scanner-only scope.

Read-only quality review confirms the alias retention finding. Scalar owner
discovery already reaches the renamed fields; missing retention classification
can make inventory validation refuse a valid carrier. The observation does not
prove silent acceptance of an omitted inventory key. The bounded correction
uses existing alias-aware resolution before candidate filtering and preserves
its identity, ambiguity, generic and unknown-external behavior. Renamed,
self/super-qualified and imported-module cases cover owned, borrowed, shared
and mixed retention, with shadow and ambiguity controls. The existing actor
remains uninterrupted before these edits and their red/green batch.

The `cfg_attr`-only actor exits zero with all 38 architecture cases passing in
339.74 seconds. The alias regression batch then exits 101: renamed `Type`
retention is absent, while non-owner, shadow, external, generic and expected
glob-refusal controls pass. Removing only the raw-terminal prefilter lets the
existing alias-aware resolver derive retention bits; generic associated-carrier
handling and identity/ambiguity assertions remain unchanged. Nine focused
scanner cases pass. Root reads both raw outcomes and confirms that only
`tests/architecture.rs` differs from the original 25-file freeze; the other 24
sources remain identical. Combined full architecture verification is active
before scoped quality checks, a corrected freeze and both re-reviews.

Combined architecture verification exits zero with all 40 cases passing in
341.41 seconds. Root reads the raw summary and exit and again checks that the
other 24 checkpoint sources are byte-identical. The sole writer proceeds to
test-target Clippy and static checks, then the corrected freeze. Original
production library, handler and integration receipts are carried for their
unchanged sources; no rerun or full-experiment completion is claimed.

Scoped architecture-target Clippy, formatting, diff and native-hash checks
pass. Source and Cargo stop for the corrected 25-file freeze. Archive hash is
`7d7407078f0fa60475f7af5c81ad5dc3fe233f327ed865db4891f3422d586e7a`;
context hash is
`5429d0e00e93d98745435aedc25ba65f039650be2f876838b4dabc212cbaed5a`.
Root independently verifies all live/archive hashes, the sole test-file delta,
unchanged Cargo and original freeze, and all 12 new receipt log/exit hashes and
actual exits. Contract re-review is active on this identity, followed by
quality re-review after approval. Both earlier findings and their red receipts
remain preserved; conditional admission is still pending.

Contract re-review approves the corrected identity. It independently verifies
all 25 live/archive files and 12 receipt log/exit hashes and finds both scanner
corrections consistent with their obligations. Manifest/profile keys, resolver
refusal assertions, exact identifier and narrow owner guards, and production
charges are unchanged. Quality re-review now examines the same frozen delta;
source and Cargo remain stopped.

Quality re-review approves the corrected freeze and resolves both scanner
findings with no new actionable issue. Both reviewers verify the same 25-file
identity and all 12 receipt hashes and exits. Approval remains limited to the
private H1 architecture checkpoint.

The sole writer now starts the planned owned conditional-recipe checkpoint.
The assignment covers retention/relocation of source obligations, independent
equation and owner/root reconstruction, and typed conditional capture ports.
It must return an owned checked template rather than another scalar or
`Result<()>` structural check. Open direct demands and unknown capture inputs
remain represented; no invented client handler, empty capture assumption or
global closed-demand restriction is authorized. Whole-graph specialization,
residual derivation, ordinary validation, module publication and actual
instances follow before public runtime cases. Root retains tracking ownership;
the implementation owner alone edits source and runs Cargo. Existing guards
and all later SQLite, arena, blueprint/tooling and adoption obligations remain.

The first actual nested-discard regression source-checks successfully, then
fails handler compilation at forest finish with `Core(InvalidPayload)`.
Root reads the exit-101 receipt and confirms ordinary builder finish refuses
pending cleanup rows. Earlier private-field compilation and invalid source
syntax attempts remain setup-only receipts. The writer is adding a qualified
cleanup carrier. The planned private boundary checks the exact builder
pending-ID inventory and transfers it with unpublished Core before relocation
through real forest correspondence. Ordinary finish and its pending-row
refusal remain unchanged; this private transfer must supply no ordinary
validation or execution authority. Transfer and admission evidence remain
pending.

The first retained-forest case passes: the actual nested-discard source checks
and compiles while carrying its cleanup equations. The exit-zero receipt is
`/tmp/ash-h1-conditional-recipe-retention-second.log`. The initial transfer
attempt's private-arena compilation failure remains preserved; the correction
uses a narrow ordinal-to-node method at the builder's arena owner. Source
equations, equalities and recomputation positions transfer through the private
finish and actual ABI correspondence. This establishes retention only.
Independent recipe reconstruction, conditional capture ports and an owned
checked-template witness remain under implementation; public admission and
ordinary executable validation are not opened.

The retention fixture now also asserts that pending equations exist and reaches
independent entry checking. That next regression exits 101 with
`EffectRow/RowUnionAmbiguous` at actual node 9 in arena 5: the old scalar row
operations run before conditional equation admission. Root reads the preserved
receipt. Exact pending/discard/recomputation inspection and per-owner recipe
reconstruction follow; deferred allowances must attach only to independently
reconstructed positions. Ordinary row algebra and all non-row, native and
evidence checks remain required. No owned checked-template result is claimed.

Read-only capture assistance identifies the private value graph/compiler as
the reusable seam, separate from the existing provider callable query. Real
handler clauses currently allocate owner tokens, and completion requires the
captured segment, request event and contexts. A symbolic outer owner therefore
needs a typed unresolved boundary relation; allocating a token or returning
empty control supplies no c proof. The assist separates reconstructable local
forest facts from unknown actual-client capture/interpreter inputs and points
to a nested Unit discard with armed cleanup for nonempty close evidence. The
writer receives this concrete API map while remaining the only source/Cargo
owner. No approved semantic gap or new authority is claimed by the analysis.

The writer reports no external/capture dependency cycle at the current
integration boundary. Actual graph/owner/position reconstruction can precede
external checking; the owned checked constructor follows external, scope,
phase and capture-port checks. The pending transfer is being restricted to
Effect Core. Retained inference IDs alone must not authorize deferred row
positions; independent equation, operation and correspondence checks remain
the next implementation evidence.

The user reiterates that cybersecurity work, including fuzzing, is excluded.
The sole writer receives this constraint; verification remains deterministic
compiler, type, Core, resource, runtime and native integration conformance.

The first equation-reconstruction batch compiles and exits 101 at the existing
independent-entry assertion: `EffectRow/RowUnionAmbiguous` at arena 5, node 9.
Root reads `/tmp/ash-h1-conditional-recipe-equation-first.log` and its actual
exit receipt. The new draft records per-node equations, actual output owners,
resume links and discard ports. This is in-progress representation evidence;
exact annotation correspondence, conditional capture admission and an owned
checked constructor remain pending. No row allowance or template authority is
claimed from the compiled draft.

Root inspects the retained records and actual nodes in that receipt. Discard
node 2 and the nested output retain inference 0; inference 1 records its union
with the exact native Connection demand. Enclosing Bind node 9 still stores
inference 0 while its second child carries the native demand. This confirms
that deferred correspondence must retain a whole-child rewrite rather than
require already-solved provisional annotations or permit arbitrary matching
tails. A read-only assist derives deterministic fixture assertions for this
boundary and the owner, relocation and conditional-capture relationships.
The sole writer continues implementation without another source or Cargo actor.

The read-only assist supplies a compact test matrix to the writer. Keep the
authentic stale Bind annotation as a positive, tied to its whole-child rewrite.
Pair it with a coherent mutation that replaces the pending native union and
direct demand with the discard tail while leaving the actual native request:
that mutation must reject. An unrelated Unit or callable annotation using the
same retained inference identity must also reject. Qualified relocation,
non-Discard claims, nested owner/root links and an explicitly unknown capture
boundary receive distinct deterministic cases. Typed equation, owner and port
assertions replace count-only evidence. Owned checked construction and late
failure with empty publication slots remain obligations; this matrix executes
none of them and adds no closed-direct-demand rule.

The live writer adds a private capture graph extraction and conditional handler
constructor. Ordinary capture analysis supplies no conditional boundary;
the new graph retains external completion edges without a fabricated Handler
or conversion to a callable summary. Root inspects this untested source and
flags per-clause output identities: all provider clauses must share their
handler's output. The writer changes those ports to one output identity,
precharges completion-map preparation and checks duplicate type formals before
insertion, preserving iterative ownership. Root also requests authentication
against the actual projected arena and charges for nullary nodes in its scan.
These are ongoing implementation corrections, not checkpoint approval.

On 2026-10-03, root confirms that the previous implementation agent handle is
missing and no Cargo or rustc process is running. The worktree retains further
code: owned checked-template admission, direct-demand reconstruction, retained
external and state facts, conditional capture ports and additional tests. The
earlier `/tmp` receipts and freeze files are unavailable. Historical recorded
results are not treated as fresh current-source verification.

Before edits resume, root preserves an unverified recovery snapshot of 1,160
tracked and untracked source/document files under
`/home/dikini/.codex/ash-provider-evidence/recovery-2026-10-03`.
Archive SHA-256 is
`38977695edb822ed15f8689fd70641be5c542642334d08b9a182788b0c1a4fd1`;
context SHA-256 is
`dafb800492aeb1a9351043a7065a2d2293ea11ce05366a89f82e3810585099a1`.
This snapshot records recovery inputs, not a reviewed freeze or test result.
A fresh GPT-6.1 Sol agent assumes sole source/Cargo ownership. New actual
commands, logs and exits are retained under
`/home/dikini/.codex/ash-provider-evidence/conditional-recipe-2026-10-03`.

The recovered `01-handler-baseline` compiles and exits 101: 53 pass, one fails
and one is ignored. Root reads its raw log and actual exit. The failure in
`conditional_recipe_refuses_known_callable_demand_in_a_pure_codomain` occurs
at positive recipe reconstruction with `ResourceEscape` at node 14, before
its intended mutation. The writer investigates that authentic input mismatch.
The ignored formal EffectRow test records an owner-kind frontier. The passing
method-local open-equation fixture retains an unused function's latent row;
its outward D is empty, so it does not establish actual open-D admission.
Root asks the writer to retain that distinction and strengthen owned graph,
contract and capture assertions before the new checkpoint is reviewed.

The preserved `02-callable-diagnostic` also exits 101 at the authentic positive
input. Source diagnosis finds that pending-position reachability observed
computation rows but omitted an unused callable's latent pending union. The
writer adds charged latent observation; existing independent callable-body
demand checking still authenticates those positions. Root inspects the change
and reads `03-handler-latent-accounting.log` with its actual exit zero:
54 pass, none fail and one formal-row case remains ignored. The intended
known-demand-erasure assertion now executes and rejects. Stronger retained
graph/contract/capture evidence, affected suites and both reviews still precede
checkpoint approval.

Stronger retained contract and capture helpers expose four assertion failures in
`04-handler-retained-assertions` (50 pass, four fail, one ignored; exit 101).
Root verifies the receipt and checks capture compilation: a request's projected
control is a sequence of operand evaluation and a generated request instruction.
The helper incorrectly expects a direct request at the projected node. The
writer authenticates both sequence links and the exact generated operation and
effect instead; contract assertions also inspect retained demands, hidden roles,
state, operation ownership and per-clause conditional input identities.

The full `06-ash-tests` compiles but aborts its library process with stack
overflow before integration cases. `07-library-serial-diagnostic` locates the
existing 64 KiB deep capture test; instrumentation in `08` separates its short
resource refusal from the failing full 4,096-binding query. The `09` debugger
command exits zero but the test receives SIGSEGV; this is diagnostic evidence,
not a passing test. Its backtrace identifies typed value-graph construction
under the newly split capture builder. The writer extracts existing finite-value
solving so its frame completes before typed graph construction, without raising
the test stack threshold or bypassing ordinary analysis.

Root reads `11-library-stack-repair.log` and its actual exit zero. The aggregate
is 1,480 passed, none failed and one ignored; isolated subprocess summaries are
not added to that total. Stronger retained assertions and the 64 KiB case pass.
The sole writer starts all explicit Ash integration targets, including
architecture, without rerunning the library batch.

Read-only formal-row audit refines the earlier owner-kind frontier diagnosis.
Current static semantics permits complete EffectRow binders only for globals
and eligible generalized locals; it excludes ordinary owner arguments and row
positions beneath kind arrows. The ignored resource/effect/interface fixture
therefore requires a candidate semantic delta, not a local Boolean guard fix.
Current Type and EffectInstance arguments have no row-argument representation.
P-1's hidden A/rho roles do not specify that owner extension. There is no verified
currently admitted source route to the fixture's capture-independent open D;
the unused local relay has an open latent equation but empty outward D. A real
c-dependent open demand from specialized captured cleanup is a distinct possible
route, still requiring actual typed evidence. The owner receives these findings
and retains the full open-D obligation without widening current owner rules.

The writer identifies `DirectDemandProof::projection_matches` as an explicit
contract-review focus. Authentic provisional rows may omit ordinary leaves while
retaining their exact conditional atom relation; full direct-demand checking
must preserve actual native work. Review must examine operator and position
correspondence under coherent mutations, rather than infer authority from
matching pending identities. This concern is retained for independent review,
not labeled resolved by the passing library batch.

The integration command's architecture executable remains live. Root confirms
its process and observes a named failure in the closed Core/interface inventory
guard while the long narrow-owner scan continues. No edits or restart occur
during this actor. The actual failure report will determine any bounded guard
correction; the remaining integration targets have no terminal results yet.

The actor ends with exit 101 after 328.21 seconds: 39 architecture cases pass
and the inventory case rejects four exact identifiers in the private provider
external bridge. Root reads the failure report: `CheckedImplementationFact`,
`CheckedRequirement`, `ImplementationAuthorization` and
`ImportedImplementationFact`. The writer confines their allowance to the
existing `src/core/provider/external.rs` boundary and extends the negative
guard for every other Core source path. There is no module-wide exemption.
Production sources retain the passing library identity. A new command runs all
explicit integration targets with `--no-fail-fast`; its results remain pending.

The writer's self-review flags two direct atom-vector comparisons whose
independent scan charges are not explicit. Root asks for immediate length
precharges if existing preparation does not cover those scans, after the live
integration actor ends and before freezing. Copy and union charges must not
silently stand in for a separate comparison. Any production correction receives
changed-code verification; independent review still audits cumulative work.

Root independently reads the actual zero exit and all top-level target summaries
from `14-integrations-corrected`: 94 requested targets match 94 executed targets,
with 1,576 passed, none failed and none ignored. All 40 architecture cases pass.
Three isolated child summaries are excluded from the aggregate. This batch
precedes the final work-accounting correction and test-block ordering change.

The writer separately charges two direct atom comparisons and the additional
projection scans. Root verifies `17-final-library` (1,480 passed, one ignored)
and `18-final-owned-budget` (one passed); the latter records selected admission
work 35,421 and checks exact, prefix, one-short, fresh and unpublished outcomes.
Clippy then rejects only a test module preceding production items in the private
external bridge. Moving the unchanged test block to the file end resolves that
ordering issue without another lint allowance. Root reads the actual zero exits
for `25-source-order-clippy`, `26-source-order-library` (1,480 passed, one
ignored) and `27-source-order-architecture` (39 passed, one filtered). The
affected architecture batch excludes the unchanged costly owner-API scanner;
its full-batch result is recorded separately, not counted as a final rerun.

On resumption, only root is present in the authoritative agent list and no Cargo
or rustc process is running. A fresh sole GPT-6.1 Sol owner checks receipt/source
identity, finishes missing static checks and prepares a durable freeze. The
checkpoint still requires independent contract and quality review. It does not
establish ordinary Core admission, public source execution or actual open-D
evidence. The user excludes cybersecurity work and fuzzing; remaining checks
exercise the experiment's deterministic language and runtime obligations.

The recovery owner completes `28-source-order-rustdoc`,
`29-source-order-format-check` and `30-source-order-diff-check`, each with actual
exit zero, then stops all source/Cargo work. Its durable freeze is under
`conditional-recipe-2026-10-03/freeze-owned-checkpoint-recovery`. Root verifies
all 1,160 archive members against current files, the full manifest, and the
256-file code manifest. Archive SHA-256 is
`63212081de0a9dc107bc1ba2e820eea428b4c9e8e991807714ab8766d72cc5e1`;
code manifest SHA-256 is
`19c8ff33cde2d593e0d9f92fc2d453eb961f80d5a6251c5def0345e43d484d99`.
Final library, Clippy and affected architecture receipts match current code;
their full manifests differ only in root's two tracking documents.

Recovery refines the scanner transfer limitation: receipt 14 differs in three
code files, and manifests preserve hashes rather than historical bodies. The
reported work-charge, ignored-test wording and test-module move cannot be
independently reconstructed byte for byte from those manifests. Earlier full
integration and costly scanner results therefore remain qualified prior
evidence; they are not exact-current success claims. A fresh GPT-6.1 Sol
contract reviewer receives the frozen private checkpoint, actual receipts,
projection-authentication concern and open-D limitation. Quality review follows
contract approval; no ordinary admission or public source case is claimed.

Independent contract review approves the private carrier within its frozen
scope. It finds actual-node projection correspondence, full reconstructed
direct demand, exact callable/latent relations and retained defining context.
Its approval does not establish ordinary annotation correctness before
specialization. Two temporary annotation checks find zero applicable edits;
their successful exits provide no mutation-refusal evidence. Root verifies
restored code identity and the actual focused result: 15 passed, one ignored.

The reviewer also runs the costly owner-API scanner against current frozen code:
one passed, exit zero, 341.80 seconds. All 256 code hashes still match. This
closes the earlier qualified scanner gap for this identity. After the reviewer
stops source/Cargo work, a separate GPT-6.1 Sol quality reviewer takes exclusive
Cargo ownership. It reviews cumulative work, new owned carriers, API boundaries
and deep disposal. The selected work count differs between process receipts;
quality review checks the actual exact-boundary guarantees rather than assuming
one process-global count.

A separate read-only design report is retained at
`conditional-recipe-2026-10-03/open-d-design/report.md`, SHA-256
`282f08fd1b1711089bc3c9a00c99c0f55fdbd1bb07fe18f6d37b9dc5c81b79c1`.
It recommends explicit saturated row-valued owner arguments for a formal open
demand, with kinded argument checking, substitution and exact effect identity;
it rejects a local checker-flag change as insufficient. Global/local row
quantification alone supplies no formal callback row to the selected provider
API. Captured cleanup remains a distinct conditional route without an admitted
principal-open-D witness. This is a proposed next design amendment, not selected
P-1 behavior, implementation evidence or current language semantics.

Independent quality review approves the frozen private owned carrier with no
definite defect. Root reads its actual receipts: three fresh-process owned
exact/prefix/one-short tests pass, with measured work 35,423, 35,422 and 35,424.
Each fixture's repeated boundary holds; precise attribution of process-level
variation remains uninstrumented. Focused deep capture, substitution failure
and external owned-tree disposal tests also pass.

A temporary deterministic clone/disposal check passes on a 64 KiB stack with
two effect arguments nested 8,192 levels deep, measured work 32,774. It covers
complete and partial disposal, exact and one-short limits, prefixes and retries.
The temporary test is restored byte for byte and is not retained coverage. Root
independently confirms all 256 frozen code hashes after the reviewer's explicit
source/Cargo stop. Both reviews approve this private checkpoint only. The next
implementation slice connects retained provider templates to existing atomic
module checking and publication; ordinary specialization, runtime and the full
source-case corpus remain required.

### Normal module publication and row-argument candidate

The sole source/Cargo writer starts the actual normal-module integration.
Unpublished evidence batches can be combined with duplicate-owner and work-limit
refusal before the existing single publication. Consuming lifecycle admission
retains independently checked code, canonical defining context and genuine
selected occurrence owners. The strengthened lifecycle fixture initially lacks
explicit imports of its implementation selections; correcting that fixture
preserves existing import semantics. Owned admission and measured work-boundary
cases then pass.

Defining source provenance now shares immutable `SourceFile` snapshots through
the loader, resolver and summaries. It avoids copying all source text for every
ordinary module. Provider compilation borrows the elaborator so module staging
can retain its cumulative budgets and unpublished selections. Root reads raw
publication receipts through `18-normal-compile-trace`: the affected provider
batch passes 176 outer tests with one ignored case, and `13-normal-group-check`
compiles. Three direct test literals initially need the new optional provider
field. After that fixture correction, the first actual normal declaration case
still fails with `Internal(InvalidState)`. The writer is tracing that failure;
normal export/import authentication and local-helper context are not complete.
No full-current or public-execution success follows from these receipts.

The complete row-argument candidate receives independent semantic review.
Revision 1 needs stable independent owner signatures, context-free tagged
application parsing and inherited-parent row roles in generated evidence.
Revision 2 addresses those findings and is approved for further evidence work.
Its review is retained at `row-argument-candidate/review-v2.md`, SHA-256
`caa0392fb371dbac14d46b0079f25fc3547b6b4b799399bcf242f344212d0edc`,
under the durable conditional-recipe evidence directory. Root verifies the
reviewed input and the final attribution-only delta. The final external draft,
SHA-256 `34d6302a773cee409e38a5cbc0db9fc4a380ccb7593e794417a31046365296c2`,
labels single-resource EffectId association as a new bounded restriction rather
than existing P-1 truth. The positive formal row derivation remains coherent;
source execution, native topology and same-substitution/same-remainder distinct
capture demands remain unproved.

A separate docs-only GPT-6.1 Sol owner integrates the candidate into semantics
and planning for final review, without selecting it or changing normative Ash.
The source owner continues the current module-publication slice. Row-aware
compiler changes require a subsequent explicit slice. The user's exclusion of
cybersecurity work and fuzzing remains in force; verification and reported
uncertainties concern language, compiler, resource and foreign-library contracts.

The documentation integration passes independent contract and prose reviews.
Root verifies the frozen documents and reads both reports, then selects complete
owner row arguments as an informative amendment to experimental P-1. The
selection changes status and pointers, preserving the reviewed typing rules and
all required evidence. Normative Ash and the active Type-only publication slice
remain unchanged; row-aware compiler work is a subsequent explicit slice.

A separate read-only analysis supplies a concrete proposed capture comparison
without the row-argument extension. An ordinary pure recursive global
`halt<T> : Unit -> T` can produce the hidden answer after discard consumes its
capability and returns Unit. Two match arms within one lexical `Connection<C>`
activation preserve exact db, effect, evidence and substitution identities;
their armed cleanup actions request H versus J. Both actual body rows are
{E,H,J}, leaving equal epsilon={H,J}. The intended per-request captures would
give D={H} versus D={J}, equal Omega={H,J}, and residuals {J} versus {H}.

Root rejects comparing separately fresh identities merely by spelling and asks
for this single-activation form. The revised external report is retained at
`capture-demand-witness/report.md`, SHA-256
`8045b2719f9565774fe801e076779de33b491280012b43f5276f37cb1242e5bc`.
It requires actual request-node/capture-port/action and surviving-interpreter
correspondence; conservative joined scalar rows cannot prove each c. The action
can have a finite close prefix, followed by divergence. No completed Scope,
native finish, source acceptance or S/M runtime success is claimed. This is a
specific next specialization witness, not satisfaction of the c obligation.

Root also reads `19-normal-boundaries`: header, acquisition, completion,
conditional handler and complete group checking succeed; `ExportSummary::freeze`
returns InvalidState. Later tracing remains in progress. The source owner must
admit the actual opaque resource family and separately authenticate body-free
contracts and retained code before ordinary module publication can succeed.

Root reads `22-summary-auth-trace` and verifies the exact refusal:
`KindStageFailure/MissingNominalKind` at source 2, bytes 270 through 306, followed
by export authentication's InvalidState. This confirms a missing abstract
resource access-family kind; earlier lookup explanations were working
inferences, not established causes.

The writer proposes rebuilding independent template checking from body-free
context at every import. Root separates immutable proof reuse from identity-only
linkage. The consuming proof already comes from actual independent source/Core
checks. Imports must authenticate a canonical body-free contract projection
against its retained graph, registry, original occurrence owners and native
facts; they need not reconstruct admission from disposed resolved bodies. The
writer accepts this smaller boundary. Contract/code association checks remain
required, and conditional proof reuse grants no ordinary executable admission.

Final selected documentation snapshots are retained under
`row-argument-candidate/integration/selected`, with preselection and initial
selection preserved separately. Semantic document SHA-256 is
`8a8de255a9f90994b97c94acf116dd853734f5653e5eefb7836197f8435ffc04`;
plan SHA-256 is
`c729e7af9b8aca48a491231319d048fe1967d5f8aa8c5a917cc60bef2de4fafc`.
The final status/prose delta clarifies the added bounded EffectId rule and wraps
sentences; reviewed semantic rules are unchanged. Markdown lint, relative links
and anchors, and whitespace checks pass. Execution and adoption remain pending.

### Normal publication and follow-on preparation

Root reads publication receipts 30 through 45 under
`provider-publication-2026-10-03`. Receipt 30 passes normal Connection declaration
checking. Receipt 35 passes three actual cases: grouped Connection/Statement
publication, body-free exports after defining code is disposed, and an alias
import diamond retaining one canonical contract. Receipt 36 passes 179 provider
tests with one formal-row case ignored. These are separate source revisions;
their 250-file manifests cover `src`, `tests`, `foreign-adapter` and Cargo files,
not a final coherent checkpoint or every workspace input.

The body-free contract certificate is separate from retained executable code.
Checked modules and the linked group retain code; export summaries and imported
facts retain only certificates. Static authentication after code disposal does
not supply executable authority. Receipt 44 passes linking and independent
linked-evidence validation with separately retained code. Receipt 45 extends
the same fixture through ordinary Core synthesis; independent validation rejects
its registry. No ordinary linked execution or SQLite operation is claimed.

The writer corrects an earlier binder inference: resource formals and hidden
answers do occur in the registry's lexical method-parameter inventory. Linking
must preserve their actual identities while assigning explicit resource
declaration ownership authenticated against the canonical resource fact and
retained code. Treating them as ordinary method binders or deleting them would
lose that relation. The next Core boundary requires the same authenticated
body-free family/owner facts, separate from executable template admission.

A read-only row-argument implementation plan is retained at
`conditional-recipe-2026-10-03/row-argument-plan/plan.md`, SHA-256
`b13906b0b5cd393a6943956f13daa293514de9cfbcc0ac01aab046d4b7578a23`.
Independent contract and quality reviews approve freeze-revalidated planning.
The observed file hashes are not a coherent compiler freeze while the
publication owner is active. M0 requires its reviewed freeze and explicit
source/Cargo handoff before the remaining milestones can begin. Actual callback
execution and the separate actual-c source witness remain unproved.

The user reiterates that cybersecurity work, including fuzzing, is excluded.
Risk descriptions concern unresolved Ash semantics or implementation
correctness. Remaining deterministic checks follow the experiment contracts;
this clarification adds no security review or tooling restriction.

Receipt 48, `48-provider-ordinary-runtime`, passes the focused normal provider
declaration case with actual exit zero. Root reads the raw receipt and its
assertions: normal module checking, separate code/certificate linking,
independent linked-evidence validation, Effect Core synthesis, independent
module Core validation and evaluation return ordinary main's `42`. The same
case rejects the alternate ordinary validation entry without module/source
authentication as `Registry`. The linked registry now retains the body-free
certificate and authenticates exact family kinds and declaration binder owners;
its defining canonical contexts predate final linking. This adds no template
conversion or resource-instance execution and does not close S-01.

A read-only review-gate inspection confirms completed local defining facts are
not yet consumed by group compilation. It also finds no normal-path transaction,
missing-code or certificate mutation cases yet. Root sends those concrete gaps
to the sole source/Cargo owner before its final batch. This is test preparation,
not independent approval of the moving source. Final freeze and ordered contract
then quality reviews remain required.

Root reads receipt 49: the normal imported-helper case passes and the
completed-local-helper case fails after lifecycle checks. The owner is wiring
actual completed local schemes, capture summaries and interface/implementation
facts into the same provider-entry authentication, separately from lowered ABI.
This is an observed missing integration path, not a semantic rejection of local
helpers.

The read-only review-gate map is retained at
`provider-publication-2026-10-03/review-gates.md`. Root also starts a read-only
instance-specialization dependency plan: the reviewed row preparation must not
assume that actual resource instances, occurrence relocation or runtime
activation already exist. The plan must place those missing shared mechanisms
explicitly before or within its callback evidence milestones. Source/Cargo
ownership remains with the publication writer; no later slice is started.

Receipt 54, `54-normal-provider-defining-facts`, passes all six normal-provider
cases with actual exit zero. Root verifies the raw results and the completed
local-fact call site. Whole-module checking creates one immutable body-free
defining-facts carrier after ordinary body evidence audit, then supplies it to
provider entries. Lowered ABI remains separate. The after-resource local helper
and imported helper both pass; grouped declarations, body-free disposal, alias
diamond and ordinary linked main also pass in this batch. Constrained local
dictionary/implementation routes and complete transaction failure evidence are
still pending.

The instance-specialization preparation is retained at
`conditional-recipe-2026-10-03/instance-specialization-plan/plan.md`, SHA-256
`b44c7ad02b7c064ad7d188744c31200a6489df9a4bc97a401039e548071bf249`.
It places the shared instance checking, immutable specialization, occurrence
relocation, independent Core/control checks and runtime admission explicitly
within row M2–M5 after owner representation readiness. Independent contract
review approves preparation only. Seven observed source references change
during that live inspection; implementation still requires reconciliation with
the publication owner's reviewed freeze and explicit handoff. Quality review
also approves preparation in composition with the row plan and selected contract.
The two reports establish no implementation, coherent freeze or executable
admission. Actual callback, actual-c, resource-instance and runtime evidence
remain unproved.

Receipts 58 and 60 strengthen normal local-helper evidence. Six original
lifecycle slots are pinned before checking, remain pending until the sole
module commit and then carry the checked application and exact immutable
selection owner/root. Retained code/certificate authentication succeeds after
resolved ownership is consumed. Receipt 60 passes eight normal cases, including
a late clause's actual Error-versus-Int mismatch with all original helper slots
pending, followed by a valid fresh retry.

Root's pre-freeze inspection identifies a partial-assembly gap in
`ResourceTypeFact::from_definition_with_budget`: a successful deep sibling can
outlive a later copy refusal before the completed fact's iterative destructor
applies. The correction stages copied binders, types and effects under a private
iterative owner and charges copied origins and argument-provenance retention.
Shared type provenance remains an Arc. Receipt 62 passes the deep late-refusal
case on a 256 KiB stack with exact, one-short, prefixed and fresh copies. Its
`provider::tests` filter passes 155 top-level cases with one ignored; the nested
child's one-pass report is not added. This filter differs from the earlier broad
`provider` filter. The new conditional clause's ordinary local helper also pins
and authenticates its two real dictionary slots; it proves no open callback
demand or runtime execution.

Receipt 63 reaches a late normal-module export kind-work refusal with the six
original helper slots pending. A fresh sufficient run succeeds, but its used
work is 52,089 versus the measured 52,090. Exact-budget equality across these
freshly resolved fixtures is not established. The source owner traces the
one-unit variation before changing traversal or tests; limits and guards are
not widened to mask it. Whole transaction budgets, remaining rejection cases,
final freeze and independent publication reviews remain pending.

The user's exclusion of cybersecurity work and fuzzing continues to apply.
Risk descriptions refer to unresolved language-design or implementation
properties: resource forms must have typed elaboration, scoped dependencies
must prevent invalid escape, and runtime ownership must follow Core completion
rules. Deterministic conformance cases remain the verification method.

Receipts 67–68 localize the fresh-fixture budget variation to independent
evidence catalog construction. The catalog orders original occurrence slots
by allocation address and previously charged each insertion-sort comparison.
Equivalent source fixtures can therefore consume different work. The writer
precharges the complete bounded sort window without changing slot identity or
widening the budget. Receipt 69 passes the focused exact, one-short, prefixed
and fresh-retry case with actual exit zero. A read-only static analysis records
the causal path separately; it ran no tests. Receipt 70 passes 11 normal cases
and fails separate-code/canonical-closure authentication. Final transaction
evidence, freeze and independent publication reviews remain pending.

Receipt 71 corrects the closure gap exposed by receipt 70. Linked evidence
admission authenticates the registry's body-free provider certificate closure
and each retained defining group's code against its certificate before kind
environment construction. It reuses the checked proof rather than replaying
source bodies. The `normal_provider_` batch passes 12 cases with actual exit
zero, including separate-code/canonical-closure rejection, ordinary main's
`42`, and exact shared-budget fresh retries. This remains a moving source
checkpoint; complete transaction failure evidence and final reviews still
precede source/Cargo handoff.

Receipt 72 extends normal exact-budget evidence to both imported and completed
local helpers, but a new local-helper-to-ordinary-main case fails final Core's
registry check. Receipt 73 identifies the physical source-order comparison:
resource formals are allocated in a different resolver phase from ordinary
global signature binders. Core recognizes the exact certificate-authenticated
provider binders as scoped for that comparison while retaining canonical IDs,
kinds, owner coverage and source provenance. Receipt 74 passes all 13 normal
cases with actual exit zero, including the local constrained helper's linked
Core validation and ordinary main returning `42`. Resource-instance and SQLite
execution remain pending. Independent Core refusal of an erased certificate
relation remains part of the closure inspection before the final freeze.

Root inspection finds that final Core computed certificate authentication but
ignored its failure when the certificate map was empty. Ordinary Core now
propagates that failure even after map erasure. Private contextual template
checking retains its separately admitted prepublication registry path; it has
no final executable authority. Receipt 75 passes all 13 normal cases and an
actual synthesized-Core mutation returns Registry after certificate erasure,
while the unmodified program returns `42`. This closes that observed final Core
gap without source replay or metadata deletion.

Receipt 77 adds actual normal-module rollback cases for a late clause result,
ordinary function result, missing interface evidence and an invalid native call.
Their 11 pinned lifecycle and ordinary slots remain pending after refusal;
fresh valid retries publish their checked selections. The batch reports 14
passed and one failed. The second-resource case stops at an incorrect fixture
slot count: ten slots include the reserved primitive state operation, while the
fixture expected nine. Its rollback claim is therefore still unproved. The
source owner continues the remaining transaction, disposal, mutation, budget
and architecture evidence before broad checks and the review freeze.

Receipt 78 completes the occurrence collector's handler and implementation
coverage but fails the second-resource diagnostic expectation. The actual
failure is a StatementState-versus-Int mismatch at finalize, after the first
resource's lifecycle and handler checks. Receipt 79 pins that mismatch category
and passes all 15 normal cases with exit zero. All ten observed source slots
remain pending after failure; a fresh valid retry exports two resource contracts
and commits nine selected dictionary slots. Its one reserved StateAccess
relation slot has separate typed authentication. Exact mismatch fields and the
remaining transaction, disposal, mutation and budget cases still precede freeze.
The external review gate map now records this verified progress without claiming
publication approval or resource-instance execution.

Receipt 80 stops at a mechanical Box-versus-Type comparison in the strengthened
second-resource assertion; it executes no new client-disposal case. Receipt 81
then executes and passes actual client resolution/checking after dependency
files, defining Core and loaded provider bodies are disposed. The retained
client uses exported contracts and a resource alias; this supplies body-free
declaration checking, not resource-instance execution. Its normal batch reports
16 passed and one failed. The method/producer mutation fixture stops because
the selected mutation seam cannot modify its catalog; no incorrect acceptance
or complete mutation refusal is proved by that failure. The writer continues
against the actual retained graph and checked facts before final verification.

Receipts 83–89 localize the richer nested-helper failure to generic evidence
applications checked without their owner's source kind parameters. The admitted
implementation head and method domains retain those parameters independently of
method-local quantifiers; exact ID/order/kind correspondence remains checked.
Receipt 91 then reaches the intended mutation and exposes an accepted changed
method position. Receipt 92 retains and compares the original admitted body-free
catalog and passes 17 normal cases. Receipt 93 exposes a separate actual producer
edge change accepted under unchanged catalog metadata; receipt 94 compares the
original evidence anchors and operator/prerequisite edges and passes 17 cases.

Receipt 95 rejects the valid nested helper while extending source and dictionary
projection checks. Repeating capture analysis at each callable is the wrong
boundary: the original checked callable type and capture proof are already
retained. Receipt 97 compares the actual source arguments, rows, binder/scheme,
callable type, dictionary binders and installer/edge relations against those
admitted facts and passes all 17 normal cases. These observations concern
immutable template publication, not source-instance specialization.

Receipt 99 passes 18 normal cases with shared constraint/coverage work and a
second-resource StateAccess refusal. Receipt 100 passes 164 top-level provider
cases with one explicit ignored case; the nested small-stack child's one-pass
result is not added. Receipt 102 passes 19 normal cases. All three shared work
ledgers cover exact/one-short, prefixed and fresh-retry boundaries for local nine
and imported six selected dictionary slots. Late defining-origin and native/state
refusals preserve every observed original pending slot. Retained-program missing
code rejects independently of successful public-summary authentication.

Receipt 103 runs all 40 architecture cases and exits 101: 37 pass and three fail.
They expose unlisted Core carrier identifiers, an unresolved borrowed trait in
the storage-field scanner, and raw partial-assembly backing-storage transfer.
The writer replaces the private borrowed trait with an explicit Imported/Defining
enum and moves completed assembly storage through a consuming infallible method,
preserving iterative refusal cleanup. Receipt 106 passes 20 normal cases with
these corrections and a narrow injected pending-append reservation refusal.
Nine original source slots remain pending, work remains charged, and a fresh
valid retry commits nine selections. This is injected reservation failure
evidence, not a claim of allocator exhaustion. Source-attached profiles, public
pending guards, broad checks, final freeze and ordered reviews remain pending.

The user again excludes cybersecurity work and fuzzing. Compiler correspondence,
type checking, Core semantics, FFI ownership and deterministic runtime conformance
remain the authorized verification scope. No commit signing is introduced.

Receipt 109 passes 39 architecture cases with the costly owner-API check
explicitly filtered. Source-attached profiles now describe actual shared proof
ownership; qualifying existing Arc aliases avoids a scanner exception without
changing Rust types or behavior. Receipt 110 passes four public SQLite tests,
but those still stop at the historical declaration guard. Strengthening the
library test to require actual checking and two exported resources reveals
receipt 111's `Internal(InvalidState)` during declaration admission. Three cases
pass and the strengthened one fails. No client instance is reached, so the
public-driver boundary cannot yet be labeled instance-only. A read-only static
comparison assists the sole source/Cargo owner; no later implementation starts.

Receipt 113's refused node is a generated function, not the initially suspected
Match. Shared pattern-decision lowering gives every continuation a pure arrow,
losing the native prepare body's effect row. Correcting the actual computation
arrow reaches receipt 114's state-bearing-function refusal. Reusing the existing
direct single-arm newtype lowering removes the unnecessary closure under checked
source exhaustiveness. Independent validation grants no new native transport
permission. Receipt 115 passes all four public SQLite cases, including actual
library checking/export. Receipt 117 passes the ordinary single/multi-arm nested
newtype effect regression through final Core and evaluation with result 42.

The user requests proof-tooling adoption at the next safe checkpoint. The source
owner holds edits and build launches after receipt 117. Root imports all 18
merged tooling/docs/toolchain paths byte-for-byte from main commit
`a2ced870f491457a60e3131ac613f295ea77e441`, then adds the requested serial build
default to the worktree's Cargo configuration. HEAD, goal and worktree remain;
no commit or merge is performed. The retained adoption manifest is
`provider-publication-2026-10-03/proof-tooling-adoption.json`.

The actual tool inventory exposes 12 Rust LSP tools and no direct Lean LSP tools.
Rust workspace-symbol, hover, definition and diagnostic requests succeed on the
current compiler; the workspace is then deactivated. Adopted Lean tooling copies
and validates OneShot sources/import artifacts against frozen evidence
`d865019fb806462484467c8722e0ab4c48766086b2911bfdd5166f5190ae73b8`.
The existing pinned adapter exposes eight tools through stdio. Its goal, hover
and intentional negative diagnostic requests exit zero in 4.20 seconds, with
sampled process-tree peak RSS 1,238,077,440 bytes. The known Python 3.10 finalizer
warning appears; a process and workspace inventory finds no surviving Lean,
Lake, Rust analyzer or compiler. Raw commands, outputs and exits are retained.

[AD-0012](https://github.com/dikini/ash-lang/blob/a2ced870f491457a60e3131ac613f295ea77e441/docs/decisions/AD-0012-proof-development-feedback-and-build-reuse.md)
and the adopted guides govern validated module-cache reuse and batched proof
changes, serial builds by default, resource-accounted exceptions and LSP shutdown
before heavy builds. Ash's reviewed frozen integration remains the proof
acceptance gate; this feedback verifies tooling, not new proofs or source-case
runtime success. Source/Cargo ownership returns to the publication writer after
the resource window; affected and broad checks precede its final freeze.

Receipt 118 passes 52 affected integration cases: 27 effect runtime, 21 module
newtype and four public SQLite tests. The public driver guard is pinned only
after all preceding dependencies/library check and the entry's resolved main
root is a resource instance. Receipt 119's full architecture/API scan is stopped
with a recorded SIGTERM/exit 101 before a known continuation-domain partial-drop
correction. No full scan success is claimed; the final source still requires it.

Receipt 120's library run aborts on a deep parameter fixture and has four earlier
Core exact-budget failures. Focused receipts 121–125 distinguish proportional
Origin retention from scoped owner/domain parameter costs; the original deep
fixtures acquire iterative ownership before assertions. No work limit is widened.
Receipt 126 passes the four corrected Core cases but aborts in a second deep
parameter fixture, with three resolver and seven evidence failures observed
before abort. Their causes require actual focused evidence. Read-only inspection
also finds a shared parameter-clone helper retaining a completed raw vector
across a later refusal; the writer reuses the existing iterative buffer owner.
These are compiler work-accounting and disposal obligations. Broad verification,
final freeze and independent publication reviews remain unfinished.

Receipts 127–128 retain focused resolver and evidence failures rather than
treating partial broad output as complete evidence. Receipt 129's broad run
finishes with 1,488 top-level passes, 19 failures and one ignored case; no parent
abort occurs. Two defining-group visits, parameter records, kinds and origin
retention contribute actual work which must be attributed independently before
updating exact expectations. Receipt 130 passes 120 resolved-module cases and
fails two; their remaining questions concern proportional source metadata and
earlier code/certificate refusal ordering. No work default or limit is widened.

Receipts 131–132 isolate the evaluator fixture's child stack overflow to
compilation, specifically resolution before checking and evaluation. The child
retains its existing 256 KiB bound. Temporary stage markers are diagnosis, not
final implementation. A read-only comparison assists the sole source/Cargo
owner; broad checks, trace removal, full architecture evidence, coherent freeze
and ordered independent reviews remain required. Proof-tooling feedback remains
separate from these acceptance gates.

Diagnostic receipts 133–134 identify two large expression-dispatch frames across
handler body reentry. Receipt 135 moves that reentry beside the existing Match
dispatch and reaches checking, where the child still overflows. Its exit is 101;
the unchanged bounded test remains failing. Read-only executable inspection
supports fixed-frame pressure at resolution, without measuring exact growth
over the predecessor or establishing the next checking cause.

Receipt 136's checking backtrace locates effect-row rebuilding under nested
handler-clause elaboration. Dispatching FinishBlock directly beside the existing
FinishHookBody completion removes the large step_expression_task frame across
block completion. Receipt 137 records a compile failure for its missing mutable
borrow; receipt 138 then passes the original fixture through the full compiler
and evaluator, including partial-failure assertions. The bound stays 256 KiB.
After trace removal, receipt 139 passes 1,507 top-level library cases with one
ignored. Its child reports do not add cases to that total.

Read-only publication coverage preparation identifies that most closure and
retained-code mutations stop before independent ordinary Core; erasure is the
existing after-synthesis negative. The source owner accepts a coherent batch of
normal link and after-synthesis certificate/source/native relation refusals,
while keeping direct helper tests separately attributed. The expensive final
architecture scan and freeze wait for that batch. The complete goal still
includes owner rows, actual instance specialization, runtime cases, arenas,
results, blueprint, tooling comparison and adoption work.

Receipt 140 passes eight direct ordinary Core closure mutations after valid
linked evidence and synthesis. Certificate presence remains for wrong kind,
origin, formal ID, unrelated family and separate missing/extra name/kind facts.
Receipt 141 passes 19 normal cases, including malformed code reinstalled at the
actual link boundary, but accepts registered-foreign erasure at final Core. This
exposes missing comparison between the certificate's retained defining native
facts and the final linked registry. The wrong module/source assertion follows
the failing native assertion and is not reached. The writer adds charged exact
correspondence under the existing complete linked-context contract; no new
language rule or passing final freeze follows. Ordinary final Core retains
body-free contracts, so executable provider-code mutations belong at separate
link/evidence admission.

Receipt 142 passes 20 normal cases after comparing the original independently
admitted native-fact owners with the final registry, including independent Core
native-erasure and wrong module/source rejection. Receipt 143's reinstalled-code
tests and receipt 144's full 1,508-pass/one-ignored library run precede additional
scan accounting and cleanup. All-target Clippy passes in receipt 147 with its
explicit unfinished-slice dead-code allowance. Receipt 148 passes 21 normal cases
and adds valid formal/answer, native-owner and actual ordinary Validator work
boundaries. The latter measures run_effect type work, with module-relation setup
outside that meter. Receipt 149 independently passes linked Type/constraint
exact, one-short, prefixed and fresh-retry checks.

Self-review notices missing main in some reinstalled-code fixtures: earlier
link InvalidState assertions could stop at the entry precondition. Direct
authenticate_code refusals remain valid mechanism evidence; those relink claims
are not complete. Receipt 150 passes 22 normal cases with corrected method/native
main fixtures. Source-only follow-up fixes template/donor main, adds positive
unmutated check/link/evidence before every mutation, and exercises conflicting
same-ID ImportedFacts certificates versus exact same-owner reuse. Execution of
these controls remains pending.

The user requests a shared-host build window for the alignment task. After
receipt 150 the writer explicitly stops Cargo/heavy-build/LSP launches; root
confirms no active workspace and notifies alignment. Empty-cmdline analyzer
entries are confirmed zombies, not live servers. Alignment reports successful
reuse of its 23 saved module receipts and progress to 38 of 66 with one serial
bounded Lean compiler. Our source work remains in this worktree and touches no
alignment input. Pending checks wait for explicit release, preserving the goal,
frozen integration gate and final publication review requirements.

Alignment explicitly releases its build window after reporting a frozen pass
covering 1,048 modules and 13,471 ordered reports, including 66 affected modules
and reuse of the 23 saved successes. This is alignment's evidence, not new proof
acceptance for provider changes. Root confirms the absence of active compilers
and language servers, then resumes the provider writer's serial Cargo window.

Receipt 151 passes all 22 normal cases with actual main42 positive controls,
template/donor corrections and imported-certificate reuse/conflict assertions.
Receipt 152's temporary diagnostics localize template, hidden-row, root and
donor substitution refusal to link. Existing combine_checked preflight checks
the separate code against its defining export certificate; the hypothesized
donor acceptance is not observed and warrants no production change. The writer
corrects an earlier report: method/native cases still used an either-stage
assertion in these receipts. Their final assertions now require link InvalidState
for all eleven mutations. Diagnostic logging is removed before receipt 153's
broad batch. Receipt 153 passes 1,509 library cases with one ignored, all 18 main
cases and 39 architecture cases with the expensive owner-API case filtered for
its separate full gate. It includes the precise eleven link-stage refusals.
The command exits 101 at interface_resources: three cases reach type/kind
exhaustion instead of their expected constraint-work or cycle diagnosis; later
integration binaries do not run. The writer investigates the provenance and
binder-retention charges source-only without changing limits or assertions.

Alignment requests another short serial Lean navigation/parent-check window.
After terminal receipt 153 the provider writer explicitly stops all builds and
LSP launches. Root independently confirms no active compiler/server and an empty
Rust workspace inventory, then yields the window. Resumption requires explicit
alignment release; final broad verification, full architecture and publication
freeze/reviews remain pending.

While builds are held, static inspection identifies a candidate cause for the
three budget failures: retained Source A/T variable copies now charge three
additional units for spelling and source-origin retention. Resolution debt
continues into resolved-kind checking, and the public driver shares resolution/
checking type work across the graph separately from constraint work. This
explains the observed earlier owning ledger but does not establish whether all
retention is necessary. Exact phase/ledger tracing after window release must
distinguish required proportional charges from avoidable copies before a fix.

Independent read-only review traces the ordinary resolver's interface-owner and
method-local registry copies through the same shared clone helper. These copies
alone add at least 13,500 units for the monomorphic width-4,500 fixture and
30,000 for the polymorphic width-5,000 fixture. These are static lower bounds,
not measured totals. Empty provider collections skip their proportional paths;
defining-source retention follows kind checking and cannot explain the
same-module kind refusal. The review proves no duplicate charge and authorizes
no limit or fixture adjustment. Its external causal memo records the exact
callpaths for the pending bounded phase trace.

Alignment explicitly releases the short window at 14:15 UTC. Its navigation
session is closed, nine light checks passed, and the remaining worker is held
for source repair after a light-check failure. Root independently confirms no
active compiler/server and no Rust LSP workspace, then resumes the provider
writer's serial window for exact phase/ledger tracing. Alignment's later repair
and full integration runs require separately coordinated windows.

Receipt 154 reproduces the three failures with temporary phase tracing (exit
101, three passes and three failures). The two width-4,500 fixtures reach entry
kind checking with resolution type work 297,013 and 297,067, then exhaust its
327,680-unit limit while constraint work is 243,001 and 243,002. The width-5,000
polymorphic dependency resolves at 305,004 type units, then checking exhausts
its separate 327,680-unit ledger while constraint work is 295,000. The trace
confirms accumulated type-work precedence, not a duplicate debit. The writer
reviews retained-record versus inline Source-origin accounting before any
correction; limits, fixtures and expected diagnostics remain unchanged.

Independent accounting review supports a caller-only inline Source fast path:
the retained binder record covers its copied Span, while spelling and kind
remain separately charged. This is representation-aware cost policy, not proof
that all prior added units were duplicate. Generic origin accounting and all
Generated/Related chain, frame, box and related-span charges remain intact.

Receipt 155 passes all six unchanged interface_resources cases with the
temporary trace still present. The width-4,500 monomorphic graph resolves at
324,038 type units and reaches its intended evidence constraint refusal; the
cycle case reaches Cycle. The width-5,000 polymorphic dependency fails twice at
checking with type work 295,002 and constraint work 325,000, then a fresh
width-1,024 run succeeds. No compiler limit, fixture width or assertion changes.
The result verifies this focused correction, not a final broad source freeze.

After terminal receipt 155 the writer explicitly holds all builds and LSP.
Root verifies no active compiler/server and an empty Rust workspace inventory,
then yields alignment's requested two-minute repair light window. Trace removal
and source-only review continue; explicit release precedes our next build.

During this hold the writer removes all temporary driver/resolver tracing and
adds direct retained-parameter budget coverage for Source, Generated and Related
origins at exact, one-short, prefixed and fresh-copy boundaries. Generic dynamic
origin charges remain unchanged. These source-only follow-ups await the next
coherent trace-free library and integration batch.

Alignment explicitly releases the repair window at 14:32 UTC. Root verifies no
active compiler/server or Rust workspace before resuming serial Cargo. Receipt
156 is formatter-only (exit zero), despite its library label; receipt 157 is
the actual trace-free library command. It aborts in the deep imported-parameter
late-clone fixture, so it supplies no full library pass.

The fixture still assigns four units to the second Source parameter prefix;
the corrected caller policy requires two, followed by one Kind unit. Its former
short limit therefore permits success, and expect_err formats the unexpectedly
successful deep provenance before iterative disposal. The writer reconciles
the exact constants and wraps unexpected success in the existing iterative
test buffer before asserting refusal. Production partial-clone guards, depth
32,768, stack 256 KiB and default limits remain unchanged. Receipt 158 reruns the
full library on those fixture corrections; it is pending.

Receipt 158 completes without abort: 1,504 pass, six fail and one is ignored.
The deep imported partial-clone case passes, as do all 22 normal provider cases
and the new Source/Generated/Related accounting case. Six remaining fixed-budget
fixtures retain old constants for one, two or 32 Source copies; their former
short limits now admit success. The writer reconciles only those removed debits
by actual retained-copy count, preserving source widths, deep provenance costs,
stack bounds, semantic assertions and independent ledgers. Receipt 159 runs the
full library on the reconciled constants; it is pending.

Receipt 159 passes 1,510 library cases with one ignored in 32.70 seconds. This
includes the reconciled exact-budget fixtures, unchanged deep partial-clone
cleanup, all normal publication cases and direct origin accounting. Child
reports do not add cases to that total. Formatter and full integration batches
follow on settled source, with the expensive owner-API architecture case reserved
for its separate full gate. No final code/context freeze or review approval yet.

Receipt 160 formats successfully. Broad receipt 161 exits 101 after passing the
library (1,510 plus one ignored), main (18), architecture (39 with one filtered)
and integrations through local newtypes, including all six interface-resource
cases. Method_parameter_resources has three passes and one stale source-formula
pin failure; later binaries do not run. The writer removes seven old B2 test
markers at this terminal boundary and reconciles formula pins with their passing
owning probes, including retained spelling/domain metadata and scoped owner-kind
scans. Implementation limits and semantic assertions remain unchanged.

Receipt 163 passes all four method-parameter integration cases after formatter
162. A source-only arithmetic clarification keeps the same measured nine-unit
total and avoids an identity operation; formatter 164 passes. Settled-source
broad receipt 165 is pending, with only the expensive owner-API scanner filtered
for its separate full architecture gate. Earlier broad receipts do not claim
this later source manifest. Tracing and obsolete B2 markers are absent.

Receipt 165 passes the complete broad command: 96 top-level binaries, 3,104
passes, one ignored library case and one deliberately filtered architecture
scanner. Its 93 non-architecture integration binaries contribute 1,537 passes,
including the repaired budget/formula suites and later specification examples.
Root independently takes the last summary per Running block, excluding nested
child reports. This does not complete the deferred full architecture gate.

All-target Clippy receipt 166 rejects one test-only int_plus_one expression in
the linked budget test. The writer changes used <= prefix + exact - 1 to the
equivalent used < prefix + exact, preserving its lower bound and all limits.
Root verifies that provider.rs is the sole code-input difference from receipt
165. That broad pass therefore remains prior-source evidence. Clippy 167 and
the remaining gates run on the corrected candidate; final broad verification
precedes coherent source/context freeze and fresh ordered reviews.

On the corrected candidate, receipt 167 passes all-target Clippy with warnings
denied and the explicit unfinished-slice dead-code allowance. Receipt 168 passes
private-item rustdoc with warnings denied; format check 169 and diff check 170
pass. Full architecture receipt 171 includes all 40 cases without filtering and
is pending. A final broad receipt will cover the equivalent test correction on
the same code inputs before source/context freeze. No source changes are planned,
but freeze and review approval are not yet established.

Full architecture receipt 171 exits 101 after 312.30 seconds: 39 pass and the
automatic owner-API scanner rejects direct ImportedFacts backing mutation through
self.provider_groups.insert. This is a newly observed owner-boundary violation,
not a passing scanner or a reason to weaken its gate. The writer localizes and
corrects it source-only; current broad/Clippy evidence predates that correction.

After terminal 171 the writer explicitly holds all Cargo/heavy-build/LSP
launches. Root verifies an empty active compiler/server and Rust workspace
inventory, then yields alignment's requested exclusive 15–25 minute frozen
integration window. Our goal/worktree remain intact. Source-only correction and
review preparation continue; explicit release precedes a rerun of full
architecture and current broad/final gates. Code/context freeze remains pending.

Source-only correction expresses Occupied/Vacant entries at all four new
certificate-map insertion sites. ImportedFacts reuses the exact same canonical
Arc and rejects a conflicting owner before displacement; summary and linked
staging reject occupied fresh-only slots. Independent read-only review finds no
remaining raw certificate-map insert, unchanged precharges and no native-policy
or scanner changes. The helper itself promises no rollback of earlier fresh
entries if a later direct call fails: the owning resolver transaction is
discarded and publishes no checked module or exports. No new architecture or
test pass is claimed during the build hold; resulting-source gates remain.

Alignment releases the frozen window at 15:16 UTC after its gate fails an
unchanged consumer's transitive import availability. It retains 52 successful
affected receipts and the failure; this is no proof integration pass for either
task. Root independently verifies no active compiler/server and no Rust LSP
workspace, then resumes the provider writer's serial focused controls and final
gates on the Entry correction. Main and alignment frozen inputs remain untouched;
later proof repair windows require separate coordination.

Formatter 172 passes. Receipt 173 passes all 22 normal publication cases on the
Entry correction, including canonical-certificate reuse/conflict controls,
transaction slots, charged late refusal, source disposal, linked/Core closure
and exact-budget retries. This verifies focused behavior, not the failed scanner.
Current Clippy 174 and later full architecture/broad gates precede freeze.

Root reads the prepared external freeze script without invoking it. It requires
successful final receipts on identical code inputs and documentation STOP;
archive verification and budget-scope wording are tightened before actual use.
The packet must preserve both recorded manifest hashes and current bytes, and
distinguish linked check/link setup and Core module-relation setup from the
actual measured authentication/validation work. No broad production budget
exemption or completed freeze is inferred from preparation.

Root verifies the refined preparation script's recorded full-manifest,
archive/current-byte and final code/inventory checks without invoking it.
Budget wording now states the exact setup exclusions. Clippy 174 passes on the
Entry candidate with the same recorded dead-code allowance; full architecture
and final broad remain pending.

Receipts 175–177 pass private-item rustdoc with warnings denied, formatting and
diff checks. Full architecture 178 passes all 40 cases in 330.95 seconds,
including the unchanged automatic owner-API scanner. Final broad verification
and the coherent source/context freeze remain pending. The writer holds before
the broad batch so alignment can use an explicitly coordinated proof window.

Root rereads the proof tooling and navigation guides and Lean skill, then
rechecks the 18 adopted files against merged commit a2ced870 with no differences;
the Cargo configuration hash also matches the adoption record. HEAD, branch,
worktree and active goal are preserved. The current inventory exposes 12 Rust
LSP tools and no direct Lean LSP tools. The pinned eight-tool Lean adapter has
verified stdio feedback; neither LSP feedback nor partial cached successes
establish frozen integration acceptance. No Rust workspace is active.

After the full architecture pass, root grants alignment's requested exclusive
proof window only after the writer's explicit BUILD HOLD and fresh empty
compiler/server/workspace inventory. The adopted serial runner is confirmed
live and records actual validated cache hits and fresh compilations; there is
no terminal proof acceptance yet. Provider broad receipt 179 awaits release.
Read-only preparation updates the acceptance matrix and M0/B0 handoff memo for
Source-origin accounting, certificate ownership and four Entry sites. Neither
reader finds a new targeted publication assertion gap. Root prepares an external
review brief for the eventual frozen packet; it preserves scope and evidence
qualifications and does not establish approval or source ownership transfer.

Final broad receipt 179 exits zero. Root independently splits top-level Running
groups and uses each group's last summary: 96 binaries, 3,104 passes, no failures,
one ignored and one filtered scanner. Every code/native/config/tool input matches
the 267-entry full architecture and focused/final gate manifests. Full architecture
178 already passes the unchanged scanner. This is resulting-source publication
verification, not whole-workspace adoption or resource-instance execution.

The writer explicitly enters BUILD HOLD without source edits or Cargo/LSP launches.
Root confirms empty compiler/server and Rust workspace inventories, then grants
alignment its ready lightweight dependency-query/private-negative window. Its
earlier module gate preserves 52 validated cache hits and 34 fresh compilations;
the supplemental query failure and remaining queries stay distinct. The provider
packet can archive and verify bytes without launching a compiler in that window.
Root completes tracking documentation and stops edits before packet creation.
Fresh contract review and then quality review still determine publication
approval. The external row caller inventory remains preparatory, not M0 completion.

Fresh contract review and then fresh quality review both pass the bounded
Type-only publication candidate without blocking findings. Each reviewer
independently verifies the v2 packet before and after source inspection and
counts current broad evidence. Approval retains the unfinished-slice Clippy
allowance, budget setup exclusions and actual pending instance boundary. It
does not establish row arguments, specialization, lifecycle runtime or adoption.

The first independent packet audit rejects omission of one measured ignored
Lean-tooling bytecode input. The original packet remains preserved. Packaging
alone changes to archive Git files together with all measured input paths; no
gate manifest is filtered and no code bytes change. V2 contains 1,175 full files
and 267 measured inputs, and root's independent archive/current/input/receipt/
identity audit passes. Both fresh reviews bind to that exact v2 identity.

Root transfers sole prospective source/Cargo ownership from the stopped
publisher to a fresh GPT-6.1 Sol row/instance owner. M0/B0 starts with read-only
reconciliation of the approved plans, reviewed code, concrete signatures,
argument carriers, original occurrence/registry owners, walkers and runtime
guards. The new owner independently authenticates the unchanged reviewed
baseline before root reopens task tracking. Source edits and builds await the
type/ownership mapping and coherent M1 batch; ordinary callbacks, actual c and
descriptor-backed runtime remain required later evidence. No commit, merge or
signature is performed, and the full SQLite/arena/borrowing/blueprint/tooling/
adoption objective remains active.

On 2026-10-03, root reviewed the external row/instance M0/B0 reconciliation and
execution mapping and released the coherent M1 structural migration to the sole
source owner. The release retains existing row-free kinds, independent owner
signatures, separate sealed associations, inherited roles, charged mixed walkers
and authenticated native Type positions. Source work is authorized; builds and
LSP require coordinated machine windows. Source admission and executable Core
remain later work. All 18 adopted proof-tooling files still match main; the
current direct inventory is 12 Rust LSP tools and zero Lean LSP tools, with eight
Lean navigation tools available through the pinned stdio adapter. Its smoke
check remains development feedback, while frozen integration is acceptance.
The external `root-m0-b0-release.json` preserves reviewed report hashes.

On 2026-10-03, an independent read-only authoring review drafted the external
FFI blueprint and tooling evidence. Root verified concrete static registration
and embedding APIs and required explicit attribution of missing executable
native binding. A safe adapter plus a foreign declaration manifest does not yet
connect Ash requests to native execution. The arena trial also distinguishes
unsupported closure layout from the retained-owner containment obligation by
requiring an admitted reference payload for that negative check. The drafts pass
Markdown lint with the existing width allowance only. Their read-time source
inventory is not a freeze; source/native authoring trials and final reports
remain pending. M1 continues with the sole source owner and no extra compiler
or LSP launches.

On 2026-10-03, the user requested more focus on goal completion and preferred
end-to-end, integration and need-driven regression tests over high-granularity
internal coverage. The plan and execution record now make S-01 the immediate
executable target, tie its prerequisites to missing execution boundaries, and
require a concrete observation or demonstrated defect to justify new tests.
Focused internal checks remain appropriate when they supply otherwise missing
required evidence or isolate an observed bug. Connected changes and affected
checks are batched; broad gates follow capability checkpoints or unresolved
regression risk. This changes work scheduling and reporting, not candidate
semantics, required evidence, independent review or final adoption gates. No
compiler change or test execution is claimed by this tracking update.

On 2026-10-03, a read-only contrasting-API walkthrough applied the draft
blueprint to zlib streaming compression. The
[native manual](https://zlib.net/manual.html#Basic) describes repeated progress
calls and input/output pointers stored in stream state. The proposed copying
wrapper therefore distinguishes copied client results from native-private
buffer retention; pointer detachment still needs adapter evidence. Its public
finish-data operation now supplies the capacity required by its native call.
Finishing compression remains separate from releasing stream ownership.
Ordinary result metadata cannot prove byte resubmission or progress: the
proposed wrapper names the retained unread suffix needed for those checks.
The external `ffi-blueprint-2026-10-03/contrast-walkthrough` draft and root review
preserve these findings without implementing a third binding. Actual blueprint
and tool trials remain pending with the SQLite, arena and borrowing cases.

On 2026-10-04, the common-support workstream preserved the original experiment
in unsigned unverified recovery commit `167bd8c` before creating
`codex/common-resource-support` in its own worktree. The paused task was not
resumed. Unrelated DN-0038 and proof-tooling drafts remain outside that commit.
The common migration extends the existing source, evidence, Core and evaluator
carriers with ordered Type/row owner arguments and original owner signatures.
Library compilation alone is preparation; declaration publication, deep-input
regressions, independent review and integration must pass before Batch 0 is
reported as delivered. SQLite and arena execution remain pending at this point.

On 2026-10-04, Batch 0 passed its compiler, declaration/publication, deep-input,
independent Core and architecture checks and was merged into the original
experimental branch at `c38b9d2f8c34077353be8d0a0a94b117867ce737`. The
[execution record](execution.md#current-checkpoint) distinguishes that delivery
from the unfinished instance bridge. Batch 1 preparation separates original
checked template code from body-free imported authority and stages immutable
instance plans and evidence for joint publication. These source changes do not
establish a working SQLite session or arena lifecycle.

The selected callback exposes a row-ordering boundary during this preparation.
Its diagnostic handler contributes the formal open row and makes no native
request. Unioning native acquisition or completion demands with that handler
output before interpreting the lifecycle phases would demand an additional
native exclusion on `Delta`. The recorded contract supplies only `Delta lacks
H`. The implementation must preserve the recorded phase interpretation and
principal handler union; adding an exclusion to admit the fixture would change
the design. Execution and independent final Core evidence for this case remain
pending.

Batch 1 final preparation now retains one reusable set of fresh template
identities and copied evidence occurrence keys before constructing the complete
final catalogue. Executable lowering uses that catalogue and independent Core
admission; it does not replay template source checking or reselect an
implementation. Fresh focused regressions pass for simultaneous Type/row
substitution, the Scope tuple result's body capture, and phase interpretation
under the recorded formal callback exclusions. These tests establish those
boundaries only. The first public S-01 execution attempt fails during kind
checking: the instance checker looks for an imported defining owner in a
local-only registry. No native SQLite call or completed session is established
by that attempt. The repair must use the authenticated original imported owner
inventory rather than inventing a use-site owner signature.

The later public SQLite receipt `batch-1-sqlite-public-suite-02.log` executes
all nine cases in that receipt on the common branch, including S-01. It observes the nested
`Completed(Completed(Ok(42), Closed), Closed)` result and actual statement
finalization before connection close. Separate repeated and overlapping scopes
observe distinct activations; the initializer counter advances once, and refused
statement acquisition executes no statement body or finisher. Original manifest
registrations without executable bindings still refuse before acquisition.
These receipts replace the earlier failed kind-check attempt as current evidence
for those programs, without establishing the remaining open-row or control cases.

The minimal arena source trial uses the same public API and generic scope engine.
`batch-2-arena-public-02.log` observes actual usage `(0, 64, 0, 4)`, native
release exactly once, repeated and nested scopes, zero capacities and acquisition
refusal. The fixtures required parentheses around constructor application in the
existing initializer grammar; no depth limit or grammar change admitted them.
Typed allocation, Layout, references and storage families remain later arena work.
These execution receipts are moving-branch evidence; review and original-branch
integration are still required by the execution record.

The 2026-10-05 full library receipt passes 1,528 cases with one explicitly
ignored advanced callback. The constrained-template regression was caused by
repeated self-proof of the same immutable native declaration during one source
admission. A bounded, fallibly allocated memo retains only successful proof for
that exact original allocation; fresh final Core admission does not inherit it.
The positive and all eleven mutation negatives pass without raising limits.
Two transform owners now expose consuming APIs instead of raw storage transfer.
Connected public, architecture and original-branch integration checks remain the
Batch 1 delivery gate.

The broad public regression gate also exposed accumulated fixed debug frames in
ordinary cell checking on the existing 256-KiB child stack. Debugger measurements
identified an 89-KiB expression dispatcher retained during equation evidence and
expression checking. Direct worklist dispatch preserves those operations while
avoiding the unrelated frame. Independent review preserves ownership, ordering,
checks and accounting; fresh regression06 passes at the original limit.

Receipt `batch-1-connected-gate-12.log` passes all 1,528 library cases (one
advanced callback remains explicitly ignored), the repaired syntax expectation,
public resource stack regression and connected SQLite/resource/Core suites.
Architecture41 passed in receipt10. These common-branch gates precede the
unsigned delivery commit and fresh original-worktree integration verification.

Batch 2 preparation keeps arena policy in its library manifest and adapter. The
compiler sees the same generic provider scope used by SQLite. The public usage
query reads the existing native backing; release observations occur after that
backing is destroyed. Configuration refusal occurs before allocation and body
execution. Fresh verification and original-branch integration remain required.

Batch 1 is verified and integrated on the original branch at unsigned merge
`7c97a454a930c7cc732ce43f1f25c15ef2eea7f7`. Fresh original compilation,
1,528 library cases, architecture41 and public/module/Core checks pass. Unrelated
drafts remain byte-for-byte unchanged. The minimal arena delivery is checked
separately; its public suite and the SQLite suite pass together in receipt04.

Batch 2 common verification passes the four public arena cases, all ten SQLite
cases, thirty-two adapter unit cases and nine physical arena cases. All-targets
compilation and strict carrier inventory pass. Reusing the original target
required invalidating only the differing foreign/export source inputs on return
to the common worktree; compatible dependency caches were retained. The arena
native test now asserts slice emptiness directly, avoiding an ambiguous empty
array comparison introduced by the added workspace dependency.

## 2026-10-05: packed copying values

The SQLite authoring interface needs separate byte and UTF-8 values. The selected
candidate now uses built-in Bytes and String with compiler-owned pure modules.
The old integer-list Bytes export cannot coexist with the built-in spelling:
the ordinary frontend rejects the old import selector before execution. The
shared delivery therefore migrates that codec and its scalar SQLite fixtures
before the complete text interface. No compatibility byte family is retained.

[The ordinary value example](examples/bytes-string.ash) uses literals, captures,
UTF-8 conversion and exact comparison. String literals remove the measured
manual byte-constructor authoring burden. No generator or unrelated authoring
tool is required for this copying checkpoint. The full String API remains out
of scope. These are candidate experiment examples, not current `main` syntax.

## 2026-10-05: generic arena integration

Unsigned common commit `eb14326` is merged into the original experiment branch
at `53db4ebb050fdcb12df84857ab8b45adfa6b2cb6`. Fresh original-worktree public
checks pass four arena and ten SQLite cases; native checks pass thirty-two
adapter unit and nine physical arena cases; all-targets compilation passes.
The arena observes actual native `(0, 64, 0, 4)` usage and exactly-once release,
including repeated/nested/zero/refused and escape boundaries. Both public-test
dependency records name the original fixture root. All twenty-one unrelated
file hashes remain unchanged. External `batch-2-integration.md` and JSON retain
merge identities and receipts. Independent arena work may start from this
integrated commit; typed allocation, references and Layout remain excluded.

Batch 3 row-context and exact provider-handler association changes are under
connected verification. Their source progress does not complete actual
per-request captured-demand realization or establish current Ash semantics.

## 2026-10-05: shared row and discard execution evidence

Fresh public control receipt07 passes thirteen cases, including the formal
open-Delta callback and its missing-lacks negative, curried and closed Impl
contexts, owned discard with outer diagnostic before finalization/close,
ordinary override refusal and repeated same-site native activations. Two
retained-dependency cases pass independently using explicitly injected native
dispositions. The finite distinct-captured-demand case still refuses pending
actual original-port realization. This is moving source evidence, not an
integrated Batch 3 delivery.

Library receipt07 passes 1,534 cases and fails one new scalar association
fixture; one advanced callback remains ignored. The fixture omitted its value
graph and authenticated capture cut; it now passes fresh static receipt09.
Original completion/resource limits and old constrained/authority/registration
regressions were unchanged. Warning cleanup removes uncalled compatibility
helpers and gates actual unit-test entry points; pending proof facts remain
retained until their shared realization is implemented or exact redundancy is
established. Mixed local readiness and request-specific capture work remain
under independent review and connected verification.

The connected actual-capture implementation builds in all-targets receipt15.
Public receipt15 passes thirteen control cases and fails the finite witness and
mixed local helper case. Provider library receipt16 passes 113 cases and fails
the finite witness and a mixed publication rollback harness; its formal open-row
case passes without an ignore. The rollback harness used a restricted provider
expression scanner on an ordinary helper containing a resource instance.

Source investigation also found two phase boundaries: provider bodies restored
lexical evidence before closing their ordinary obligations, and handler helper
results were checked before resource discovery supplied native acquisition
results. Reviewed repairs close the ordinary body obligations once, keep capture
route lookup read-only, and validate exact handler-call results after discovery.
Retained state-association validation now compares the original canonical owner
signature and native state roles. These repairs and their refusal cases are
applied but await fresh compiler, public and bounded regression checks. They
do not complete or integrate Batch 3.


The common branch reconciles the independently verified packed-value merge
`8adf4b2` from the original branch. Fresh all-targets receipt21 passes; public
control receipt21 passes fourteen cases, including the mixed local helper, and
fails three. The lexical fixture needed a local nominal key under current Ash;
the corrected Token-key case still fails checking in receipt23. Provider library
receipt23 passes 113 cases and fails the finite witness and publication rollback
assertion. An owner-vector Core test invocation matched zero tests and is not
positive evidence. Debugger receipts23 isolate the finite and latent-answer
cases at final independent scope admission, after source realization. The exact
capture graph domain and lifecycle answer substitution remain under repair.
All three retention cases pass in receipt22, including consumed versus retained
storage on report conversion failure. The original limits remain unchanged;
Batch 3 is not yet an integrated delivery.

## 2026-10-05: shared lookup ownership handoff

The SQLite workstream transfers isolated unsigned lookup commit `0ac9c747`,
with both private indices retaining exact canonical identities, original match
order and lexical fallback. Common merge `41410a9` preserves both histories;
fresh compilation and 1,539 library cases pass, with the inherited advanced
callback still ignored in this baseline. The 56 pending common files and 45
pending SQLite files are separately preserved. Common now owns all shared
compiler/Core/capture/provider/generic runtime edits; SQLite retains adapter,
library and example work. Serial Cargo windows avoid concurrent builds.

Larger copying/reuse and persistence cases still refuse at the unchanged
327680 limit. Watcher membership is the next measured cost; the pending native
String/TEXT and generic error-classification snapshots are not part of the
isolated repair. Fresh connected verification passes 193 cases, including all
forty-one architecture checks and the existing public SQLite/arena lifecycles.
Formatting and changed-document review pass. Unsigned original integration
`456bb4c367b39354ddf4cb830be124298f71fdf4` passes fresh all-targets compilation,
127 capture library cases and 136 public cases. SQLite merges that checkpoint
while preserving its pending files. This changes execution order, not the P-1
goal or current Ash semantics.


## 2026-10-05: connected common control and refusal evidence

Fresh receipt31 compiles all targets without warnings. Capture reconstruction
passes 139 cases; the owner-vector matrix after both transforms and the
source-derived fragment local-scope matrix pass. The finite same-substitution,
same-scalar-row witness now completes through the public driver with distinct
captured demands and actual native owners. Control passes sixteen of eighteen
cases, including the refreshed answer under ordinary enclosing typing.

Two remaining public cases expose ordinary contextual evidence boundaries:
a conditional resource body closes a Make obligation before the enclosing
result determines its type, and the lexical open-row Run obligation refuses
selection. Provider checks pass 216 cases and fail two fixture assertions:
written row arguments and the imported authenticated StateAccess registry view.
These are recorded failures, not completed delivery.

Nine codec cases pass. A new real-payload test incorrectly assumed the ordinary
evaluator used the compiler's finite cumulative limit; evaluation has an
unbounded cumulative instantiation ledger. Its observed success contradicts the
fixture expectation. The test is being changed to observe actual native codec
admission refusal without adding a runtime limit. All existing limits remain
unchanged. The isolated watcher cost delivery will let SQLite rerun realistic
copying and persistence independently of the remaining control repair.

Formatting and changed-document review pass. Unsigned original integration and
fresh integrated checks remain the delivery gate. This changes execution order, not the P-1 goal or
current Ash semantics.

## 2026-10-05: bounded watcher membership

The next isolated common delivery replaces repeated scans of each capture
slot's reader list with an analysis-local index of exact source/reader slot
pairs. Slot creation contexts remain part of their identities. The ordered
reader list still determines notifications; no capture, evidence or owner
authority comes from the index. Both retained entries are charged and reserved
before insertion. Duplicate visits retain their original notification position.

Focused regression cases cover distinct creation contexts, notification order,
wide repeated visits, exact work and one-short refusal with prefilled ledgers.
The selected Type work limit remains 327680. This does not add a runtime limit
or complete the pending contextual control and generic codec changes. All 65
pending common paths remain in immutable source copies and a retained stash;
SQLite independently preserves its adapter and library files. Fresh common verification passes all-targets compilation, 1,541 library
cases with one inherited ignore, and 183 connected public/architecture cases.
Unsigned original-branch integration and fresh integrated checks remain the
delivery gate. The unrelated inherited baseline warnings remain visible; the
pending B3 cleanup is not included in this isolated delivery.

## Shared edge membership checkpoint (2026-10-05)

SQLite reproduced three copying refusals and one persistence refusal after the
watcher delivery at `3f8e03e0`. Its first recorded refusal consumed 327,674
units and requested 19 more for an edge-membership scan with 18 existing
edges. Ordinary helper-module partition probes also refused before native
acquisition. Those probes do not satisfy the required flat programs.

The common repair indexes exact target/source slot pairs within one capture
analysis. Slot identities retain creation contexts. The existing edge vector
still determines propagation order; watcher membership remains independent.
Duplicate membership costs one unit. New edge insertion admits and reserves
the index entry, ordered edge, any missing notification watch, and queue
entry before changing semantic state. Refusal leaves all relations, revision,
and queue flags intact. The default 327,680-unit work limit is unchanged.

External contract and allocation/work reviews passed for patch `156c1e24`.
Fresh common checks passed: all-target build, 1,543 library cases (one
inherited ignore), 142 connected public cases, and 41 architecture cases.
Integration checks and larger SQLite reproduction remain pending. All 67
common Batch 3 paths were preserved in a retained stash and pinned source
copies before isolating this delivery. The source-control and lexical-row
repairs remain separate unverified progress.

## 2026-10-05: connected control, validation and consumer handoffs

Connected receipt68 passes 1,577 library cases without an ignore and 44 public
control, codec, retention and diagnostic cases. The finite capture-demand witness
now completes; it remains separate from the formal open-row callback. Exact
original identities and enclosing declaration row facts constrain specialization
and independent final validation. Large debug source-dispatch frames caused the
256-KiB owned-discard regression; mechanical outlining restores that existing
bound without changing checks, accounting or execution order.

The realistic SQLite programs still record four default-work refusals. The
current-source reset profile reaches exactly 327,680 units with no diagnostic
overflow. It supports a measured follow-up, not a dynamic-result memoization
shortcut or a larger limit. Temporary probe restoration verifies all original
file contents and both Git diffs. A separate ordinary bare-row program exposes
loss of an enclosing exclusion; its repair must reuse that established context
and keep strict equality. Preparation and partial probes remain distinct from
verified integration.

SQLite retains native/library ownership. Common retains shared compiler, Core,
capture, provider checking, generic runtime and merge ownership. Arena prepares
its independent codec and pinned candidate handoff after the verified original
tip, with no concurrent common writes. Serial Cargo windows admit focused native
checks while common changes are reviewed; consumers merge the next verified
original tip before their independent delivery. Typed arena allocation and its
publication protocol remain outside this common workstream.

The ordinary bare-row counterexample passes through final Core in receipt77
once both initializer-check and retained binding annotations use the established
context. Connected evidence now passes 1,578 library and 45 public cases. The
strict architecture gate exposed one missing shared-map alias and two moved
borrowed carrier coordinates, corrected without weakening its fixed-point
comparison. Full common verification and original-branch integration remain
pending; the realistic SQLite work refusals remain explicit.

## 2026-10-05: verified common row/control delivery

Connected receipts 87/89/90/91 complete the required common checks before
integration. The stale probe artifact and obsolete formula guards are recorded
in execution, including their causes and focused corrections. Source limits
and exact accounting assertions remain in place. Contract, quality and
documentation review pass. Original-branch unsigned merge and fresh unfiltered
verification remain the delivery checkpoint; larger SQLite budget cases and
typed arena work retain their independent scope.

## 2026-10-05: common integration

Verified common commit `9080b9508be3a8a0b5bea2332826b6301cc4cdea` is integrated by
unsigned original merge `3f9dd7565992169a1d9a77278105c99d6c8b4cdb`. Both histories
and all twenty-three unrelated working files are preserved. The external
`batch-3-integration` receipt records the final original tip and whole unfiltered
verification outcome, which governs completion and the consumer handoff.
Independent SQLite and arena merges follow that verified checkpoint. Shared
source remains common-owned, and Cargo leases remain explicit and serial.


## 2026-10-07: completed-phase preparation checkpoint

The selected shared source records a delivered control-call prefix only after
success, consumes a known failed row equation without redundant membership work,
and borrows prepared replacement Types through the existing substitution kernel.
The connected Common normal gate passes workspace and public tests, independent
Core/rebuild cases, all 43 architecture checks, build, formatting, strict lint
and warning-denied docs. Source commit, preserving original merge and integrated
full verification are the next delivery checkpoint.

The original four SQLite programs supply actual native cost evidence under
restored diagnostic ceilings. Selected changes save work but do not cure the
larger three normal-limit refusals. Dirty-edge, strict-predecessor and constructor
staging candidates are rejected and exactly reversed; passing native execution
alone is insufficient when measured work rises. A private typed-route/frame
candidate targets contextual expansion and has no execution claim yet. Shared
compiler ownership remains Common's, native/library ownership remains SQLite's,
and engine windows remain serial. DN-0036 retains experimental authority.


## 2026-10-07: completed-phase integration

Common commit `1fa1f4f91d2c29bd8f38d180991336963d9aff75` is integrated by
unsigned Original merge `f0a8e59a8ac824af959f72ff19af10a7563d0ba7`.
The original-worktree full gate passes all six stages with 3,364 parent passes,
zero failures or ignored cases, and all unrelated work preserved. Receipt 284
records the actual return and independent raw-log and guard audit. No limits
change, and the three larger SQLite normal-budget deficits remain unresolved.
Fusion continues the private frame consumer; a smaller context-extension reuse
candidate is source-reviewed but uncompiled and unmeasured. Neither candidate
is part of this verified delivery. Library/native ownership and serial engine
coordination remain unchanged.
