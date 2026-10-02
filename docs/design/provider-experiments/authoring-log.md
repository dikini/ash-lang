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
