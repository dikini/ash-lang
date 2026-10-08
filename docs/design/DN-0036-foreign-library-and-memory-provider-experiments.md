# DN-0036: Foreign Library and Memory Provider Experiments

- ID: `DN-0036`
- Status: exploring
- Related: [DN-0035](DN-0035-region-memory-management-and-verified-providers.md),
  [DN-0031](DN-0031-resource-composition-concept-map.md),
  [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md),
  [DN-0034](DN-0034-one-shot-kernel-soundness-and-practicality.md),
  [DN-0025](DN-0025-library-and-package-milestones.md),
  [DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md),
  [AD-0004](../decisions/AD-0004-small-step-semantic-method.md),
  [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This design note governs two bounded design experiments and their comparison.
> It defines no current Ash semantics and accepts no production architecture.
> Experimental implementations are evidence. Successful designs require the
> proposal, decision, task, and verification steps described below before they
> become part of Ash or its standard library.

## Question

Can library-defined providers connect Ash to foreign code and manage scoped
storage through useful source APIs whose safety contracts are enforced by type
checking? Which mechanisms must the language provide, which can be ordinary
library definitions, and which tools make those libraries practical to author?

Study two connected cases: a SQLite binding and a memory resource beginning
with a fixed-capacity scoped arena. Their purpose is to discover:

- underlying design pressures and counterexamples to candidate abstractions;
- implementation requirements specific to each case and reusable across cases;
- what convenient client and provider syntax must express;
- which surface additions and Core operational rules are needed, and which
  behavior can reuse existing forms and transitions;
- which properties can be inferred and which need explicit contracts or evidence;
- how types, effects, dependencies, and usage rules establish safety;
- a repeatable blueprint and supporting tooling for foreign-library authors.

A working native wrapper or allocator alone does not answer these questions.
The evidence must connect source descriptions, checking, execution, and costs.

[DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md) records the separate
program for authoring foreign-library interfaces in Ash through generic host
ABI and linking infrastructure. Findings from these experiments can inform that
program; it does not change this note's experiment contracts or completion
criteria.

## Context

### Current semantic foundation

The [specification](../../spec/README.md) defines passive modules, rank-1
ordinary values, interfaces, exact effect instances, lexical handlers, and
single-use nonescaping continuations. Modules have no runtime initialization.
The [dynamic semantics](../../spec/dynamic-semantics.md) give ordinary values an
evaluator-managed heap. General regions and selectable storage disciplines are
not current language features.

The two [builtin resource providers](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
introduce an acquisition identity, duplicable non-owning access, sealed provider
evidence, an exact effect interpreter, and scope-owned completion. Inferred
dependencies prevent access from escaping, including through closures,
evidence, and request operands. A fresh runtime activation distinguishes
repeated acquisitions. Capture/resume retains the owned scope; checked discard
closes owned abandoned scopes. [Cleanup](../../spec/static-semantics.md#scoped-cleanup-actions)
has its own completion and interpretation obligations.

These mechanisms do not provide general library-defined acquisition, borrowing,
ownership transfer, foreign representations, or view-invalidation checking.
Lexical scope does not establish address stability, compatible layout, or
permission for aliases to mutate shared storage. A live resource owner does
not imply that every view previously obtained from it is still valid.

The [elaboration contract](../../spec/elaboration.md#surface-erasure) retains an
authenticated Effect `Resource` carrier for the closed builtin APIs. Selected
interface evidence already lowers to ordinary functions, but a source `with`
cannot manufacture sealed resource authority. General providers must account
for that authority rather than assume interfaces already supply it.

### Transferable evidence and pressure

The [native-buffer evidence](effect-ash/narrow-foreign-provider-evidence.md)
establishes a bounded native allocation adapter, checked access, activation
identity, owned release, failure handling, and independent validation. Its
exclusions include library-defined acquisition and fallible native close. Its
combined recursive cleanup case also exposes checker-cost pressure; increasing
limits is not evidence that a new analysis scales.

[DN-0031](DN-0031-resource-composition-concept-map.md) and
[DN-0032](DN-0032-algebra-of-scoped-resource-composition.md) distinguish resource
authority, interpretation, provider code, and composition. Those proposed roles
guide comparisons without selecting a syntax or adding current semantics.
[DN-0035](DN-0035-region-memory-management-and-verified-providers.md) supplies the
broader memory direction and reference corpus. This note bounds its initial
experiment; it does not assume regions or borrowing already exist.

[DN-0034](DN-0034-one-shot-kernel-soundness-and-practicality.md) distinguishes
semantic soundness from implementation correspondence. Existing continuation
proofs transfer only within their admitted fragment. New storage and foreign
rules need their own obligations and an explicit connection to execution.

## Constraints

- Preserve current ordinary immutable sharing, closure use, module boundaries,
  exact effect identity, and completion behavior in the comparison corpus.
  Report any proposed semantic change explicitly.
- Keep source name scope, allocation lifetime, access permission, interpretation,
  and release authority distinct. Reuse current mechanisms where their actual
  contracts suffice.
- Give each new rule a concrete positive case and a counterexample. Measure
  rejected useful programs and annotation burden as well as unsafe admissions.
- Keep arena ownership scoped. Do not package or transport an arena owner with
  dependent values, extend its lifetime by returning it, or transfer it between
  processes. Passing non-owning access within the owner's lifetime is allowed
  subject to the candidate access rules.
- Captured control may retain an owned scope under the admitted continuation
  rules. This does not make its owner a transportable source value. Borrow
  obligations must remain valid while control is captured.
- Treat processes as future pressure consistent with shared-nothing storage.
  Process implementation, cross-process sharing, and large-message transport
  without copying are outside these experiments.
- Begin with synchronous foreign calls that finish before Ash resumes. Exclude
  foreign callbacks into Ash, escaping continuations, threads, asynchronous
  execution, dynamic loading, and a universal ABI. Record limitations without
  designing those mechanisms in advance.
- Keep foreign contracts, checked provider obligations, runtime tests, and
  proved properties distinguishable. A declared signature is not evidence that
  arbitrary foreign code obeys its memory contract.

## Candidate directions

### Provider descriptions

Compare the same operations and lifecycle under these descriptions:

| Candidate | Question and tradeoff |
| --- | --- |
| Explicit acquisition, ordinary handlers, and cleanup | Establishes the reusable baseline and exposes relationships authors must repeat. Identify any authority or typing rule the baseline still needs. |
| A provider declaration packaging those parts | May make state, operation coverage, dependencies, and completion explicit in one place. Test whether it introduces independent semantics or can elaborate to the baseline. |
| Ordinary definitions plus scoped installation | Tests whether reusable functions and evidence can assemble a provider with little dedicated syntax. Expose any need for a body type beyond current rank-1 source positions. |

Do not choose a candidate because its declaration looks shorter in isolation.
Compare provider authoring, importing clients, helpers, diagnostics, and the
resulting checked representation. A generic foreign boundary may require a
trusted primitive; SQLite-specific behavior should remain library material.

### Memory descriptions

Start with explicit arena acquisition and typed allocation. Compare that with
ordinary construction directed to an applicable scoped provider, as proposed
in DN-0035. Determine how helpers and closures obtain the allocation context,
how allocation effects appear in types, and how independent results escape.
Nearest-region construction is a candidate, not an assumed rule.

For data crossing the FFI, compare copying into independent storage with scoped
borrowing. Retained access needs a stronger dependency than access lasting only
for one call. Transferring arena ownership is not a candidate.

Counting and tracing are later reclamation comparisons under the same scoped
owner. Neither changes the owner's lifetime or permits dependent values to
escape. They need not become a mandatory sequence or prerequisites for an arena
proposal; every claim of generality must name the policies actually tested.

## Evidence and experiments

The initial [experiment package](provider-experiments/README.md) records the
bounded plan, contract inventory, paired scenarios, surface/Core comparison,
and worktree inputs. Its expected outcomes remain experimental; observed
results must identify the checker or native harness that established them.

### Common method and experimental boundary

Keep prototypes and their fixtures in an identified experimental directory or
checkout. Before coding a slice, record the Ash revision, admitted source
fragment, candidate contracts, trusted primitives, implementation steps,
comparison cases, and reproducible commands. Record the native library version,
build configuration, host ABI, and toolchain where applicable.

Implement these experiments by extending the existing Ash compiler and runtime
in a separate repository worktree under `.worktree/`. Use the current parser,
resolver, elaborator, Core validator, and effect machine. Native helper tests
may establish foreign behavior or allocation cost, but source examples must
exercise Ash's existing driver and the experimental extensions to that pipeline.
An isolated unsafe adapter is a foreign-call boundary, not another language
implementation. A Rust wrapper's borrow checking does not establish Ash typing.
Hand-constructed Core can isolate a question but is insufficient for syntax,
inference, or library-authoring conclusions.

For each case retain the source, expected admission or rejection, inferred and
explicit information, diagnostic cause, resulting checked form, execution
observations, and relevant costs. Cross module imports and generic helpers in
the source corpus. Keep foreign calls behind one identifiable adapter so their
assumptions and instrumentation can be reviewed.

The dynamic account should use small-step configurations consistent with
AD-0004. Any proposed product representation must have a path through resolved
identities, typed elaboration, independent Core validation, transformations,
and explicit machine execution under AD-0006 through AD-0008. An experimental
shortcut must identify the missing correspondence rather than silently bypass
these product boundaries.

### Surface syntax and Core operational semantics

Each experiment must produce a candidate semantic delta alongside its executable
evidence. It must connect surface programs to typed Core and to their execution,
including the foreign or storage boundary. An authoring API and successful
native calls are insufficient without this account.

Always follow the types. Distinguish a resource type definition, which composes
its provider, formal unique-identity parameter, effect interface, and handlers,
from an expression establishing an initialized instance with a lexical lifetime.
Derive input and state types, operation and handler types, outward effects,
result types, and dependency rules before proposing their surface spelling.
Reuse current effect and handler conventions where their contracts suffice.
Lexical resource instances do not settle program-lifetime resources; global
identity, initialization, publication, and shutdown remain separate questions.

For surface syntax, describe any proposed foreign declarations, provider
definitions, acquisition forms, allocation, and scoped access constructs. State
their grammar, lexical implications, precedence, binder scopes, import/export
behavior, and interaction with existing expressions and declarations. Compare
reuse of current syntax with additions. If no new form is needed for a mechanism,
show the ordinary definitions that express it and record that result explicitly.
Label all new forms as experimental.

For every candidate construct, retain a mapping to its resolution and typing
rules, effect and dependency information, and elaborated Core representation.
Distinguish syntax that erases into existing operations from behavior needing a
new primitive, additional Core metadata, or changed rules for an existing node.
Explain why the current closed builtin resource relation does or does not need
to change. Do not add a Core operation merely to mirror a surface spelling.

Extend the Core small-step account for each required behavior. Define the
configuration components, values, ownership and access invariants, and terminal
outcomes needed by the admitted fragment. Identify compile-time facts that erase
and runtime state that remains; do not assume all borrowed access needs runtime
tracking. Cover these transition questions:

| Behavior | Required operational account |
| --- | --- |
| Establishment | Order and scope of initialization and operand evaluation, partial acquisition, publication of authority, and entry into the body. |
| Foreign invocation | Argument preparation, the contracted host interaction, returned values or failure, and any committed external effects. State the host relation's assumptions rather than model arbitrary C execution as verified Ash. |
| Storage and access | Allocation and object initialization, aliasing, reads, writes, retained access, view creation, invalidation, copying, and capacity failure. |
| Interpretation | Exact instance selection, source-handler precedence, provider interpretation, and which interpretation context executes provider operations and completion. |
| Control | Capture and resume of owners and access obligations, checked discard, nested scopes, and required completion that cannot be skipped. |
| Completion | Normal return, owned abandonment, release order, and failures that consume an owner versus failures that leave it live. Distinguish source completion from internal host teardown. |

Use one-step rules with explained configuration and side conditions, following
AD-0004 and the [formal-notation guide](../project/notation.md). State a proposed
change in evaluation order or observation explicitly. Reused transitions should
be identified as reused; candidate semantics must not arise solely from a host
adapter's implementation or a test's expected output.

Derive representative traces for both experiments and their shared cases. The
checker must establish the invariants those transitions require. Verification
must cover preservation and progress for the admitted fragment under its stated
foreign assumptions, source-to-Core correspondence, and agreement between the
operational account and the experimental machine. Negative source cases should
reject before invalid native access. Existing transforms must preserve the new
facts and independently validate their results.

The candidate delta should identify the affected specification chapters:
[lexical structure](../../spec/lexical-structure.md),
[syntax](../../spec/syntax.md), [name resolution](../../spec/name-resolution.md),
[static semantics](../../spec/static-semantics.md),
[elaboration](../../spec/elaboration.md), and
[dynamic semantics](../../spec/dynamic-semantics.md). Record unchanged areas
where reuse is established. These are proposed updates; the normative files
change only with the accepted product implementation and required evidence.

### Experiment A: SQLite provider

#### Scope and foreign contracts

Use SQLite's C interface for a synchronous connection with nested prepared
statements. Start with an in-memory database, then add a temporary file that is
closed and reopened to demonstrate external persistence. Use integers and
bytes for the initial data boundary. Record the minimal representation support
needed for SQL, paths, lengths, and results; prototype encodings are not a
decision about Ash strings or collections.

The initial operation set should cover open, prepare, bind, step, read a column,
reset or rebind, finalize, and close. Define the minimum supporting error and
metadata queries from the actual calls used. Pin an exact SQLite build when
the experiment runs. The following upstream contracts motivate cases:

| Contract | Pressure on the provider |
| --- | --- |
| [Initialization](https://www.sqlite.org/c3ref/initialize.html) may happen through ordinary entry calls; explicit shutdown requires all SQLite resources to have completed. | Distinguish host-wide initialization from each connection. Imports remain passive; one connection must not claim authority to shut down another. |
| [Opening](https://www.sqlite.org/c3ref/open.html) may produce a connection handle even when it reports failure. | Dispose of partial acquisition before returning an Ash failure; publish authority only after successful establishment. |
| [Binding](https://www.sqlite.org/c3ref/bind_blob.html) distinguishes a copy made before return from storage retained until rebinding or finalization. Reset does not clear bindings. | Express temporary and retained access separately, including the point at which access is relinquished. |
| [Column results](https://www.sqlite.org/c3ref/column_blob.html) require a valid row; returned byte views may be invalidated by stepping, resetting, finalizing, or conversion. | Relate views to an access interval or protocol state, not merely to a live statement. Distinguish empty bytes, SQL null, and allocation failure. |
| [Finalization](https://www.sqlite.org/c3ref/finalize.html) destroys the statement and may report its preceding evaluation error. | Separate resource consumption from the reported outcome; an error does not always mean the owner remains live. |
| [Close](https://www.sqlite.org/c3ref/close.html) can refuse while statements remain; deferred close has different destruction timing. | Establish dependent completion order and preserve the native postcondition on failure. Do not hide a failed order by silently selecting deferred destruction. |

For SQLite's internal allocations, initially use its own allocation discipline.
Model the Ash-visible ownership and release contract without claiming that all
foreign storage belongs to an Ash arena. Allocator replacement is unnecessary
for the first comparison; investigate it only if a retained case requires it.

#### SQLite construction sequence

1. Inventory the selected foreign calls and their preconditions, ownership,
   postconditions, error results, and invalidation behavior. Implement a narrow
   host adapter and observations for real acquisition and release. Distinguish
   injected failures from failures observed in the native library.
2. Run a complete connection/statement program with copied inputs and outputs.
   Retain acquisition, typed requests, interpretation, and completion in the
   candidate provider description. A query hardcoded into a native builtin is
   only an adapter smoke test.
3. Move the provider API and implementation into experimental library modules.
   Run an importing client and generic helper, then compare the three provider
   descriptions over the same checked behavior.
4. Add retained input bytes and scoped column views. Make valid use convenient
   and reject mutation, invalidation, escape, or release that violates the
   active contract. Compare borrowing with the copying baseline.
5. Exercise failure and control composition, then connect the retained-byte
   case to the arena experiment. State which memory guarantees come from each
   provider and which remain foreign assumptions.

Use a fixture that binds arena-backed bytes, evaluates a parameterized statement,
reads a scoped result view, copies the selected output, and completes statement,
connection, and arena in a valid order. Its copying variant should remain usable
when the borrowed variant's lifetime requirements cannot be satisfied.

#### Required SQLite cases

| Case | Required comparison or observation |
| --- | --- |
| SQL-01: lifecycle | Successful acquisition, query, copied result, statement finalization, and connection close; repeat with two live connections and through imports. |
| SQL-02: partial establishment | Failed open or prepare publishes no usable owner; any partial native state has an identified completion path. |
| SQL-03: retained input | Valid retained bytes survive every foreign use; premature mutation or arena completion rejects. Reset is not mistaken for release of retained input. |
| SQL-04: temporary output | A view is usable in its admitted interval; invalidating operations and hidden escaping captures reject. Copied output remains usable. |
| SQL-05: result and protocol | Row, completion, error, empty bytes, and null remain distinct. Checked preconditions or runtime validation guard column access and numeric conversions. |
| SQL-06: control and completion | Capture/resume preserves owners; owned discard completes dependent resources in order. Required outside completion and running cleanup cannot be skipped. |
| SQL-07: failure reporting | Body and completion failures retain their relationship and order; consumed and still-live native owners are distinguished. No blanket retry or cleanup-success claim. |
| SQL-08: library boundary | Public summaries preserve the contracts needed by a client that lacks provider bodies. Forged provider facts or mismatched instances reject. |
| SQL-09: external observation | A temporary file retains the expected data across close/reopen; the test owns and removes its files. Record native calls separately from model traces. |

### Experiment B: memory and region resource

#### Initial arena contract

Acquire an independently owned, fixed-capacity arena whose contents are opaque
storage. Typed allocation produces access to objects within it. The candidate
must define capacity units, metadata and alignment costs, initialization,
overflow checks, and the outcome of insufficient space. Failed allocation must
preserve existing objects and publish no partially initialized access.

The initial arena reclaims storage at owner completion. Binding or dropping an
alias does not relocate or individually free the object. Objects can share
references while valid; opacity prevents fabrication of access from arbitrary
addresses or integers. Typed operations expose contents without exposing raw
storage. Decide stable-address requirements for foreign access explicitly.

The owner remains scoped and cannot travel with returned objects. Independent
copies may escape. An inner arena may hold access to outer storage while that
owner remains live. Outer storage must not retain access to completed inner
storage. Begin with conservative rejection of such inward dependencies; compare
a scoped borrow only where its removal and captured uses can be established.

Complete actions that use arena storage before reclaiming that storage. Bulk
byte reclamation is not a substitute for required resource completion. First
test ordinary data and closures, then a separately tracked resource whose
cleanup accesses arena data. Do not assume every ordinary object has a
destructor or that the arena should discover destructors by scanning objects.

#### Memory construction sequence

1. Define the bounded storage model and typed allocation operations. Compare
   one arena with repeated scratch arenas; retain allocation and release
   observations and capacity-boundary failures.
2. Add shared immutable graphs, captured values, nested arenas, and generic
   helpers. Compare explicit allocation with the candidate default allocation
   context. Preserve ordinary binding and distinguish it from construction.
3. Add scoped shared and exclusive access where concrete mutations require it.
   Exercise aliases and captured control, including a handler trying to use
   conflicting access while a borrow remains captured.
4. Run the SQLite retained-input and output-view cases with this storage model.
   Measure copying, retained bytes, and author annotations against independent
   copies. Storage ownership and view validity must both be checked.
5. Compare earlier reclamation within the same nontransportable owner when the
   arena cases are understood. A reference-counted provider is one candidate;
   cyclic graphs and hidden roots supply pressure for tracing or another policy.
   Record cycle behavior and actual guarantees. A collector implementation
   requires a newly bounded comparison within this experiment before coding.

Ordinary immutable sharing must not require choosing a unique owner for every
source alias. A candidate may infer dependencies or use scoped access types;
any additional restriction needs a case that explains it. Cyclic data remains
in the reference corpus even if one candidate requires additional construction
support or cannot reclaim cycles early.

#### Required memory cases

| Case | Required comparison or observation |
| --- | --- |
| MEM-01: capacity | Exact-fit and insufficient-capacity allocations account for alignment and metadata, preserve earlier objects, and expose no partial value. |
| MEM-02: sharing | Repeated aliases, a persistent structure, and a shared cyclic graph remain valid for the owner's lifetime; bindings do not silently copy payloads. |
| MEM-03: nesting | An inner object can depend on outer storage; escaping inner access rejects through fields, helpers, evidence, and closures. Returning an outer projection can remain valid. |
| MEM-04: copying | Copy into independent storage preserves the stated value relationships. Define deep versus shallow copying, sharing, and cycle behavior for the admitted fragment. |
| MEM-05: borrowing | Compatible reads compose; conflicting mutation, invalidation, and release reject, including conflicts reached through aliases and effects. |
| MEM-06: control | Capture/resume retains storage and access obligations; owned abandonment performs required completion before release. Borrow checking cannot ignore suspended uses. |
| MEM-07: scope restriction | Returning an arena owner or an owner-plus-dependent package rejects. Keeping the owner alive through a source reference count is not an escape route. |
| MEM-08: bounded retention | Repeated completed scratch arenas release their storage. Distinguish payload, metadata, checker work, runtime bookkeeping, and native-library allocations. |
| MEM-09: policy comparison | For any later counting or tracing candidate, compare the same sharing, cycle, closure, failure, and completion cases. State roots, cycle limitations, and reclamation costs. |

### Type checking, inference, and provider verification

For each candidate, give types and a small-step account before claiming safety.
The target is compositional verification: checked clients satisfy the provider's
preconditions, and checked provider operations preserve storage validity,
access permissions, and completion obligations. State any assumptions on trusted
primitives and foreign code. Tests supplement this argument.

Use these questions to derive the typing rules rather than assuming a general
borrow checker or proof language:

| Information | Inference and explicit-contract comparison |
| --- | --- |
| Resource and allocation identity | Infer local relationships where possible; determine how generic signatures and module summaries preserve them. |
| Stored and callable dependencies | Propagate actual retained access through values, selected methods, and control; identify annotations needed when bodies are unavailable. |
| Effect and interpretation requirements | Infer outward rows and exact instances; explicitly describe primitive effects and required completion interpretation. |
| Access and invalidation | Compare inferred usage with declared read, write, retain, and invalidate contracts. Foreign bodies cannot supply source-based inference. |
| State transitions and failure | Specify which outcomes create, retain, or consume authority. Check branch joins and rollback of partial establishment. |
| Representation | Declare the foreign layout, encoding, width, alignment, and address requirements; check conversions and call-site compatibility. |
| Numeric and external conditions | Use runtime checks where values or foreign results decide validity. Determine whether checked results introduce typed evidence for later use. |
| Provider correctness | Identify checkable implementation obligations and explicit external assumptions. Ordinary interface evidence must not stand in for an arbitrary safety proof. |

Type checking must rule out the admitted fragment's invalid access and
completion patterns; it need not predict allocation success or external I/O
results. Runtime checks may establish facts consumed by checked code. Document
whether the checker infers them, requires annotations, or rejects an otherwise
safe program because its reasoning is incomplete.

Compare checking with provider bodies present and with only authenticated public
contracts. Include recursive and higher-order helpers within the admitted
fragment, branch-sensitive use, and malformed evidence. Establish preservation
of the candidate invariant and progress relative to explicit foreign contracts;
do not claim termination or eventual release of divergent programs.

Before a product proposal relies on a property, connect its source checking to
the retained typed representation and concrete operations. Check independent
validation and preservation across the existing transforms. Record finite
checker work and structured exhaustion, so a safety result does not depend on
an unbounded analysis or an unspecified runtime registry.

### Syntax and developer experience

Write complete examples for both library authors and callers. Every candidate
must show declaration, import, acquisition, provider state, operation coverage,
handler installation, invocation, error handling, and completion. Include a
generic helper and one diagnostic repair. Label candidate syntax explicitly.

Measure repeated declarations, required annotations, exposed lifetime or state
parameters, conversion code, and effort to locate a rejected dependency.
Compare the same behavior and information, not unequal examples with hidden
work inside native code. Explain which surface forms erase to ordinary library
definitions and which need a new checking or execution rule.
Include parse and resolution examples for each addition, paired with its Core
mapping and operational trace. Convenient syntax must preserve the behavior
established by the semantic comparison.

### Foreign-library development blueprint

Derive a worked blueprint from the SQLite implementation and revise it after
the memory interaction cases. It should let another author reproduce:

1. Inventory the foreign API, supported native versions, ABI, and initialization.
2. State ownership, retained access, invalidation, failure, and release contracts.
3. Define the Ash values, opaque access, effects, operations, and resource types.
4. Implement conversions and foreign calls behind the stated trusted boundary.
5. Assemble acquisition, handlers, dependencies, and completion into a provider.
6. Export contracts sufficient for independent client checking.
7. Build, link, import, test, diagnose, and update the binding reproducibly.

Every step should reference a real fixture or artifact. Distinguish generated
facts, author-supplied contracts, proved obligations, and assumed native behavior.
Record limitations. Validate transfer by applying the procedure to the arena's
native allocation boundary and by a walkthrough of one contrasting foreign API;
a second complete library binding is not required by this initial experiment.

### Tooling investigation

Keep an authoring log of repetition, errors, manual checks, and difficult
diagnoses. Derive tools from those observations:

| Developer activity | Candidate assistance and evidence of value |
| --- | --- |
| Bind symbols and representations | Generate mechanical signatures and check layouts; compare with hand-authored bindings. Missing semantic contracts remain visible. |
| Describe provider contracts | Check completeness and consistency; trace retained access or invalidation errors to the responsible declaration. |
| Assemble a provider | Generate justified forwarding or lifecycle boilerplate; verify generated code through the same checking boundary. |
| Build and link | Record native inputs and configurations; diagnose missing symbols and incompatible representations with a reproducible fixture. |
| Investigate behavior | Observe acquisition, access, copying, and release; inject failures and retain minimal counterexamples. |
| Maintain a binding | Detect changed foreign signatures or build assumptions and identify contracts requiring review. |

For each recommendation state the observed problem, minimal useful tool,
remaining author judgment, and measured reduction in work or ambiguity.
Separate syntax problems from tooling problems. A small experimental utility
is sufficient to test a recommendation; a general package manager, binding
generator, or IDE is not a prerequisite.

## Stages, deliverables, and completion

| Stage | Work and exit evidence |
| --- | --- |
| 1. Establish cases | Pin the source and native inputs, inventory contracts, and write paired valid/invalid scenarios. Identify representation gaps and the initial surface-to-Core semantic questions. |
| 2. Build independent baselines | Run a copying SQLite bridge and a fixed arena with typed allocation. Separate native behavior observations from proposed Ash behavior. |
| 3. Check candidate descriptions | Define candidate grammar, resolution, typing, Core mapping, and small-step rules. Execute checked examples, compare syntax and inference, and cross imports and generic helpers. |
| 4. Compose memory and foreign access | Run retained bytes, temporary views, copying, borrowing, and continuation/completion cases through both providers. Resolve counterexamples or record bounded rejection. |
| 5. Evaluate reuse | Compare memory policies only where needed for the intended claim; complete the blueprint, tooling trials, cost report, and language-versus-library analysis. |
| 6. Prepare adoption | Retain the supported surface syntax and Core operational delta, specification obligations, library APIs, architectural choices, remaining gaps, and proposed product checkpoints. |

The first two baselines can progress independently after the shared case
inventory. Their integration determines later typing and implementation work.
Revise the next bounded slice when evidence changes the question. These stages
are experiment guidance, not an accepted product implementation plan.

Retain an evidence report with reproducible commands, results for each named
case, counterexamples, checking limitations, costs, and unresolved assumptions.
Candidate surface syntax and its Core mapping, the operational account, the
authoring blueprint, and tooling recommendations are required outputs even if
the semantic candidate fails. Record negative findings as experiment results
rather than weakening cases until a candidate passes.

An experiment is complete when it answers its bounded questions with this
evidence. A successful candidate additionally admits the required useful cases,
rejects the prohibited cases, connects its safety argument to execution, and
has a credible implementation and library-authoring path. Partial success must
name the supported fragment; it does not establish a general FFI or memory model.

## Path into Ash and its standard library

Design the experiments for eventual adoption by identifying the smallest
language mechanism that supports ordinary library implementations of both
cases. Use this allocation of responsibility as a hypothesis to test:

| Layer | Candidate responsibility |
| --- | --- |
| Language and checking | Scoped authority, dependencies, access rules, effects, provider installation, and the contracts that public signatures must preserve. |
| Trusted runtime and foreign boundary | Native calls, representation checks, primitive storage operations, and execution support that cannot be ordinary Ash code. |
| Standard library | Reusable resource/provider definitions, scoped arenas, typed views, conversions, and completion/reporting helpers supported by accepted language rules. |
| SQLite library | SQLite operations, protocol and error mapping, native contracts, and database-specific policy. Evaluate inclusion as an optional standard-library component or separately distributed library. |
| Developer tools | Binding assistance, build integration, diagnostics, and validation utilities justified by the experiments. |

Standard-library authors should use the proposed public mechanisms. Each
required compiler privilege needs a named safety reason and a negative test.
An implementation that requires a new compiler resource kind for every library
has not established reusable library-defined provision. Conversely, avoiding a
primitive is not a success if it hides unchecked authority in generated code.

The adoption report must include:

- the semantic delta from the current specification, including any changes to
  ordinary allocation, rank-1 boundaries, effects, or module summaries;
- proposed surface grammar and binding rules, elaboration for each addition,
  and Core configuration and transition updates with representative derivations;
- a source-to-Core account, validation and transform obligations, runtime
  invariants, and preservation of current Pure and Effect behavior;
- public library examples, documented costs and failures, compatibility and
  migration cases, and reproducible native build requirements;
- a simplification audit against the existing cell and native-buffer mechanisms,
  with evidence before proposing their replacement;
- supported targets and foreign versions, explicit trust assumptions, and gaps
  that prevent broader claims.

Then follow the [artifact guide](../project/artifacts.md): semantic changes need
an accepted change proposal; converged non-language architecture needs a
decision. Authorized tasks own detailed product execution plans. Implement each
coherent product checkpoint with parsing and resolution cases, typing and Core
validation tests, operational traces, applicable proof or correspondence
evidence, specification and library documentation, and full verification.
Any changed surface syntax and Core operational semantics must be specified in
the same product checkpoint as their implementation. Integrating that accepted
product checkpoint into `main` establishes current Ash behavior. Retaining a
bounded experiment is a separate action and grants no such authority.

Possible checkpoints are a checked foreign boundary and scoped provision,
scoped arena allocation and access, and library APIs with developer tooling.
Their order and split depend on the demonstrated dependencies; every retained
checkpoint must be usable and preserve its complete safety contract. A SQLite
example should continue to exercise the language/standard-library combination
after adoption, so the reusable mechanism is tested by an external library.

Bounded scope does not require a disposable implementation. Retain useful
extensions to existing Ash on the experiment branch with reproducible inputs,
comparison results, and stated limitations. Successful code may become the basis
of the product implementation after it satisfies the accepted contract and
product checks. Discard or replace failed candidate machinery when justified by
the findings; preserve its useful counterexamples. Retention alone establishes
neither current language semantics nor production authority.

Do not merge unsuccessful candidate machinery into `main`. A successful
experiment proceeds through the adoption work above using the useful retained
implementation. Failure does not require deleting its branch or evidence.

On 2026-10-08 the user separately authorized consolidating the completed,
verified common, SQLite and selected arena deliveries and retaining them in
`main`, conditional on combined verification. This is an explicit experimental
retention checkpoint, not product adoption. Keep the experimental entry points,
fixtures, semantic delta, trusted foreign assumptions and limitations identified;
leave `spec/` unchanged. The accepted proposal, architectural decisions and
product correspondence work described above remain required for adoption.
Exclude unsuccessful optimization candidates and the paused Lean and Core
one-shot work from that integration. Preserve their histories and unrelated
working drafts during cleanup. The [execution record](provider-experiments/execution.md)
records completed capabilities and the actual integration and verification
receipts; this authorization does not imply that the final gate has passed.

## Open questions

- What minimum rule makes library-defined acquisition authoritative without
  turning ordinary interface evidence into unchecked resource authority?
- Which surface additions are necessary, and what minimum Core configuration
  and transition changes implement them without duplicating existing behavior?
- Can the provider's supplied body remain expressible within current rank-1
  source positions, or does a scoped binder need a new typing rule?
- Which dependencies and usage relationships can inference recover across
  helpers and modules, and which public contracts need explicit expression?
- What distinguishes owner lifetime from a shorter access interval or protocol
  state without burdening every ordinary alias?
- How can source handler overrides preserve the access contracts of a storage
  provider, including while conflicting authority is captured?
- Which allocation-context and result-copying rules keep native Ash code
  convenient while exposing costs and failure behavior?
- What provider properties can checking establish directly, what evidence needs
  a separate checker, and what is necessarily assumed about foreign primitives?
- What is the smallest public language and runtime boundary that lets both
  experiments become maintained libraries without case-specific compiler paths?
