# DN-0046: Agent Semantic Exploration and Feedback

- ID: `DN-0046`
- Status: exploring
- Related: [DN-0045](DN-0045-native-compilation-and-interactive-execution.md),
  [DN-0029](DN-0029-human-diagnostic-presentation.md),
  [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0010](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md)

> This working design note is informative. It defines no current Ash semantics,
> accepts no architecture, and authorizes no implementation or prototype. The
> candidate interface, analysis and experiments remain open to revision.

## Question

How should Ash let an AI programmer navigate checked source, ask semantic
questions and run small experiments without reconstructing compiler facts from
text searches or diagnostic prose? Can planned LSP support, semantic search and
REPL-like experiments share one view of the program while preserving the
compiler's checking, execution and authority boundaries?

## Context

Ash is intended for human and AI programmers. The candidate agent interface
complements planned LSP support: agents could consume definition, reference,
type and diagnostic information alongside broader questions and experiments.
These services and an agent protocol are proposed, not current Ash tooling.

[AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md) establishes
resolution before checking, binder identities distinct from spellings, and
structured outcomes with causal source relationships. These support semantic
navigation without guaranteeing identity stability across edited snapshots.

[AD-0010](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md)
already separates human presentation from locale-independent, schema-versioned
JSON diagnostics. Semantic reasons, named facts and label relationships belong
to compiler phases. An agent adapter should consume those facts rather than
parse localized prose or recreate a second typechecker.

The [current specification](../../spec/README.md) describes passive modules,
static import and evidence selection, and lexical effect interpretation. Modules
have no runtime initialization or runtime value. An exploration session therefore
does not inherit a language-defined mutable module world. Resource activation,
continuation capture and cleanup remain execution concerns, not navigation state.

### Dependency on native compilation work

[DN-0045](DN-0045-native-compilation-and-interactive-execution.md) owns the
exploration of shared checking, lowering, source-snapshot and execution contracts
for interpreted and native paths. This note depends on those contracts: an agent
adapter must ask the same compiler services about the same inputs and must not
create separate development semantics, lowering rules or runtime guarantees.

That dependency does not require completed optimized AOT or JIT before any
semantic exploration is useful. Navigation, checked queries and bounded runs
could first use the current interpreter. Later execution paths could serve the
same requests when their supported fragment and verification justify it. Backend
choice and native compilation order remain DN-0045 questions.

### Current compiler building blocks

The compiler already supplies parts of this workflow. These are implementation
facts, not an existing workspace-session or semantic-query contract:

- The [module loader](../../src/module.rs) constructs a dependency-ordered graph
  from source paths. It does not provide versioned unsaved overlays or a
  content-version identity for an agent session.
- [Resolved occurrences and checked modules](../../src/resolved.rs) retain
  declaration identities, source origins, checked global schemes, selected
  occurrence evidence and dependency summaries. They provide inputs for
  navigation and signature queries, not a bounded public search index.
- The [driver's `run_path`](../../src/driver.rs) loads, checks, links, validates
  and evaluates a modular graph in one operation. Its success returns an
  observation, not a reusable checked workspace that clients can query before
  choosing whether to execute.
- [Diagnostics](../../src/diagnostic.rs) and their
  [presentation](../../src/presentation.rs) already provide structured reasons,
  facts and causal labels. They support failure explanations; they do not expose
  every successful type, evidence or dependency derivation.
- The [elaborator](../../src/elaborate.rs) exposes standalone expression
  synthesis and checking, returning a `TypedNode` with type and effects. Its
  admitted context does not reconstruct a linked module program or an arbitrary
  executable lexical environment. Complete-entry probes therefore remain a
  smaller proposed service boundary than general evaluation at a source position.

A candidate preparation service would retain or project compiler-owned results
before execution, together with their source and configuration inputs. Linking
currently consumes checked modules, so reuse needs an explicit ownership and
projection design. The query adapter would inspect selected evidence rather than
select implementations again. The current
[module publication and linking rules](../../spec/static-semantics.md#globals-and-modules)
remain authoritative: a failed module publishes neither a checked module nor its
checked summary, and final Core synthesis consumes authenticated evidence.

[AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md) defers a separate
fully typed surface tree until a consumer justifies it. The initial candidate is
source-associated fact tables for the queries being tested, published by the
owning compiler phases. General expression-type inspection would require retaining
additional facts; neither spans nor Core node IDs alone establish a universal
source-occurrence identity. This note does not yet justify duplicating the whole
typed tree.

## Constraints

- Compiler-owned resolution, checking and validation remain authoritative. LSP,
  semantic search and experiment adapters do not own language rules.
- A response identifies the source snapshot and relevant compiler configuration
  that produced it. Dependency content and unsaved edits belong to that snapshot.
- A query distinguishes checked facts, conservative possibilities, incomplete
  analysis and observations from one execution. Unknown is not an empty result.
- Answers for a chosen lexical context preserve import, opacity and access rules.
  Navigation to a defining identity does not grant that context permission to use
  hidden constructors or private declarations.
- Output is compact and machine-readable, with source relationships and explicit
  limits. Human rendering can use the same facts without becoming the protocol.
- Independent questions may be batched against one snapshot. Batching does not
  turn dependent executions or edits into simultaneous operations.
- A small experiment checks its complete entry and lexical authority. It cannot
  borrow a resume capability, resource handle or foreign authority from a tool.
- Compiler caches and program state have separate lifetimes. A cached checked
  module does not keep its previous resource activations alive.
- No source edit or semantic query automatically replays effectful execution.
  Runtime failures and cleanup outcomes retain their original guarantees.

## Candidate directions

| Direction | Benefit | Limitation to test |
| --- | --- | --- |
| LSP alone | Familiar navigation. | Broader queries need extensions. |
| Separate tools | Narrow adapters. | Client reconciles snapshots and state. |
| Integrated session | Shared snapshot. | Coordination must justify its cost. |

Separate LSP, search and execution tools offer a baseline if explicit snapshot
references suffice. The working direction is an integrated session using shared
services, with additional compiler-owned queries where LSP does not fit. The
session coordinates requests without requiring persistent execution state. New
query contracts must justify their cost without creating a second compiler.

### Semantic search

Semantic search, or semantic grep, would select checked relationships rather
than matching spellings alone. Useful questions to investigate include:

- Which occurrences refer to one resolved declaration across aliases and
  re-exports, and which similarly spelled names refer to different declarations?
- Which checked functions expose a given result type, nominal identity, interface
  requirement or exact effect instance in their signatures?
- Where are exact interface methods selected or forwarded as ordinary evidence
  functions, and which declaration supplied the selected evidence?
- Which known functions or caller paths may request an operation, including
  requests handled internally and requests made by clauses outside their handler?
- Which checked dependencies connect a stored value, closure or operation to a
  scoped resource, and which source positions explain a rejected escape or discard?

The first questions can expose verified resolution and typing facts. Control
questions need a stated analysis scope and conservative results. Current
[capture checking](../../spec/static-semantics.md#effects) retains summaries for
known functions, closures, recursion and imports; higher-order callees and open
rows can remain uncertain. Generic identities may coincide after specialization.
An empty outward row does not imply absence of internally handled requests.

Existing summaries are evidence for possible query services, not a ready public
query contract. A search must report whether it inspected checked bodies,
dependency summaries or an incomplete source region. A list of possible requests
is not a proof that each runs, nor is an unobserved path proof of impossibility.

### Concrete workflow: repair an escaping callback

Consider the task: return a callback that remembers the integer read from a
temporary cell. The requirement is to remember the copied value, so moving the
read before scope exit preserves the intended behavior. A callback that must read
changing live state would require a different design.

Current [resource rules](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
track stored dependencies separately from visible types and outward effect rows.
An identity-free function type does not erase a retained resource dependency.
Copied integers and closures retaining only those copies may escape; the
[execution rules](../../spec/dynamic-semantics.md#scoped-cell-execution) let such
closures run after the cell payload has been released.

The proposed agent workflow is:

1. **Establish snapshot S0 and check it.** Admit the source, dependencies, root
   configuration and relevant compiler configuration. Use a rejected candidate
   whose callback contains an internally handled cell read: its outward type can
   be `Unit -> Int`, but its stored resource dependency still rejects escape with
   `type.resource-escape`. A direct read with an incompatible outward row may
   fail ordinary typing first; the workflow must preserve diagnostic precedence.
2. **Explore the relevant relationships.** Follow the diagnostic's labelled
   occurrences to the cell acquisition, callback and helper declarations. Find
   references by resolved identity across aliases, then inspect relevant caller
   signatures. Report completed resolution facts separately from checked facts
   unavailable because the module failed.
3. **Explain the failure.** Expose the compiler's available causal labels:
   returned closure, retained cell access or evidence, and the acquisition that
   closes before the closure is used. A richer explanation query could connect
   those facts without reconstructing resource rules in the adapter. Unknown
   relevant higher-order behavior remains unknown.
4. **Create source variant S1.** Read the integer while the cell scope is live,
   then return a closure retaining only that copied integer. S1 has its own
   snapshot identity; S0's diagnostic remains historical evidence.
5. **Check and run a complete probe.** Construct an entry that creates the callback,
   leaves the resource scope and then invokes it. Check, link and independently
   validate that program before running it. A callback that returns its saved
   integer should return `41` for an initializer of `41`; another initializer
   should produce its corresponding value. These are proposed probe expectations,
   not observations produced by a current agent service.
6. **Retain the evidence and check affected callers.** Keep the original rejected
   capture and the accepted copied-value case as source regressions. Each probe
   starts from explicit fresh state; compiler caches may remain warm. A query
   result from S0 cannot silently serve as evidence about S1.

Existing [typing cases](../../tests/resource_scope_typing.rs),
`identity_free_closure_cannot_escape_its_resource_owner` and
`copied_integer_and_constant_closure_have_no_stored_resource_dependency`, anchor
the rejected and accepted cases. The
[runtime case](../../tests/resource_scope_runtime.rs)
`copied_closure_runs_after_payload_release` invokes a copied-value closure after
scope exit and expects `42` from a saved `41` plus one. These fixtures support the
language behavior; they do not demonstrate the proposed session, query or probe
construction services.

### Shared compiler services

The candidate session coordinates these services. Planned LSP support, agent
requests and human presentation would consume the same compiler-owned results.
The service boundaries do not decide whether additional requests travel through
LSP extensions or a separate agent adapter.

| Service | Required result |
| --- | --- |
| Snapshots and dependencies | Source content, unsaved variants, imports and configuration, with versions, result freshness and dependency invalidation. |
| Preparation and checking | Resolution, checking, evidence selection, linking and independent Core validation, with completed stages and reusable results. |
| Navigation and semantic search | Definitions, references, checked signatures, selected evidence and bounded predicates over resolved identities, with coverage and pagination. |
| Explanations | Compiler-owned diagnostic reasons and source causes; later, justified explanations of successful typing, evidence and dependency choices. |
| Probe preparation | A complete derived entry or source variant with inputs and fixtures, preserving lexical access, expected typing, evidence, handler context and resource scope. |
| Execution and observation | A run against validated Core, explicit initial state and limits, with its execution path, values, failures and completion status; interpreted first and native when justified by DN-0045. |

A candidate response contract identifies its snapshot, configuration, completed
analysis stage and covered source or dependencies. It separates checked facts,
conservative possibilities, incomplete analysis and observations. Bounds,
truncation and a deliberate continuation mechanism prevent a partial result from
looking exhaustive. Execution results additionally identify the entry and inputs.

A failed snapshot may still expose completed resolution information and its
diagnostics. It cannot expose a failed module as successfully checked or publish
partially emitted Core as executable. Signature effect rows, outward computation
rows, conservative possible requests and observed requests need separate query
meanings; none substitutes for the others.

### Smallest useful first scope

The first candidate scope should exercise one explicit source snapshot and a
complete checked entry through the current interpreter:

1. Admit the module graph and source/configuration inputs under a snapshot identity.
2. Expose declaration/reference navigation, checked global schemes, selected
   occurrence evidence and existing structured diagnostics.
3. Admit an edited source variant as another snapshot and check its complete entry.
4. Execute that validated entry from fresh state and attach its observation to the
   matching snapshot, entry and inputs.

This scope tests the repair workflow without requiring optimized AOT, JIT, a CPS
decision, persistent runtime values or general evaluation at a source location.
Compiler-owned expression-type projections, richer dependency explanations and
conservative control queries are later extensions to measure individually. Cache
reuse can then be measured against the same workflow without changing its results.

Initially, a probe is an ordinary complete entry supplied in a source variant.
Selection of a location alone does not establish an executable lexical
environment. A generated wrapper must preserve expected typing, evidence
selection and scope; adding a function can introduce a resume barrier. General
lexical probe construction, expression-evaluation syntax and supported source
transformations remain open.

This is a candidate comparison scope, not implementation authorization. Its value
is testable: can an agent follow the cause, make a correct source variant and
obtain repeatable feedback with less context reconstruction and fewer round trips?

### Freshness, output and state

A session should distinguish source versions, dependency inputs, analysis results
and execution observations. After an edit, a client may inspect an older result
as history, but the adapter must not silently present it as current. Returned
identities and source spans need an explicit relationship to their snapshot;
cross-snapshot correspondence remains a question rather than an assumed property.

Batched navigation and semantic questions can reduce tool round trips. Results
should state limits and incomplete regions and permit deliberate continuation
without flooding the agent with whole files or repeated diagnostic catalogues.
An experiment result should identify its entry, inputs, execution path and
completion status, with values, failures and cleanup observations kept distinct.

A long-lived compiler service may reuse parsed sources, checked summaries and
compiled code. Fresh program runs can still start with separate execution state.
A future persistent REPL world would need explicit creation, reset and disposal,
including retained values and resource obligations. Keeping compiler caches warm
does not require that additional world model. Independent isolated runs offer a
baseline for repeatable experiments and parallel agent work.

### Effect and resource authority

An experiment uses authority established by its checked source. Current
[effect execution](../../spec/dynamic-semantics.md#effect-handlers-and-completion)
selects the nearest exact accepting interpretation and preserves the clause's
surrounding control. The adapter cannot silently install ambient handlers,
replace effect results with mocks or transfer live scope owners between runs.

[Resource scopes](../../spec/dynamic-semantics.md#scoped-cell-execution) create
fresh activations and move ownership through capture and resume. Their handles
are not durable session identifiers. [Cleanup](../../spec/dynamic-semantics.md#scoped-cleanup-actions)
distinguishes normal completion, owned abandonment, running actions and internal
termination. Stopping a probe is not evidence that source cleanup completed.

Foreign interaction under the work explored by
[DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md) adds host inputs and
effects that resetting Ash state may not undo. A probe must make those inputs and
selected authority explicit. Automatic re-execution after an edit could repeat
external mutations; static feedback and requested execution should remain separate.
This note adds no isolation guarantee for arbitrary native code or foreign callbacks.

## Evidence and experiments

[SWE-agent](https://arxiv.org/html/2405.15793v3), section 5.1 and Table 3, compared
agent interfaces on 300 SWE-bench Lite bug-fix tasks using GPT-4 Turbo. Syntax
feedback, summarized search and bounded observations improved results in that
setting. This supports testing concise semantic responses and useful correction
feedback. It does not establish an Ash query design, a universal latency target,
or a benefit from JIT or persistent REPL state. These remain hypotheses for Ash.

A future authorized comparison should give all three candidates the same checked
source snapshots, services and task budget. Tasks should cover aliased identities,
selected evidence, an internally handled request, an uncertain higher-order call,
a resource escape and a small executable counterexample. Include an edit between
queries, a dependency change and an execution that cannot promise completed cleanup.

Compare correct answers and honest uncertainty, source freshness, diagnostic
causes, agent round trips, output size and time to a useful correction. Count cold
and cached checking separately from execution. Repeat observations from explicit
initial state, and compare supported interpreted and native runs against DN-0045's
common behavior contract when both paths exist. Faster results do not excuse
different accepted source or hidden authority.

If a later authorization permits a bounded prototype, it should test whether the
integrated session reduces reconciliation and round trips while preserving those
facts. Retain the comparison data, query counterexamples and contracts supported
by the evidence. Discard adapters that duplicate semantic rules, require stale
state or add coordination without demonstrated benefit. Prototype code remains
disposable design evidence until an architectural decision and task authorize
product retention. This note grants no such authorization.

## Open questions

- Which questions can use ordinary LSP requests, and which justify additional
  compiler-owned semantic queries?
- What snapshot identity covers unsaved files, dependency summaries and compiler
  configuration without requiring cross-edit binder stability?
- How should partial checking and conservative control summaries expose useful
  facts while making uncertainty unavoidable to the client?
- Which lexical probe contexts can be reconstructed without changing typing,
  evidence, resume barriers or resource authority?
- Do agent tasks need persistent values, or do cached compilation and fresh runs
  provide sufficient exploration? How would a retained world close its owners?
- What response bounds and batching choices improve task success for humans and
  agents using the same underlying services?
