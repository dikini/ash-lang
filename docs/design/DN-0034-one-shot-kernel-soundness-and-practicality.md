# DN-0034: Verification Foundation for Ash Semantics and Implementation

- ID: `DN-0034`
- Status: evaluating
- Related: [DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md),
  [DN-0031](DN-0031-resource-composition-concept-map.md),
  [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md)

> This note assesses a verification direction. It defines no current Ash
> semantics, accepts no architecture, and authorizes no implementation or new
> project policy. Tooling and workflow recommendations below remain candidates.

## Question

How can the one-shot formalization become a maintainable foundation for proving
both the soundness of existing and proposed Ash operational semantics and the
correctness of their implementation, while language development continues?

The one-shot fragment is an intended base for extension. The goal is broader
than publishing proofs or extracting a standalone continuation checker. It is
to connect specified behavior, formal semantics, safety properties, and actual
implementation behavior, then preserve those connections through changes.

## Context and evidence boundary

The [specification](../../spec/README.md) defines current Ash. Its
[handler and completion rules](../../spec/dynamic-semantics.md#effect-handlers-and-completion)
and [static semantics](../../spec/static-semantics.md) govern exact dispatch,
one-shot non-escape, checked discard, resource support, and cleanup obligations.
The [Core decision](../decisions/AD-0007-typed-core-dialects.md) requires typed
structure and independent validation; the
[evaluator decision](../decisions/AD-0008-explicit-evaluator-machine.md) supplies
the explicit-machine boundary. DN-0033 supplies candidate semantics and proof
experiments, with its [evidence register](direct-effects/one-shot/README.md) and
[mathematical companion](direct-effects/one-shot/KERNEL.md).

As inspected on 2026-09-30, the current annotated-state M0–M4 boundary includes
structural resource admission, all 32 transition families, initial admission,
constructive preservation, progress under the admitted builtin-signature law,
and bounded execution from an admitted program. The operative statements are
[initial admission](direct-effects/one-shot/SourceScheduledInitialAdmission.lean)
and [M4](direct-effects/one-shot/SourceScheduledM4.lean). Earlier sections of the
large evidence documents describe narrower or superseded proof boundaries;
counts of historical open items do not measure current completion.

These results require the existing structural certificates. They establish
source-selected preserving execution, not preservation for arbitrary raw
annotation choices. Initial admission means experimental calculus input, not
an automatic translation of every accepted Ash program. Finite-prefix
construction does not prove termination or eventual release during divergence.

Core alignment is active separately on `codex/core-alignment`. This assessment
uses its WIP snapshot `b940171`, including TASK-0032 at
`docs/tasks/TASK-0032-core-one-shot-alignment.md` and comparison evidence at
`docs/design/direct-effects/one-shot/CORE-ALIGNMENT.md` on that branch. These
records are branch-local evidence, not integrated product truth. They target
static admission from independently validated Core and execution correspondence
for a declared monomorphic fragment containing handlers, requests, sequencing,
resume, discard, cells, cleanup, and supporting ordinary constructs.

The recorded comparison has already produced useful results: the direct versus
bound resume-operand discrepancy led to CP-0021 and locally verified
regressions; constructing full-fixture admission exposed continuation-interface
coherence and declaration-recipe gaps in the proof model. Exported Core,
an independent Core machine, value relations, and selected transition proofs
provide bridge components. General admission, configuration simulation, and the
integrated correspondence theorem remain unfinished. These findings support
continued investment without establishing correctness for all implemented Ash.

## Assessment

### Soundness, correctness, and intended behavior

Semantic soundness concerns the formal language: admitted programs preserve
types, interpretation requirements, ownership and completion obligations, and
can advance or reach a permitted outcome. The theorem must state its admission
rules and environmental assumptions. Safety does not imply termination.

Implementation correctness concerns correspondence with those semantics.
Compilation must preserve intended behavior, and implementation transitions
must have justified semantic matches. Administrative steps need a progress
argument when they match no semantic step. Observations must include relevant
results, effects, ownership events, failures, and divergence; the direction and
strength of the relation must be explicit.

Correctness of a proposed semantic change also needs stated intended laws and
observations. A sound calculus can specify an unwanted cleanup order. Examples,
observable properties, and specification review establish intent; safety and
correspondence proofs answer different questions.

The eventual chain includes surface elaboration, validated Core, execution,
and external boundaries. A theorem about a Lean model of Core execution still
needs an explicit justification for its connection to the Rust implementation.
Exported inputs and matching traces are useful evidence but do not prove that
connection for every program or execution.

### Practical value and maintenance risk

The formalization addresses actual Ash interactions: requests capture mixed
handler, resource, and unfinished clause control. Shared ownership and
completion invariants explain why a local result type or effect row alone does
not suffice. Current comparison findings show practical value through defect
classification, semantic clarification, and regression cases.

The alignment effort turns that value into a concrete verification programme.
Its admission and simulation boundaries are more useful near-term priorities
than speculative standalone analyzers. For example,
[Usage.lean](direct-effects/one-shot/Usage.lean) checks local consumption under
supplied rights and explicitly excludes capture compatibility and resource-safe
disposal; it is not already an Ash safety checker.

Maintainability remains an open assessment. File count, theorem count, and
completed-case percentages do not establish usability or predict maintenance
cost. Useful evidence is whether contributors can find assumptions, extend a
construct, repair affected proofs, and reproduce a discrepancy without
reconstructing the entire experiment history.

## Parallel development and extension pressure

Language features, proof coverage, principled FFI, surface DX, and generated
property tests can advance concurrently. Their shared coordination boundary is
the behavior and invariants changed by each increment, together with the exact
revision and fragment to which a proof or comparison applies.

| Effort | Connection to the verification foundation |
| --- | --- |
| New Ash features | State the semantic delta and changed invariants; retain positive and negative evidence and mark correspondence coverage. |
| Broader Lean coverage | Extend admission, execution and correspondence together where possible; distinguish model extension from coverage of implemented behavior. |
| Multishot and escaping continuations | Revisit duplication, lifetime, transfer and completion assumptions explicitly. Reuse one-shot results only where their premises still hold. |
| Discard and abandonment extensions | Preserve structural closing order, surviving interpreter requirements and running completion protection. Current one-shot discard already provides a base. |
| Principled FFI | Express provider contracts using resources and effects where sufficient; state foreign lifetime, aliasing, callback, failure and concurrency assumptions. Distinguish assumed contracts from verified foreign implementations. |
| Surface DX | Relate convenient syntax and elaboration to Core behavior; test diagnostics and rejection as well as successful execution. |
| Tuned property tests | Use laws, model/implementation agreement and expected rejection as explicit oracles; retain seeds and minimized counterexamples. |

The candidate workflow permits features to advance before complete proof
coverage, with the gap recorded and owned. It does not weaken existing product
verification or mark an unsupported feature verified. A change to a shared
verified invariant needs an assessment of affected guarantees. Independent
changes should not wait for unrelated proofs or a full-language checkpoint.

## Tooling priorities

Build on existing checks and alignment components. Each additional tool should
remove a demonstrated repeated cost or close a specific evidence gap.

| Capability | Useful result and boundary |
| --- | --- |
| Reproducible proof checks | Pin the toolchain, check affected dependency closures, audit theorem dependencies and axioms, and retain source revision and build provenance. Cache reuse must authenticate inputs. |
| Verified-coverage navigation | Connect constructs and interactions to theorem entry points, implementation boundaries, assumptions, exclusions and regressions. Generate dependency details from code where possible. |
| Core export and execution comparison | Reuse actual validated Core and explicit observations to expose discrepancies. Keep exporter, model and observer limitations visible. |
| Generation and shrinking | Generate admitted cases and targeted invalid cases, compare against explicit oracles, and shrink while preserving the relevant typing or control interaction. |
| Change-impact assistance | Identify affected imports, theorem interfaces, rules and fixtures; begin with compiler dependencies and maintained links before building a separate index. |

Property generation can be biased by coverage, rare control interactions, or
past failures. Compare tuning strategies using useful discrepancies found,
reproducibility, and shrinking quality. Coverage is an exploration signal, not
a correctness oracle. Generated passing tests supplement proofs.

Standalone analyzers, dashboards, automatic proof adaptation, and skeleton
proof generation remain possible later tools. They need a demonstrated user
workflow and trustworthy input boundary. They are not prerequisites for
continuing Core alignment or language development.

## Documentation and project artifacts

Use the existing [artifact lifecycle](../project/artifacts.md) and
[documentation policy](../project/documentation.md). The candidate below adds
information at its natural owner rather than a second approval pipeline.

| Information needed | Smallest suitable artifact |
| --- | --- |
| Current language behavior | Existing `spec/` chapters; formal evidence links must not replace their authority. |
| Proposed semantic delta and required evidence | Existing change proposal, including affected invariants and verification coverage when relevant. |
| Uncertain rules or proof experiments | A design note with a bounded question, comparison criteria and retention conditions. |
| Accepted verification architecture or trusted boundary | An architectural decision once exploration converges. Routine lemma and test changes need no new decision. |
| Work ownership, dependencies and remaining gaps | Existing active task; use an execution plan only when sequencing is complicated enough to justify one. |
| Connected verification guarantees | A compact current coverage section in the proof README, linking theorem endpoints, supported fragments, assumptions, implementation evidence and exclusions. |
| Reproducible discrepancies | Executable fixtures plus brief classification in the owning task or evidence record. Keep explanations beside the evidence. |
| Contributor guidance | One concise guide in the proof directory, linked from its README; split it only when it becomes difficult to use. |

The coverage section should distinguish proved, experimentally compared,
unsupported, and invalidated claims. Record the revision for comparisons that
have not been re-established on the current tree. Keep test-only exporters and
observers distinguishable from mechanized implementation guarantees. Reuse
existing evidence registers and avoid a manually maintained theorem catalogue.

The contributor guide should explain the verification contract and trusted
boundary, existing check commands, theorem/module conventions, and one worked
semantic extension. Include a short discrepancy recipe: reproduce, minimize,
classify, locate authority, repair, and recheck. Link detailed premises from
Lean rather than duplicating them in prose.

A new permanent artifact is justified when it owns information that cannot be
kept clearly in these existing places. This note recommends the coverage
section and guide as maintenance aids; it does not create new gates or require
a separate verification proposal, readiness checklist, or coordination report
for every feature.

### Reducing coordination friction

Keep each fact at one owner. Proposals explain semantic changes; tasks track
work; evidence records explain results; theorem statements carry premises.
Cross-link those owners instead of copying status into several documents.
Automate counts, dependency graphs and check results where they are useful.

Use a short verification-impact paragraph in an existing proposal or task:
changed behavior or invariants, affected proof boundary, relevant checks, and
any remaining gap with its owner. Omit it when the change has no verification
impact. Review those facts in the existing review rather than scheduling a
separate handoff ceremony.

Use focused checks while iterating and the governing integration checks at
completion. Publish stable theorem interfaces for shared work; coordinate
changes to those interfaces directly. Parallel branches can pin a common
baseline and exchange small fixtures or lemmas without waiting for every
workstream to converge. Keep execution plans temporary and remove completed
transition artifacts according to the existing lifecycle.

### Module organization

Provide feature-oriented entry points for handlers, resources, cleanup and
continuation operations. Organize Lean internals by dependencies and stable
boundaries such as admission, shared invariants, runtime relations and
simulation. Substitution, ownership accounting and transport cross features;
forcing them into separate feature silos can duplicate proofs.

Restructure when changes repeatedly touch unrelated layers, duplicate machinery
or require excessive context. WIP status permits useful refactoring, but a
large file count alone does not justify reorganizing the entire library.

## Recommendation and evaluation criteria

Continue developing the one-shot foundation and the active Core alignment
bridge. Make its verified boundary and assumptions easy to inspect, then
extend coverage through concrete language work. Introduce tooling and guidance
incrementally where they make that work cheaper or its guarantees clearer.

A useful next evaluation is a real semantic extension carried through intended
laws, operational rules, admission, implementation, regression evidence and
correspondence. Compare the context needed, changed proof surface, check cost,
and defects or missing assumptions discovered. Retain experimental tooling when
it repeatedly improves that workflow; simplify or discard it when its upkeep
exceeds its benefit. No additional prototype is authorized by this note.

## Open questions

- Which reusable admission and simulation interfaces emerge from Core alignment?
- What claim can be established between the Lean Core machine and the Rust
  evaluator, and which implementation components remain trusted?
- Which observations and environmental assumptions are required for failures,
  divergence and foreign providers?
- Which one-shot invariants survive duplication and escape, and which require
  new contracts or proofs?
- How much proof lag is acceptable for a feature, and which existing guarantees
  must be re-established before its integration?
- Which generation and shrinking approach finds useful interaction failures at
  acceptable maintenance cost?
- Does the proposed coverage section and contributor guide remove enough
  repeated context reconstruction, or can existing material be simplified first?
