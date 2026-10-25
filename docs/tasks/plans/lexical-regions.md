# Lexical regions execution plan

Owned by [TASK-0055](../TASK-0055-lexical-regions.md). This plan orders work; it
is neither current language truth nor an accepted semantic proposal.
[DN-0054](../../design/DN-0054-base-lexical-region-memory-contracts.md) is the
canonical intended-design summary. DN-0055's wider algebra informs bounded
questions without becoming another milestone prerequisite.

## Outcome and current authority

[M2 #53](https://github.com/dikini/ash-lang/issues/53) requires ordinary default
and explicit placement, lexical ownership, bulk reclamation, closures and
recursive immutable graphs together. Intermediate data-only or explicit-only
PRs do not complete it. M1's slim FFI and Main integration are complete at
`0d8df03d4db2e70294487fc2e61f3629ff33b246` / PR #143. Current specification,
mathematical Int, rank-1 typing and existing resource/Cell/control rules remain
the baseline until the accepted R2 transition is implemented and integrated.

User-approved design directions constrain R1/R2; they are not proof results or
permission to skip the proposal. Start R1 and R2 together. Hold product R3 until
the accepted R2 contract and final matching bounded R1 proof are retained.

## Approved directions and remaining contract

| Boundary | Approved direction | R1/R2 must make concrete |
| --- | --- | --- |
| Complete allocator | `RegionAllocator<R>` has `allocate : Request -> Storage<R>` and `release : Unit -> Unit`; same implementation/state and region discipline fixed at initialization; owner controls release. | Exact source/effect/module exposure and ownership of the pair. An allocation projection alone is not the complete interface. |
| Storage | Host-backed default required; fixed capacity uses the same ordinary effect contract. Logical region close is distinct from a shared allocator's lifetime. | Request/Storage layouts, size/alignment/accounting and actual supplied-storage construction for objects, owned buffers and closures. |
| Placement | Closest declared live allocation context; entry establishes root through result observation. Calls forward caller selection; ordinary blocks/calls acquire no region. Explicit selection restores the prior context; aliases never move. | Checked entry configuration, source forms, public annotations and explicit lowering. |
| Closures | Record uses creation context and actual dependencies; invocation uses caller context for fresh allocations; captured explicit R remains R. | Public/opaque summaries, validation and representation correspondence without higher-rank callable values. |
| Effects | Allocation is an ordinary effect. Purity-compatible surface defaults include allocation; extra observable effects stay visible. Core has no implicits. | Full default expansion, explicit Core bindings/arguments/request targets and handler/cleanup relationships. Broader omitted-definition-row inference is excluded. |
| Bootstrap | Small private nonrecursive Request and existing host startup/control under existing limits. | Concrete representation and established foundation for setup, error delivery and root observation; no recursive allocation-to-request-allocation. |
| Construction | Evaluate operands once, request independent requirements, initialize supplied storage locally, publish only valid initialized access. | Exact reservation/initialization transitions; actual storage, not quota-only accounting. |
| Failure/control | Ordinary effects and checked discard; no replay, rollback, fallback or new result wrapper. Capture/resume retains exact context/owners/pending state. | Refusal effects and precise operand/reservation order, cleanup context restoration and safe local versus forbidden running-action discard. |
| Recursive data | Existing guarded slots, function templates, aliases and source-order initialization; ordinary immutable cycles remain distinct from owner cycles. | Pending/completed slot invariants, suspend/resume and unpublished-state abandonment. No new whole-group transaction. |

The source/Core candidate uses schematic lexical declaration and selection
forms and monomorphic default-allocation forwarding to an exact region effect.
A region-independent storage view must preserve actual residency and lifetime.
[CP-0025](../../proposals/CP-0025-lexical-region-construction.md) records the
accepted transition contract, including the selected source forms and layout
obligations. It remains distinct from current language truth; use that contract
rather than inferring semantics from this plan.

Ordinary construction on current Main does not yet carry the proposed allocation
effect. R2 must state that semantic delta explicitly. Surface `! {}` would include
the defined purity-compatible defaults; `! {Console}` adds Console. This grants
no permission to hide an allocator's additional observable effects or infer
unrelated omitted rows. All expanded effects and selected targets remain explicit
in checked contracts and Core.

A saved release action owns the paired provider function/state, not captured
handlers. Removed nearest interpreters cannot be resurrected or replaced by
outer same-instance interpreters. Preserve `effect.cleanup-context`, Cell's
strict payload outlives relation and request-payload boundaries. Closing resumes
its captured allocation context and restoration frames; successful discard
restores the clause context. Required completion precedes permitted bulk release.
Native backing remains an ordinary module contract assumption, not compiler
quarantine, a native-correctness theorem or a new security protocol.

## R1/R2 candidate checkpoint

The [finite model guide](../../design/lexical-regions/README.md),
[correspondence report](../../design/lexical-regions/correspondence.md) and
[evidence record](../../design/lexical-regions/evidence.md) describe the reviewed
eight-module candidate. The frozen gate passed all 195 reports through eight
independently validated cache reuses, with zero fresh compiler invocations;
exact source/registration transfer passed. Independent actual-gate audit has
cleared this bounded result and root accepted CP-0025's matched semantic content.
Current-head review, milestone retention and author acceptance remain pending.
Product R3 remains held until the accepted contract and matched proof are
retained and verified. This checkpoint changes no
original acceptance criterion or required product evidence.

## Ordered deliveries

### R1 — bounded model and matched proof (#65)

Define sequential states/transitions parameterized by the ordinary allocator
contract; fixed capacity is one instance, not a universal physical arena.
Track initialized residency, value dependencies, owner/completion state,
selected context and pending construction. Model all six features and the
construction, projection, closure capture, ordinary cycle, refusal, failure,
suspension, escape and invalid-release counterexamples.

Prove preservation for the admitted transitions with explicit assumptions and
source/Core correspondence obligations. Use
[AD-0012](../../decisions/AD-0012-proof-development-feedback-and-build-reuse.md):
frozen Lean integration, compiler/import pins, reports, dependency and axiom
audits. Model-only preservation does not prove the compiler or native allocator.
Do not expand R1 into all DN-0055 permissions/channels, general memory-safety
proofs or alternative collectors. Review R1 and R2 together before product work.

### R2 — accepted placement and construction contract (#66)

Prepare the semantic change proposal alongside R1, including current behavior,
proposed source/Core/effect expansion, complete pair, default/call/closure
behavior, actual-storage layout obligations, initialization/publication,
refusal/cleanup/abandonment, access/escape and bulk-close rules. Supply intended
operational transitions and connected examples before development. Freeze the
exact model-to-contract map and obtain independent review and acceptance; do
not promote this plan or DN-0054 into language truth. Add a representation AD
only for a genuine non-language decision, not by default.

### R3 — connected construction pipeline (#67)

After accepted R2 and final matched R1 proof, implement host-backed default and
explicit placement through source, public summaries, Core validation/transforms
and runtime. Reuse typed value/recursive-slot machinery through a narrow
supplied-storage seam. Include persistent buffers and closure storage; retaining
host payload allocation while merely debiting region capacity does not satisfy
this outcome. Preserve initialized-only publication and actual dependency facts.

Cover immutable products/nominal data, region-stored closures and recursive
immutable graphs. Intermediate PRs may stage those cases, but all are required.
Keep aliases/residency fixed, mathematical integers unchanged and owner cycles
rejected. No new general allocator framework or primitive-type family is required.

### R4 — completion and composition (#68)

Develop the minimal close foundation with R3; complete paired owned release,
Cell/cleanup/capture/control interaction, shared allocator isolation and bulk
reclamation. Preserve one-shot context/activation identity, account for abandoned
unpublished construction, and release once after required completion. A running
cleanup or unfinished close cannot be abandoned; an inner safely delimited
refusal may finish locally under existing discard rules. No per-reference graph
freeing, rollback or foreign retained-owner status protocol is added.

Account for metadata, scratch, captured state and teardown as well as payload.
Validate exact/short/retry and deep iterative disposal without changing existing
ledgers or introducing uncharged fallback work.

### R5 — connected milestone and Main gate (#70)

Compare default and explicit host-backed/fixed-capacity cases with ordinary heap
construction on results, retention, refusal and completion order. Cover all six
features, public/imported/opaque and transformed Core paths, negative lifetime
and forgery cases, and actual supplied storage. Record native assumptions and
unsupported cases honestly; unsupported required closures/graphs cannot close M2.

Update normative specification only with retained implementation and tests.
Complete independent exact-head review, retained tree/ref verification and author
acceptance. Remove completed transition/task/plan artifacts under policy and
verify the resulting final tree. Prepare separately authorized Main integration;
M3 retained control, M4 workers, overall program #51 and deployment are separate.

## Verification cadence and resource limits

Use focused affected checks per PR. R1's frozen proof gate and R2 correspondence
are mandatory, not substituted by product tests. At R-core, run the normal full
gate when R3 and shared R4 close form a connected representation/completion
checkpoint. At R-final, run it on the stable integrated product/specification and
post-transition-cleanup tree before Main. A single suitable equal-input receipt
may serve both checkpoints or transfer to Main only with complete file,
configuration, tool, runner and artifact equality; Markdown is an input too.

Use the existing owned worktree and compatible shared cache. Serialize heavy
compilers, retain successful compatible artifacts and use bounded local feedback
under AD-0012. No broad benchmark, compiler optimization search, backend matrix,
new verification framework or repeated full build per small planning edit.
The R1 candidate's proof gate and exact transfer are recorded above. Task/plan
prose requires Markdown/artifact/link/authority review; it does not require
repeating equal-input proof checks or running product Cargo/native gates.

## Planning evidence and exclusions

The staged launch was independently certified from the approved plan, intended
operational semantics, allocator interface and source/Core candidate. Their
frozen SHA-256 inputs, in that order, are:

```text
25482b735b96ec0b3768e0d38045d6c669b42d10b3eab5138cc2febb1bdadcc6
d568a19d6836dfaa54e5c2e605b2b9b68da92d03a6f3e49b3019306a002ac299
21dd96dae020dd344d75c2c49ae751cb6c032da032691802f2c5068de7fb09f2
7b710eb6b6f915c6bd6ad17f614cec31407eb11852080ba8c3695025d5d22a01
```

These identify planning inputs, not executable receipts or proof coverage.
DN-0054 and this owned plan consolidate their decisions without retaining four
duplicate design documents. Exact R2 source/Core semantics remain a proposal.
Only usage/lifetime-based automatic placement inference is deferred as an
optimization of placement. Region collection/RC, moving objects, ownership
transport, concurrency, a custom backend matrix, broader row inference and new
FFI types are outside this M2 assignment.
