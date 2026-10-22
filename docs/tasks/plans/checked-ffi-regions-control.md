# Checked FFI, Regions, and Scoped Control Execution Plan

Owned by [TASK-0050](../TASK-0050-checked-ffi-regions-control-program.md).
Prepared on 2026-10-21 against Main
`7949b6d9136b0152ee9104e67bd0451cb9db4727`.

This is a task-owned planning document, not semantic or architectural authority.
The original authorization covered workflow documents only. The user subsequently
authorized agent work toward M1; TASK-0050 records the local P0/F1/F2 preparation
assignment. That assignment permits the bounded F2 probes and candidate contracts;
product tasks require accepted governing artifacts. The user later authorized
autonomous recommended choices, unsigned local commits and a separate worktree.
The orchestrator adopted reviewed CP-0024 under that delegation; TASK-0050 records
local M1 delivery roles. GitHub publication and per-item GitHub integration are authorized
as recorded below; Main integration retains its separate gate.

## Baseline and agreed endpoint

Main already contains bounded source-authored FFI and generic cells. Use its
[current-at-pin specification](https://github.com/dikini/ash-lang/blob/7949b6d9136b0152ee9104e67bd0451cb9db4727/spec/README.md),
[generic-cell semantics](https://github.com/dikini/ash-lang/blob/7949b6d9136b0152ee9104e67bd0451cb9db4727/spec/static-semantics.md#generic-cell-foundation),
and
[AD-0013 generated-bridge decision](https://github.com/dikini/ash-lang/blob/7949b6d9136b0152ee9104e67bd0451cb9db4727/docs/decisions/AD-0013-generated-native-bridges-and-program-builds.md).
The older planning checkout is not a product restart point. Preserve later
Main work when refreshing this pin; do not restore retired CP-0023 or cell tasks.

The user selected this staged program:

| Milestone | Intended outcome | Product sequence |
| --- | --- | --- |
| M1: Checked FFI | Opt-in in-process checks and Linux isolated execution over common contracts. | First; neither regions nor scheduling is a prerequisite. |
| M2: Lexical regions | Explicit fixed-arena allocation, checked construction, and ownership preservation. | After M1; design/proof preparation may overlap when separately authorized. |
| M3: Retained control | One local continuation store and library scheduling with checked drain. | After M2; reuse existing resource/cleanup machinery. |
| M4: Pinned network | Two owning workers, copied channels, and checked bidirectional shutdown. | After M3; finish the program with integrated examples. |

This sequence is a delivery preference, not a claim that all later mechanisms
semantically depend on every earlier feature. The named dependencies below
identify actual readiness requirements. Shared compiler writers and heavy
builds remain serialized under the agent workflow.

Existing FFI builds retain their supported behavior. The new profile admits
only operations whose entire required contract closure satisfies its checks.
It cannot acquire its guarantees through a legacy execution path or fall back
from isolated to in-process mode. Mode and policy are fixed per host activation.

The endpoint excludes migration, shared continuation stores, zero-copy or
ownership-transfer channels, additional collectors, implicit allocation
placement, general borrowing, callbacks, asynchronous native APIs, arbitrary
native-stack suspension, general proof syntax, and worker-failure recovery.
Keep these as design pressure without adding implementation issues for them.

## Authority and GitHub workflow

The user authorized GitHub publication and one PR per work item on 2026-10-21.
The latest instruction requires GitHub squash-and-merge into the milestone branch
after successful independent review, with a GitHub merge commit when squash is
unavailable. Locally authored commits remain unsigned. The published hierarchy belongs to
[overall milestone 2](https://github.com/dikini/ash-lang/milestone/2). This table
maps plan keys to GitHub records; those records own live progress.

| Plan key | Published issue |
| --- | --- |
| TASK-0050 | [#51](https://github.com/dikini/ash-lang/issues/51) |
| M1 | [#52](https://github.com/dikini/ash-lang/issues/52) |
| M2 | [#53](https://github.com/dikini/ash-lang/issues/53) |
| M3 | [#54](https://github.com/dikini/ash-lang/issues/54) |
| M4 | [#55](https://github.com/dikini/ash-lang/issues/55) |
| P0 | [#56](https://github.com/dikini/ash-lang/issues/56) |
| F1 | [#57](https://github.com/dikini/ash-lang/issues/57) |
| F2 | [#58](https://github.com/dikini/ash-lang/issues/58) |
| F3 | [#59](https://github.com/dikini/ash-lang/issues/59) |
| F4 | [#60](https://github.com/dikini/ash-lang/issues/60) |
| F5 | [#61](https://github.com/dikini/ash-lang/issues/61) |
| F6 | [#62](https://github.com/dikini/ash-lang/issues/62) |
| F7 | [#63](https://github.com/dikini/ash-lang/issues/63) |
| F8 | [#64](https://github.com/dikini/ash-lang/issues/64) |
| R1 | [#65](https://github.com/dikini/ash-lang/issues/65) |
| R2 | [#66](https://github.com/dikini/ash-lang/issues/66) |
| R3 | [#67](https://github.com/dikini/ash-lang/issues/67) |
| R4 | [#68](https://github.com/dikini/ash-lang/issues/68) |
| R5 | [#70](https://github.com/dikini/ash-lang/issues/70) |
| C1 | [#71](https://github.com/dikini/ash-lang/issues/71) |
| C2 | [#72](https://github.com/dikini/ash-lang/issues/72) |
| C3 | [#73](https://github.com/dikini/ash-lang/issues/73) |
| C4 | [#74](https://github.com/dikini/ash-lang/issues/74) |
| C5 | [#75](https://github.com/dikini/ash-lang/issues/75) |
| N1 | [#76](https://github.com/dikini/ash-lang/issues/76) |
| N2 | [#77](https://github.com/dikini/ash-lang/issues/77) |
| N3 | [#78](https://github.com/dikini/ash-lang/issues/78) |
| N4 | [#79](https://github.com/dikini/ash-lang/issues/79) |
| N5 | [#80](https://github.com/dikini/ash-lang/issues/80) |
| N6 | [#81](https://github.com/dikini/ash-lang/issues/81) |

Each milestone issue owns its outcome, dependencies, child links, acceptance
map, final Main PR, and closure. Child issues use the outcome, dependencies,
authority, acceptance, PR slices, and roles recorded below. Add exact refs and
assignments at launch. Keep the acceptance scope intact across partial PRs.

Readiness means the reviewed subset named in a dependency, not closure of the
whole issue. In M1, F1/F2 establish contracts/profile, F3 supplies carriers,
F4/F6 connect runtime and artifacts, and F5 supplies in-process library cases
before F7 adds isolation. F5's isolated acceptance closes after F7; F7 does not
wait for that acceptance to start. Similarly, C3 can use reviewed C2 carriers
while C2's public release paths remain blocked on C3. PM records these subset
handoffs and their exact commits; no staged permission bypasses validation.

A design note informs contract preparation. A semantic change needs an accepted
change proposal; a converged non-language choice needs an accepted architectural
decision. Only then create the corresponding product task. Experimental and
proof work needs a bounded authorized assignment with its question, assumptions,
comparison cases, and retention conditions. No issue or plan substitutes for
those artifacts. Contract acceptance and implementation acceptance are distinct.

For later delivery, use one integration branch per milestone under `codex/`
and the checkpoint/worktree lifecycle in
[AD-0011](../../decisions/AD-0011-milestone-worktree-lifecycle.md).
Draft slice PRs target the active checkpoint or milestone retaining branch named
in the assignment. For this run, the user's latest explicit instruction overrides
the normal AD-0011 merge method: after successful exact-head review/checks, use
GitHub squash-and-merge, with a GitHub merge commit when squash is unavailable.
Keep locally authored commits unsigned; GitHub signing follows the chosen merge
method. Retain the PR head, GitHub merge commit and tree/verification correspondence,
then fetch and synchronize local/origin retaining refs. Earlier local squash
receipts remain historical evidence and do not authorize future local squashes. Each milestone still
has a separately gated final Main PR. Do not carry forward
a historical unsigned-merge exception as permission for a new delivery.

Every PR identifies its issue criteria, complete or partial coverage, exact
head/base, focused checks, review, last full-gate receipt, intervening changes,
and next checkpoint. At retention, the author records Delivered, Remaining,
Awaiting, and Owner with the commit and evidence links; the reviewer checks it
and PM confirms application/readback. No partial PR auto-closes an issue.

### Responsible roles

These role sets apply to each issue's Roles field. The current local M1
preparation assignment is recorded in TASK-0050; other roles remain unassigned.

| Role set | Responsibilities |
| --- | --- |
| Contract | Design author drafts; independent semantic reviewer checks; project lead accepts or returns the contract; PM records readiness. |
| Platform | Platform developer owns the bounded experiment and realization; independent platform reviewer checks containment; project lead accepts architecture; PM owns readiness. |
| Product | Developer owns implementation, evidence and acceptance updates; independent reviewer checks the current head; assigned integrator retains; PM confirms closure. |
| Proof | Proof author owns model/theorems and explicit assumptions; independent proof reviewer checks coverage and soundness; build operator runs frozen integration; PM records the synchronization gate. |
| Closure | PM owns the whole acceptance map; authors supply evidence and updates; reviewer audits completeness; build operator runs gates; integrator retains; human owns Main authorization. |

All sets use the existing
[agent workflow](../../project/agent-workflow.md),
[orchestrator skill](../../../.agents/skills/ash-orchestrator/SKILL.md), and
[role preferences](../../../.agents/ash-workflow.yaml) at a future launch.
The developer authors each acceptance update; a contract author fills that role
for a documentation-only contract PR. Independent review is not self-review.

### P0: Reconcile and publish the program baseline

- Outcome: establish the GitHub hierarchy and a documentation PR on the current
  product history without importing obsolete product code or cell tasks.
- Dependencies: separate publication authorization; refreshed Main pin and live
  issue/PR inventory; the present four-document preparation.
- Authority: TASK-0050's documentation scope, AD-0002, and AD-0011. Publication
  and branch operations require a later assignment; no semantic acceptance.
- Acceptance: preserve selected DN-0053 through DN-0057 refinements and their
  links, identify completed foundations, map all issue keys, and record pending
  contract/launch gates. Preserve unrelated work and current Main changes.
- PR slices: documentation/provenance reconciliation, then any review repairs.
- Roles: Contract, with PM responsible for publication and dependency mapping.

## M1: Checked FFI

Design input is
[DN-0057](../../design/DN-0057-checked-ffi-module-boundaries.md), its
[worked cases](../../design/foreign-authoring/minimal-ffi-contract-cases.md),
[checked representation](../../design/foreign-authoring/minimal-ffi-checked-representation.md),
[canonical transitions](../../design/foreign-authoring/minimal-ffi-transitions.md),
[exhaustion contract](../../design/foreign-authoring/minimal-ffi-exhaustion-and-ownership.md),
[SQLite policy](../../design/foreign-authoring/minimal-ffi-sqlite-policy.md),
[ABI profile](../../design/foreign-authoring/minimal-ffi-abi-profile.md), and
[launch profile](../../design/foreign-authoring/minimal-ffi-launch-and-artifacts.md).
The [consistency review](../../design/foreign-authoring/minimal-ffi-consistency-review.md)
records proposed resolutions and remaining Linux acceptance gaps, not production
evidence. The tables remain the single proposed owner of combined transitions.

### F1: Adopt checked FFI contracts

Current candidate: [CP-0024](../../proposals/CP-0024-checked-foreign-host-profile.md)
and its [complete evidence map](../../design/foreign-authoring/checked-ffi-evidence-map.md).
The orchestrator adopted the independently reviewed contract under the user's
explicit delegation on 2026-10-21. Product evidence remains pending.

- Outcome: an accepted semantic delta for authenticated host authority, exact
  effects, wrapper dependencies, transitive assumptions, publication, reporting,
  and separate local/native completion.
- Dependencies: P0 product-baseline reconciliation.
- Authority: DN-0057 informs a new proposal; the current specification governs
  existing behavior. Obtain explicit acceptance before product tasks start.
- Acceptance: freeze the opt-in source/build boundary and compatibility rules;
  map O1-O10, X1-X5, L1-L23, K1-K9, and T1-T16 to required evidence. Specify
  empty-row entry, fixed host mode, wrong-host rejection, and no legacy bypass.
  Keep result validity, containment, and native assumptions separate.
- PR slices: common semantic proposal and evidence map; accepted revision and
  authorized task breakdown after review. No normative spec update yet.
- Roles: Contract.

### F2: Validate the Linux execution profile

Current preparation: [bounded experiment contract](../../design/foreign-authoring/linux-profile-experiment.md)
and [Stage A evidence](../../design/foreign-authoring/linux-profile-probe/README.md).
[AD-0015](../../decisions/AD-0015-linux-scalar-inprocess-whole-images.md) accepts
only owner-free scalar GNU in-process mechanisms, explicit trusted closure and
refusal obligations after reviewed packaging/source/diagnostic evidence. Strict
per-image approval, protected store/context/F6 enforcement, isolated Stage B,
SQLite and owner/resource evidence remain pending. No whole F2 criterion is
completed by this partial architecture decision.
[AD-0016](../../decisions/AD-0016-linux-owner-inprocess-whole-images.md) later
selects owner/resource GNU in-process whole-image mechanisms under finite
trusted native/runtime/allocator/closure premises. It supplies an architecture
basis for appropriately assigned F4/F6 work, not per-image strict approval,
protected context/store enforcement, checked activation, isolation, SQLite or
whole F2 completion.

- Outcome: a tested, accepted Linux x86-64 executor architecture and explicit
  deployment prerequisites for in-process and isolated checked images.
- Dependencies: P0; reconcile the realization with F1 before acceptance.
- Authority: a separately authorized bounded experiment under DN-0057, then a
  new architecture decision. The launch note alone grants no experiment rights.
- Acceptance: fix and test post-exec/re-exec UID, groups and capabilities,
  syscall policy, immutable static-image execution, private root/storage grants,
  quotas, resource limits, termination and reaping. Refuse unavailable controls.
  Record failed configurations; retain evidence, not prototype machinery by default.
- PR slices: experiment contract; reproducible deployment evidence; architecture
  decision and production requirements. A failed comparison returns to design.
- Roles: Platform.

### F3: Carry checked contracts through modules and Core

- Outcome: extend existing canonical contracts and phase projections with host,
  assumption, result, dependency, and completion facts independently validated
  across source, summaries, linking, Core, and private program images.
- Dependencies: accepted F1 and its authorized product task.
- Authority: F1 proposal and current typed-Core/bridge decisions; architecture
  changes beyond those boundaries need their own accepted decision.
- Acceptance: preserve defining identities through opaque exports, aliases and
  complete Type/Row instantiation. Reject forged independent-result facts,
  hidden-capture loss, host-effect erasure, and stale transformed contracts.
  Unsupported partial paths publish no permission. Charge all new analysis.
- PR slices: contract/summary carriers; source and linked admission; independent
  Core/image reconstruction and transformation tests, with matching spec deltas.
- Roles: Product.

### F4: Implement monitored in-process execution

- Outcome: common call admission, reserved control storage, guarded acquisition,
  protocol monitoring, bounded copy interaction, quarantine, and local completion.
- Dependencies: reviewed F3 carriers; accepted F1; authorized runtime task.
- Authority: F1's adopted transitions and existing evaluator ownership model.
- Acceptance: preflight before native entry; commit known disposition and local
  discharge before fallible reporting; preserve dependencies after retention.
  Distinguish evaluator exhaustion, native failure and optional diagnostics.
  Copy windows expose no pointer, callback, suspension, or partial value.
  Do not expose execution before F3 admission and F6 artifact admission connect.
- PR slices: reservation/owner records; native-call and completion transitions;
  copy/publication integration and adversarial budget evidence.
- Roles: Product.

### F5: Deliver checked SQLite bindings

- Outcome: Ash-owned SQLite policy for copied nullable UTF-8 and scoped
  connection/statement lifecycles using common checked machinery.
- Dependencies: connected F3/F4 and accepted F1; executable acceptance also
  requires F6. Isolated acceptance follows F7.
- Authority: F1's adopted SQLite contract and an authorized library task.
- Acceptance: null differs from empty text; preserve embedded zero bytes and
  original row/column kind across refused copies. Reset preserves binding
  uncertainty; finalize errors still consume; close refusal retains backing.
  Cover partial acquisition and diagnostic loss. Exercise minimal arena lifecycle
  as a contrasting resource; no SQLite-name policy in common compiler/runtime.
- PR slices: input/copy policy; lifecycle/report policy; generated-host cases
  for SQLite and the contrasting common-mechanism regression.
- Roles: Product.

### F6: Admit immutable execution artifacts

- Outcome: checked build preparation and admission bind approved executable
  bytes to contracts, bridge plans, native inputs, tools, runtime and policy.
- Dependencies: F3 contract projection; accepted F2 profile and authorized task.
- Authority: F2 architecture and the accepted generated-Rust-bridge boundary.
- Acceptance: freeze versioned deterministic receipts and supported ABI checks;
  preserve generated Rust calls, using C compilation for required header checks.
  Verify authorized immutable bytes before native startup; reject changed or
  unapproved inputs, unsupported versions and substituted operation mappings.
  Existing builds retain their supported static/shared behavior outside this profile.
- PR slices: receipt/plan emission; approval and immutable-image admission;
  build configuration, diagnostics and tamper tests.
- Roles: Product and Platform.

### F7: Implement isolated execution and supervision

- Outcome: one native subprocess per connection group, with bounded private-pipe
  protocol, parent admission and independent termination/reaping authority.
- Dependencies: connected F3/F4/F6 and F5's reviewed in-process binding subset;
  accepted F2 and an authorized supervisor task. F5's isolated cases remain open.
- Authority: F1 common semantics and F2 executor architecture. Freeze wire and
  receipt versions before connecting worker and parent implementations.
- Acceptance: one request in flight; fresh sessions and monotonic requests;
  validate complete control before payload and preserve admitted outcomes after
  later loss. Reject malformed success separately from valid conversion refusal.
  No native pointers on the wire, replay, stale finish, or mode fallback.
  Reserve shutdown capacity; retain reservations until termination is observed.
- PR slices: protocol/worker realization; parent validation/supervision;
  restricted launch and fault/limit integration.
- Roles: Product and Platform.

### F8: Close the checked FFI milestone

- Outcome: both checked modes, public usage/diagnostics, specification, evidence,
  verified milestone retention and a separately authorized Main delivery.
- Dependencies: complete F1-F7 outcomes on the connected candidate.
- Authority: adopted F1/F2 artifacts, implementation tasks and closure assignment.
- Acceptance: map every canonical transition/trace, module/Core negative case,
  actual native case and containment obligation to evidence. Expose transitive
  assumptions and mode differences; compare costs without claiming native truth.
  Pass final review/full gate and verify the retained result before issue closure.
- PR slices: integrated cases and documentation; checkpoint evidence and
  transition cleanup; final Main PR under separate authorization.
- Roles: Closure.

## M2: Lexical regions and ownership

Use [DN-0054](../../design/DN-0054-base-lexical-region-memory-contracts.md) and
[DN-0055](../../design/DN-0055-algebra-of-regions-lifetimes-and-ownership.md).
Keep placement, usable validity, backing protection, completion, and access
distinct. Existing cells keep their strict retained-payload outlives rule.

### R1: Define and prove the lexical ownership model

- Outcome: a bounded fixed-arena transition model and mechanized preservation
  of initialized residency, required uses, owner dependencies and completion.
- Dependencies: P0; use current resource/cell semantics and reconcile retained
  foreign composition with F1. Preparation can precede F8 if authorized.
- Authority: a bounded proof assignment under DN-0054/DN-0055 and AD-0012.
- Acceptance: include failed/pending construction, suspension, projection,
  ordinary graph cycles, retained backing, and invalid early release. State
  assumptions and source/Core correspondence obligations; no general memory-safety
  claim follows from a model-only theorem.
- PR slices: definitions/counterexamples; transition preservation proofs;
  frozen proof receipt and correspondence requirements for R2/R3.
- Roles: Proof.

### R2: Adopt explicit region construction contracts

- Outcome: an accepted proposal for explicit region access and the admitted
  representation, construction, failure, projection and bulk-reclamation rules.
- Dependencies: R1 model/proof review; reconcile the final contract with R1
  before acceptance. Product delivery follows F8.
- Authority: DN-0054/DN-0055 inform a new semantic proposal and, where needed,
  representation architecture decision; obtain acceptance before product tasks.
- Acceptance: freeze the explicit API and first graph/closure fragment. Separate
  independent reservation from local younger-dependent initialization; define
  publication and abandoned reservations. Keep ordinary construction unchanged,
  no hidden heap fallback, and no cell lifetime or cycle relaxation.
- PR slices: proposal and evidence map; representation decision if needed;
  authorized task breakdown after acceptance.
- Roles: Contract and Proof.

### R3: Implement checked region construction

- Outcome: explicit fixed-arena allocation with authenticated representation,
  reservations, local initialization and publication through source/Core/runtime.
- Dependencies: accepted R2, R1 proof gate and verified F8 baseline.
- Authority: R2 artifacts and an authorized construction task.
- Acceptance: preserve projection/capture dependencies through helpers, opaque
  summaries and transforms. Reject forged layouts/reservations and partial reads.
  Cover immutable products and nominal data, then the selected closure/recursive
  graph fragment. Never narrow mathematical integers silently or relocate aliases.
- PR slices: typed allocation and provenance; reservation/local initialization;
  admitted closures/graphs with connected validation and accounting.
- Roles: Product, with Proof review of model correspondence.

### R4: Implement reclamation and resource composition

- Outcome: ordered bulk reclamation with cells, cleanup, captures and native
  retained-owner protection under the selected lexical scheme.
- Dependencies: reviewed R3 foundation and accepted R2.
- Authority: R2 completion contract and an authorized runtime task.
- Acceptance: retain the same activation through resume; dispose unpublished
  construction on abandonment; release once after required completion. Quarantine
  preserves physical backing without extending source access. Account for metadata,
  scratch, captured control and teardown as well as payload bytes.
- PR slices: runtime reclamation; mixed cell/native/control compositions;
  exact/short budget and deep-disposal evidence.
- Roles: Product.

### R5: Close the region milestone

- Outcome: verified explicit lexical region product checkpoint and Main delivery.
- Dependencies: complete R1-R4 outcomes on one candidate.
- Authority: accepted region artifacts, tasks and closure assignment.
- Acceptance: source/Core/runtime cases match the bounded model; compare fixed
  regions with ordinary heap construction on results, retention, allocation
  refusal and completion order. Record unsupported representations explicitly.
  Complete specification, independent review, full gate and retained verification.
- PR slices: integrated evidence/examples; checkpoint closure and cleanup;
  separately authorized Main PR.
- Roles: Closure and Proof.

## M3: Scoped continuation retention and library scheduling

Use [DN-0056](../../design/DN-0056-scoped-continuation-retention-and-library-scheduling.md).
The selected planning direction reuses resource scope and cleanup. Generic
cells do not admit owned continuation payloads. Scheduling stays in libraries;
no separate Task, Drive, or release-gate Core primitive is planned.

### C1: Specify and prove owned continuation storage

- Outcome: accepted store/transfer/restoration semantics and a mechanized bounded
  unique-ownership/completion model for one local executor.
- Dependencies: P0 and current control semantics; reconcile region support with
  R2/R5 before product delivery. Model preparation may run earlier if authorized.
- Authority: bounded DN-0056 proof assignment, then accepted semantic proposal
  and any needed architecture decision; AD-0012 governs proof integration.
- Acceptance: fix ports, exact interpretation, branch authority, current-consumer
  returns, external support and failure ownership. Prove the selected transitions;
  reject capturing the store owner into itself or skipping required completion.
- PR slices: model and proof; semantic/Core contract and evidence map;
  authorized task breakdown after acceptance.
- Roles: Contract and Proof.

### C2: Implement store operations and runtime ownership

- Outcome: authenticated retain/continue/probe operations, fixed-port owned
  captures, generation-qualified non-owning locators and iterative disposal.
- Dependencies: accepted C1/proof gate and verified R5 baseline.
- Authority: C1 contracts and an authorized store task.
- Acceptance: reserve before committed transfer, restore at most once into the
  admitted consumer, preserve active/captured ownership and cleanup phase.
  Copied or stale locators grant no new authority. Public release admission
  remains closed until C3 proves its conditions on the connected implementation.
- PR slices: checked carriers and operation admission; evaluator storage/moves;
  generation, capacity and completion tests.
- Roles: Product and Proof.

### C3: Implement checked drain analysis

- Outcome: finite normal-return relations establishing empty-store state at
  every admitted normal release predecessor.
- Dependencies: C1 and reviewed C2 contracts/carriers; a bounded proof assignment
  for the analysis rules precedes reliance on their release facts.
- Authority: accepted analysis semantics and soundness obligations from C1;
  revise the proposal if the bounded analysis cannot establish required cases.
- Acceptance: mechanize the selected relation/fixed-point rules; authenticate
  actual handler-selected probes, result/state correlation and freshness. Include
  mutually recursive/imported control and handler/cleanup suffixes. Unknown
  external calls are conservative. Core reconstructs after transformations;
  exhaustion publishes no partial release permission or termination claim.
- PR slices: analysis model/proof; inference and summary flow; independent
  validation, transformed-control tests and bounded-work evidence.
- Roles: Proof and Product.

### C4: Deliver scheduling libraries

- Outcome: coroutine selection, cooperative queues and explicit gas-guarded
  safe-point selection using one retention mechanism.
- Dependencies: connected C2/C3 with their proof gates.
- Authority: accepted C1/C3 contracts and an authorized library task.
- Acceptance: parent R waits for P while Q remains retained; final drain completes Q.
  Exercise checkpoints around resume, suspended cleanup, repeated yielding
  during drain, and false/true gas guards. Preserve current-consumer return;
  lost ready-queue entries cannot erase store ownership. No fairness guarantee.
- PR slices: coroutine/cooperative libraries; explicit checkpoint policy;
  common scenario corpus and documentation.
- Roles: Product.

### C5: Close the local execution milestone

- Outcome: retained local-control product with proof, source/Core/runtime
  correspondence and executable scheduling examples.
- Dependencies: complete C1-C4 outcomes.
- Authority: accepted local-control artifacts, tasks and closure assignment.
- Acceptance: include fake/stale probes, unsafe handler suffixes, substituted
  callbacks, wrong interpretation, shared branch authority and exhausted transfer
  preparation. Complete specification, proof integration, independent review,
  full gate and retained verification before Main acceptance.
- PR slices: integrated evidence; checkpoint closure and cleanup; Main PR.
- Roles: Closure and Proof.

## M4: Pinned workers and checked network shutdown

Use DN-0055's protocol constraints and DN-0056's pinned-worker and causal-ledger
comparisons. These kernel-thread workers are distinct from FFI subprocesses.
Each owns its evaluator and continuation store. Synchronous FFI occupies its
worker until return; this milestone adds no native-stack suspension.

### N1: Adopt worker and copied-channel contracts

- Outcome: accepted entry/capture admission, polarized endpoint authority,
  bounded FIFO publication/receipt, visibility, waiting, end-of-input and
  backing-settlement contracts for two workers.
- Dependencies: C1/C3 completion contracts; align product delivery with C5.
- Authority: a new semantic proposal and converged host/channel architecture
  decision informed by DN-0055/DN-0056.
- Acceptance: define resource-free copied payloads, commit points, pre/post-entry
  failure ownership, stale notifications and genuine End. Kernel preemption
  changes no Ash ownership. State transport/native assumptions and terminal
  failure limits; no silent resource transfer or worker recovery.
- PR slices: protocol contract and cases; host/transport decision and proof
  obligations; authorized product tasks after acceptance.
- Roles: Contract and Platform, with Proof review.

### N2: Implement pinned workers and one-way completion

- Outcome: exclusive local stores communicating through admitted copied channels,
  with producer/receiver completion and support settlement.
- Dependencies: accepted N1 and verified C5 baseline; discharge the bounded
  worker/channel preservation obligations before using them to authorize release.
- Authority: N1 artifacts and an authorized worker/channel task.
- Acceptance: construct resources on the owning worker; only it restores local
  slots. Preserve accepted but unpublished, queued and receiver-held obligations.
  Keep receiving while a bounded producer finishes. Release only after endpoints,
  cleanup, wait registrations and backing users settle.
- PR slices: admitted worker entry and copied channel; notification and one-way
  shutdown; concurrency, failure and capacity evidence.
- Roles: Product, Platform and Proof.

### N3: Prove the functional ledger and restricted checker

- Outcome: mechanized finite-list ledger invariants and sound restricted
  checking rules, followed by a bounded Core checker for those rules.
- Dependencies: C3's actual-completion boundary and accepted N1 accounting/
  transport premises; proof preparation need not wait for N2 implementation.
- Authority: a bounded proof assignment, accepted checker semantics and any
  verifier architecture decision; no general source proof language.
- Acceptance: prove registration, retirement, acknowledgement, whole-entry and
  order-preserving RemoveById, freshness and current-successor-state obligations.
  Bind untrusted plans to actual linked definitions; check induction premises,
  dependencies and all reachable branches. Unsupported transforms must preserve
  a checkable form or reject; proof exhaustion grants no permission.
- PR slices: model/lemmas and checker-rule soundness; accepted verification
  contract; Rust reconstruction and mutation/transform rejection evidence.
- Roles: Proof and Product, with Contract acceptance before product work.

### N4: Implement bidirectional completion analysis

- Outcome: compose verified ledger transitions, actual local completion and
  transport premises into checked recursive application-drain summaries.
- Dependencies: reviewed N2 mechanisms and N3 proof/checker gate.
- Authority: accepted N1/N3 contracts and an authorized analysis task.
- Acceptance: register children before publication; preserve parent coverage
  until authentic acknowledgement. Reject stale emptiness, forged completion,
  obsolete ledger inputs, raw publication bypasses and application/control
  envelope confusion. Revalidate after transformations and through imports.
- PR slices: protocol facts/current-state analysis; recursive completion
  composition; adversarial control, transform and budget evidence.
- Roles: Product and Proof.

### N5: Deliver two-phase shutdown

- Outcome: library shutdown first establishes stable application quiescence,
  then completes passive service and settles all remaining support.
- Dependencies: connected N2-N4 and accepted normal/abandonment obligations.
- Authority: adopted network contracts and an authorized library task.
- Acceptance: seal new roots while allowing covered descendants; keep both
  workers and notifications serviceable through feedback. Then close application
  sends, observe genuine End, finish retained service/cleanup and settle endpoints,
  workers and backing. AppQuiet alone cannot release a store or support.
- PR slices: causal application drain; endpoint/service settlement;
  bounded-queue feedback and producing-cleanup scenarios.
- Roles: Product and Proof.

### N6: Close the network milestone and program

- Outcome: verified two-worker program with the four milestones retained and
  their complete acceptance records linked from the parent issue.
- Dependencies: complete N1-N5 and retained M1-M3 outcomes.
- Authority: adopted network artifacts, tasks and final closure assignment.
- Acceptance: demonstrate checked SQLite request/reply work with local
  regions/cells, retained computations and copied messages in both FFI modes.
  Validate orderly shutdown and failure limits without claiming deadlock freedom,
  termination or native correctness. Complete specification, proof/full gates,
  independent review, retained verification and separately authorized Main delivery.
- PR slices: cross-milestone examples/evidence; final closure/transition cleanup;
  Main PR and verified acceptance updates.
- Roles: Closure and Proof.

## Verification checkpoints

Focused verification and independent current-head review apply to every future
delivery. Full gates apply at the following connected boundaries, not every PR.
The named closure issue's PM owns scheduling and assigns one build operator.

| Gate | Trigger and required inputs | Owner | Enables |
| --- | --- | --- | --- |
| F-core | F3/F4/F6 connected; a real generated host exercises common acquisition, copy, completion and admission. | F8 PM | Library and isolation acceptance on the shared mechanisms. |
| F-final | F5/F7 integrated with F2 deployment evidence and complete F1 case map. | F8 PM | M1 closure and separate Main gate. |
| R-model | Frozen R1 proofs match the accepted R2 fragment and its assumptions. | R5 PM / proof operator | Reliance on the new region preservation rules. |
| R-core | R3/R4 connected, including pending construction and retained native backing. | R5 PM | Integrated region comparison and dependent acceptance. |
| R-final | Complete representation/composition corpus, proof correspondence and specification. | R5 PM | M2 closure and separate Main gate. |
| C-proof | C1 and C3 selected ownership/analysis rules have accepted frozen proof evidence. | C5 PM / proof operator | Reliance on retention and drain release facts. |
| C-core | C2/C3 connected with independent validation and runtime ownership. | C5 PM | Scheduling-library acceptance. |
| C-final | C4 and all local control/negative cases integrated. | C5 PM | M3 closure and separate Main gate. |
| N-core | N2 connected and worker/channel preservation obligations discharged. | N6 PM | Network protocol implementation acceptance. |
| N-proof | N3 frozen model/checker proof and actual-Core reconstruction pass. | N6 PM / proof operator | Reliance on ledger facts in N4/N5. |
| N-final | N4/N5 plus both-mode end-to-end examples integrated. | N6 PM | M4/program closure and separate Main gate. |

At each full workspace checkpoint and before Main integration run the current
documented command on frozen inputs:

```sh
CARGO_BUILD_JOBS=1 cargo xtask verify
```

Proof gates use the repository's frozen Lean integration workflow under
[AD-0012](../../decisions/AD-0012-proof-development-feedback-and-build-reuse.md),
including source/compiler/dependency pins, expected reports and axiom checks.
Language-server feedback does not close a proof gate. The proof assignment must
name its exact module closure and runner arguments before execution; do not
invent a generic command that omits theorem coverage. Relate the model to the
implemented Core rules and retain correspondence tests; model proof alone is
not a compiler-implementation or native-binary correctness theorem.

Keep source, configuration, compiler/runtime, headers, native artifacts, launch
policy and proof pins with receipts. Separate actual native observations from
injected failures. Exercise exact budgets, one-short refusal and a fresh
sufficient execution at affected layers; never replay an uncertain external
effect to obtain a passing result. Preserve depth/stack/work/capacity policies.

Required acceptance families include:

- FFI: every canonical O/X/L/K/T row and distinguishing trace, summary/Core
  forgery, wrong-host use, copied-output independence, original-kind caching,
  local-close precedence, consumption before report loss, partial acquisition,
  quarantine, stale sessions, worker versus parent exhaustion, and no retry.
- Isolation: malformed versus plausible false replies, faults before startup
  compatibility, post-exec/re-exec privilege checks, ambient-authority denial,
  pinned-image substitution, unavailable-control refusal, actual limit
  enforcement, timeouts and delayed reaping. Plausible replies do not prove truth.
- Regions: exact fit/refusal/overflow, partial initialization, closure and
  graph provenance, projection, owner-cycle rejection, suspended construction,
  structural discard, retained dependencies and release ordering.
- Local control: duplicate/stale locators, wrong interpreter/consumer, unsafe
  branch sharing, lost queue entries, fake/stale probes, mutually recursive
  drains, handler/cleanup suffixes and same-typed transformed callbacks.
- Networks: accepted/in-flight/received work during closure, bounded-queue
  feedback, producing cleanup, duplicate/forged acknowledgements, stale ledger
  versions, incorrect RemoveById payloads, incomplete proof branches and backing
  release before endpoint/notification settlement.

An early gate is not milestone completion. Carry the last full-gate receipt,
intervening changes and next owner/trigger in handoffs. A final checkpoint can
serve as the pre-Main gate only under demonstrated input equality. Verify the
actual retained result and refresh affected evidence after movement. Keep
criterion-wide verification pending where its complete scope is not yet covered.

## Future launch and closure handoff

This section is a preparation checklist, not an imperative launch prompt.
A later authorized launcher must supply:

1. Exact current product/retaining refs and commits, selected milestone/issues,
   accepted proposal/decision links, and active repository tasks.
2. Developer, independent reviewer, PM, integrator, acceptance owner and build
   operator; role settings from the repository unless explicitly overridden.
3. Separate permissions for design, experiments/proofs, implementation,
   publication, pushes, branch integration, signing, Main and cleanup. Missing
   permissions are not supplied by this document or a copied launch template.
4. Dependency readiness receipts, unresolved semantic/platform questions,
   required case subset and complete milestone acceptance map.
5. The next full-gate/proof checkpoint, its trigger and owner, build serialization,
   input pins and evidence location outside disposable caches.
6. Initial issue checkbox state; the author/reviewer/PM acceptance-update path;
   the actual next owner and bounded completion condition.

At each closure, retain implementation, tests, specification, evidence and review
together before retiring proposals/tasks. Main semantics change only after the
separate Main gate and verified retention. Remove completed checkpoint worktrees
and branches only under AD-0011's clean-state and ancestry checks. Preserve exact
planning history without merging obsolete code to manufacture ancestry.

TASK-0050 owns this plan until it is superseded or the program closes. Consolidate
durable conclusions in the appropriate artifacts and then retire this temporary
plan; do not promote it into a second specification or permanent progress tracker.
