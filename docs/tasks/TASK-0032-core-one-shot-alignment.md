# TASK-0032: Align Effect Core with the annotated one-shot calculus

- ID: `TASK-0032`
- Status: active
- Related: [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md),
  [CP-0021](../proposals/CP-0021-local-effects-in-resume-operands.md),
  [DN-0033](../design/DN-0033-direct-effects-and-continuation-capabilities.md),
  [execution plan](core-one-shot-alignment-plan.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

The user authorizes comparison, necessary alignment changes and verification of
validated Effect Core against the completed annotated one-shot M0–M4 calculus.
The accepted Core and evaluator decisions govern implementation boundaries.
DN-0033 governs formal experiments. A demonstrated language change requires a
proposal before product implementation; a repair to current specified behavior
does not change the language contract.

Use GPT-6 Astra for orchestration, analysis and integration, and GPT-6.1 Sol
with medium reasoning for implementation workers. Verify each assignment.

## Work

The stable inventory below measures deliverables, not equal amounts of effort.
Subcase inventories will be recorded in the comparison evidence after inspection.

| Package | Named inventory | Acceptance |
| --- | --- | --- |
| C1 | C1.1 fragment and construct map; C1.2 cleanup comparison; C1.3 direct/bound resume comparison; C1.4 discrepancy classification; C1.5 finite translation/transition inventory | Explicit transitions and reproducible evidence distinguish admission differences, runtime disagreements, representation and missing proofs. |
| C2 | C2.1 typed translation; C2.2 exact identities/signatures; C2.3 lexical resources/capabilities; C2.4 initial admission | Translation constructs the existing structural admission judgments from static input without future-execution assumptions. |
| C3 | C3.1 configuration relation; C3.2 transition simulation; C3.3 observations/ownership; C3.4 capacity and preparation; C3.5 nonvacuity | Actual Core steps have the stated calculus match, including administrative-step justification and progress measure. |
| C4 | C4.1 discrepancy resolutions; C4.2 positive regressions; C4.3 negative regressions | All demonstrated disagreements in the declared fragment are resolved with authority and evidence. |
| C5 | C5.1 integrated theorem; C5.2 coverage/specification records; C5.3 grouped verification; C5.4 independent review | Mechanized model claims, Rust evidence and exclusions remain explicit; checks contain no proof holes or unjustified axioms. |

Start with handlers, requests, sequencing, resume, discard, cells and cleanup.
Classify ordinary constructs, polymorphism, synchronous hooks and native buffers
explicitly. Multishot, escaping continuations, suspension and asynchronous hooks
remain separate targets. A small first example does not reduce the final scope.

## Progress

- Baseline: `124e164`, clean `main`; work uses `codex/core-alignment` in
  `.worktree/core-alignment`.
- Verified orchestrator assignment: `gpt-6-astra`, high reasoning.
- Current specification removes captured source handlers during discard and
  rejects cleanup whose nearest interpreter would be removed. The calculus
  retains captured handlers until lexical unwind reaches them. Comparison must
  first determine whether this difference is observable for validated Core.
- M0–M4 endpoints have been inspected. Their theorem boundary is annotated
  initial admission and constructive calculus execution, not Core admission or
  arbitrary-annotation preservation. Fresh baseline verification passed.
- C1 and verified C2–C4 components are integrated. General admission, full
  simulation and the integrated correctness theorem remain open.
- Intermediate commit `76380f4` retains the reviewed comparison, CP-0021 repair
  and first proof components. This does not close the product checkpoint or
  complete Core alignment.

### Increment 1 local results

- C1.1–C1.5 are recorded in the
  [comparison evidence](../design/direct-effects/one-shot/CORE-ALIGNMENT.md).
  Independent review confirmed the finite inventory: 23 Core node alternatives,
  19 Core frame alternatives, 16 calculus expressions and 32 calculus transition
  families. These counts are coverage inventories, not correspondence proofs.
- Six cleanup comparison tests pass, including exact cell closing order,
  nearest-interpreter rejection, the complete kernel fixture and a pure closure
  retaining a live cell. The complete fixture returns 11 and enters write
  applications 7 then 11, skipping 99.
- CP-0021 is implemented and locally reviewed: five direct/bound/nonempty-row/
  imported-summary resume regressions pass. Independent validation rejects
  missing operand effects, missing continuation effects and inflated rows.
  Focused work-limit and rollback checks pass, along with 172 related runtime,
  resource, hook and cleanup tests. Full `cargo xtask verify` passed, including
  formatting, metadata, build, lint, workspace tests and documentation.
- [CoreClosing](../design/direct-effects/one-shot/CoreClosing.lean) proves exact
  retained-frame order and owner partition for successful discard projection.
  Independent compilation and scope review pass. This is part of C3.2/C3.3;
  callback execution and full configuration simulation remain outstanding.
- C2 workers are constructing the finite Core syntax translation and admission
  for the complete kernel fixture. The callable-support component passed
  independent compilation and scope review and is registered in `check.sh`.
  No general compiler is counted complete yet.
- The cache-aware registered Lean baseline build and recursive audit passed:
  763 modules, 10,622 exact dependency reports and 1,885 local links/anchors.
  Only `propext`, `Quot.sound` and `Classical.choice` occur in the reports.
  New alignment modules receive separate checks before registration.
  The combined audit including `CoreClosing` and `CoreCallableSupport` also
  passed: 765 modules, 10,636 dependency reports and 1,891 links/anchors. For
  149 worktree files with newer copy timestamps, the audit verified byte equality
  with the baseline source and cache freshness against that source.
  A duplicate uncached baseline build was stopped deliberately; its exit 143 is
  not a verification result. No failing proof was bypassed.

### Increment 2 components

- `CoreSyntax` and `CoreTranslation` passed fresh independent compilation.
  They retain the finite graph and metadata, check the supported local shapes,
  and translate strict syntax with lexical owner mapping. Request, resource and
  cleanup equations and administrative-name separation are proved. Metadata
  authentication, fuel sufficiency and initial admission remain open.
- The test-only Rust exporter and generated 55-node fixture passed seven focused
  Rust tests, clippy and independent Lean kernel checks. Commit `83c9969` retains
  them and the admission-gap evidence. The manifest remains data, not a static
  authentication theorem. Actual-loop snapshots and the independent Core
  machine are separate batches; neither may assume calculus validity.
- The complete kernel admission fixture exposed a failed phase-transport
  argument: consuming saved owner demand can change a suffix request's protection
  bit. The negative row-certificate witness and a conditional separation repair
  component both passed independent compilation. Existing unwind ownership and
  uniqueness derive the new condition for disposing captures. The condition is
  now integrated into the clause interface; resume-only external demands remain
  unrestricted. The intended kernel fragment has not been reduced.
- C4.1 is reopened for D8's experimental admission repair. C4.2/C4.3 retain the
  locally verified D2 regressions and will be extended with the repair. The
  local completed count therefore changes from 3/3 for D2 to 2/3 overall; this
  records new work under the existing inventory, not a D2 regression.
- The independent graph-based `CoreMachine` and its examples passed fresh
  independent compilation. Named full-graph checks prove result 11 and writes
  `[7, 11]`, with only `propext`; focused cases cover lexical environments,
  exact selection, full-prefix resume, nested closing order and consumed-owner
  rejection. The first `rfl` attempt was stopped for excessive memory use;
  kernel-checked `decide` passes the same assertions. Both modules are registered
  in `check.sh`. The general value/configuration relation and simulation remain
  open, so C3's completed-deliverable count stays unchanged.
- Commit `042af37` retains the independent machine and registered checks. The
  actual-loop Rust observer also passed ten focused tests, a fresh independent
  rerun, clippy with warnings denied and formatting checks. It retains structured
  configurations and explicit observer exclusions. Review corrected the resume
  expectation to use nearest exact owner selection and made module normalization
  consistent across each trace. Snapshot-to-model conversion is the next batch;
  general correspondence is not established by these tests.
- The conditional closing-separation repair is locally verified at every changed
  capture constructor. The complete Boolean clause now has ordinary and
  protected row certificates; cleanup around the protected kernel body has
  source and authentication evidence. Focused builds passed for the fixture and
  M4 endpoints (449 modules) and the other changed runtime constructors (469
  modules; overlapping inventories). Independent fixture/coherence/M4 compilation
  passed with standard axioms only. A full normalized `Program`, translation
  bridge and general admission compiler remain open; C4.1 stays open until the
  complete kernel admission construction validates this repair in context.
- `CoreValueRelation` passed fresh independent compilation and review. It relates
  scalars, handles, tuple locations and lexical closures using the existing
  translator; proves heap extension and actual variable/resource lookup; and
  checks template expansion and shadowing. It retains finite closure closedness
  and nonrecursion evidence that static Core admission must still construct.
  Full configuration and transition correspondence remain open.
- `CoreStrictSteps` and the required lexical substitution lemmas passed fresh
  independent compilation and statement review. Completed application, bind and
  Boolean selection have actual Core successors, positive ordinary calculus
  steps and related lexical results. Both stack tails remain explicit and
  unchanged; their relation is still a separate obligation. The modules use
  standard axioms only and are registered in `check.sh`.
- `CoreAdministrativeSteps` passed fresh independent compilation and review.
  Its literal/variable/lambda entry and tuple-allocation witnesses retain current
  interpretation, actual successor, related result and decreasing rank. The
  allowed-family check and malformed-state negatives prevent unrestricted
  zero-step matching. Whole-frame/configuration correspondence remains open.
- Full normalized resource source/authentication construction reached a second
  declaration boundary, D9: the current consuming-recipe grammar has no suffix
  after resume. Fresh independent compilation verifies full normalized source/
  authentication evidence and rejection of the exact declaration plan. The
  structural request-footprint extension is the next bounded C2.4/C4.1 batch.
  The complete fixture and scope remain unchanged; no `Program` completion is
  claimed.
- D9's standalone `SourcePlainSuffixTransport` passed fresh independent
  compilation and review. Static request footprints and receiver checks derive
  the inserted suffix's pending checks, including resumed and discarded owner
  contexts. The actual plain frame is retained, with ordinary/unwind behavior
  distinguished. The verified `ClauseRecipe.suffix` extension now constructs the
  exact normalized declaration certificate. The affected M4 gate passed across
  450 dependency modules. Full kernel `Program` construction remains open.
- The actual Rust trace bridge passed independent verification: 91 snapshots,
  exactly 90 independent model transitions, terminal 11, writes `[7, 11]`,
  cleanup-start order and final resource release. Checker/comparison soundness
  and missing/extra-boundary rejection are kernel-checked with standard axioms.
  The fresh combined Rust run passed 18 observer/exporter tests. This is finite
  implementation evidence; full model/calculus simulation remains open.

- `CoreStrictFrames` passed fresh independent compilation and statement review.
  Ordinary saved frames retain lexical interpretations, and actual application
  focus/return has positive target transitions. Value-ready arguments retain the
  whole application until Core completes argument evaluation. Static PlainData
  authentication and the whole-stack relation remain open.

- The repaired grouped `cargo xtask verify` passed formatting, metadata, build,
  Clippy, tests and documentation checks: 2,896 tests passed, none failed and two
  explicit fixture-regeneration tests were ignored. The test-only exporter and
  observer now use the architecture scanner's established `_tests.rs` convention.
- A fresh full build of the 780 registered proof modules passed. The audit checked
  10,740 exact dependency reports and 1,945 local links/anchors, with only standard
  Lean axioms and no proof holes. Four subsequent modules passed independent
  dependency builds before registration: `CoreTranslationFuel`, `CoreStrictStack`,
  `CoreStrictPotential` and `CoreTypeSupport`. The additive audit then passed
  for all 784 registered sources, 10,781 dependency reports and 1,949 local
  links/anchors; it preserved the original 780 source hashes.
- Fuel sufficiency now follows from the existing graph checker. Type decoration
  preserves exact request rows and adds explicit retention data. The mixed-stack
  component and one graph-derived potential cover the proved value-ready
  application/tuple traversal cases. General admission, annotation authentication,
  reachable-state phase discipline and complete simulation remain open.
- `CoreKernelProgram` now constructs the complete normalized fixture's `Program`,
  including structural receiving-tail checks, root accounting and initial
  admission. The existing M4 finite-prefix endpoint applies. Fresh independent
  compilation and statement review pass without supplied certificates or future
  execution premises. This validates D8/D9 in context and closes C4.1 for the
  identified repairs: C4 returns from 2/3 to 3/3. New findings may reopen it.
  The actual exported graph bridge and general C2 admission remain open.
- `CoreAdministrativeTransport` extends value entry and tuple allocation to
  existing mixed ordinary stacks while preserving one exact target and the
  strict potential. `CoreOperationSignatures` constructs exact declaration-port
  lookup, rejects conflicting aliases and proves retention independence. Both
  passed fresh independent compilation and statement review. Runtime owner-scope
  coverage and authentication of declaration inputs remain separate obligations.
- The additive registered audit passed for 787 unchanged-or-freshly-compiled
  sources, 10,807 exact dependency reports and 1,952 local links/anchors. It
  preserved the previous 784 module hashes; only standard Lean axioms occur.
- `CoreOwnerMapBoundary` isolates a D5 relation-coverage gap: callable reentry
  succeeds in validated Rust, while a caller-wide owner map can make the current
  value interpretation impossible. Root translation and legal clause bindings
  remain sound. Fresh independent Lean and Rust CLI checks pass. The next C3.1
  repair separates lexical callable/frame maps from dynamic owner activations;
  it does not change the supported fragment or claim a runtime discrepancy.
  Its additive audit passes across 788 registered sources, 10,821 dependency
  reports and 1,954 local links/anchors, preserving the previous 787 hashes.
- `CoreBuiltinSignatures` passed fresh independent compilation and review.
  Every supplied cell entry is checked, primitive enrichment retains the whole
  table, and exact port erasure constructs existing builtin compatibility.
  The initial-example comparison is explicitly restricted to one finite domain.
  Functional operation enrichment and Rust registry authentication remain open.
- `CoreExportedAdmission` passed fresh independent compilation and review.
  Actual exported getter/application nodes retain their resource instantiation
  and typed lexical bindings. Source/Auth, current structural admission and
  independent accounting are constructed at the cell receiver. A general static
  graph derivation and the full exported initial `Program` remain open.
  Both new leaves are registered; the next combined audit follows the in-flight
  shared value-relation repair rather than auditing a changing proof tree.
- The lexical-value repair and all eight affected/dependent modules passed
  fresh independent compilation and review. Callable values now use certified
  empty capability maps; generic beta retains the caller's saved-frame map.
  `CoreCallableChecks` constructs the exact certificate from executable graph
  checks and feeds it into actual lambda entry. Post-beta administrative
  transport, individual saved-frame maps and reachable-state construction remain
  open; the new component does not close C3.1 or C3.2.
- A retained higher-order resource fixture returns Unit in validated Rust when
  an operation accepts and invokes a pure closure retaining a cell. The isolated
  D4 support refinement still needs a justification preserving the operation's
  declared input port. This remains within C2.3, without a new exclusion.
- The combined audit passes for 791 registered modules, 10,851 exact dependency
  reports and 1,958 local links/anchors. Eleven new or transitively affected
  modules received fresh independent compilation; 780 unchanged source/report
  pairs were retained from the verified snapshot. Source hashes, import order,
  standard axioms, trust scan and artifact checks pass.
- `CoreHigherOrderSupport` passed fresh independent compilation and statement
  review. Its positive source request and negative authentication results expose
  the exact D4 gap for a retained closure passed through an unchanged pure
  operation input. The cell-request refinement changes that input port; merely
  removing the capture guard would invalidate existing substitution and
  resource-exit support arguments. C4.1 is reopened, changing C4 from 3/3 for the
  previous repairs to 2/3 overall. This does not refute every translation or
  change the supported fragment. The next comparison is independent retention
  versus proved capture erasure. This new leaf is independently verified;
  the next combined audit waits for the ordinary-stack edits to freeze.
- `CoreGraphAdmission` now constructs source/authentication evidence and a
  synchronized translation from a separate static graph derivation. Its ordinary
  rules include binary pairs, both Boolean arm orders, Unit match and a checked
  nonrecursive function wrapper. Concrete getter, setter and three write-site
  derivations use the exported graph. The binding spine remains conditional on
  handler41; handler, resume/discard, cleanup and resource constructors are not
  yet present. The next batch must make resource environments, owner contracts,
  worlds and lexical maps recursive indices before adding those cases.
- The single ordinary-stack relation now carries explicit per-frame maps.
  `beta_admin_caller_bind` composes actual beta, ranked integer entry and caller
  return, restoring the saved map and supplied scope while preserving older
  annotations. Generic value/tuple transport and covered application/tuple
  traversal use the same relation and potential. This closes the identified
  post-beta component gap, not reachable-state authentication or full simulation.
- Fresh independent compilation and statement review passed for both batches.
  The combined audit covers 793 modules, 10,881 exact dependency reports and
  1,964 local links/anchors: six new or affected modules were freshly compiled,
  and 787 unchanged verified source/report pairs were retained. Standard axioms,
  source hashes, import order, trust, whitespace and artifact checks pass.
  Changed-section Markdown lint passes. The full DN-0033 lint retains its 14
  pre-existing line-length findings; comparison with the preceding revision
  found no new lint finding.
- The D4 interface review also identified fixed rich callable refinements in
  ordinary higher-order helpers, branch results and operation outputs. The
  design note now records these boundaries. A payload-indexed input prototype
  alone would not resolve general higher-order admission; this changes the next
  repair estimate from a local guard adjustment to a bounded interface experiment.
- `CoreOrdinaryCompletion` and its narrow potential-family extension passed
  fresh independent compilation and statement review. Unit/Boolean completion
  restores saved maps and scopes; value-ready bind/Unit/Boolean entry decreases
  the shared potential. Singleton wrapper entry derives its template successor
  from current closing evidence. Exported wrapper54/function50 and the supplied
  main/Unit-match prefix reach effect48. Whole-program reachability, non-value
  traversal and effect-frame correspondence are not claimed. The next runtime
  batch adds exact handler/cell boundaries so ordinary tails compose beneath
  them; it does not introduce an opaque effect suffix.
- The graph compiler now indexes resources, contracts, worlds and owner maps
  recursively. Resume/discard constructors and `Clause.compiled` passed fresh
  independent compilation: actual clause40 retains condition30, resume32/Unit31,
  binder10, write11/bind38 and discard39. A finite row-uniqueness lemma resolves
  an elaborator transport mismatch without an extra premise. Handler41,
  cleanup and resource48 construction remain open; protected offers retain
  their existing separate obligations.
- The combined audit passes for 794 registered modules, 10,895 exact dependency
  reports and 1,965 local links/anchors. Four new or transitively affected
  modules received fresh independent compilation; 790 unchanged verified
  source/report pairs were retained. Standard axioms, source hashes, import
  order, trust, whitespace and artifact checks pass. Changed Markdown passes
  lint. Product Rust is unchanged by this batch.
- `CorePayloadRefinement` passed fresh independent compilation and review as
  partial interface evidence. It constructs actual capture/call/beta steps and
  selected body checks for distinct same-port closures, with computed retained
  support and an executable check tied to the actual receiving stack. Inner
  reception accepts the cell-retaining closure; outer reception rejects it.
  The old lambda authentication and fixed rich operation-table obstructions
  remain explicit. Formal helper/branch/result transport and full initial
  admission remain open; the shared interface has not been selected for rewrite.
- Four Rust regressions retain the corresponding Core evidence. All ten
  cleanup/alignment integration tests pass, including exact same-operation and
  same-type checks on distinct lowered closure bodies, inside/outside resource
  reception, and both ordinary-helper branch choices. Targeted clippy with
  warnings denied and formatting checks pass. No product semantics changed.
- The combined audit including the bounded prototype passes for 795 modules,
  10,921 exact dependency reports and 1,971 local links/anchors. Five new or
  affected modules have fresh independent compilation evidence; 790 unchanged
  verified source/report pairs are retained. The design-note lint still has its
  same 14 pre-existing findings, with no new finding.
- Full `cargo xtask verify` for the integrated increment passes: 2,900 tests
  passed, none failed and two were ignored. Formatting, metadata, build, Clippy
  and documentation checks also passed. This includes the four new higher-order
  regressions; it does not establish the missing general correspondence proof.
- `CoreRefinementJoins` completes the bounded helper/branch assessment and passes
  fresh independent compilation with eleven standard-axiom reports. Actual
  helper traces and branch support checks pass, while structural inversions
  prove the current fixed helper input and homogeneous branch result cannot
  admit the two unchanged closure bodies. This rules out treating the earlier
  per-payload prototype as a complete interface repair. Callable inputs/results,
  branch joins and continuation refinements remain part of C4.1.
- Exact handler/cell entry and normal-return components now compose with mapped
  stacks. A shared resource initializer relation covers both pushed and
  value-ready flattened phases; its entry decreases the common potential.
  The exported resource48 prefix reaches body47 by actual initializer evaluation,
  acquisition and generated handle binding. Six new or affected modules pass
  fresh independent compilation. The supplied key7 starting counter is not a
  reachability proof. Fresh history, target-world equality, scope authentication,
  captured owners and cleanup still require integration.
- The integrated boundary/guarded-body increment passes the combined audit for
  799 registered modules and 10,957 exact dependency reports. Ten new or affected
  modules have fresh independent compilation; 789 unchanged verified
  source/report pairs are retained. Only standard axioms occur, with no proof
  holes or new lint findings. Product code and tests are unchanged since the
  successful 2,900-test gate.
- `CoreInitialPrefix` connects twelve actual transitions from the exported
  `CoreMachine.initial` state to body47 with acquired key0. Every intermediate
  state has the component relation; silent steps use named strict-potential
  witnesses, and five positive target steps yield the exact ledger
  `[resource 0]` created and nothing discharged. `CoreAllocationHistory` derives
  historical resource freshness from actual initial executions and connects it
  to that prefix and checked traces. These are raw execution and resource-key
  results; M4 validity, annotation authentication and target-world correspondence
  remain open.
- `CoreCallablePlanRefinement` constructs actual-row M4 static certificates and
  their installation-support checks from `PurePlan`. Existing accounting lemmas
  preserve the exact context and root when relating each actual body to the
  common pure contract. The retained-cell instance preserves computed support
  and the inner-accept/outer-reject checks. This closes the bounded certificate
  experiment, not the lambda/application/result interface repair. It does not
  assume successful execution or grant arbitrary continuation admission.
- All three leaves pass fresh independent warnings-as-errors compilation and
  statement review. The selected-source integration audit passes for 802
  registered modules, 10,999 exact dependency reports and 1,981 local links or
  anchors. Three new modules have fresh independent compilation evidence; the
  799 unchanged source/report pairs are retained. The audit uses the committed
  graph compiler while its handler extension is still being implemented; that
  unfinished extension is outside this increment's verification claim. Staged
  proof sources match the audited manifest. Trust, import order, whitespace and
  artifact checks pass, with no new Markdown lint findings.
- The handler compiler now constructs actual handler41 and its declaration
  modes. A separate recursively checked finite clause-body witness supplies
  port typing and actual translation even when an offered mode is unavailable.
  The finite usage checker supplies one-shot consumption. `Spine.closedCompiled`
  constructs resource body47 without an input handler derivation; resource48
  and the whole initial `Program` remain open. Independent statement review and
  fresh compilation pass.
- `CoreHandlerPrefix` extends the same actual initial execution to handler41's
  body29 in twenty Core transitions, retaining the component relation at every
  intermediate state and the exact creation ledger. It stops before cleanup
  registration. `CoreAllocationCorrespondence` derives successor resource
  history from actual steps and local event matching. Its fixed initial-prefix
  instance constructs target `RunSteps`, resource world `[0]` and freshness
  without supplied world equality. Neither result establishes M4 validity or
  broader owner freshness. Both leaves pass independent compilation and review.
- The combined handler/history audit passes for 804 registered modules, 11,030
  exact dependency reports and 1,983 local links or anchors. Three new or
  changed modules have fresh independent compilation evidence; 801 unchanged
  verified source/report pairs are retained. The isolated source snapshot now
  copies and hashes the pinned Lean toolchain file: omitting it initially
  selected the newer global compiler and failed to load a dependency. The
  corrected build uses Lean 4.33.1. Trust, import order, whitespace and artifact
  checks pass. Product Rust remains unchanged since the 2,900-test gate.
- The next bounded C4 checkpoint is contextual row refinement into actual
  post-beta body admission. It transports current `Code`, its exact
  `CodeChecked` certificate and same-root `Accounting.Run`, then reuses actual
  authenticated substitution. Pre-beta application admission, heterogeneous
  callable inputs/results and continuation transport remain separate work.

| Package | Completed / total identified items | Current state | Outstanding items | Dependencies or blockers | Estimated remaining active work |
| --- | --- | --- | --- | --- | --- |
| C1 | 5 / 5 | Integrated comparison and discrepancy inventory | Maintain findings | None | Complete; records follow new evidence |
| C2 | 0 / 4 | Handler41 and actual resource-body spine compiler integrated | Full graph admission, metadata authentication, general compiler | Resource constructor/root admission; higher-order refinement gap | Resource/root source batch 1–2 hours; full estimate unresolved |
| C3 | 0 / 5 | Twenty-transition initial prefix and resource correspondence integrated | Reachable annotations, remaining phases, captured owners, cleanup and full simulation | Static annotations and state/ownership relation | Cleanup-registration batch 1–2 hours; full estimate unresolved |
| C4 | 2 / 3 | D2/D8/D9 repairs verified; contextual refinement transport being implemented | Resolve retained support and callable refinements without changing declared ports | Lambda/application/result and M4 preservation transport | Bounded post-beta checkpoint 45–75 minutes; full repair estimate unresolved |
| C5 | 0 / 4 | Product gate and 804-module combined audit passed | Integrated theorem, final coverage, grouped verification and independent review | C2–C4 | No useful total until the higher-order interface is settled |

## Verification

Use focused Rust regressions and grouped Lean dependency builds during each
increment. At integration run `cargo xtask verify`, the one-shot `check.sh`,
the existing recursive proof/axiom audit, Markdown lint, changed-link checks and
authority review. Inspect theorem statements and dependencies as well as results.
Independent review covers source semantics before code quality and theorem scope.

## Discoveries

Historical proof sections retain old open obligations. Current endpoint code and
the final M0–M4 evidence determine the baseline; historical prose must not reset
completed milestones.

## Deviations

No scope change. The C1 fragment and transition inventories remain the acceptance
boundary for C2–C5; verified components do not replace their full coverage.
