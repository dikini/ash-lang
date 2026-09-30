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

| Package | Completed / identified | State | Outstanding | Dependency / next estimate |
| --- | --- | --- | --- | --- |
| C1 | 5 / 5 | Committed, verified and reviewed; D8/D9 classified | Maintain findings through integration | Under 1 active hour for records |
| C2 | 0 / 4 | Complete normalized kernel admission and exact declaration-port construction verified | Actual graph bridge, authenticated metadata and general static compiler | Exported administrative syntax and builtin compatibility next, about 1–2 active hours; generalization estimate unresolved |
| C3 | 0 / 5 | Finite Rust trace, strict steps, mixed-stack value transport and shared potential verified | Reachable configuration relation, transitions and observations | Lexical owner scopes and remaining ordinary cases next, about 1–2 active hours; full proof estimate unresolved |
| C4 | 3 / 3 for identified repairs | D2 regressions and D8/D9 complete normalized admission verified | Maintain resolution as C2/C3 discover further obligations | No current demonstrated unresolved discrepancy |
| C5 | 0 / 4 | Product and 780-module proof gates passed; seven new modules separately verified | Integrated theorem, current checks and final scope audit | Depends on C2–C4 |

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
