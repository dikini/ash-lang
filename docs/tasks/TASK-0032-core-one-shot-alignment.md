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

Use GPT-6.1 Sol for orchestration, analysis and integration, and GPT-6.1 Sol
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
- Initial verified orchestrator assignment: `gpt-6-astra`, high reasoning.
- The user paused development, then resumed on 2026-10-01 with an updated
  objective assigning `gpt-6.1-sol` to orchestration. The resumed assignment is
  verified as `gpt-6.1-sol`, xhigh reasoning; implementation workers retain
  `gpt-6.1-sol` with medium reasoning. The accepted scope and C1–C5 inventory
  remain unchanged.
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

### Current deliverable board — 2026-10-02 06:52 UTC

The package counts measure whole-fragment acceptance. This board shows movement
inside those packages. Each row names a fixed deliverable or subcase inventory;
its phase changes only when the corresponding evidence exists. Constructor
counts measure implemented cases, not equal effort or a percentage of C2.

| Deliverable or inventory | Implemented | Independently reviewed | Current-source verification | Integrated commit | Change since paused checkpoint `f1fc1e4` |
| --- | --- | --- | --- | --- | --- |
| Finite original cell API and resource checker: nine body forms | **9 / 9 forms** | **Passed** | **Ten schema, twenty checker and fifteen probe reports** | **This checkpoint** | **Finite original data → computed fresh Source/Auth and all-identity private families** |
| Paired resource read/return: two exact-environment consumers | **2 / 2 consumers** | **Passed** | **Two reports; full actual rich/storage environments retained** | **This checkpoint** | **Formal return → actual translated handle bind and request before return** |
| Cleanup registration/body/start: nine producer and six probe reports | **15 / 15 reports** | **Passed** | **Exact three-step active-scope prefix** | **This checkpoint** | **Registration-site lineage → same original running start** |
| **Finite-resource/registration six-leaf batch** | **6 / 6 modules** | **6 / 6** | **62 additional ordered reports; 61 new names** | **This checkpoint** | **Compiled once in 9.4 seconds; 931 unchanged artifacts reused** |
| Original cell registry and initial-admission connection | Compatibility/transport implemented locally; root authoring | Pending | Eight local compatibility/transport reports pass; closed root construction active | Not integrated | Initial Program facets must be constructed from finite checks |
| General cleanup entry above a running suffix | Implemented locally | Pending | General producer, nested Generated.cleanup path and affected overlay pass; dependency freeze pending | Not integrated | Exact registered history and current-site/anchor providers remain distinct |
| Same-graph callable annotation gate | Yes | Passed | Passed | `d2f26e1` | Unchanged |
| Rich initial Site and first-step connection | Yes | Passed | Passed | `d2f26e1` | Unchanged |
| Actual capture/beta/bind/resume ownership receipts | Yes | Passed | Passed | `d2f26e1` | Unchanged |
| Cleanup registration/entry/return origin receipts | Yes | Passed | Passed | `d2f26e1` | Unchanged |
| Registry-derived operation metadata export | Yes | Passed | Passed | `d2f26e1` | Unchanged |
| Generated operation declaration checker | Yes | Passed | Passed | `d2f26e1` | Unchanged |
| **Retained six-deliverable batch** | **6 / 6** | **6 / 6** | **6 / 6** | **`d2f26e1`** | **Unchanged** |
| Recursive C2 source/authentication checker: 16 Code constructors | **14 / 16** | **14 / 16** | **14 / 16** | **`ab71211`** | Unchanged |
| Missing rich source constructors: cleanup and resource | **2 / 2** | **2 / 2** | **2 / 2** | **`acb7724`** | **1 / 2 → 2 / 2; finite checker remains 14 / 16** |
| Bounded returned-storage and actual-initializer origin producer | Yes | Passed | Passed | `ab71211` | Unchanged |
| Running cleanup capture/restore/finish: inside-anchored path family | Implemented | Passed | Passed | `3fad8e8` | Unchanged |
| Literal-site ancestry through actual capture/beta/bind | Implemented | **Passed** | **Passed** | `3fad8e8` | Unchanged |
| **Bounded C3 two-deliverable batch** | **2 / 2** | **2 / 2** | **2 / 2** | **`3fad8e8`** | **Unchanged** |
| Same-literal paired initializer/substitution/application consumer | Implemented | Passed | Passed | `b04701b` | Unchanged |
| Past mapped handler/clause installation and actual capture/resume receipts | Implemented | Passed | Passed | `b04701b` | Unchanged |
| **Paired C2/C3 two-deliverable batch** | **2 / 2** | **2 / 2** | **2 / 2** | **`b04701b`** | Unchanged |
| Parameterized storage recipes and generic higher-order formal return from a fresh scope | Implemented | Passed | Passed | `bfc72e1` | Unchanged |
| General installation/completion history, heap transport and guarded actual capture | Implemented | Passed | Passed | `bfc72e1` | Unchanged |
| **General-history/recipe two-deliverable batch** | **2 / 2** | **2 / 2** | **2 / 2** | **`bfc72e1`** | Unchanged |
| Same-history nearest owner selection and actual full-prefix resume | Implemented | Passed | Passed | `a336e3b` | Unchanged |
| Literal captured-callee ordinary call: separate original callee recipe/map and actual caller argument | Implemented | Passed | Passed | `d03a333` | Unchanged |
| Exact same-history handler selection and actual capture from physical lookup | Implemented | Passed | Passed | `9ccc2fb` | Unchanged |
| Checked outside-anchor running receipt restoration through actual full-prefix resume | Implemented | Passed | Passed | `9ccc2fb` | Unchanged |
| **Handler-selection/outside two-deliverable batch** | **2 / 2** | **2 / 2** | **2 / 2** | **`9ccc2fb`** | Unchanged |
| Actual caller bind/reset/return factories: five named reports | **5 / 5** | **5 / 5** | **5 / 5** | **`0d6965c`** | Unchanged |
| Guarded cleanup activation: two named marker-return/finish factories | **2 / 2** | **2 / 2, passed** | **Exact current-source replay passed** | **`c5fb370`** | Unchanged |
| Original closed initializer runtime binding v1: two named reports | Static inversion valid; combined consumer vacuous | **Rejected: contradictory inputs** | Kernel contradiction confirmed independently | Excluded | Unchanged; v2 repair is a separate applicable path |
| Runtime binding repair v2: three named value-ready/check-lambda reports | **3 / 3** | **3 / 3, passed** | **Exact current-source replay passed** | **`c5fb370`** | Unchanged |
| Captured substitution: eight named replacement/body receipts | **8 / 8** | **8 / 8, passed** | **Exact current-source replay passed** | **`c5fb370`** | Unchanged |
| Running occurrence: four actual start/bind/beta/history reports | **4 / 4** | **4 / 4, passed** | **Exact current-source replay passed** | **`c5fb370`** | Unchanged |
| Captured lambda constructor: nine same-family reconstruction reports | **9 / 9** | **9 / 9, passed** | **Exact current-source replay passed** | **`c5fb370`** | Unchanged |
| **Five-component capture/origin batch** | **5 / 5** | **5 / 5** | **5 / 5; 26 reports** | **`c5fb370`** | Unchanged |
| Captured recipe transport: thirteen named checker reports | **13 / 13** | **13 / 13, passed** | **Exact current-source replay passed** | **`f1fc1e4`** | Unchanged |
| Running capture/resume: eight named generated-marker reports | **8 / 8** | **8 / 8, passed** | **Exact current-source replay passed** | **`f1fc1e4`** | Unchanged |
| **Recipe/capture/initializer three-component batch** | **3 / 3** | **3 / 3** | **3 / 3; 26 reports** | **`f1fc1e4`** | Unchanged |
| Runtime closure connection: five named initializer-head/generated-binding reports | **5 / 5** | **5 / 5, passed** | **Exact current-source replay passed** | **`f1fc1e4`** | Unchanged |
| Outer lambda evaluation: four named origin/evaluation reports | **4 / 4** | **4 / 4, passed** | **Exact current-source replay passed** | **`2de8f55`** | **Reviewed → registered and verified** |
| Clause execution, tuple heap transport and full-prefix resume: thirteen named reports | **13 / 13** | **13 / 13, passed** | **Exact current-source replay passed** | **`2de8f55`** | **Frozen → reviewed, registered and verified** |
| Local handler installation/capture/return: seven named reports | **7 / 7** | **7 / 7, passed** | **Exact current-source replay passed** | **`2de8f55`** | **Frozen → reviewed, registered and verified** |
| **Outer/clause/local-handler three-component batch** | **3 / 3** | **3 / 3** | **3 / 3; 24 reports** | **`2de8f55`** | **All three finished components integrated together** |
| Recursive closure origins: four diagnostic reports | Dependency assessed | Diagnosis checked locally | Four diagnostic reports passed | Not registered | Diagnostics remain assessment evidence; producer is below |
| Recursive literal-lambda ordinary prefix and consumers: nineteen named reports | **19 / 19** | **Passed** | **Exact current-source replay passed** | **`aa71286`** | **Diagnostic → conditional arbitrary-length producer, evaluated lambda and nearest lookup** |
| Generated running callback chronology: twelve named producer classes | **12 / 12 classes** | **Passed** | **Twenty current chronology reports; initial callback retained; new composition/cycle rows below** | **`aa71286`** | **Local factories → initial exact-endpoint callback; current nested completion is below** |
| Current-operation preparation and phase-local cursor: thirteen named reports | **13 / 13** | **Passed** | **Exact current-source replay passed** | **`aa71286`** | **Assessment → bounded conditional interface; full footprint/ledger origin remains open** |
| Preparation exact-budget/finite-key/reservation probes: twenty-one named reports | **21 / 21** | **Passed** | **Exact current-source replay passed** | **`aa71286`** | **New represented-operation counterevidence** |
| Discard failure-boundary Rust QA: success, pre-consumption and post-consumption cases | **3 / 3 cases** | **Passed** | **Seven-test related group passed independently** | **`aa71286`** | **New actual disposal-refusal evidence; internal shape, no general reachability claim** |
| **Recursive/chronology/preparation four-leaf batch** | **4 / 4 leaves** | **4 / 4** | **4 / 4; 64 reports** | **`aa71286`** | **Frozen → reviewed, registered and verified together** |
| Resource foundation: fifteen changed modules and three leaves/probes | **18 / 18 sources** | **Passed** | **53 consumers + three modules; 444 reports** | **`acb7724`** | **Resource rule and full pointwise transports supplied** |
| History composition: capture outputs and resume/handler/spent heads | **4 / 4 interfaces** | **Passed** | **Twenty chronology reports passed** | **`acb7724`** | **Equality failure → same-current structural decomposition** |
| Computed normal cleanup completion: nine named reports | **9 / 9** | **Passed** | **Passed** | **`acb7724`** | **Running owner → restored saved result/scope, retired owner** |
| SAME-start nested cycle: eighteen actual Core steps including start | **18 / 18 steps** | **Passed** | **Eight nested reports, seven simple probes and six guards** | **`acb7724`** | **Six-edge callback → seventeen-edge nested path through completion** |
| Activation-map preparation: fourteen reports and twenty probes | **34 / 34 reports** | **Passed** | **Passed** | **`acb7724`** | **Computed requests and same endpoint agreement** |
| Runtime metadata Rust QA: two computed-budget tests | **2 / 2 tests** | **Passed** | **Passed** | **`acb7724`** | **Exact/one-short diagnostics and observation prefix; bounded internal shape** |
| **Resource/cycle/metadata coherent batch** | **3 / 3 components** | **3 / 3** | **64 affected modules; 80 additional reports** | **`acb7724`** | **Compiled once; 863 unaffected artifacts reused** |
| Current ticket bounds: twelve named operation families | **12 / 12 families** | **Passed** | **Seven producer reports + eleven probes/five interfaces** | **`bbe7317`** | **External current TicketBound → produced from original start** |
| First acquired map origin: two indexed transition consumers | **2 / 2 consumers** | **Passed** | **Nine producer reports + thirteen probes** | **`bbe7317`** | **Supplied map agreement → derived empty and installed agreement** |
| **Current-bound/map-origin two-component batch** | **2 / 2 components** | **2 / 2** | **Four fresh leaves; forty additional reports** | **`bbe7317`** | **927 unchanged artifacts reused; 3.5-second compile** |

The cleanup, site-lineage and past-frame rows are components of C3.1/C3.2;
the paired-operand row serves C2.3/C4.1. They are not new package acceptance items.
Each two-leaf batch records bounded component progress, not whole-fragment acceptance.
Its checks cover the named paths; unconditional caller activation guards, armed
projection and disposal history remain open. A phase change means the stated
check passed. An unchanged row records no new result.

Retained implementation and verification summary:

- The recursive checker retains 14 reviewed and verified forms. Cleanup recursively constructs source/authentication from the same
  callback and body. Resume/discard use exact owner insertion, numeric shadow,
  scope, policy, allowance and held guards without comparing full contracts by
  signature. Handler and resource are the two missing forms.
- Both missing rich source constructors, cleanup and resource, and their
  pointwise transports are retained: 2/2. Full contracts and public plans/rows
  remain fixed. Finite handler/resource checking remains open at 14/16.
  The bounded returned-storage producer is retained after
  review; it derives actual initializer origins and exact application/substitution
  contracts while preserving the retaining-closure rejection.
- The preceding checker/storage checkpoint `ab71211` adds 28 standard reports.
  Its audited assembly covers 893 registered modules and 11,842 exact reports. All 29 changed
  cleanup reverse consumers were independently replayed in the 38-module review
  with 299 reports. The other 862 modules retain their fresh current-source
  association and identical direct-import hashes. This is an audited assembly,
  not a new uncached build of all 893 modules.
- The preceding running-cleanup checkpoint `d2f26e1` constructs actual capture, protected
  disposal rejection and full-prefix resume/finish when the original scope path
  is anchored inside the same captured suffix. Independent replay passes all
  twelve reports and the public interface probe. This checkpoint retains the
  transport alongside literal-site ancestry: initial/selected-clause/child
  receipts and actual capture/beta/bind factories. An ancestry receipt records
  enclosing-handler metadata and a strict postorder site bound, not a whole
  execution ancestry trace. At that checkpoint, outside-anchored restoration
  and armed projection remained open. Checked outside restoration is now retained;
  general changed-tail activation and armed projection remain open. Canonical
  maps and dynamic ticket freshness alone do not supply those providers.
- The six-deliverable batch remains retained in unsigned commit `d2f26e1`. Its
  fresh 891-module build and full Rust verification remain valid for unchanged
  Rust sources: 2,902 tests, no failures and two intentionally ignored tests.

The retained checker forms are unit, Boolean, integer, activation reference,
variable, pair, bind, application, request, branch, lambda, cleanup, resume and
discard. The count measures bounded support in the annotation language, not
acceptance of every composition. Finite structural instructions do not validate
arbitrary higher-order Contract/Plan/Rows origin. Interior graph metadata,
registry/owner origin and runtime captured-value admission remain C2 obligations.
The storage producer separately establishes storage/domain/result receipts;
it is not a full typechecker or runtime closure relation.

The preceding cleanup/site checkpoint `3fad8e8` retains two reviewed leaves and
25 reports in its 895-module assembly. The paired checkpoint `b04701b` adds the paired-operand
consumer and past mapped-frame installations: both reviewed, fresh compiled and
retained. Their 24 reports reproduce the reviewed source and artifact bytes;
15 paired-origin public probes and both existing retaining-value/template
negatives pass unchanged. All 895 unchanged modules retain exact parent source,
log, artifact and direct-import associations. That preceding assembly has 897
modules and 11,891 ordered standard-only reports. No Rust sources changed.

The preceding checkpoint `bfc72e1` retains the reviewed general-history and recipe leaves. Fresh
integration reproduces their exact source/artifact bytes and 27 standard-only
reports. That preceding assembly has 899 registered modules and 11,918 ordered
reports; all 897 unchanged modules retain their preceding exact source/log/artifact
and direct-import associations. This is an audited assembly, not a new uncached
build of every module. No Rust sources changed.

The preceding checkpoint `a336e3b` adds eight owner/resume reports to GeneralHistory's preceding
seventeen. Fresh compilation of the full changed leaf reproduces all 25 reviewed
reports and the exact source/artifact bytes. That preceding assembly has 899
modules, now with 11,926 ordered standard-only reports. All 898 unchanged modules
retain exact preceding source/log/artifact/direct-import associations. This is
one fresh changed leaf in an audited current-source assembly, not an uncached
build of every module. No Rust sources change.

The preceding checkpoint `d03a333` retains the reviewed literal captured-callee ordinary-call
consumer. Fresh integration reproduces its exact reviewed source/artifact bytes
and seven standard-only reports. That preceding assembly has 900 registered modules
and 11,933 ordered reports; all 899 unchanged modules retain exact preceding
source/log/artifact/direct-import associations. This is one fresh added leaf,
not an uncached build of every module. No Rust sources change.

The preceding checkpoint `9ccc2fb` retains the reviewed same-history handler-selection and checked
outside-origin consumers. Fresh integration reproduces both exact reviewed
source/artifact sets and twelve standard-only reports. That assembly has
902 registered modules and 11,945 ordered reports; all 900 unchanged modules
retain exact preceding source/log/artifact/direct-import associations.

Checkpoint `0d6965c` retains [CoreCallableCallerBarriers.lean](../design/direct-effects/one-shot/CoreCallableCallerBarriers.lean).
Its five named reports cover actual bind entry, current heap transport, beta
reset, original-suffix bind return and a same-active-caller clause miss.
Independent replay passes five reports and seven public probes. Fresh integration
reproduces its exact reviewed source/artifact bytes and five reports. That preceding
assembly has 903 registered modules and 11,950 ordered standard-only reports;
all 902 unchanged modules retain exact preceding source/log/artifact/direct-import
associations. This is one fresh added leaf, not an uncached build of every module.
No Rust sources change. Whole-fragment acceptance counts remain unchanged.

The preceding checkpoint `c5fb370` registers guarded cleanup activation,
captured substitution, corrected runtime binding, running occurrence and the
direct captured-lambda constructor. All five pass independent semantic review.
Fresh integration reproduces their exact reviewed source/artifact bytes and
26 ordered standard-only reports. The audited assembly contains 908 registered
modules and 11,976 reports. All 903 unchanged modules retain exact preceding
source/log/artifact/direct-import associations. This is five fresh leaves in an
audited assembly, not an uncached build of every module. No Rust sources change;
the earlier full Rust verification remains the Rust evidence.

The preceding intermediate two-leaf assembly registers
[CoreCallableCapturedRecipes.lean](../design/direct-effects/one-shot/CoreCallableCapturedRecipes.lean)
and [CoreCallableRunningCapture.lean](../design/direct-effects/one-shot/CoreCallableRunningCapture.lean).
Both pass independent review. Fresh integration reproduces their exact reviewed
source/artifact/log bytes and 21 ordered standard-only reports. The audited
assembly contains 910 registered modules and 11,997 reports. All 908 unchanged
modules retain exact preceding source/log/artifact/direct-import associations.
This is two fresh leaves in an audited assembly, not an uncached rebuild of
every module. No Rust sources change.

Checkpoint `f1fc1e4` also registers
[CoreCallableInitializerHead.lean](../design/direct-effects/one-shot/CoreCallableInitializerHead.lean).
It extracts the same original nearest-binding initializer and full bind path,
replays its original rich/storage checks, and uses actual three-step initializer
evaluation to derive the ValueRel and completed binding environment. The same
lambda family and finite/storage checks are then constructed from that value.
Independent review passes five reports, six probes and the two unchanged
retaining negatives. Fresh integration reproduces exact reviewed source,
artifact, log and ordered reports. This scope is one closed initializer; outer
callee evaluation and general runtime closure admission remain open.

That preceding audited assembly has 911 registered modules and 12,002 standard-only
reports. Its 910 preceding source/log/artifact/direct-import associations are
unchanged. Across `f1fc1e4`'s three new leaves, 26 reports have fresh exact
reviewed matches; all 908 modules from parent `c5fb370` remain unchanged.

Current parallel checkpoints:

| Existing obligation | Previous report | Current phase and result | Next observable output | Estimated active work |
| --- | --- | --- | --- | --- |
| C2.1 / C2.3 | Resource foundation absent | **Foundation integrated:** both missing source constructors, varying Plan/Rows transport and paired-formal receipts | Finite original-template handler/resource annotations with Source/Auth outputs | Next checkpoint 2–4 active hours; C2 range 15–26 agent-hours |
| C3.1 / C3.2 | Nested cycle uninstantiated | **Completion integrated:** 17 post-start edges/18 Core steps, exact prefix and original receipt | Current activation/TicketBound/guard providers; projection/disposal | Next checkpoint 2–4 active hours; C3 range 16–29 agent-hours |
| C3.4 | Preparation with supplied ledgers | **Metadata slice integrated:** acquisition 2n+3/request 3 + scan, endpoint agreement and two Rust tests | Actual indexed C2 map/observer/ledger origins and remaining metadata consumers | Within existing C3.4 range; wider providers open |
| C3.2 | Outside restoration integrated | **Unchanged:** physical selection and outside-anchor receipts | Current route/readiness and activation guards | C2 and chronological transport |

The new constructor closes the particular coupling gap between substituted body
receipts and the private family of the whole returned lambda. It evaluates the
original family at the exact restored lexical environment and actual call,
computes the new private Plan/full Rows, and constructs that whole lambda from
the same transformed family. This is existing C2.3 work, not a new acceptance
item. General higher-order admission still needs general initializer/resource origins,
validated metadata production, varied full storage contracts, resource construction
and the remaining handlers. The new prefix producer covers literal lambda
initializers under supplied original check successes.

Runtime binding v1 remains excluded: its nonvalue initializer focus contradicted
ValueRel for the same original Code. The repaired v2 proves an applicable path
for a current closed original lambda initializer, using its actual successful
check and evaluation; the administrative rank decreases. It does not establish
open/evaluating or capture-substituted initializer lineage.

RunningOccurrence constructs local actual start/bind/beta factories from the
same original running receipt and current histories. CleanupActivation derives
actual spent-marker Unit return and normal finish with current inside or checked
outside guards. Those guards remain inputs. The integrated RunningCapture
checkpoint derives actual capture above the selected tail handler and immediate
live-head resume with a generated marker. These preceding local factories did not establish continuous callback/clause
chronology or heap-changing transport; the resumed clause leaf adds bounded
actual tuple heap transport. The new generated chronology connects twelve named operation classes; whole
reachable coverage remains open.
No universal intermediate scan-success claim is made. Changed-tail activation,
armed projection, disposal, rich successor preservation and whole simulation
remain open.

The resource foundation, generated nested normal completion and bounded
metadata slice are integrated. Finite static annotation construction and actual
current guard/origin providers remain next. General initial admission, whole
reachable simulation, changed-tail activation, projection/disposal and full
preparation remain existing obligations. The fragment and inventory stay fixed.

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
- `CoreCallableRefinementTransport` passes fresh independent compilation and
  review, including verification of all 436 transitive dependency source
  hashes. Its eight reports use standard axioms only. It transports current
  `Code`, its exact `CodeChecked` certificate and same-root `Accounting.Run`,
  then constructs actual post-beta admission by authenticated substitution.
  Identity, composition, pure-plan and pure-prefix constructors are included.
  Pre-beta application admission, heterogeneous callable inputs/results and
  continuation transport remain separate work.
- The identical-root interface cannot cover arbitrary branching bodies:
  accounting constructs a choice of requirement trees. DN-0033 now requires
  the next bounded checkpoint to transport checked roots and disposal
  annotations while preserving owner demand and the current budget. This
  extends D4's existing obligation; it neither changes the supported fragment
  nor adds an acceptance item.
- The combined audit including contextual refinement passes for 805 registered
  modules, 11,038 exact dependency reports and 1,984 local links or anchors.
  The new leaf has fresh independent compilation evidence; all 804 baseline
  source/report pairs are unchanged in the integration snapshot. Active resource
  and cleanup work is excluded from that snapshot. Trust, import order,
  whitespace and artifact checks pass; changed Markdown is clean except for
  the same 14 pre-existing DN-0033 lint findings.

- The resource compiler now constructs Source/Auth and translation for actual
  resource48 and exported root54, retaining the handle binding, Unit match,
  main closure and invocation. Resource hiding is proved over the actual body
  requirements. `Main.rootCompiled` has no supplied handler/resource or desired
  invariant premise. The worker's 464-module focused gate passes; complete
  actual-root `Program` certificates are the next C2 batch.
- The armed-cleanup relation retains the actual delayed action, lexical
  environment and callback. Its generic registration proof derives both body
  and callback interpretations from one current environment derivation. The
  concrete initial chain now reaches guarded body24 in 24 Core transitions,
  with exact created ledger `[resource 0, cleanup 0]` and no discharged owners.
  Action27 remains unevaluated; a missing callback rejects. The worker's
  eleven-module focused gate passes. Capture, cleanup execution and M4 validity
  remain separate obligations.
- `CoreCallableRootRefinement` constructs changed normal/annotated roots and
  checked accounting while preserving owner demand and the current budget.
  Choice combines independently checked alternatives at the same phases.
  All eleven reports pass independent compilation with standard axioms, all
  437 dependency source hashes match the baseline, and peer review passes.
  This completes the bounded branch-accounting checkpoint, not callable value
  typing. The next C4 decision must address value judgments and substitution.
- The combined root/cleanup/refinement audit passes for 808 registered modules,
  11,074 exact dependency reports and 1,988 local links or anchors. Thirteen new
  or affected modules have
  fresh independent compilation evidence; 795 unchanged verified source/report
  pairs are retained. Trust, import order, whitespace and artifact checks pass.
  Rust is unchanged since the 2,900-test product gate.
- C4's next gate is now the contract-source value interface specified in
  DN-0033, rather than further accounting prerequisites. Test a common callable
  contract with private lambda-body evidence and independent retained support;
  prove compositional closed substitution and whole-expression helper/branch/
  returned-callable cases. Ordinary port typing or separately specialized
  legacy derivations do not satisfy this gate. A shared M4 migration still
  requires the current, pending and coherent value interfaces and their
  preservation boundaries to be connected.
- The ticket-history prerequisite is implemented and independently compiled:
  actual-step analysis derives `capturedTickets = range nextOwner`, freshness
  and history preservation through resume/discard. The repeated static
  handler/owner fixture issues distinct tickets; missing-clause dispatch issues
  none. Thirteen reports use standard axioms, and 26 dependency source hashes
  match the integrated baseline. The leaf is now registered and integrated;
  its worker has moved to the central C4 prototype. The grouped audit covers
  809 registered modules, 11,087 exact dependency reports and 1,990 local links
  or anchors. Fresh independent compilation covers the new leaf; 808 unchanged
  verified source/report pairs are retained. Active worker changes are excluded
  from this integration snapshot. Import order, trust, whitespace and artifact
  checks pass. Historical freshness does not establish live-owner uniqueness
  or agreement with the target ticket world.
- Review of the contract-source migration identifies a separate declaration
  obligation: `ExecutionSite.certified` certifies the actual plan. Existing row
  refinement transports code, resource checks and accounting, but does not
  construct that field for a different private body plan. The ordinary
  prototype must expose structural certification; handler-bearing private
  bodies must retain actual declaration evidence or prove its transport before
  M4 migration. This refines the existing D4 acceptance boundary without
  changing the supported fragment.
- `CoreGraphProgram` now constructs complete initial admission for actual
  exported root54, including declaration recipes, contextual code/resource
  certificates and independent accounting for its exact rows. The initial M4
  state is constructed and its machine equals the runtime relation's root
  target. All 23 reports pass fresh independent compilation with standard
  axioms; 475 dependency sources match the integrated baseline. The worker's
  477-module gate also passes. General metadata authentication and D4 remain
  open. The next bounded integration batch connects this state to actual Core
  execution through resource entry, using source-selected successor metadata.
  The combined audit passes for 810 registered modules, 11,110 exact dependency
  reports and 1,991 local links or anchors. The new leaf has independent
  compilation evidence; 809 unchanged verified source/report pairs are retained.
  Active runtime and callable-source work is excluded from the snapshot.

- `CoreAdmittedPrefix` connects the constructed initial M4 state to the first
  12 actual Core transitions, through resource entry and handle binding. All
  intermediate points have constructed valid target snapshots, using the same
  source-selected resource answer. Its five positive target steps issue only
  resource0. Seven dependency reports pass independent compilation against
  477 transitive source files. No desired successor validity is assumed.
- `CoreRequestFrames` and `CoreCaptureEntry` derive exact selected-clause
  translation, preserve parameter masking, relate recursive live/spent captures
  and prove nearest-handler selection with matching-cell barriers. The actual
  initial chain reaches clause body40 in 28 Core transitions, retaining the
  pending second request and cleanup callback. Its exact issued ledger is
  `[resource 0, cleanup 0, ticket 0]`, with no discharges. All 14 affected modules
  pass fresh independent warnings-as-errors compilation. Capture annotations
  and M4 validity remain separate; resume/discard and cleanup execution are next.
- The combined admitted-entry/capture audit passes for 813 registered modules,
  11,140 exact dependency reports and 1,994 local links or anchors. Fourteen
  modules have fresh independent compilation evidence; 799 unchanged verified
  source/report pairs are retained. Trust, import order, whitespace, artifacts
  and changed Markdown checks pass. Active shared handler-installation and
  callable-source changes are excluded. Rust is unchanged since the 2,900-test
  product gate.
- The D4 migration map now identifies each current, frame, operation, captured
  continuation and initial-admission consumer of the value interface. Source
  scalar requirements remain distinct from the contextual accounting root;
  transporting the latter cannot fill `Admitted.previous`. Effectful extension
  must index source evidence by exact operation/continuation contracts and
  execution scope. These are existing general-admission obligations, not new
  language features or additional acceptance items.
- The ordinary contract-source gate passes fresh independent compilation:
  11 source-judgment reports and 23 example reports. Whole helper, retained
  support, branch-result and returned-callable cases preserve one public
  contract and private body evidence. The returned-callable trace now includes
  its actual invocation; review rejected stopping at the caller's final bind.
  Legacy `Auth` and M4 admission are not claimed. The next C4 batch adds an
  authenticated source interface with scalar requirements and exact global
  operation/owner/scope indices, tested across an operation boundary.
- `CoreAdmittedHandlerPrefix` connects the same resource answer and source-
  selected frame/handler data through 20 actual Core transitions and nine target
  events, with every intermediate target admitted. Supplied occurrence0 is
  proved fresh from the current empty history. The final world/history are
  `[0]`, issued ledger is `[resource 0]`, and nothing is completed. The shared
  installation proof is factored once with the old existential wrapper retained.
  All 169 affected registered modules and the three new leaves pass fresh
  independent compilation. A temporary worker model-capacity failure recovered
  on retry without substituting the required model.
- The combined installation/contract-source audit passes for 816 registered
  modules, 11,179 exact dependency reports and 2,002 local links or anchors.
  Fresh independent compilation covers 172 affected or new modules; 644
  unchanged verified source/report pairs are retained. Import order, trust,
  whitespace, artifact and changed Markdown checks pass. Active resume and
  next-stage admission work is excluded from this snapshot. Rust remains
  unchanged since the 2,900-test product gate.

- `CoreResumeFrames` and `CoreResumeEntry` extend the same runtime chain to
  first resume completion after 35 actual Core transitions. The exact owner
  cut restores the captured frames, caller frames, spent marker and outside
  frames with their saved maps. The issued ledger remains
  `[resource 0, cleanup 0, ticket 0]`; ticket0 is discharged once. Negative
  proofs reject reusing it, searching dormant captures and unchanged-state
  silent matching. Scope coherence and annotation authentication remain
  explicit inputs, not claims of general reachable-state coverage.
- The resume audit covers 818 registered modules and 11,206 exact dependency
  reports. All 16 affected modules pass fresh independent warnings-as-errors
  compilation; 802 unchanged verified source/report pairs are retained. Active
  callable admission and cleanup admission work is excluded from the frozen
  snapshot. No Rust code changed. The next runtime batch starts at the same
  reached state and connects the second request and capture.

- `CoreAdmittedCleanupPrefix` extends the same admitted handler prefix to
  actual s24: 24 Core transitions and 11 target events, with every intermediate
  target admitted. Cleanup registration supplies the selected action data;
  identity0 freshness follows from the issued resource0 ledger. The final
  world/history are `[0]`, issued owners are `[resource 0, cleanup 0]` and
  nothing is completed. The callback remains delayed. `CoreReadyBindings`
  factors the repeated lambda-binding composition without changing the prior
  wrapper statements or choosing fixed source annotations.
- All six affected modules pass fresh independent compilation. The combined
  cleanup-admission audit covers 820 registered modules and 11,211 exact
  dependency reports, retaining 814 unchanged verified source/report pairs.
  Active callable admission and second-capture work is excluded. Rust remains
  unchanged. The next admitted-state batch connects first capture using the
  same chosen action, handler and resource answer.

- `CoreCallableContractAdmission` and its effectful examples pass fresh
  independent compilation: 13 source reports and 12 example reports use only
  `propext` and `Quot.sound`. Fixed global operation contracts, scalar
  requirements, recursive private-body certification and independent support
  survive substitution. One bound helper accepts both same-contract requesting
  bodies. Actual bind/beta steps and signature/support negatives are verified.
- Current code/resource certificate and accounting transport remains conditional
  on supplied current checks. Enclosing handler admission/response and M4's
  current/pending/coherent migration remain open. The owner registry still uses
  legacy contracts; the experimental imports also prevent a direct import back
  into the M4 file. The next bounded plan must resolve that dependency and carry
  the same source evidence through current, saved-frame and operation-result
  boundaries. This records the existing D4 obligation, not a scope expansion.
- The combined effectful-source audit covers 822 registered modules and 11,236
  exact dependency reports. Both new leaves have independent compilation
  evidence; 820 unchanged verified source/report pairs are retained. Active
  first-capture admission and second-capture runtime work is excluded.

- `CoreSecondCapture` extends the same initial related execution to 40 actual
  Core transitions. Ticket1 captures the pending write99, armed cleanup27 and
  handler41; write11, spent ticket0 and the getter/cell remain outside. Its
  creation ledger adds ticket1 and its discharge ledger remains `[ticket 0]`.
  Exact nearest-owner selection and delayed callback observations are proved.
  All 11 reports pass fresh independent compilation.
- The combined second-capture audit covers 823 registered modules and 11,247
  exact dependency reports, retaining 822 unchanged verified source/report
  pairs. The following closing batch must use the current lexical unwind
  machine, which excludes the old plan-based raw discard. Its relation must
  account for Core's projected handler frames and the calculus's retained
  lexical scopes. This is existing C3 coverage, not a new fragment exclusion.

- `CoreAdmittedCapturePrefix` reaches actual s28 with 28 Core transitions and
  13 target events from the same admitted root. Every intermediate point has
  a related admitted snapshot. The source-selected result, handler, action and
  focused frame survive the actual capture; exact cut/clause uniqueness connects
  them to M4 preservation. The final ledger issues resource0, cleanup0 and
  ticket0, completes nothing, and assigns the clause's actual required rights.
- `SourceScheduledCapture.capture_successor_metadata` exposes the existing
  proof's annotations and successor shape; the original theorem remains a
  same-statement wrapper. Resume/close footprints remain explicit chosen
  bookkeeping annotations. All 25 affected modules pass fresh independent
  warnings-as-errors compilation. Admitted resume and later execution remain
  open; the next batch must retain the same selected witnesses through s35.
- The combined admitted-capture audit covers 824 registered modules and 11,252
  exact dependency reports, retaining 799 unchanged verified source/report
  pairs. Active higher-order and discard files are excluded from this frozen
  snapshot. No Rust code changed.

- `CoreUnwindRelation` and `CoreDiscardPrefix` connect 45 actual Core transitions
  in one current lexical-machine chain, ending immediately after ticket1's
  discard. The complete target ledger creates resource0, cleanup0, ticket0,
  ticket1 and close0; it discharges ticket1 and ticket0. Exact closing spines,
  the empty nested-consumption list and the delayed callback are proved.
  Cell0 dispatch agrees for the actual callback; unrelated user0 dispatch is
  explicitly shown to differ.
- Review rejected an initial two-phase connection without guards for the
  inherited raw prefix. A proof-exposure tactic was stopped for excessive
  reduction cost. The retained repair strengthens `CoreInitialPrefix.Positive`
  with explicit lexical ordinary guards and lifts it by direct induction.
  Existing construction sites discharge those guards; the old raw discard is
  proved unavailable through this interface. All 15 affected modules pass fresh
  independent warnings-as-errors compilation. Callback execution remains open.
- The combined lexical-discard audit covers 826 registered modules and 11,279
  exact dependency reports, retaining 811 unchanged verified source/report
  pairs. Active admitted-resume and higher-order files are excluded. No Rust
  code changed.

- `CoreAdmittedResumePrefix` extends the same admitted capture to actual s35:
  35 Core transitions and 16 target events, with Related and Admitted evidence
  at every intermediate point. It retains the selected input contract and
  symbolic rows, derives the caller frame from source focus, and determines
  owner0 and the full restored stack from the actual current resume event.
  Saved owner maps remain authenticated witnesses rather than being inferred
  from physical-frame equality. The ledger completes ticket0; all three owner
  stores remove owner0 while world/history, issued owners and rights remain
  unchanged.
- The combined admitted-resume audit covers 827 registered modules and 11,284
  exact dependency reports, retaining 826 unchanged verified source/report
  pairs. The new leaf passes fresh independent warnings-as-errors compilation.
  Active higher-order and cleanup-execution files are excluded. No Rust code
  changed. The next admitted-prefix batch must connect the same selected data
  through second capture.

- `CoreCleanupRunFrames` and `CoreCleanupRunPrefix` extend the same current
  lexical-machine chain to 51 actual Core transitions. Cleanup starts once and
  callback beta enters body12 in its saved environment. The running relation
  retains the original captured relation, exact closing projection, saved Unit,
  physical completion tail and lexical handler scope. The ledger stays unchanged
  from discard; cell write and cleanup/close completion remain open.
- A narrowly indexed administrative link reuses the existing ordinary witnesses
  above that tail and requires the actual full Core step. Its strict potential
  decrease is proved, and an unchanged step is rejected. The combined audit
  covers 829 registered modules and 11,299 exact dependency reports: four freshly
  compiled affected modules and 825 unchanged verified source/report pairs.
  Active admitted-second-capture and higher-order edits are excluded. No Rust
  code changed.

- `CoreCallableContractExecution` connects recursive current source and saved
  plain/cell frames to existing checking/accounting structures. Focus, exact
  builtin reply, plug and bind transport one predecessor's evidence. The
  concrete example constructs that predecessor with live cell0 and one helper
  used with two differently sequenced cell-reading closures, then applies all
  four generic transports in a connected raw trace.
- Review caught a saved input bound incorrectly fixed to the empty set. The
  retained interface instead bounds resources by the receiving context and
  current world, independently of the function port. The builtin reply checks
  the same global operation key and derives the contextual receiver from the
  physical cell update. Full M4 validity and handler/owner/resource-exit
  migration remain open.
- The combined callable-execution audit covers 831 registered modules and
  11,317 exact dependency reports: two freshly compiled leaves and 829 unchanged
  verified source/report pairs. Active second-capture and callback-write edits
  are excluded. The clause-cell result and escape fixtures below supply fresh
  CLI evidence for subsequent saved-frame transport; no Rust implementation
  changed.

- `CoreAdmittedSecondCapturePrefix` reaches actual s40 from the same admitted
  first-resume witnesses: 40 Core transitions and 20 target events. It retains
  authentic saved owner maps, selected ports, action, handler and post-resume
  frame, with separate symbolic row choices for both capture epochs. Every Core
  point and the additional intermediate plug/bind target have admitted snapshots.
  Fresh ticket1 follows from the issued ledger; ticket0 remains spent outside
  the new capture. The final ledger issues resource0, cleanup0, ticket0 and
  ticket1, completing only ticket0.
- The first-resume metadata endpoint exposes existing focus/handler equations;
  its original statement is retained as a projection wrapper. The existing
  physical-cut uniqueness proof is public and reused. The combined audit covers
  832 registered modules and 11,326 exact dependency reports: three freshly
  compiled affected modules and 829 unchanged verified source/report pairs.
  Active handler/owner migration and callback-write edits are excluded. No Rust
  code changed.

- `CoreCellWriteFrames` and `CoreCleanupWritePrefix` extend the same runtime
  chain to 63 actual Core transitions. The reached callback determines the
  setter and pair operands; named tuple allocation supplies the heap extension.
  The cell update derives the changed outside stack from the existing captured
  relation, retaining the lexical handler and all pending/spent frames.
- Exact actual-step equations establish the selected cell0 write and reject a
  mismatched handle. Write7 and cleanup start each occur once; cleanup and close
  are still unfinished, and the target ownership ledger is unchanged. Six
  affected modules pass independent warnings-as-errors compilation; the combined
  audit covers 834 modules and 11,348 exact dependency reports, retaining 828
  unchanged verified source/report pairs. Active admission files are excluded.
- A simplifier loop in dependent spent-frame decomposition was resolved with
  explicit extracted answer/scope equations and bounded rewrites. No proof
  limit increase, new axiom or Rust implementation change was required.

- `CoreCallableContractRegistries` separates immutable operations/policy from
  common owner input/answer contracts. The same recursive source is indexed by
  owners and resource worlds, with resume/discard constructors and constructive
  substitution, certification and lower typing. Owner insertion preserves the
  registry and commutes with erasure; private callable bodies remain retained.
- Scoped `erase_at` replaces unrestricted empty-ticket erasure; `erase` remains
  for empty scope. `value_demand` requires an actual value, replacing the former
  all-expression statement. Existing finite example statements are unchanged.
  All five affected modules pass independent warnings-as-errors compilation,
  with 50 standard-axiom reports. The combined audit covers 835 modules and
  11,355 exact dependency reports, retaining 830 unchanged verified pairs.
  Handler capture and changing-world support transport remain open.

- `CoreAdmittedDiscardPrefix` connects the same source-selected second capture
  through actual s45: 45 Core transitions and 22 calculus events. Branch
  preservation and `Allocating.Request.discard` construct the successor; close0
  freshness follows from the existing issued ledger. Current event inversion
  determines owner1 and the retained unwind stack. Every Core point remains
  Related and Admitted, without fixing the source-selected ports or owner maps.
- Final issued owners add close0, completed owners become tickets1/0, and all
  three stores remove owner1. The existing owner-head decomposition is public
  and reused unchanged. Three affected modules pass independent compilation
  against the newer runtime baseline. The combined audit covers 836 modules and
  11,359 exact reports, retaining 833 unchanged verified pairs. No new blocker or
  Rust implementation change arose; admitted cleanup/completion remains open.

- `CoreCleanupFinishPrefix` and `CoreFinalPrefix` extend the same runtime chain
  through all 90 actual Core transitions. The retained handler advances in an
  explicit extra target event after cleanup completion. Close completion and
  spent-clause returns recover the actual saved callers; the final caller writes
  11, reads 11 and releases resource0. Result 11, empty stacks, exact observation
  order, complete target discharge accounting and terminality are proved.
- The new `awaitingClose` relation requires returned Unit, the actual close frame
  and the same recursively related mapped tail. Eight affected modules pass
  independent compilation, including admitted discard. The combined audit
  covers 838 modules and 11,395 exact reports, retaining 830 unchanged verified
  pairs. No Rust implementation changed. The admitted-completion batch below
  supplies the remaining example suffix; general simulation remains open.
- Handler extension exposed a substitution statement limitation: actual clause
  syntax changes, so the literal old handler plan cannot remain its index.
  The next proof must construct and certify the substituted plan while retaining
  the public contract and signature. This revises the earlier handler-entry
  estimate; a bounded statement plan must precede implementation.

- The general-transition review identified normal cleanup start/finish as the
  next missing C3.2 component. `CoreNormalCleanupSteps` now proves both for
  arbitrary states and saved return values. The same delayed action, saved-value
  relation and mapped outside stack construct both endpoint interpretations and
  the actual Core transitions. Unit completion restores the saved value and
  scope; a non-Unit result is rejected. Callback success and future validity
  are not premises.
- `RunningTail.normal` and its heap transport reuse the existing running-step
  interface. Ten affected modules pass independent compilation, including
  discarded cleanup and admitted discard. The combined audit covers 839 modules
  and 11,400 exact reports, retaining 829 unchanged verified pairs. General
  callback dispatch, cell updates, projection/retirement and static readiness
  remain C3 obligations; no additional example variant or Rust change was added.
- Further batches target named general obligations. The existing example's
  admitted completion is recorded below; its runtime trace will not be extended. Handler substitution reuses proof-level family selection and
  existing signature/row transport; it does not require a new syntax walker.
  The connected handler/caller checkpoint must pass before that repair is
  integrated. Initial admission remains a separate static construction.

- The next C3.2 batch proves generic actual cell read/write completion.
  `CoreCellSteps` derives effect instantiation, operand decoding and nearest
  selection from the same current witnesses, then constructs both endpoint
  interpretations and positive target transitions. `WriteCut.live` preserves
  dormant captures while updating the active outside cell.
- Immediate normal-cleanup-tail corollaries preserve arbitrary saved values and
  delayed actions. Five affected modules pass independent compilation; the
  combined audit covers 840 modules and 11,412 exact reports, retaining 835
  unchanged verified pairs. Arbitrary callback prefixes, nested running cleanup,
  projected-handler dispatch and static authentication remain open. This batch
  adds no example variant or Rust implementation change.

- `CoreCompletionSteps` generalizes consumed-clause return and Unit close
  completion from the current frame/value evidence. Both construct actual Core
  successors and positive lexical transitions; rejection lemmas exclude live
  clause returns and non-Unit close results. No relation representation changed.
  Outside tails must have ordinary mapped interpretations, and close labels match
  locally. General close-name mapping and nested retirement remain open.
- The new leaf passes independent compilation with six standard-only reports.
  The combined audit covers 841 modules and 11,418 exact reports, retaining 840
  unchanged verified pairs. No additional example or Rust change was introduced.

- Handler review identified an authentication gap before caller transport:
  aggregate `Supported` and actual-plan certification do not authenticate each
  stored clause support bound. The existing declaration-support substitution
  proof relies on port-bounded values, which cannot be reused for a pure callable
  retaining resources absent from its public port. The required per-clause
  evidence must use actual support environments and remain available inside
  private lambda bodies. Review also found that full row equality cannot cover
  later-world inputs: it would preserve an old empty clause bound after a
  resource-retaining value is substituted. Fixed-bound substitution needs its
  explicit support hypotheses; restoration needs authenticated reannotation.
  The proposed companion must explain how this interacts with the lambda's
  universal checking refinement before implementation. The earlier one-hour
  connected-handler estimate is no longer supported; a twenty-minute interface
  review is resolving this representation question. No helper-only Source
  checkpoint will be integrated.

- `CoreEmptyDiscard` completes the general empty-projection batch, including
  nested live/spent captures. The same mapped cut constructs actual Core next,
  a finite positive target segment and the related successor. Core consumes
  nested tickets before children; lexical retirement follows children. Exact
  orders and a permutation preserve ticket multiplicity. Empty projection
  excludes retained resource/cleanup frames.
- Core's close counter stays unchanged. The target close label is chosen
  independently, created and discharged within the segment. Target freshness
  remains an explicit admission obligation; neither future validity nor a
  historical name map is assumed. Rust's observation projection erases close
  ghost labels. Nonempty projected callbacks and general admission remain open.
- The bounded admitted example is complete through the same 90 actual Core
  transitions and 41 target events. `admittedFinalCompletion` preserves the
  source-selected annotations and derives the callback/getter/setter code from
  reached environments. Every Core point is related to an admitted snapshot;
  target-only cleanup and bind intermediates are admitted explicitly. The final
  result is integer 11 with an empty stack and all five issued owners discharged.
- The three new leaves pass independent compilation against the current baseline
  with ten exact standard-only reports. Grouped integration covers 844 modules
  and 11,428 reports, retaining 841 unchanged verified pairs.
  `CoreValueUniqueness` establishes finite closing-code uniqueness, not annotation
  uniqueness. This finishes the finite-example line; general admission,
  simulation and the integrated theorem remain open.

- The C4 interface review found that universal private checking is too strong:
  public pure rows admit an empty receiver, while private handler rows retaining
  a resource require that resource at the receiver. The approved repair uses
  open body evidence indexed by call world, receiver bound and argument support,
  with hereditary authentication of the same selected clause rows. Existing
  code/accounting interfaces and completed M4 theorems remain unchanged.
  The next integration gate must connect substitution through supported source,
  saved frames and the current execution site to handler capture. Helper-only
  results will not close this gate. The bounded estimate is 90–120 active minutes;
  restored-world rebasing follows and remains outside that estimate.
- Independent interface review confirms two required current support facts.
  Overall expression dependencies omit clause formals, so they cannot bound
  all selected declaration rows. Private checking must also receive the
  authenticated formal/receiver bound. Capture must then prove actual payload
  support within the selected formal bound and the post-capture clause receiver;
  cells inside the dormant capture are not visible there. Existing lower capture
  checking preserves selected row evidence but does not supply this operand
  fact. No further saved-frame mismatch was identified when the same selected
  rows and hereditary support witnesses are retained. These are implementation
  acceptance requirements, not completed transport theorems.
- The C3 review found that the original projected relation cannot represent
  progress after a resource release or a target-only retirement marker. The
  approved batch adds a residual projection carrier derived from the same
  mapped capture and successful Core projection. It separates local Core and
  target close labels, matches each actual resource pop with finite lexical
  advances, and connects final close completion in one execution chain.
  Arbitrary nested live/spent captures are included. The resource-only guard is
  a batch boundary; general cleanup remains in the fragment. Estimated active
  work is 2–3 hours, running in parallel with C4. Both estimates cover their
  connected checkpoints, not completion of C2–C5.
- A separate bounded C3.2 batch completes the missing strict-focus cases:
  pair and application entry/return, bind and Unit-match initialization,
  Boolean conditions and resource initialization. Each rule must derive mapped
  endpoints, actual Core next and its positive target segment from current
  translation and closing evidence. Existing request/resume and value-ready
  rules are reused. Validated Core cleanup already holds a closed callback;
  its non-value target focus case is unreachable and must be proved so.
  This batch owns one new leaf, has no dependency on the C4 repair or resource
  cursor, and is estimated at 2–3 active hours in parallel with those batches.
- Both C3 batches are now implemented and independently compiled. Resource-only
  nonempty discard connects the same owner cut through `closing.length + 2`
  actual Core steps, with exact releases, nested retirement and a separately
  named target close. Its accounted chain supplies both execution and ledger
  evidence. The strict-focus leaf supplies eight operational rules and proves
  non-value cleanup registration unreachable for an authenticated callback.
  Current translation, readiness and mapped-tail evidence remain premises;
  general admission and callback lifting remain open.
- The independent rebuild exposed two additional exhaustive matches in the
  admitted-completion leaf. Both received only an impossible eval/unwind case;
  its statements and 90-step example are unchanged. The corrected combined
  build passes for 16 affected modules. The three new leaves add 26 reports,
  giving 847 registered modules and 11,454 exact reports with 831 unchanged
  verified pairs. No new fixture or Rust change was added.
- The C4 connected-gate estimate has slipped. The receiver-conditioned
  interface and open source-family prefix compile, but general substitution,
  hereditary formation and the supported-source/frame/site connection remain.
  The next 30-minute checkpoint is compiled hereditary formation and actual
  caller specialization; the worker estimates another 90–120 active minutes
  after that checkpoint. The family must also select the actual lexical support
  environment: an older conservative bound can retain a resource that a later
  callable does not read. This refines the existing support obligation without
  changing the public contract or completed M4 proofs.
- The cleanup review recommends a general retained cursor with authenticated
  cleanup nodes, derived from the same captured frames and actual projection.
  Construction, finite normalization and actual cleanup start/finish are
  estimated at 2–3 active hours. General callback-body lifting and exact effect
  dispatch remain separate obligations. Implementation is held pending the next
  C4 checkpoint; no additional finite examples are planned.
- Independent C4 review disproved the proposed unconditional private-code
  refinement. Public pure rows admit any caller context; a private locally
  handled request requires the whole caller context to be checked. A fresh
  Lean proof constructs an unchecked caller tail and derives the contradiction,
  with four standard-only reports. The repair must consume current retained
  source and retained support checks, already fields of the execution site.
  Existing return-mode and installation-history transport lemmas apply. This
  corrects the earlier decision to leave the code interface unchanged; it does
  not change completed M4 proofs or demonstrate a runtime disagreement.
  The negative review remains outside the registered proof suite pending the
  connected C4 gate. Its effect on the implementation estimate is under review.
- The worker accepted that correction and the related receiving-bound coverage
  requirements. A saved bind suffix must accept the full current receiver;
  plugging then specializes its lexical entry to the actual value's support.
  Clause formation must likewise cover admissible inputs. Capture must derive
  actual payload support at the selected post-cut receiver, preserving the
  operation-operand retention rule already specified by Ash. A bounded
  20-minute review is tracing that evidence through existing validation metadata
  and lower proof interfaces before choosing the upper companion's policy index.
- That review found the required finite data in Rust's existing capture
  analysis: request ports, value/call contexts, actual closure dependencies and
  crossed acquisition occurrences. The validator consumes the check result;
  ordinary Core request type/row metadata does not retain the certificate.
  C2 must construct and authenticate this evidence. C4 must preserve the same
  request-flow identity through substitution and capture. Neither public port
  resources nor raw validation success supplies the missing Lean proof.
- The next bounded bridge uses finite dependency and crossed-origin records
  with one current activation-origin realization. Checked origin disjointness
  derives avoidance of the same captured prefix. Existing cut reconstruction
  and visible-resource decomposition then derive the post-cut payload bound;
  ambient resources remain admissible. The bridge is estimated at 45–60 active
  minutes and feeds the connected capture gate. It does not implement a new
  analysis or finish C2 certificate construction.
- The corrected receiver-refinement interface independently compiles with
  warnings as errors and six standard-only reports. It remains unregistered
  pending the connected C4 gate. With that interface checkpoint reviewed, the
  previously held C3 general cleanup-projection batch is authorized for 2–3
  active hours in parallel. Its cursor/start/finish proofs have no dependency on
  the changing callable-admission files; no finite examples are being extended.
- The payload bridge is implemented and independently compiled against 441
  recorded dependency pairs, with six standard-only reports. A finite check
  derives origin separation; current operand and captured-prefix realizations
  derive support at the actual post-cut receiver. The consumer must authenticate
  the current request/call-context index and use the actual operand's dependency
  bound. The bridge remains unregistered until the connected C4 gate passes.
- Source certification and world extension compile. Hereditary formation is
  being checked after explicit binder and registry arguments were corrected.
  The next checkpoint specializes the same authenticated lambda derivation,
  then proves changed-plan substitution and supported-source preservation.
  The worker estimates 60–90 active minutes after formation checks for that
  checkpoint. Saved frames, execution sites and actual handler capture follow;
  this replaces the earlier estimate for the whole connected gate.
- Following the user's concern about time spent aligning existing proofs,
  further admission work is bounded by that connected dependency chain. Another
  interface redesign requires a scope review before expansion. Additional
  finite examples and optional generalization remain excluded. Passing helper
  proofs alone does not close C4.1.
- The general cleanup-projection batch is implemented and independently
  verified. Its cursor derives from the same captured frames and successful
  Core projection. An accounted chain connects actual discard to cleanup start;
  current Unit completion, resource release with later cleanups and final close
  are also matched. General callback-body lifting and exact dispatch remain
  open. The grouped rebuild passes for 18 affected modules, with 831 unchanged
  verified pairs: 849 registered modules and 11,467 exact reports. No finite
  example or Rust behavior was added.
- The next C3.2 batch reuses existing callback component proofs through suffix
  extension. Review of every Core evaluator case found that a successful step
  preserves its outcome when the same physical suffix is appended to both
  endpoint stacks: successful owner/interpreter lookup only extends the selected
  outside tail, leaving captures and discard fuel unchanged. Terminal and
  rejected outcomes do not have this property. The bounded implementation must
  prove this law, heap extension and guarded target-step extension, then derive
  both running-cleanup endpoints and exact ledgers from existing isolated
  component witnesses. A general beta-under-running-cleanup theorem supplies the
  required connection; no new finite example is planned. The two-leaf batch is
  estimated at 2–3 active hours in parallel with C4 and does not address requests
  whose selection enters the appended tail, freshness or admission.
- The C4 consumer review confirms the smallest remaining connection:
  changed-plan substitution with signature equality, hereditary support,
  saved-frame plugging, then actual handler capture. Existing clause-row
  substitution and declaration-policy transport avoid a new annotation walker.
  A bounded interface review also checks whether the corrected current-tail
  refinement admits the existing internally handled-request case across code,
  support checking and accounting before further migration relies on it.
- The C4 formation checkpoint now passes independent pinned compilation:
  source certification, world extension and authenticated current lambda
  specialization produce three reports using only `propext` and `Quot.sound`.
  All 441 imported source/artifact pairs remained unchanged. This verifies the
  full-receiver bind/declaration constructors and selection of the same private
  body, rows and refinement through hereditary evidence. The full admission file
  remains uncompiled work in progress beyond this prefix. Changed-plan
  substitution and supported-source preservation are now the active 60–90
  minute checkpoint; no connected handler-admission result is claimed.
- Supported-source integration keeps aggregate syntax support separate from the
  hereditary receiver. A handler may have empty expression dependencies while
  its formal-argument clause bound includes a resource. The finite lexical
  environment must agree with the existing support environment, and the site
  must authenticate its full current receiver for saved-bind input coverage.
  Canonical construction therefore consumes the same source's hereditary
  evidence instead of deriving it from aggregate bounds alone.
- The current-tail refinement review found a constructor route for the existing
  private immediate-resume handler's code and support checking. Its accounting
  witness still requires fresh-owner identity for an arbitrary current waiting
  root and transport through two empty requirement prefixes. A bounded parallel
  implementation will prove these facts and the complete concrete refinement in
  one leaf. Neither helper becomes an additional interface premise. The full
  positive witness remains unproved; no new fixture family or policy index is
  authorized by this check.
- The complete minimal refinement witness is estimated at 60–90 active minutes
  in parallel with substitution. Its current-root argument must follow from the
  accounting waiting derivation and fresh-owner provenance. Review recommends
  reusing `LocalOwner` directly if its discharge transport avoids a duplicate
  structural predicate. The witness still must prove all three refinement fields.
- The C5 endpoint review confirms direct reuse of M4's raw-trace ownership and
  terminal-accounting results once correspondence supplies actual lexical events
  and the initial ledger. Each event requires creation freshness against issued
  history; current accounted chains establish multiplicities but do not derive
  that freshness. General admission must still connect the common callable
  source to the complete preserved state. No existing M4 theorem is weakened or
  treated as proving those missing connections.
- Local implementation checkpoints now compile for successful Core-step suffix
  extension and for fresh-owner identity over an arbitrary current accounting
  waiting root. The latter uses one private structural predicate after direct
  dependent elimination proved awkward; it adds no checked-root, uniqueness or
  future-state premise. Parent statement review found no additional semantic
  assumption. Both remain unregistered pending their connected batch outputs:
  callback beta under an arbitrary running tail and the full three-field
  positive handler refinement, respectively.

- The connected C3 suffix batch now passes independent pinned compilation.
  `CoreSuffixSplice` covers every successful Core step and derives heap extension;
  target extension preserves the ordinary guard and exact event lists.
  `CoreRunningSplice.beta_running` constructs application correspondence under
  an arbitrary retained cleanup tail from current component witnesses. The same
  transition supplies accounting. The grouped result contains 851 registered
  modules and 11,487 exact reports, with two fresh and 849 unchanged pairs.
  This completes the bounded batch within its estimate. Dispatch into the
  retained tail, nested callback/unwind coverage, readiness and freshness remain
  separate C3 obligations.
- The minimal private-handler refinement now passes the worker's pinned gate for
  all three fields: code, checked support and arbitrary caller accounting. Its
  six reports use only standard axioms; no additional interface premise was
  introduced. The leaf is frozen for parent review and remains unregistered
  until the connected C4 admission batch. This establishes nonvacuity of the
  corrected interface, not general higher-order admission.

- Parent review and independent pinned compilation now verify the complete
  minimal private-handler refinement. All 441 source/artifact inputs remained
  unchanged; six reports use only standard axioms. The code and checked fields
  restore the supplied current caller after immediate resume. Accounting retains
  its arbitrary current requirement tree beneath two empty prefixes and removes
  the fresh local owner's obligations using the existing rules. No additional
  interface premise is introduced. The leaf remains unregistered until the
  connected C4 batch.
- Changed-plan substitution exposed a uniformity obligation in C4.1:
  `SourceOffer.available` stores one plan per owner and authenticates it for
  every compatible continuation contract. A separate existential successor plan
  for each contract does not supply that shared plan. Logical choice cannot
  exchange these quantifiers. The bounded scope review compares existing
  signature-preserving rewriting with deterministic substitution guided by the
  source code. Any transform must retain public application contracts, honor
  binding shadowing and update actual nested declaration witnesses. Changing
  owner-contract indices or existing M4 interfaces is not authorized by this
  finding. The prior 60–90 minute substitution estimate is uncertain until this
  uniform construction is settled.

- Scope review approved a deterministic, source-guided annotation substitution
  for that uniformity obligation. Existing `ClauseMap.plan` would also rewrite
  an application's public contract plan, while `substituteClauses` alone leaves
  nested offered bodies unchanged. The local transform therefore preserves the
  public suffix, follows source binders and maps available mode families
  pointwise over owners. A separate worker owns its one new leaf and signature
  laws; the admission worker owns structural source and hereditary preservation.
  No owner-contract index or shared M4 interface changes are planned. Transform
  work is bounded at 60–90 active minutes; source/support preservation is
  estimated at 60–90 minutes after declarations are available, with overlap;
  saved-frame/site/capture connection is another estimated 60–90 minutes. These
  estimates exclude unresolved restored-world transport and do not claim a
  general admission completion date.
- C3 dispatch review identified a narrower prerequisite before another component
  batch: projected cleanup physically removes handlers and flattens saved live
  captures, so the correspondence must derive current selector agreement.
  Current resource ownership and target support may establish the builtin-cell
  case without a new checker certificate; a bounded read-only review checks
  this route first. User-handler capture and nested running cleanup also exceed
  the existing ordinary captured-stack carrier. Conditional dispatch code and
  carrier redesign are held until their current evidence is identified.

- The C3 builtin review found that the existing current ownership invariant
  resolves saved-cell interception. The source-selected target `CellUpdate`
  reaches an outside cell; whole-stack uniqueness excludes that resource owner
  from a dormant saved capture. The same retained cursor authenticates every
  flattened physical cell. Crossed lexical handlers miss the request by that
  target selection, so no user-only handler restriction or new transparency
  checker is needed. A connected 1–2 active hour read/write batch is authorized:
  derive the target cut from current scope realization and builtin selection,
  then derive physical selection, actual Core execution and both related
  endpoints with the same accounting witness. Existing M4 selection induction
  and ledger uniqueness are reused. A supplied successor relation or cut-only
  helper does not satisfy this batch. User-effect capture and nested running
  cleanup remain outside this increment, within the existing C3 obligations.

- The deterministic annotation transform now passes independent pinned
  compilation. Its three signature laws use only `propext` and `Quot.sound`;
  all 252 imported source/artifact pairs stayed unchanged. Parent statement
  review confirms that application public plans, binder shadowing and uniform
  owner-indexed mode plans are retained as intended. The transformation finished
  within its bound and remains unregistered pending connected source/support
  preservation. The admission worker now uses the exact deterministic output.
- Review clarified the later saved-support obligation: existing M4 resume
  preservation keeps the same current world across the resume step. The saved
  evidence may predate resources acquired by the clause, so its old receiver
  bounds must be reconstructed for the restored continuation. Existing world
  extension is reusable; a theorem for shrinking the historical world is not
  required by the motivating fixture. This does not yet prove that larger
  saved-input bounds can be authenticated by the common-contract companion.

- Projected builtin dispatch now derives the physical read/write cut from
  current scope realization, selection and the same stack ledger. Existing
  uniqueness excludes interception by saved cells. Both theorems construct
  actual Core execution, a positive target transition, both related endpoints
  and exact observations; accounting uses the same witness. Independent pinned
  compilation passes with nine standard-only reports. The grouped result is
  852 registered modules and 11,496 exact reports, with one fresh and 851
  unchanged verified pairs. This closes the bounded builtin batch within its
  estimate. User-handler capture, nested running completions and the general
  simulation obligations remain open; C3 stays at 0/5.

- The next C3 scope review selects nested normal cleanup. A structural
  `RunningTail.append` case can combine the existing normal carrier with an
  enclosing running tail, without repeating saved-value or cleanup fields.
  The connected batch must derive actual start and Unit completion, both related
  endpoints, exact observations and the same cleanup discharge. Existing
  successful-step suffix laws and normal cleanup proofs supply the execution
  evidence. Nineteen registered consumers require an affected build. The batch
  is estimated at 1.5–2.5 active hours alongside C4. User-handler capture and
  completing a projected inner callback into unwind remain outside this
  increment, within the existing general C3 obligations.

- Nested normal cleanup start and finish now pass independent pinned compilation
  with all 19 existing consumers. Structural tail composition retains the same
  delayed cleanup, arbitrary saved value, mapped pending prefix and enclosing
  tail. Actual Unit completion restores the saved value and scope, records the
  exact finish observation and discharges that cleanup in the same transition
  witness. Callback beta reuses the existing theorem. The grouped result contains
  853 registered modules and 11,503 exact reports: 20 fresh and 833 unchanged
  verified pairs. The batch completed ahead of its 1.5–2.5 hour estimate through
  direct proof reuse. General user capture, nested dispatch and projected inner
  unwind remain open; C3 remains 0/5.

- General deterministic source substitution now passes independent pinned
  compilation. The mutual theorem covers source expressions, clause bodies,
  offered modes and declarations, including receiver-dependent lambdas and
  nested handler literals. Available owner plans are selected independently of
  the subsequently quantified owner contract. Public contracts, scalar
  requirements, checking signatures and complete rows are retained. All 442
  imported source/artifact pairs stayed unchanged; the theorem uses only
  `propext` and `Quot.sound`. This resolves the identified uniformity obstruction.
  Hereditary support preservation and the saved-frame/capture consumers remain
  unfinished, so the checkpoint stays unregistered pending the connected gate.

- After another pause, the user explicitly resumed higher-order support
  preservation and general capture/resume correspondence in parallel. Both
  existing workers are verified as `gpt-6.1-sol` with medium reasoning. Their
  source ownership is separate; no further finite example extension is planned.
- Closed-value world extension and receiver transport pass independent pinned
  compilation. Environment and resolved-owner transport now also pass independent
  compilation and separate interface and proof-quality review. The latter two
  modules have five exact standard-only axiom reports, with 443 and 444 frozen
  imported modules respectively. Review found a missing direct-import hash in
  worker metadata; parent metadata now records the source, selected artifact and
  linked checkpoint hashes. These helpers remain unregistered pending connected
  hereditary authentication and supported-source preservation.
- Exact dependency membership after closed substitution, reverse actual-support
  inclusion, finite lexical-known transport and authentication under agreeing
  lexical environments now pass independent pinned compilation and review. Five
  exact reports contain only standard axioms. The parent builds record 445 and
  446 consumed imported modules; the worker's unified manifest also includes its
  two outputs. Review found worker artifact shadowing in its search path, so the
  parent compilation uses only frozen parent inputs and records their selected
  hashes. Recursive replacement authentication is conditioned
  on the substituted name actually occurring, so a lambda that does not capture
  that name need not receive the replacement's resources. Completing hereditary
  and supported-source preservation is estimated at 90–150 active minutes on
  resumption; the frame/site/capture connection and saved restoration remain
  subsequent gates.
- General capture requires a physical segment that can retain running cleanup,
  unfinished close operations and nested owners. Adding that segment directly to
  the old relation would invalidate its existing running-only classification.
  Parent scope review instead approved an upper-layer relation with an embedding
  of the old relation and step witnesses. New capture and resume proofs must
  construct both endpoints from the same structural segment and actual Core
  execution. The first normal/protected capture and resume gate is estimated at
  2–3 active hours in parallel with support preservation. Projected interior
  handler selection still needs authenticated request-route evidence; the first
  gate does not close general simulation.

- Higher-order hereditary authentication and supported-source substitution now
  pass independent pinned compilation and interface review. The mutual proof
  covers nested lambda bodies, available owner families, protected declarations
  and handler literals. It retains the same public contracts, requirements,
  demand and receiving bound, selecting the same private source family. The
  concrete declaration policy discharges its signature transport automatically;
  an unused substituted name needs no requirement that the replacement's
  resources lie in the body's receiver. Five final
  modules produce seven standard-only reports and eleven reviewed public
  interfaces, with 449 unchanged imported source/artifact pairs. This finishes
  the requested support-preservation checkpoint. It remains unregistered until
  the existing connected C4 gate constructs saved frames, the execution site
  and actual capture; restored-world support is also still open.
- The general capture/resume runtime gate is implemented and frozen. An upper
  relation embeds the existing relation and accepts arbitrary authenticated
  segments containing running cleanup, unfinished close, nested owners and
  retained projections. Actual handler and owner lookup derive the split and
  cut; capture and resume construct both endpoints and restore the same saved
  segment. A connected immediate-resume clause chain gives four actual Core
  steps, two decreasing administrative matches, exact observations and the
  same ownership accounting. Protected saved obligations cannot be discarded.
  Both leaves pass independent pinned compilation and review with 45
  standard-only reports. Registration and the grouped audit cover 855 modules
  and 11,548 exact reports, retaining 853 unchanged verified pairs; 2,054 local
  links and anchors pass. The connected runtime gate is integrated without
  changing the existing relation or its consumers.
- Current projected-handler route certificates remain explicit inputs. Their
  C2 producer must connect a request from the same isolated callback to its
  exact `ActionData.requests` and the same closing-scope routes. Resume also
  retains current scope resolution to the selected ticket; raw correspondence
  does not establish admitted ledger validity or uniqueness. General completion
  and unwind after restoration, and ordinary callback-local discard with a
  protected outside segment, remain separate C3 transition obligations. No M4
  interface, Rust behavior or finite example changes accompany these proofs.

- The user authorized the next two consumer batches in parallel. C4 promotes
  the reviewed substitution/authentication layers into the callable admission
  companion, carries the actual receiver through saved frames and the current
  execution site, and connects the selected handler capture. Signature and row
  equality must transport the existing checks and accounting; a desired
  successor site is not an input. Consumer inspection revises the earlier
  60–90 minute connection estimate to 60–90 minutes for receiver-aware frame
  execution and 90–150 minutes for actual capture, or 2.5–4 active hours in total.
  Restored-world support remains separate. Registration waits for the complete
  connected gate rather than helper-only checkpoints.
- C3 extends the upper relation with current discard and unwind configurations.
  The batch covers normal cleanup completion, consumed-clause return and close
  completion over general restored tails, then projected cleanup/resource
  transitions and callback-local discard with protected obligations outside
  the selected capture. The local-discard case selects an ordinary mapped
  capture; arbitrary outside segments remain intact. Current projection
  preflight is explicit, and recursive protected-capture rejection remains
  unchanged. Estimated active work is 2–3 hours in parallel with C4. This yields
  approximately 2.5–4 hours elapsed implementation time before independent
  review and affected verification, subject to the identified interfaces.
- At the user's request, C4 is now split between receiver-aware frame/site
  migration and a separate selected-handler capture leaf. The first worker owns
  the shared execution definitions and publishes their interface; the capture
  worker owns only the new consumer leaf. Family selection must invert the same
  installed declaration authentication, and operand receiver checks use actual
  support rather than a conservative aggregate bound. The two implementation
  estimates can overlap: 60–90 minutes for frame migration and 90–150 minutes
  for capture, followed by their join and verification. The previous sequential
  2.5–4 hour estimate therefore no longer describes the parallel schedule.
- C4 now has a third worker for the two existing admission and execution
  example modules. Ownership is disjoint: shared definitions, selected capture,
  and existing examples. The examples retain their acceptance and rejection
  cases; this split adds no new finite execution variant. Their migration is
  estimated at 60–90 active minutes and overlaps the two proof workers.
- Lean rejected the proposed mutual witness indexed by exact `Pending` proofs
  before constructor elaboration. The approved local encoding experiment uses
  one structural `SelectedPending` witness for the predecessor, exact selected
  handler source and outside tail. Its indices retain the full answer, private
  source families, plans and rows. Capture must derive all three together from
  the current site; an independently chosen same-port source is insufficient.
  This is local execution evidence, with no change to M4 or source contracts.
  The six constructor cases and joint predecessor/outside projections now
  compile under the pinned compiler, and parent source review accepts the
  encoding. Owner insertion and cell updates still require joint transport of
  that evidence. The shared worker estimates 45–75 active minutes for these
  transports, rebuilding ordinary consumers and promotion. Final independent
  review and connected verification remain required before integration.
- C3's restored-tail batch is implemented and passes both stages of independent
  review. Connected chains cover resume followed by normal cleanup completion,
  unwinding cleanup followed by close completion, and local discard followed by
  resource release. They retain the same saved values, selected captures and
  protected outside segments, with exact observation and discharge order. Four
  affected modules pass independent pinned compilation with 53 standard-only
  reports. Grouped verification covers 858 modules and 11,572 exact reports,
  retaining 854 unchanged verified pairs; all 2,057 local links and anchors pass.
  The restored-tail batch is integrated. Direct reuse of cursor normalization,
  suffix and projection proofs completed implementation ahead of the 2–3 hour
  estimate. Current Unit redexes and structural projection preflight remain
  explicit; callback termination and arbitrary selected-segment projection are
  not established by this batch.
- C4's connected fixed-world gate is implemented and passes both stages of
  independent review. The promoted source/authentication/substitution layers
  reach receiver-aware saved frames and execution sites, then actual selected
  handler capture. The successor site, guarded capture and actual Core step
  retain the same full contract, private family and complete rows. Joint owner
  and cell-update transport preserves the predecessor and active outside tail;
  all ordinary builtin and cell-reply methods remain. The existing twelve
  admission and five execution reports and negative cases are retained.
- Fresh parent compilation verifies 21 affected modules with 96 standard-only
  reports under Lean 4.33.1. The worker's version metadata was collected outside
  its compilation directory and selected a different toolchain. That record is
  retained; fresh parent builds and same-directory compiler, library and
  standard-library hashes supply the authoritative pinned evidence. Review
  accepts the complete source/artifact closure. Grouped verification covers 875
  registered modules and 11,623 exact reports, retaining 854 unchanged verified
  pairs. All 2,061 local links and anchors, import order, trust, whitespace,
  artifact scans and changed-document Markdown lint pass. One trailing space in
  Execution was removed and its three dependent modules freshly rebuilt.
- Existing structural proofs completed the joint transport sooner than the
  revised 45–75 minute estimate. The requested C3 restoration batch and C4
  consumer connection now require no further implementation. C4.1 stays open
  for higher-order saved-support transport after restoration; current request
  metadata/origin production remains C2 work. No new finite example or unrelated
  work package was added.
- The next C4.1 batch runs saved-support reconstruction and the actual resume
  consumer in parallel. A pinned local counterexample shows that a declaration
  reading its formal cannot retain an empty stored support bound when its
  receiver gains a resource. Same-receiver world authentication transport and
  the exact declaration obstruction compile locally with four standard-only
  reports. These prerequisites are not an integrated restoration result.
- Independent interface review accepts deterministic support reconstruction:
  compute each stored declaration bound from the same body's dependencies and
  the actual lexical receiver. Preserve complete row structure, contracts,
  signatures, clause rights, offered modes, owner demands, footprints and private
  plans; identify only the changed support leaves explicitly. Public callable
  contract rows remain fixed. The actual consumer must derive its successor
  source, resource checks and accounting from the predecessor.
- The companion pending relation lacks the consumed-owner case emitted by actual
  resume. Its minimal spent constructor and matching existing transport cases
  are assigned to the resume consumer. That worker owns the shared Execution
  module; the support worker owns its separate reconstruction leaf. The third
  worker constructs the independent callback-source/request connection. Runtime
  cleanup correspondence alone does not authenticate the same action's request
  list, so the initial callback source must retain that static identity before
  current request membership and closing routes are derived. All three workers'
  actual GPT-6.1 Sol medium assignments are verified from session metadata.
- No package count changes at this interface checkpoint. The restoration batch
  is estimated at 3–6 active hours for support reconstruction and 2–4 for its
  consumer, plus 1–2 for integration and review: about 4–8 elapsed hours with the
  two implementations in parallel. The callback connection is estimated at 2–4
  active hours in the third slot. Estimates depend on constructive transport of
  the existing certificate and accounting across the changed support leaves;
  the next bounded checkpoint checks that interface. These estimates replace
  the prior unknown restoration interface, not the remaining whole-goal work.
- The callback request/route connection is implemented and independently
  reviewed. Fresh parent compilation passes with 20 standard-only reports and
  all 465 selected dependency source/artifact pairs checked under Lean 4.33.1.
  The same stored action constructs its initial source and authentication;
  actual local execution retains its exact request allowance. Current membership
  and closing routes connect to actual projected cell read dispatch. The leaf is
  registered and its coverage limits are recorded. Validated Core metadata must
  still construct the stored static evidence; C2 remains open. Direct reuse of
  existing typing and dispatch proofs finished this bounded implementation ahead
  of its 2–4 hour estimate.
  Its grouped audit covers 876 registered modules and 11,643 exact reports,
  retaining the unchanged 875-module baseline. All 2,064 local links and anchors,
  import order, trust, whitespace, artifact scans and five changed-document
  Markdown checks pass. Concurrent restoration work has separate evidence.
- C4.1 now has three independent lanes. The source/authentication worker has
  frozen deterministic support, frame and handler reconstruction, plus exact
  context decomposition, with 23 local standard-only reports. The third worker
  then completed raw `Code`/`Pending` and `Run`/`Wait` transport across that
  structural delta, with six local reports and six public interface checks.
  Requests reconstruct the same selected private body family; resume and discard
  split saved and active tails. Scalar demand and the root are unchanged.
  Independent parent reconstruction remains required for this new component.
- The resume worker's consumed-owner constructors and existing transports pass
  fresh pinned compilation with 38 reports. Exact selected-handler and typed
  prefix suffix rebasing passes with 13 local reports, including nested dormant
  captures. These results remain prerequisites. Canonical resource checking and
  the actual restored successor site are the remaining implementation gates.
  A checking leaf imports the frozen accounting and support leaves to avoid an
  import cycle. It must derive checks from the same installation and computed
  bounds; an assumed desired successor is inadmissible. The completed accounting
  worker now independently reviews the resume lane. Counts remain unchanged.
- Fresh parent compilation reconstructs the shared consumed-owner changes,
  frozen support/context leaf, raw admission/accounting and existing execution
  examples: five modules, 72 standard-only reports under the same pinned compiler
  and library. Independent review accepts context selection, cuts, splitting and
  request budgets. Signature equality alone does not establish literal source
  and plan identity; the canonical checking receipt must retain the original
  installation provenance. No source contract or M4 index was weakened.
- C2 and C3 proceed independently of the remaining restoration consumer.
  `CoreCallbackAdmissionProducer` constructs the same closed callback's source,
  authentication, translation link and initial application typing from a stronger
  graph derivation. Its private-plan endpoint inverts the actual lambda before
  recovering the plan and complete rows. Independent compilation reproduces
  11 reports and the exact artifact/log, checking 495 dependency pairs. Validated
  shape metadata does not yet construct that derivation, captured environments
  lack static substitution evidence, and declaration certification remains open.
  The bounded producer is complete; the general C2 count remains 0/4.
  Registration found three older dependency sources in its frozen graph. A
  coherent rebuild of those modules and affected consumers passes for ten
  modules and 93 reports against the current baseline, with all 495 dependency
  pairs checked before and after. The producer source is unchanged; the earlier
  artifact reproduction is scoped to its predecessor graph.
- `CoreResumeReadiness` derives active handler definitions from the same related
  physical segment and actual owner cut, then reuses the existing actual Core
  and positive target resume witness with the full saved prefix. Independent
  review and compilation reproduce six reports and the exact artifact/log,
  checking 283 dependency pairs. This covers the experimental graph counterpart
  of the Rust post-consumption handler lookup. Allocation, storage, control-work,
  registration and disposal preparation, and the general Rust bridge remain
  open. The component is complete; the general C3 count remains 0/5.
- Their registered subset contains 878 modules and 11,660 exact reports, reusing
  the unchanged 876-module callback baseline. Concurrent restoration work has
  separate evidence and is excluded from this subset. Both bounded components
  finished within their revised preparation estimates; a whole-package estimate
  still depends on the validated Core admission bridge and simulation coverage.
- C4's checked restoration recursor now compiles all 23 code and pending
  constructor cases against the concrete raw certificate reconstructed from the
  predecessor. Its frozen leaf has 18 local standard-only reports; independent
  review remains required. The actual resume consumer still must splice the
  saved source onto the current front. A handler's entry allowance can exceed
  its private residual, so the front producer must retain and append the exact
  selected installation's entry allowance. Private handler residuals and
  full owner-contract interfaces remain fixed. The prior elapsed estimate is
  at risk; this bounded splice and its review determine the revised estimate.
- The checked restoration and actual resume consumer now pass independent
  review. `Site.resume` in `CoreCallableRestoredResume.lean` derives canonical saved
  support/checking, the complete saved/front/spent/outside splice, actual operand
  reauthentication, root consumption and the spent phase from the current site.
  The exact selected entry allowance widens only the outer front allowance;
  private handler residuals, literal plans, all non-support row data and full
  contracts remain unchanged; support bounds are deterministically reannotated.
  `Site.resume_plug` connects the physical restored plain head
  to the existing bind consumer. Fresh independent compilation checks 33 reports
  and 463 exact dependency pairs. The checkpoint's inherited Checking-stage
  metadata is recorded separately from its actual resume report count and scope.
- `CoreCallbackRecipeProducer` passes independent review and 12 fresh reports.
  Its suffix recipe certifies the existing consuming clause's full family for
  every owner, including occupied components. `callback_lambda` constructs the
  same checked lambda and stored callback from an actual body derivation at its
  literal plan and rows plus structural recipes; translation, instantiation,
  initial typing and start follow. Validated Core must still produce or validate
  these annotations and captured-environment evidence. The factory exposed an
  accidental auto-implicit policy parameter in `StoredCallback.certified`;
  qualifying the intended cleanup policy removes it while retaining all private
  and all-owner obligations. Independent routes compilation checks 20 reports.
- `CoreCallableResumeCorrespondence.Site.resume_correspondence` passes independent
  review and four fresh reports with 503 exact dependency pairs. The current
  actual lookup, related segment/value and explicit dynamic-name and scope
  coherence select the same complete cut as the checked resume consumer. Its
  rich successor therefore inhabits the actual Core endpoint with the same full
  contract, root consumption, phase, resumed observation and ownership
  accounting. No desired future invariant or endpoint is assumed. General
  reachable configurations must still construct the current coherence premises.
- The bounded C2 and C3 lanes proceed in parallel. Their next assessments target
  the validated metadata annotation producer and current configuration coherence,
  respectively. The earlier whole-goal estimate is no longer reliable; these
  concrete gaps determine the next implementation batches. Counts retain the
  original full-package inventory rather than counting components as packages.
- The registered grouped audit passes for 885 modules, 11,760 exact reports
  and 2,083 local links/anchors. The complete changed-source reverse dependency
  closure contains 12 freshly compiled modules with 174 reports; 873 unchanged
  modules retain exact baseline source and report provenance. The three final
  consumers pass 49 fresh parent reports against a coherent 534-pair dependency
  set. Source and selected artifact hashes, compiler/libraries, report names,
  standard axioms, import order, trust, whitespace and artifact exclusion pass.
  Unregistered prototypes and unrelated user files remain outside the subset.
  This completes the bounded restoration integration; full C2–C5 remain open.
- The next parallel increment has three proof lanes and one existing-export
  connection. C2 checks finite callable metadata and lexical support against the
  same graph, then feeds the receiver-aware lambda interface; recursive body
  admission and literal private-plan provenance remain separate. C3 constructs
  current capture-history and saved-scope receipts consumed by actual resume.
  C4 constructs the rich initial site and its available lower progress
  connection, avoiding the refuted legacy authentication adapter.
- The independent C2.2 export batch owns
  `src/core/alignment_export_tests.rs` and a generated
  `CoreExportedOperationMetadata.lean`. The existing registry traversal already
  instantiates every operation signature but retains it only as manifest text.
  Emit structured `CoreOperationSignatures.RawEntry` data from that same
  traversal and identity mapping in a separate module, leaving graph export
  unchanged. Check the generated declarations with the existing port builder,
  exact origin-manifest equality, stable export, and positive/negative signature
  checks. This supplies executable declaration input, not enriched private
  callable evidence or general Core admission. Reuse the existing fixture;
  no additional finite example is planned.

| Package | Completed / total identified items | Current state | Outstanding items | Dependencies or blockers | Estimated remaining active work |
| --- | --- | --- | --- | --- | --- |
| C1 | 5 / 5 | Integrated comparison and discrepancy inventory | Maintain findings | None | Complete |
| C2 | 0 / 4 | 14/16 original checker forms plus finite resource sidecar and exact paired consumers integrated | Initial registry/admission connection; finite handler and broader resource bodies; metadata/storage origins | Original graph/private-family/storage origins; checked cell-registry transport | 15–26 combined agent-hours before contingency; next producer checkpoint 2–4 active hours |
| C3 | 0 / 5 | Current ticket bounds, first-acquisition maps and exact registered cleanup start integrated | General cleanup entry; saved-anchor guards; projection/disposal; full simulation/preparation | C2 admission; current site/position transport and original Rust map/ledger origins | 16–29 combined agent-hours before contingency; next guard checkpoint 2–4 active hours |
| C4 | 2 / 3 | Restoration/resume repairs and regressions retained | Discrepancy closure across the declared fragment | General C2/C3 coverage may expose further required repairs | 3–6 combined agent-hours before contingency |
| C5 | 0 / 4 | Full 90-step admitted example independently verified | General theorem, coverage records, grouped verification and independent review | C2–C4 | 6–10 combined agent-hours before contingency |

Checkpoints `2de8f55` and `aa71286` integrated three leaves/24 reports and
four leaves/64 reports respectively. Checkpoint `acb7724` coalesced three
reviewed components; `bbe7317` batched two additive consumers. The current
increment batches finite resource checking and registered cleanup start. The original paired
Admission/static/storage successes remain upstream providers; 14/16 checker forms
do not establish arbitrary initial admission. Current guards, changed-tail
activation and projection/disposal remain open. Two user-owned unregistered
handler prototypes remain excluded and unchanged.

Checkpoint `acb7724` retained the
[rich resource foundation](../design/direct-effects/one-shot/CoreCallableRichResourceFoundation.lean).
It adds the existing lower resource rule to IndexedSource and hereditary
authentication, preserving fresh world/receiver opening, original-world output
formation, residual allowance and Hides. Substitution and restoration retain
total full Plan/Rows families at every identity; Source/Auth recursion applies
only to fresh openings. The paired-formal consumer constructs integer-init and
formal-return resource Source/Auth from the same upstream paired receipt,
preserving full rich/storage contracts, original map and exact slot result.
It does not manufacture that upstream Admission.
[Pointwise probes](../design/direct-effects/one-shot/ResourcePointwiseProbes.lean) reproduce the old
substitution failure and preserve varying identities;
[retention/namespace probes](../design/direct-effects/one-shot/ResourceFoundationProbes.lean) reject fresh
capture into an older receiver and preserve ordinary formals with equal names.
Both missing rich source constructors are supplied. The finite checker remains
14/16; handler/resource annotations and general admission remain open.

[Generated completion](../design/direct-effects/one-shot/CoreCallableGeneratedCleanupCompletion.lean)
computes normal finish from the same generated history and original receipt,
restores saved value/code/scope and retires that cleanup owner. CaptureData
retains clause/closing equations already produced by capture. Structural
resume and handler/spent head decompositions fix direct-versus-append history
composition, deriving physical selection and complete receipt partitions from
the same current constructors. No arbitrary equivalence or desired matching is
accepted. The [nested probe](../design/direct-effects/one-shot/GeneratedNestedHandlerProbes.lean) has
17 post-start edges and 18 actual Core steps including start, exact four-frame
full-prefix restoration, both handler returns, spent return and completion.
Original typed receipts persist through capture, operand evaluation, resume and
return. [Completion guards](../design/direct-effects/one-shot/GeneratedCompletionGuards.lean) preserve the
spent barrier. At that checkpoint, the current TicketBound provider remained
external; the following increment derives it for this generated chronology.
Saved-scope activation, deeper maps, projection/disposal and whole reachable
simulation remain open.

[Metadata preparation](../design/direct-effects/one-shot/CoreRuntimeMetadataPreparation.lean) retains
finite map presence/distinct activation entries and rejects rows/nonactivation
entries. Current literal resource/request control computes ordered requests:
acquisition 2n+3 even for a shadowing key; cell effect 3 before top-down frame
visits. Clone failures report optional request None, parameter charges Some(1).
Produced map/effect/cut agreement connects to the same actual Core endpoint.
Same effect-ID handler metadata and wider structural type/row traversal remain
unsupported. Runtime ledger/word/disposal/map-erasure/physical-length guards
are supplied current obligations. Generic Origin is an unindexed passthrough;
it proves no full C2 lineage or observer origin. Faithful Rust Host replies
must return at the zero-size row reservation while retaining its ordinal;
arbitrary abstract refusals are not executable failure equivalence.
[Metadata probes](../design/direct-effects/one-shot/CoreRuntimeMetadataPreparationExamples.lean) and two
independently replayed internal-Machine Rust tests check computed exact/one-short
budgets, shadowing, diagnostics and published observation prefixes. They do not
prove validated-program reachability. The initially selected write operation
was a fixture error; retained QA uses the original read. Runtime behavior and
normative semantics are unchanged.

Seventeen existing modules changed; nine new modules/probes were registered.
The 64 affected modules compiled once in 205.8 seconds, with 6.3 seconds
preparation/hash checking. Immutable hardlinks reused 863 unaffected artifacts
and logs. Every selected direct-import hash agreed in one cache. That checkpoint
contained 927 modules and 12,170 ordered standard-only reports, 80 more than
`aa71286`. M0–M4, the fragment and whole-package counts were unchanged.

Checkpoint `bbe7317` retained the
[current ticket-bound producer](../design/direct-effects/one-shot/CoreCallableGeneratedTicketBound.lean).
It derives actual capture-event coupling for all twelve named operations,
transports ticket-name counts through their finite target traces, and derives
the current full-point and lexical-suffix bounds by induction over the same
generated chronology. Multi-step bind return uses the existing transition
name bound. Completion consumes the produced current bound; only the original
pre-start suffix bound remains an input. [Ticket probes](../design/direct-effects/one-shot/GeneratedTicketBoundProbes.lean)
reuse the eighteen-step nested cycle, including its nonempty captured/spent
name, and reject an unissued spent name. Seven producer and eleven probe reports
pass. Original admission and saved-scope activation remain separate obligations.

[First-acquisition map origin](../design/direct-effects/one-shot/CoreRuntimeIndexedMetadataOrigin.lean)
derives empty-map agreement from the existing ProducedBindings output indexed
by the same full rich/storage/lexical environment. The original empty finite
map retains its supplied absent or present-empty flag. The actual acquisition
computes the singleton map and its agreement with the installed environment;
a current request consumes that exact key/map/environment without a supplied
erasure-agreement premise. [Origin probes](../design/direct-effects/one-shot/CoreRuntimeIndexedMetadataOriginProbes.lean)
check exact/one-short acquisition and request budgets, original presence,
finite keys and diagnostics. Nine producer and thirteen probe reports pass.
These are separate conditional current steps: no continuous acquisition-to-request
execution, original Rust presence/ledger/physical-length origin, prior mixed
map coverage or general graph admission is proved. The translated resource's
original handle-binding wrapper and full Source/Auth/storage association remain
C2 dependencies; this leaf contains no arbitrary Origin passthrough.

Both additive components passed author-disjoint semantic and quality reviews.
Their four leaves compiled together in 3.5 seconds, with 8.1 seconds of
preparation/hash checks; all 927 prior artifacts and logs were reused unchanged.
That checkpoint contained 931 modules and 12,210 ordered standard-only reports,
forty more than `acb7724`, with exact selected direct-import hashes.
No Rust source changed and no Rust test group was rerun.

The current increment retains the [finite original cell schema](../design/direct-effects/one-shot/CoreCallableFiniteCellRegistry.lean)
and [resource template checker](../design/direct-effects/one-shot/CoreCallableFiniteResourceTemplate.lean).
The schema checks the same exported raw read/write declarations and source
manifest, with their original API formal binder. Resource-opening binders remain
independent. Non-cell operation lookup preserves the original full contracts.
Finite body tags cover scalar values, references, ordinary variables, pairs,
binds and cell read/write. They compute actual opened Code, requirements,
dependencies, private Plans and full Rows at every identity. Source/Auth apply
only at fresh identities. Original names, positional slots, shadow order and
receiver issuance are checked; each initial environment equals the entire
original Bindings list. The resource checker constructs Source/Auth for an
integer initializer and non-retaining output under its explicit cell registry.

[Paired consumers](../design/direct-effects/one-shot/CoreCallableFiniteResourceConsumers.lean) take the same
produced ArgumentReceipt, bind the translated resource handle, read the fresh
cell and return the original full contract. Source uses the entire original
rich environment and lexical map; lower storage uses the entire original
storage map and original stored contract. [Probes](../design/direct-effects/one-shot/FiniteResourceTemplateProbes.lean)
check varying private resource-family members, shadowing, binder namespaces,
fresh-reference escape and retained higher-order contract fields. The 47
ordered reports include one repeated existing non-retention report. This is
a separate finite checker: the original StaticProducer remains 14/16. Its
initial registry/admission connection, general initializer and new higher-order
resource-body constructors, handler, branch, cleanup and nested resources remain
open. The graph wrapper result assumes its original shape check; the lower
storage result is a constructed derivation, not an extended recipe checker.

[Cleanup registration sites](../design/direct-effects/one-shot/CoreCallableGeneratedCleanupRegistration.lean)
derive action/body child lineage from the same actual registration node and
produce the original full cleanup receipt. Actual body steps derive heap
extension and connect that receipt and original suffix to the same normal start
and Generated.initial endpoint. The child-site consumer rejects immediate
re-entry to the original active caller's handler; it receives no independently
supplied body-site proof. [Registration probes](../design/direct-effects/one-shot/GeneratedCleanupRegistrationProbes.lean)
compose three actual Core steps at an active captured caller scope, retaining
that original scope while callback invocation uses empty scope. Nine producer
and six probe reports pass. Registration currently consumes MappedHistory;
arbitrary general-suffix registration, initial admitted reachability, general
body progress and changed-tail capture/resume anchor transport remain open.
This does not remove outsideCheck or derive unconditional activation guards.

Both components pass author-disjoint semantic and quality review and fresh
isolated replay. Their six leaves compile together in 9.4 seconds, with 5.4
seconds of preparation/hash checking, reusing all 931 prior artifacts and logs.
The current audited assembly contains 937 modules and 12,272 ordered standard-only
reports: 62 additional reports and 61 new report names. Selected direct-import
hashes agree in one cache. No Rust source changed and no Rust tests were rerun.
M0–M4, the declared fragment and whole-package acceptance counts are unchanged.

The planning range is 40–71 combined agent-hours of identified work, or 50–90
with approximately 25% unexpected proof-failure/rework allowance. Expected
resumed elapsed work is 25–45 hours with two proof lanes plus review/integration;
the central planning estimate is about 35 hours, with low-to-moderate confidence.
Session logs record approximately 30 main-task and 72 sub-agent active-turn
hours, including checks, coordination and waits. The last six development hours
used about 18.5 combined agent-hours and retained ten proof implementation
commits. General admission and generated simulation are harder integration
obligations, so component delivery rates are not extrapolated directly.
These whole-goal estimates replace prior estimates covering only bounded gates.

After this gate, C2 connects checked exact cell-entry compatibility and the
finite resource checker to original initial admission, then extends the missing
handler and resource-body forms. C3 connects actual cleanup registration over
general histories to Generated operations and derives capture/resume position
transport for saved-scope activation, followed by projection/disposal. Original
Rust map/ledger origin and remaining metadata consumers are C3.4 dependencies. Next checkpoints remain bounded at
2–4 active hours with disjoint outputs. Reassess at the original 4–6 resumed-hour
gate; this prerequisite progress does not itself narrow the whole-goal range.
Batch related edits/reverse consumers without narrowing acceptance.

### Acceptance detail at the current checkpoint

The counts above measure closed whole-fragment acceptance items. They do not
measure implementation activity or completed proof components. The detail below
records those components and the remaining obligation for each original item;
the inventory and acceptance boundary are unchanged. Report proof status as
integrated, independently reviewed, locally verified, or in development.
Compilation and axiom-report counts are verification evidence, not measures of
semantic coverage or equal amounts of work.

| Item | Verified component and status | Exact remaining acceptance obligation |
| --- | --- | --- |
| C2.1 typed translation | Finite Core syntax translation and supported type realization are integrated. [GraphAnnotationChecks](../design/direct-effects/one-shot/CoreCallableGraphAnnotationChecks.lean) independently verifies same-site function/binder/body metadata and computed support guards. | Construct the recursive structural source and authentication derivation from validated graph/annotation data; the lambda gate currently receives the body derivation. The producer retains 14 of 16 constructor forms, including receiver-aware lambda, cleanup, resume and discard. Rich cleanup/resource source and full pointwise transports are retained. The bounded storage producer is retained; the finite resource sidecar now constructs exact opened Source/Auth from finite data, including full returned slots. Original registry/initial admission integration, handler checking and broader resource-body/full-contract recipe specialization remain open. |
| C2.2 exact identities/signatures | Exact effect argument trees, type realization and conflict-checked declaration-port construction are integrated. Structured declarations now come from the same Rust registry traversal and identity maps; independent review passes with nine Rust tests and fresh Lean metadata compilation against 52 dependencies. One regeneration test is intentionally ignored. | The generated declaration checker is independently reviewed and current-source verified; this checkpoint retains its integration. Manifest equality pairs the artifacts; it does not prove general Rust-to-Lean translation soundness or private callable certification. |
| C2.3 lexical resources/capabilities | Receiver-conditioned source support, actual operand authentication and restored support/checking are integrated. The new graph annotation gate has passed independent review. | Derive actual bound-value/captured-environment authentication and literal private-plan origin. Recursive body authentication and private-row refinement remain inputs to the gate. |
| C2.4 initial admission | [InitialAdmission](../design/direct-effects/one-shot/CoreCallableInitialAdmission.lean) constructs the rich initial Site from the same supplied static Source/Auth, contracts, plan, rows and accounting; independent review passes. It projects typing/joint validity and an actual first progress step. | Produce that static Program from validated Core. General rich successor preservation and M4 availability are not established by the first-step projection. |
| C3.1 configuration relation | Existing value/environment/frame relations are integrated. [ReachableResume](../design/direct-effects/one-shot/CoreCallableReachableResume.lean) has passed independent review for current and saved frame ownership/scope receipts. | Construct and preserve the combined relation for all reachable states, including cleanup, disposal, handler exit and restored saved-prefix scopes. Arbitrary GeneralChain data do not authenticate these receipts. |
| C3.2 transition simulation | Actual transition components include strict computation, cells, handlers, capture, resume, discard and cleanup. The checked resume successor inhabits the actual Core endpoint. Newly reviewed capture/beta/bind/resume factories produce their current coherence premises. | Assemble whole-fragment step coverage under the same reachable relation. The cleanup-origin batch is independently reviewed and current-source verified for actual registration, callback entry and return; later disposal/projection transport remains open. |
| C3.3 observations/ownership | Exact restored prefix, consumed root, spent phase, resume observation and accounting are integrated. Current history now derives dynamic ticket uniqueness in the reviewed resume factory. | Preserve these observations and ownership guarantees throughout every covered execution, including cleanup and disposal, using one reachable invariant. |
| C3.4 capacity and preparation | Runtime failure classes are recorded. The formal resume-readiness component derives post-consumption handler availability from the actual physical segment. | Connect allocation, storage, control-work, registration and disposal preparation to Rust execution; do not equate successful formal freshness with runtime reservation success. |
| C3.5 nonvacuity | Existing transition consumers use actual Core endpoints and positive calculus steps; ranked administrative components are integrated. | Establish the justified administrative matching/progress measure for the complete simulation, not only its individual transition components. |

The retained six-deliverable checkpoint `d2f26e1` was independently reviewed
and current-source verified. At that checkpoint, all 891 registered Lean modules were freshly compiled
from the same frozen current sources using pinned Lean 4.33.1, warnings as
errors, and only the newly produced dependency cache and standard libraries.
All 11,814 ordered axiom reports use only the standard axioms. The independent
packaging audit checks source, compiler/library, command, log, artifact and direct
import hashes. This replaces the earlier cache association whose recorded source
hashes did not establish which source produced the selected artifact. No failing
current proof was bypassed. Full `cargo xtask verify` passes, including 2,902 tests
with no failures and two intentionally ignored tests. This checkpoint retains the six-deliverable
integration.

The retained C2 producer constructs same-code Source/Auth for 14 constructor
forms without taking these judgments as annotation inputs. It checks whole graph
shape, root type/effect metadata and the same translated literal Code. The retained
14-case checkpoint includes resume/discard. Handler and resource remain
unimplemented in that checkpoint. Literal full contract and
plan-family origin, interior metadata, registry/owner origin and actual runtime
captured values remain separate obligations; the structural instruction grammar
is bounded, not a serialization proof for all typed input data.

Rich cleanup source/authentication and environment, owner, allowance, substitution,
receiver and restoration transports are retained. The callback's full Unit→Unit
contract, requests, latent row, public plan and complete public rows remain fixed;
the actual callback/body plans and rows are recursively constructed. This is
source and transport coverage, not general cleanup transition preservation.
The preceding checker/storage checkpoint `ab71211` assembled 893 modules:
fresh checker and storage-producer compilations, the complete 29-consumer cleanup
reverse closure and 862 unchanged current-source associations.
That checkpoint contains 11,842 exact standard-only reports, with direct-import artifact hashes
preserved. Resource admission still requires paired returned-storage evidence at
the same body/value origin and replacement contract. The bounded storage
producer is retained after review; control/resource/cleanup and runtime origin
remain open there.

The remaining whole-goal estimate depends on constructing that complete resource
interface and combined reachable-state relation without assuming their target
invariants. The next review/adoption batches remain bounded and do not change the
acceptance inventory or declare C2–C5 complete.

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

Close-identity correspondence must cover both empty and nonempty discard
projection. Core increments its ghost close counter only for nonempty work;
the lexical calculus creates a close owner on every discard. The current
nonempty fixture cannot justify equating these counters in general. This
refines the existing C3.1/C3.3 ownership obligations without changing the
fragment or acceptance inventory.

Higher-order resume can add receiving resources after capture. The retained
[positive fixture](../design/direct-effects/one-shot/fixtures/core-resume-clause-cell-closure.ash)
captures before acquisition, then resumes with a closure retaining a cell
acquired in its clause; invocation within the restored continuation returns
`Unit`. The [outside fixture](../design/direct-effects/one-shot/fixtures/core-resume-clause-cell-closure-outside.ash)
is rejected with `type.resource-escape`. Both results were checked through the
current worktree's CLI. C2.3/C4.1 therefore require saved source/support transport
under the restored world and receiving context, beyond the current fixed-world
plain/cell checkpoint. This records existing scope rather than adding a package.

## Deviations

No scope change. The C1 fragment and transition inventories remain the acceptance
boundary for C2–C5; verified components do not replace their full coverage.
