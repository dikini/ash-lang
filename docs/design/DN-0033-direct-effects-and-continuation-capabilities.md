# DN-0033: Direct Effects and Continuation Capabilities

- ID: `DN-0033`
- Status: exploring
- Related: [DN-0031](DN-0031-resource-composition-concept-map.md), [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md), [DN-0009](DN-0009-effects-handlers-and-continuations.md), [DN-0012](DN-0012-coeffects-and-hooks.md), [DN-0013](DN-0013-session-and-resource-protocol-stress-tests.md)

> This note proposes a direct operational foundation. It defines no current
> Ash semantics, accepts no architecture, and authorizes no implementation.
> The sequential rules below are a candidate calculus; the resource,
> duplication, transfer, and scheduling extensions have explicit proof
> obligations. No full one-shot type-safety theorem or complete inference algorithm
> is claimed.

The [one-shot formalization](direct-effects/one-shot/README.md) develops the
structural judgments and checked proofs for this note's first kernel. Its
evidence status distinguishes completed lemmas from remaining obligations;
the schematic predicates below are not proof assumptions.

## Current Core alignment pressure

[TASK-0032](../tasks/TASK-0032-core-one-shot-alignment.md) compares validated Core
with the completed annotated M0–M4 endpoints. The
[comparison record](direct-effects/one-shot/CORE-ALIGNMENT.md) owns its current
coverage and discrepancies; historical experiment boundaries below do not
supersede that task or reopen completed calculus milestones.

The bounded [callback route experiment](direct-effects/one-shot/CoreCallbackRequestRoutes.lean)
retains one authenticated stored action through actual local execution and uses
its exact request allowance to construct projected cell dispatch. Its static
producer from validated Core metadata remains a task obligation. This result
supplies admission and correspondence evidence at the stated boundary; it does
not define a language rule.

The [closed-callback producer](direct-effects/one-shot/CoreCallbackAdmissionProducer.lean)
now constructs source and authentication from an existing graph derivation for
the same closed action, retaining the actual lambda's private plan and rows.
Validated metadata must still construct that derivation and declaration
certification. The [resume readiness component](direct-effects/one-shot/CoreResumeReadiness.lean)
derives handler definitions from the selected saved segment and connects them
to actual modeled resume. It leaves runtime capacity and the general Rust
relation open. Both results refine the comparison evidence without changing
current language semantics.

The [callback recipe factory](direct-effects/one-shot/CoreCallbackRecipeProducer.lean)
now constructs certification and the same stored callback from an actual checked
body, literal plan, complete rows and structural recipe. Producing those
annotations from validated Core remains open. The
[restored resume consumer](direct-effects/one-shot/CoreCallableRestoredResume.lean)
reconstructs support, checking and accounting at the actual receiving context,
and the [Core connection](direct-effects/one-shot/CoreCallableResumeCorrespondence.lean)
derives the rich successor at the modeled resume endpoint. Current name and
scope coherence remain explicit premises. These results test the higher-order
restoration obligation without weakening private contracts or changing M4;
general admission, simulation and Rust capacity treatment remain task work.

The [finite annotation gate](direct-effects/one-shot/CoreCallableGraphAnnotationChecks.lean)
now checks same-site metadata and actual receiver bounds; private body evidence
remains an input. The [rich initial constructor](direct-effects/one-shot/CoreCallableInitialAdmission.lean)
uses that stronger static boundary for an initial Site and lower first progress
step. [Reachable resume](direct-effects/one-shot/CoreCallableReachableResume.lean)
derives current owner-name and scope coherence for its actual transition
factories, and [cleanup origins](direct-effects/one-shot/CoreCallableCleanupOrigins.lean)
recover the same registered caller scope at normal completion. The
[structured declaration consumer](direct-effects/one-shot/CoreExportedOperationChecks.lean)
checks exact operation ports from the existing Rust export. These are bounded
admission/correspondence inputs. General resource admission additionally needs
an actual returned-storage contract: a resource-free output port does not exclude
a closure retaining the acquired cell. The task records this missing rich
resource/cleanup source boundary and its required constructive producer.

The [recursive producer](direct-effects/one-shot/CoreCallableStaticProducer.lean)
now constructs body source/authentication for fourteen constructor forms. The rich
cleanup grammar and its required transports retain full callback contracts and
public plans/rows. Resource admission still needs paired actual returned-storage
and replacement evidence; the bounded storage and owner-checker components are
reviewed and retained, with remaining control/runtime origin obligations explicit. These additions test constructive admission within the
stated instruction grammar, not full composition completeness, runtime value
origins or general simulation.

The [running-cleanup transport](direct-effects/one-shot/CoreCallableCleanupReachableTransport.lean)
retains the same installed callback and saved caller receipt through actual
capture, rejects physical disposal of running completion and restores ownership
through full-prefix resume/Unit completion when the original owner match remains
inside the captured suffix. The [literal-site lineage producer](direct-effects/one-shot/CoreCallableSiteLineage.lean)
derives current clause/child ancestry and actual capture/beta/bind site receipts.
Outside-anchored restoration still needs past installation receipts for moved
handler frames; current ancestry and fresh dynamic tickets alone do not supply
that history. These bounded components do not close general reachability or
whole-fragment simulation.

The [paired initializer/operand consumer](direct-effects/one-shot/CoreCallablePairedOrigin.lean)
checks the same actual initializer and operand at their full rich and exact
storage contracts. It constructs substitution/application Source/Auth and
same-code storage receipts with the original return bound. The [past frame producer](direct-effects/one-shot/CoreCallableFrameInstallations.lean)
keeps the full selected Clause, handler data and original suffix/maps while
constructing actual capture/resume receipt movement. These reviewed components
supply missing pairing data. The [general-history extension](direct-effects/one-shot/CoreCallableGeneralHistory.lean)
now retains the same installations through heap extension, running completions,
normal cleanup start/finish and guarded actual capture. Current capture
route/effect/index/lookup production, outside-owner misses, projection and disposal
remain open. The [parameterized storage recipes](direct-effects/one-shot/CoreCallableStorageRecipes.lean)
retain full actual higher-order contracts and prove a universal formal-return
fresh-opening case. This is not arbitrary universal body acceptance or rich
resource Source/Auth. Captured-callee origins and actual-return observer transport
remain separate obligations. Both bounded leaves passed independent review and current-source integration.
Whole-fragment admission and simulation remain open.
The reviewed general-history extension derives nearest owner selection, stops at
a matching spent marker, and constructs actual full-prefix resume history with
the same installed Clause/header. Current operand and scope-resolution guards
remain; outside-caller barrier history, projection, disposal and whole
reachability stay open. The extension passes independent review and fresh
current-source integration.

The [literal ordinary-call consumer](direct-effects/one-shot/CoreCallablePairedCall.lean)
now computes original callee body/recipe agreement with separate callee and
caller bindings/maps, actual nearest captured-slot bounds, exact original storage
domain/result and same substituted-body storage. It passes independent review
and fresh integration. Runtime closure origin, deterministic captured recipe
substitution and universal varying-storage families remain open; a current
concrete call does not close rich resource admission.

The [physical handler selector](direct-effects/one-shot/CoreGeneralHandlerSelection.lean)
now derives the exact same-history candidate and effect from actual successful
lookup and feeds actual capture. The [checked outside restoration](direct-effects/one-shot/CoreCallableOutsideOrigin.lean)
derives the original live/spent caller path and same running receipt from the
current front/spent scan. Both pass independent review and current-source
integration. Current route/readiness and scan guards remain. Dormant running
history retains original origin; changed-tail caller activation needs actual
return history at completion, not a universal immediate scan-success assumption.
Rich admission, projection/disposal and whole simulation remain open.

The [caller bind/reset/return factories](direct-effects/one-shot/CoreCallableCallerBarriers.lean)
now retain actual same-literal bind installation, immutable original suffix
history and beta reset. Actual return at the saved bind head over that same
suffix constructs caller continuation site/scope and positive target steps.
A same-active-caller clause miss is local; repeated dynamic reset activations
remain allowed. These five reports pass independent review and current-source
integration. Combined chronological occurrence history for changed-tail cleanup
activation, projection, disposal and whole simulation remain open.

The preceding capture/origin checkpoint integrates five independently reviewed proof leaves.
[Captured substitution](direct-effects/one-shot/CoreCallableCapturedSubstitution.lean)
retains the full storage contract and exact restored-lexical private family;
the [direct lambda constructor](direct-effects/one-shot/CoreCallableCapturedLambdaConstructor.lean)
now constructs the whole returned lambda from that same transformed family.
This discharges their particular family-coupling gap, not general admission.
[Runtime binding v2](direct-effects/one-shot/CoreCallableRuntimeBindingOrigins.lean)
derives actual checked-lambda evaluation and value-ready bind installation.
Its original nonvalue-focus/value consumer was vacuous and remains excluded;
open/evaluating and capture-substituted initializer lineage remain open.
[Running occurrence](direct-effects/one-shot/CoreCallableRunningOccurrence.lean)
constructs local actual start/bind/beta history;
[cleanup activation](direct-effects/one-shot/CoreCallableCleanupActivation.lean)
derives actual marker return/finish with explicit current guards.

Their 26 fresh standard-only reports join an audited 908-module, 11,976-report
assembly, preserving the 903 unchanged dependency associations.

The preceding checkpoint `f1fc1e4` integrates
[finite captured recipes](direct-effects/one-shot/CoreCallableCapturedRecipes.lean)
and [generated-marker capture/resume](direct-effects/one-shot/CoreCallableRunningCapture.lean).
The first transports the exact successful finite checker with separate original
callee and frozen caller-specialized annotations, preserving full Contracts.
The second derives actual selected capture and immediate owner consumption from
the same running occurrence, preserving its full original clause/header and
generating the spent marker. Both pass independent review; exact fresh source,
artifact, log and report matches join an audited 910-module, 11,997-report
assembly with all 908 preceding associations unchanged.

At checkpoint `f1fc1e4`, continuous clause/callback history, actual heap-changing
transport, derived activation guards, varied storage/resource/control admission,
projection/disposal and whole correspondence remained open. [The generated initializer connection](direct-effects/one-shot/CoreCallableInitializerHead.lean) now passes independent
review and exact fresh source/artifact/log/report verification. Its five reports
extract the same original initializer/path and rich/storage checks, derive
actual three-step evaluation and the completed binding MEnv/raw-body closing,
and construct the same whole lambda family plus finite/storage judgments.
At that checkpoint it covered one closed initializer; outer callee evaluation,
multi-binding/open initializer lineage and general resource/control admission
remained open.

The preceding audited assembly contains 911 modules and 12,002 ordered standard-only
reports, with all 910 preceding associations unchanged. Checkpoint `f1fc1e4`'s
three new leaves add 26 exact reviewed reports above parent `c5fb370`'s 908 modules.
The other two leaves were freshly compiled in the preceding 910-module assembly;
this is an audited assembly, not an uncached rebuild of every module.
Checkpoint `2de8f55` added three independently reviewed components.
[Outer lambda evaluation](direct-effects/one-shot/CoreCallableOuterLambdaOrigins.lean) derives actual evaluation and ValueRel
at the same completed binding environment, retaining the original full private
family and exact finite/storage checks. It covers one binding. At that checkpoint,
recursive open initializer origins and general resource admission remained open.

[Clause execution](direct-effects/one-shot/CoreCallableRunningClauseOccurrence.lean) derives actual bind/beta/return fronts,
heap extension from tuple allocation, first physical owner selection and
full-prefix resume into the same running completion. Its local carrier does
not establish that arbitrary traces are generated executions.
[Local handler execution](direct-effects/one-shot/CoreCallableRunningLocalHandler.lean) derives actual installation,
head-local capture and normal return from that same clause occurrence. Capture
retains the old running completion outside the local cut, dormant in the
original owner receipt; normal return restores the same suffix.

At checkpoint `2de8f55`, these three leaves added 24 standard-only reports. That assembly
contains 914 modules and 12,026 reports, retaining all 911 preceding
source/artifact/log/direct-import associations. Their three productive
registration commands compile together against one coherent audited cache;
the measured leaf compilation takes 9.7 seconds. Reused dependency artifacts
are immutable hardlinks; this is an audited incremental assembly. Rust sources
were unchanged. At that checkpoint, generated mixed callback/clause chronology,
spent-marker retirement, derived activation guards, projection/disposal, resource
admission and whole simulation remained open. M0–M4 and the declared fragment
were unchanged.

Checkpoint `aa71286` constructed
[recursive ordinary runtime origins](direct-effects/one-shot/CoreCallableOrdinaryRuntimeOrigins.lean)
for arbitrary-length original prefixes of literal lambda bindings. The producer
starts with an actual empty environment, retains the same original binding path,
full private families and original recipe/map/storage checks, and constructs
three actual Core steps per installation. Its consumers evaluate the same next
lambda and recover nearest runtime lookup. Original graph/static/storage check
successes remain supplied guards. The open-initializer theorem is conditional;
no concrete inhabitant of all its full guards is claimed. Arbitrary evaluating
initializers, resource/template origins and validated metadata manufacture remain
open C2 obligations.

[Generated chronology](direct-effects/one-shot/CoreCallableGeneratedChronology.lean) extends only
through twelve named current-operation producers at the preceding exact endpoint.
It derives actual Core steps, positive or ranked administrative matching,
accounting and the complete original running receipt, including dormant captures.
At checkpoint `aa71286`, one callback had six generated operations and seven
Core steps including start. Mixed fronts and the spent barrier were checked;
the nested cycle and normal retirement were open. The current increment below
supplies those bounded paths.

[Runtime preparation](direct-effects/one-shot/CoreRuntimePreparation.lean) computes represented
cleanup/resume/discard-preflight checks from current control and the actual owner
cut, with concrete ordered reservation replies and explicit runtime-ledger guards.
Successful cleanup/resume erase to actual Core next; discard preflight yields
projection readiness, never completion. The cursor/stop records are phase-local,
not a generated projection history. [Preparation probes](direct-effects/one-shot/CoreRuntimePreparationExamples.lean)
check exact budgets, one-short refusal, finite keys, invariant exclusion and
reservation order. Complete metadata/cost/ledger origin, surrounding disposal
checks and whole C3.4 remain open.

Checkpoint `aa71286` added four registrations/64 reports, reaching 918 modules
and 12,090 reports with all 914 preceding associations unchanged. Its leaf batch
compiled in 10.0 seconds. Seven independent Rust tests checked the consumed
discard disposal boundary, without general reachability.

Checkpoint `acb7724` retained the
[rich resource foundation](direct-effects/one-shot/CoreCallableRichResourceFoundation.lean).
It adds the existing lower resource rule to IndexedSource and hereditary
authentication, preserving fresh world/receiver opening, original-world output
formation, residual allowance and Hides. Substitution and restoration retain
total full Plan/Rows families at every identity; Source/Auth recursion applies
only to fresh openings. The paired-formal consumer constructs integer-init and
formal-return resource Source/Auth from the same upstream paired receipt,
preserving full rich/storage contracts, original map and exact slot result.
It does not manufacture that upstream Admission.
[Pointwise probes](direct-effects/one-shot/ResourcePointwiseProbes.lean) reproduce the old
substitution failure and preserve varying identities;
[retention/namespace probes](direct-effects/one-shot/ResourceFoundationProbes.lean) reject fresh
capture into an older receiver and preserve ordinary formals with equal names.
Both missing rich source constructors are supplied. The finite checker remains
14/16; handler/resource annotations and general admission remain open.

[Generated completion](direct-effects/one-shot/CoreCallableGeneratedCleanupCompletion.lean)
computes normal finish from the same generated history and original receipt,
restores saved value/code/scope and retires that cleanup owner. CaptureData
retains clause/closing equations already produced by capture. Structural
resume and handler/spent head decompositions fix direct-versus-append history
composition, deriving physical selection and complete receipt partitions from
the same current constructors. No arbitrary equivalence or desired matching is
accepted. The [nested probe](direct-effects/one-shot/GeneratedNestedHandlerProbes.lean) has
17 post-start edges and 18 actual Core steps including start, exact four-frame
full-prefix restoration, both handler returns, spent return and completion.
Original typed receipts persist through capture, operand evaluation, resume and
return. [Completion guards](direct-effects/one-shot/GeneratedCompletionGuards.lean) preserve the
spent barrier. At that checkpoint, the current TicketBound provider remained
external; the following increment derives it for this generated chronology.
Saved-scope activation, deeper maps, projection/disposal and whole reachable
simulation remain open.

[Metadata preparation](direct-effects/one-shot/CoreRuntimeMetadataPreparation.lean) retains
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
[Metadata probes](direct-effects/one-shot/CoreRuntimeMetadataPreparationExamples.lean) and two
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
[current ticket-bound producer](direct-effects/one-shot/CoreCallableGeneratedTicketBound.lean).
It derives actual capture-event coupling for all twelve named operations,
transports ticket-name counts through their finite target traces, and derives
the current full-point and lexical-suffix bounds by induction over the same
generated chronology. Multi-step bind return uses the existing transition
name bound. Completion consumes the produced current bound; only the original
pre-start suffix bound remains an input. [Ticket probes](direct-effects/one-shot/GeneratedTicketBoundProbes.lean)
reuse the eighteen-step nested cycle, including its nonempty captured/spent
name, and reject an unissued spent name. Seven producer and eleven probe reports
pass. Original admission and saved-scope activation remain separate obligations.

[First-acquisition map origin](direct-effects/one-shot/CoreRuntimeIndexedMetadataOrigin.lean)
derives empty-map agreement from the existing ProducedBindings output indexed
by the same full rich/storage/lexical environment. The original empty finite
map retains its supplied absent or present-empty flag. The actual acquisition
computes the singleton map and its agreement with the installed environment;
a current request consumes that exact key/map/environment without a supplied
erasure-agreement premise. [Origin probes](direct-effects/one-shot/CoreRuntimeIndexedMetadataOriginProbes.lean)
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

Checkpoint `c81a6cb` retained the [finite original cell schema](direct-effects/one-shot/CoreCallableFiniteCellRegistry.lean)
and [resource template checker](direct-effects/one-shot/CoreCallableFiniteResourceTemplate.lean).
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

[Paired consumers](direct-effects/one-shot/CoreCallableFiniteResourceConsumers.lean) take the same
produced ArgumentReceipt, bind the translated resource handle, read the fresh
cell and return the original full contract. Source uses the entire original
rich environment and lexical map; lower storage uses the entire original
storage map and original stored contract. [Probes](direct-effects/one-shot/FiniteResourceTemplateProbes.lean)
check varying private resource-family members, shadowing, binder namespaces,
fresh-reference escape and retained higher-order contract fields. The 47
ordered reports include one repeated existing non-retention report. This is
a separate finite checker: the original StaticProducer remains 14/16. Its
initial registry/admission connection was still open at that checkpoint.
General initializer and new higher-order resource-body constructors, handler,
branch, cleanup and nested resources remained open. The graph wrapper result assumes its original shape check; the lower
storage result is a constructed derivation, not an extended recipe checker.

[Cleanup registration sites](direct-effects/one-shot/CoreCallableGeneratedCleanupRegistration.lean)
derive action/body child lineage from the same actual registration node and
produce the original full cleanup receipt. Actual body steps derive heap
extension and connect that receipt and original suffix to the same normal start
and Generated.initial endpoint. The child-site consumer rejects immediate
re-entry to the original active caller's handler; it receives no independently
supplied body-site proof. [Registration probes](direct-effects/one-shot/GeneratedCleanupRegistrationProbes.lean)
compose three actual Core steps at an active captured caller scope, retaining
that original scope while callback invocation uses empty scope. Nine producer
and six probe reports pass. That registration producer consumes MappedHistory; arbitrary general-suffix
registration was still open at `c81a6cb`. Initial admitted reachability, general
body progress and changed-tail capture/resume anchor transport remain open.
This does not remove outsideCheck or derive unconditional activation guards.

Both components passed author-disjoint semantic and quality review and fresh
isolated replay at `c81a6cb`. Their six leaves compiled together in 9.4 seconds,
with 5.4 seconds of preparation/hash checking, reusing all 931 prior artifacts
and logs. That assembly contained 937 modules and 12,272 ordered standard-only
reports: 62 additional reports and 61 new report names. No Rust sources changed.

Checkpoint `985caff` connected the finite cell checker to original admission.
[Exact registry compatibility](direct-effects/one-shot/CoreCallableFiniteRegistryCompatibility.lean)
checks the actual CellApi and every original full scalar cell record. It
preserves successful selected lookups, including full non-cell contracts and
original lookup order. Fresh cell operations can be added, so this is not
registry equality. [Checked transport](direct-effects/one-shot/CoreCallableFiniteRegistryBridge.lean)
runs the original Annotation checker and transports only its produced
fourteen-constructor StaticTree. Code, full contracts, environments,
requirements, dependencies, private Plans and full Rows remain the same indices.
No handler/resource registry congruence or unchecked fallback is assumed.

The [closed initial root](direct-effects/one-shot/CoreCallableFiniteCellInitialRoot.lean) checks
one connected original eight-node graph: bind7(integer17), resource3(integer0),
the ordinary handle9 bind, fresh read, and return7. Shape and translation match
the same rootCode. Original initializer checks and the finite resource check
construct Source/Auth; code/installation certificates, usage, accounting,
row annotation and recursive checks construct every initial Program facet.
No admission, invariant or future-progress proof is an input. The
[bridge probes](direct-effects/one-shot/FiniteCellAdmissionBridgeProbes.lean) reject incompatible
full cell records, nearest-record/API mismatches and shadowed original handles.
The [checked cell port ABI](direct-effects/one-shot/CoreCallableFiniteCellPortABI.lean) derives
the existing builtin equality for arbitrary full non-cell entries.
[Initial progress](direct-effects/one-shot/FiniteCellInitialProgressProbes.lean) consumes this
same constructed Program and produces an actual calculus NamedAccessStep and
its joint projection. This is not a Core-machine simulation or rich successor
preservation. The formal graph checks are not a replay of Rust graph validation.
General resource/initializer composition, handler and broader body forms,
static storage origins, rich whole-state preservation and full M4 remain open.
The original checker remains 14/16; the old Annotation.resource constructor
is still absent. This bounded connected root does not close whole C2 admission.

[General cleanup registration](direct-effects/one-shot/CoreCallableGeneralCleanupRegistration.lean)
now consumes the SAME GeneralHistory rather than only a mapped suffix. Its
original receipt is explicitly coupled to that history, original node/action,
identity, environment and actual registration edge. The changed
[Generated chronology](direct-effects/one-shot/CoreCallableGeneratedChronology.lean) adds cleanup
as its thirteenth operation, computing the successor/history and retaining the
same original running stamp. The [ticket-bound producer](direct-effects/one-shot/CoreCallableGeneratedTicketBound.lean)
preserves its bound through cleanupArmed, which creates no captured ticket.
[General-entry probes](direct-effects/one-shot/GeneralGeneratedCleanupEntryProbes.lean) register
key1 above the existing key0 completion after the SAME actual start and five
callback edges: six Generated edges and seven Core steps from start_before.
The existing current-site, ownership and environment-closing guards remain
conditional. Saved-anchor/changed-tail scope transport, arbitrary body progress,
projection/disposal and general initial admitted reachability remain open.

All three components passed author-disjoint semantic and quality review and
fresh isolated replay at `985caff`. That grouped batch compiled seventeen
affected modules once in 23.2 seconds, with 7.0 seconds of preparation/hash
checking. Eight new sources and two existing changes added 49 reports to its
945-module/12,321-report coherent assembly; 928 unchanged artifacts/logs were
reused. The lower registration module preceded its changed chronology consumer,
with other registration order and provenance checks retained. No Rust sources
changed and no Rust tests were rerun.

The current [site-origin producer](direct-effects/one-shot/CoreCallableGeneratedSiteOrigins.lean)
derives canonical current and mapped owners, current evaluating-site lineage,
and saved strict-right lineage from the SAME original RunningStartPast. A
simultaneous induction covers all thirteen existing Generated operations. Start
uses the original installed receipt. Cleanup/bind/handler descent uses the
preceding current site's control and scope, rather than copying duplicate
operation lineage fields. Entry computes both actual child sites from the
same parent and finite Postorder evidence. Swap consumes its same singleton
mapped owner/right-site receipt. Capture uses the selected handler's original
installation map; it never substitutes the operand's current map.

[Real consumers](direct-effects/one-shot/CoreCallableGeneratedSiteConsumers.lean) remove current
lineage from CleanupCurrent and HandlerCurrent inputs. Cleanup derives it from
Generated before invoking the original registration factory. Handler derives
it before constructing the actual installation with the SAME current.history;
no desired installation or endpoint is supplied. The selected-handler helper
also derives canonicality from that same installation. [Probes](direct-effects/one-shot/GeneratedSiteOriginProbes.lean)
replace only those supplied lineage fields in the original nested cleanup and
active handler paths. Exact private fixture-prefix bytes are retained and
audited. Cleanup still registers key1 after five prior Generated edges, with
seven Core steps from start_before. The active handler uses its same nine-edge
captured prefix; exported resumed_trace is consumed directly. Five producer,
seven consumer and thirteen probe reports pass author-disjoint review and
fresh isolated replay, including the missing-interface baseline check.

This removes independent current-lineage inputs for these consumers. Full
CurrentOwnership, physical CurrentScopeOrigin and environment-closing remain
conditional. The current thirteen operations never promote restored physical
strict frames into current.maps. Deeper restored strict provenance, saved
anchors/changed-tail scope transport, general initial admitted reachability,
projection/disposal and whole-fragment simulation remain open.

The same increment includes the [general resource initializer](direct-effects/one-shot/CoreCallableGeneralResourceInitializer.lean).
Its entry point executes the original finite Annotation checker through exact
registry recheck, then the retained body check. It receives no Source/Auth,
Rechecked, ArgumentReceipt, desired check-success or future-progress provider.
The initializer remains checked as the full Integer contract, with its original
preceding environment/world/allowed scope. Its actual Code, demand,
Requirements, dependencies, private Plan and full Rows are retained. The
result sequences those original indices with the SAME computed resource-body
families, total at every identity and authenticated only fresh. The existing
literal-only API remains a specialization; a whole-resource StaticTree is not
invented, since that old grammar has no resource constructor.

The [connected consumer](direct-effects/one-shot/CoreCallableGeneralResourceInitialRoot.lean)
reuses the prior Cell root's entries/globals/policy/body, outer7, resource3,
handle9, read and return7. Only the initializer changes to the nonvalue
bind20(integer0)(variable20). The same extended ten-node graph checks and
translates to its original code. Produced Source/Auth, full finite initial
Program facets and the existing calculus NamedAccessStep are connected to that
same root. Four producer and sixteen consumer/probe reports pass independent
review and fresh replay, with six exact interface checks. The actual unsupported
initializer RecipeTag propagates its rejection; invalid API and fresh-reference
escape also reject. Generic Program certificate/accounting production, original
Annotation.resource/PairedOrigin resource admission, broader body/handler forms,
storage request checking, Rust validator replay and rich whole-state/M4 coverage
remain open. Original checker coverage stays 14/16; no new fragment exclusion is
introduced.

The five new sources are coalesced into one integration increment. The first
three related C3 leaves compiled once in 4.2 seconds; the two C2 leaves compiled
once in 53.4 seconds against that
immutable intermediate assembly. Final preparation/hash checking took
5.7 seconds. The intermediate
948-module/12,346-report assembly is evidence, not a git commit; HEAD stayed
`985caff` throughout both subbatches. All three already-compiled C3 artifacts and
all 945 original artifacts were reused for the C2 subbatch. Checkpoint `05cff7d` contains 950 modules and 12,366 ordered standard-only
reports, forty-five
more than `985caff`. Exact source/artifact/log/import associations and compiler
library pins agree. No Rust sources changed and no Rust tests were rerun.
M0–M4, the declared fragment and whole-package acceptance counts are unchanged.

The next increment derives [evaluated physical scope origins](direct-effects/one-shot/CoreCallableGeneratedCurrentScopeOrigins.lean)
through all thirteen existing Generated operation forms. One simultaneous
induction produces the current origin at actual evaluate controls and the
origin of every saved strict map at its exact physical suffix. The original
start installation supplies canonical owners; no caller-supplied current or
successor origin is accepted. Cleanup, bind and handler descent use the
preceding evaluate origin. Entry creates a saved dynamic path and Swap consumes
that SAME path. BindReturn retains its original receipt at the exact computed
suffix; no unrelated or changed tail is substituted. Capture creates the actual
fresh clause head from the selected installation. Returned resume, handler and
spent-marker endpoints retain their actual controls and frames without asserting
an unevaluated physical occurrence.

The [real cleanup and handler consumers](direct-effects/one-shot/CoreCallableGeneratedCurrentScopeConsumers.lean)
remove current ownership and origin fields as well as the previously removed
lineage fields. Cleanup ownership combines the produced evaluate origin with
the existing SAME-start ticket-bound theorem. Its only bound input remains the
original pre-start suffix obligation. Handler origin comes directly from actual
control inversion. Exact action/handler data, closure/readiness, counters,
computed successors and current history remain indexed by those same inputs.

The [focused probes](direct-effects/one-shot/GeneratedCurrentScopeOriginProbes.lean) reuse the
pinned original private prefixes. Nested cleanup key 1 follows five prior
Generated edges and seven actual Core steps; the inner-handler construction
follows the same captured execution. The exported resumed trace is consumed
directly, retaining returned Unit, no strict maps and its exact four restored
frames. A wrong dynamic ticket is rejected at the SAME first physical owner
even when its canonical static map is unchanged. Four producer, six consumer
and thirteen probe reports pass independent review and fresh replay.

The three related leaves compile together once in
4.2 seconds, with
7.3 seconds of preparation
and hash checks. All 950 parent artifacts and logs are reused unchanged. The
assembly at `2484040` contains 953 modules and 12,389 ordered
standard-only reports, twenty-three more than `05cff7d`, with exact source,
artifact, log and selected-import associations. No Rust sources changed or
Rust tests were rerun. M0–M4, the fragment and whole-package counts remain
unchanged.

This closes the current evaluate/saved-map scope provider for those thirteen
forms. It does not produce a dormant cleanup caller's activation over a changed
suffix, saved-anchor transport or prefix misses. Strong all-endpoint origins,
deeper restored strict-frame promotion, environment-closing, disposal/projection,
general C2 admission and the complete C3/C5 correspondence remain open. At `2484040`, the next
C3 assessment targeted the original registration-to-start history and actual
completion activation guards. C2 was implementing the assessed finite
higher-order resource-body composition. This work changes no current language
semantics and makes no claim that the remaining proofs are already available.

The next paired increment checks [compositional resource bodies](direct-effects/one-shot/CoreCallableCompositionalResourceBody.lean)
from finite data. New lambda, application and Bool-branch constructors combine
with ordinary bindings, variables and products. Original opaque slots preserve
their exact position and whole private contract; same-name shadowing cannot
select an older slot. A lambda checks its body under its own declared allowance
and computes its isolated requirements and private checking family. Application
checks the whole function domain/result and exposed recipe. The identity family
is structural finite data, with constness of full dependencies, Plan and Rows
rather than only erased ports. No desired Source/Auth or future-success proof
is supplied as metadata.

The [opening checker](direct-effects/one-shot/CoreCallableCompositionalResourceOpening.lean)
executes the original finite initializer recheck before the body gate. Its
result retains that exact initializer receipt and constructs the all-fresh
Source/Auth openings, requirement hiding and combined resource Source/Auth.
The [connected original graph](direct-effects/one-shot/CoreCallableCompositionalResourceRoot.lean)
retains outer7, handle9 and the nonliteral initializer. Its resource body binds
a fresh-cell reader, binds a higher-order function taking that whole callable
contract, applies both through ordinary variables, and returns outer7 through a
Bool branch. Actual shape, translation and closed Source/Auth pass. Four
metadata negatives reject a falsely pure cell reader, escape of a fresh-reading
callable, an older shadowed slot and an unsupported exact recipe. The three
leaves have thirty-two standard-only reports and nine interface checks.

Stored-capture nonretention remains a separate C2.3 obligation. One retained
boundary check accepts Source/Auth for a pure callable that aliases handle9 and
returns Integer, while its literal dependency still names handle9. Requirement
hiding and full checking-family constness do not certify stored captures. The
next bounded storage producer must reuse actual dependencies and the nearest
whole paired storage binding; the fresh-read escape negative does not establish
rejection of every retaining callable. Rust final validation already reconstructs
capture information; this formal separation is not a demonstrated Rust bug.

The [initial chronology](direct-effects/one-shot/CoreCallableInitialChronology.lean) fixes the
actual Core initial graph/root/environment, empty frames and empty history.
Shape and exact root translation are current guards. Named existing Operations
extend that same endpoint-threaded history. An additive initial ready-lambda-bind
bootstrap reuses the established three-edge producer: two ranked administrative
edges and one positive bind step. It does not accept an arbitrary CoreSteps
chain or change the thirteen existing Operation forms. Original site, evaluated
scope and ticket-bound obligations are derived along this history.

The [causal callback-start consumer](direct-effects/one-shot/CoreCallableGeneralStartedFrom.lean)
retains the exact initial prefix, cleanup registration, named body prefix,
original installed receipt and heap-weakened history at normal callback start.
Its Generated consumer preserves actual initial-to-current Core steps, the
calculus target trace and ticket bound without an independent initialBound seed.
The [focused probes](direct-effects/one-shot/InitialChronologyProbes.lean) reuse the existing
authenticatedCleanup graph: three bootstrap edges, registration, the Unit body
edge and normal start make six actual Core edges. Exact translation rejects a
false Unit initial focus. Twelve producer, six consumer and eight probe reports
pass. This is causal coverage for the represented named families; it does not
construct general C2 admission or remove dormant activation/outsideCheck guards.

Both independently reviewed components passed an initial six-leaf compile batch
in 46.7 seconds, with
7.1 seconds of
preparation and hash checks; all 953 parent artifacts were reused. Packaging
then caught seven redundant final newline bytes in one new Lean file. An
independently reviewed whitespace-only correction recompiles that file and its
two consumers in 42.6
seconds, with 9.4
seconds of preparation. It reuses 956 artifacts, including every C3 leaf. All
affected reports and artifact bytes match the initial assembly. The
assembly committed as `5688835` contains 959 modules and 12,447 ordered standard-only reports,
fifty-eight more than committed `2484040`. Both assembly gates are retained;
neither is presented as a separate Git commit.
No Rust source changed or Rust test was rerun. M0–M4, the declared fragment and
whole-package acceptance counts remain unchanged. General handler/resource
admission, stored captures, dormant first-anchor transport, deeper strict-frame
promotion, disposal, complete simulation and the integrated theorem remain open.

The [compositional storage producer](direct-effects/one-shot/CoreCallableCompositionalResourceStorage.lean)
now checks the SAME finite resource Code. It computes captures from actual Code
dependencies and the nearest whole paired storage binding. Symbolic old/fresh
atoms preserve complete function domains, results and captures; structural
transport derives the lower judgment for every fresh identity. Lambda,
application, bindings, products and Bool branches reuse the existing lower
constructors. Only the checked original cell API authorizes read/write.
This lower storage judgment is paired with the Source/Auth gate for typing.

The combined checker executes the rich initializer/body check, original storage
initializer check and symbolic body opening. It preserves the original paired
maps and constructs the lower judgment for the exact resource Code. The
[connected probes](direct-effects/one-shot/CompositionalResourceStorageProbes.lean) reuse the
23-node resource graph and nonliteral initializer; the outer paired prefix
comes from executed original checks. The retained pure-handle-alias example
passes Source/Auth but fails outside storage admission. Nearest shadowed return
and full opaque application-domain negatives also reject. This is stored-capture
admission for the finite composed body, not general Core admission or concrete
runtime environment/storage lineage. Original checker coverage stays 14/16.

The [outside-activation origins](direct-effects/one-shot/GeneratedOutsideActivationOrigins.lean)
retain SAME initial chronology, intervening handler installation and immediate
cleanup registration. The [finish consumer](direct-effects/one-shot/GeneratedOutsideActivationConsumers.lean)
derives saved-scope alignment, the original kept split/first-owner position and
inserted spent-marker outsideCheck. It supplies the existing Activation.outside
without independent proofs of those desired checks. Current RunningHead,
physical-tail shape, returned Unit and EmptyFocus remain explicit guards.

The [connected outside-activation prefix](direct-effects/one-shot/GeneratedOutsideActivationProbes.lean)
has 23 actual Core edges from CoreMachine.initial through cleanup finish and
the corresponding target trace. The callback captures completion plus the
intervening handler; its actual resume inserts that handler's spent marker
before the original caller. SAME CaptureData, selected installation and
ResumeSplit determine the tail. The enclosing handler capability remains live
at this endpoint: this is represented-prefix evidence, not admitted
whole-program execution. Stable callback operations, immediate installation to
cleanup, empty resume front and the current tail guard bound this result.
General changed-tail/multi-cycle transport and deeper strict promotion remain
open. Conditional same-pair obstruction is not an admitted product bug.

These two independently reviewed components compile together as five new
leaves in 42.9 seconds,
with 7.2 seconds of preparation and
association checks. All 959 parent artifacts and logs are reused unchanged.
The assembly committed as `45d6f09` contains 964 modules and
12,513 ordered standard-only reports,
66 more than `5688835`.
No Rust source changed or Rust test was rerun. General initial admission,
handler/resource integration, runtime storage origins, saved-anchor transport,
disposal, whole simulation/preparation and the integrated theorem remain open.
M0–M4, normative semantics, exclusions and C1–C5 acceptance counts are unchanged.

The [generated bind producer](direct-effects/one-shot/CoreCallableGeneratedBindProducers.lean)
now derives the existing non-value bind input from SAME current site and
evaluated-scope origins. Literal node metadata, child translations, current
environment closing, PlainData, ClosedExcept, non-value initializer and
EmptyFocus remain explicit. The existing bind_enter constructs the saved caller
from the entire current GeneralHistory; the producer retains exact predecessor
and original-history equations. It takes no desired saved caller or successor.
The physical successor prepends the actual bind frame to the full suffix.

The [chronology consumers](direct-effects/one-shot/CoreCallableGeneratedBindConsumers.lean)
derive these origins from SAME InitialChronology or Generated, append the named
bind operation, and preserve the original actual Core prefix and target trace.
The [generic interfaces](direct-effects/one-shot/GeneratedBindProducerInterfaces.lean)
prove actual-prefix extension, explicit positive target steps, returned-control
exclusion and rejection of a literal Unit initializer at this strict-bind gate.
These are generic interfaces under current readiness guards, not extra graph
fixtures or unconditional transition availability. Arbitrary physical suffixes
are retained; deeper mapped strict focus/plug, restored right-site origins,
bind-return extraction, general saved-anchor transport and full admission remain
open. Existing strict proofs already compute positive entry and plug steps;
their endpoints still need connection to the generated chronology.

Independent review replays all three leaves once with 18 exact standard-only
reports, twelve public interfaces, the missing-interface negative check and
534 actual dependency selections. The integration batch compiles the three
related leaves in 2.1 seconds, with
8.8 seconds of preparation and association checks.
All 964 parent source/artifact/log associations remain unchanged and are reused.
The assembly committed as `70b41c0` contains 967 modules and 12,531 ordered
standard-only reports, eighteen more than `45d6f09`. No Rust source changed or
Rust test was rerun. This advances C3.1/C3.2 without closing a whole-fragment
acceptance item; package counts, estimates, exclusions and normative semantics
remain unchanged.

The [compositional admission facets](direct-effects/one-shot/CoreCallableCompositionalAdmissionFacets.lean)
now interpret the original finite initializer recipe and compositional Checking
into contextual SourceAdmission.Code, dependent CodeChecked and Accounting.Run.
The structural cell check constructs exact rows at every identity; Source/Auth
freshness is supplied by the separately executed original rich gate. Closed
opaque Plan/Rows remain whole and use their original finite RecipeTag. Literal
requests unavailable in this context and invocation without a continuation
reject. Actual syntax is checked to construct Uses, including lambda bodies.

The closed-root checker executes the original outer and resource rich checks,
then checks contextual availability, usage, support, evaluated accounting and
budget. Its metadata carries no desired Source/Auth, contextual certificate,
accounting, usage or future-success family. The
[SAME23-node initial Program probes](direct-effects/one-shot/CompositionalInitialAdmissionProbes.lean)
retain the nonliteral initializer and higher-order lambda/app/Bool body. The
full-index witness preserves the original private Plan, full Rows and rich
Source requirements. Its independently computed accounting root remains a
choice of two done branches and evaluates to the empty row. It is not replaced
by the rich Source requirements. The same Program yields an actual calculus
NamedAccessStep and joint successor validity through the existing initial
progress interface; this is a first step, not whole Core execution.

Independent review passes seventeen exact standard-only reports, eight public
interfaces, three missing-interface negative checks and 549 actual dependency
selections. The intermediate two-leaf gate compiles in
22.3 seconds, with 9.9 seconds of
preparation and association checks. All 967 parent source/artifact/log
associations remain unchanged and are reused. This immutable intermediate
assembly contains 969 modules and 12,548 ordered standard-only reports, seventeen more
than `70b41c0`. Earlier failed/light 959/964 diagnostics remain separate from
this committed-parent verification.

This Program checker does not consume the separate lower storage receipt or
prove stored-capture nonretention. It handles one outer integer binding and the
finite composed resource slice; general original resource/handler checking,
cleanup/invocation contextual interpretation, retained runtime/callable origins,
rich successor preservation, whole M4 availability and Rust validation remain
open. Original checker coverage stays 14/16 and whole C2 stays 0/4. No Rust
source changed or Rust test was rerun. C1–C5 counts, estimates, fragment scope
and normative semantics remain unchanged.

The [general strict-focus producer](direct-effects/one-shot/CoreCallableGeneralStrictFocus.lean)
computes positive pair-left/application-function endpoints over the entire
general physical suffix. SAME current chronology derives both child-site
lineages and a saved ordinary-frame origin. The installation receipt retains
the original node, right literal/code/environment, saved map, complete
PlainData.scope and below-history. Each entry takes one Core and one Raw step.

The [saved-right consumers](direct-effects/one-shot/CoreCallableStrictFocusConsumers.lean)
retain that receipt through a middle of existing named Operation outputs.
Actual returned head, unchanged original physical/lexical tail and history,
operand ValueRel, heap extension, full return PlainData, matching saved scope,
non-value right code and EmptyFocus remain explicit. Pair-right and application-
argument compute one Core edge and two Raw steps: plug, then focus. They restore
the SAME saved map/scope and derive right-site/current origins without an
independently supplied saved lineage or desired origin.

The [generic strict episode interfaces](direct-effects/one-shot/GeneralStrictFocusInterfaces.lean)
retain SAME InitialChronology or Generated prefix, computed entry, named middle
and computed right return. Actual Core steps, target trace and accounting
compose through that original prefix. The literal-operation consumer retains
the installation and performs its actual right transition. Wrong returned entry
control and value-selected entry/right children fail the current strict gates.
No graph fixture is added. Arbitrary nesting, repeated new-focus episodes,
capture/resume changed tails, general saved-anchor transport and admission
remain open. These are C3.1/C3.2 components, not new acceptance items.

Both components join one five-leaf checkpoint with 46 additional reports:
seventeen contextual-admission reports and twenty-nine strict-episode reports.
Independent reviews pass all five leaves, twenty public interfaces, exact
ordered standard-only reports, expected missing-interface failures and their
actual dependency selections. The final gate compiles only the three strict
leaves in 3.1 seconds, with
7.2 seconds of preparation and association checks.
It reuses all 969 intermediate artifacts and logs, including both facets;
the expensive facets are not recompiled. All 967 committed-parent associations
remain unchanged. The 969 assembly is an immutable integration intermediate,
not a separate Git commit. The `633f0a4` coherent assembly contains 972 modules
and 12,577 ordered standard-only reports, 46 more than `70b41c0`. No Rust source
changed or Rust test was rerun. C1–C5 counts, estimates, exclusions and normative
semantics remain unchanged.

The [composed resource-origin producer](direct-effects/one-shot/CoreCallableComposedResourceOrigins.lean)
executes original finite initializer annotations and storage recipes on the
SAME root bind path, deriving paired origins from its transcript. Graph shape,
translation and root-code equality are checked. The resource opening retains
that original graph/prefix and full rich/storage maps. Selected internal bind
and initializer producers retain computational Body and Recipe constructors,
execute both child recipes and compute exact intermediate slots/domains. These
metadata cannot be recovered from proof-erased Produced or a noninjective
Source/Auth demand split. Current child checks produce Source/Auth and the
lower storage judgment with actual ordered shadowing and arbitrary fresh-cell
identity; no desired derivation or successful future family is an input.

The [captured-handle consumer](direct-effects/one-shot/CoreCallableComposedCapturedHandle.lean)
checks the exact selected resource reference under its complete outside maps.
Existing constructor-origin reconstruction, structural declaration-policy
transport and lower substitution retain the full public contract and private
Family at every lexical/call point. The [connected probes](direct-effects/one-shot/ComposedResourceOriginProbes.lean)
reuse the original23 graph: outer7, resource3 and its nonliteral initializer,
handle9, reader12 and higher13. Both callable current checks quantify arbitrary
fresh identity. One static identity1 reconstruction produces the exact closed
reader and full lower storage contract. It is not an actual acquired Core
owner. Wrong-root, alias/storage, nearest-shadow and opaque-domain negatives
retain their separate meanings; source acceptance alone does not establish
stored-capture nonretention.

Independent review passes 38 ordered standard-only reports, sixteen public
interfaces, three missing-interface failures without an artifact, 555 actual
dependency selections and all 972 parent/eight-library associations. Its first
fresh replay found a probe artifact identity difference: the author follow-up
used a relative path whose Lean main-module name included the development
folder. Sources, theorem names and report logs match exactly. Compiler source
and binary metadata establish the path-derived name; canonical basename
artifacts are pinned separately. The immutable author checkpoint, failed
association assertion and successful fresh replay are retained. Finishing the
review reused those three successful compiles, without replaying them.

One related three-leaf integration gate compiles in
81.9 seconds, with
5.3 seconds of preparation and association checks.
It reuses all 972 parent artifacts and logs. The `4d2397c` coherent assembly
contains 975 modules and 12,615 ordered standard-only reports, 38 more than
`633f0a4`. No Rust source changed or Rust test was rerun. This advances existing
C2.1/C2.3 obligations without changing the original checker14/16 inventory,
C1–C5 acceptance counts, estimates or normative semantics.

Actual Core initializer execution, acquisition, MEnv/ValueRel/EnvCloses,
whole Program and full general admission remain open. The next assessed
runtime connection computes the original initial-to-reader path with twelve
Core edges and activation0 from actual history. Focused acquisition matches
three Raw steps: plug the saved resource initializer, enterCell and synthetic
handle bind. It does not consume a supplied Chain or desired closure origin.
At that checkpoint, finite handler Source/Auth and changed-tail restoration
were parallel bounded work. The following checkpoint integrates both.

The [finite clause-template checker](direct-effects/one-shot/CoreCallableFiniteClauseTemplate.lean)
and [handler Source/Auth producer](direct-effects/one-shot/CoreCallableFiniteHandlerSource.lean)
now derive the SAME handler judgment from literal original metadata. Pure
operands, resume, pure bind prefixes and Bool branches retain complete opaque
contracts and private plans/rows. Clause producers quantify every compatible
full owner contract, including its resume demand. Actual current-use checks
reject available, double-used and escaped continuation code before the supported
form check. Registry coverage and uniqueness, nearest references, rights,
receiver support and ordinary/protected offers are executed. Canonical owner0
is used only to erase an already universal producer to port typing.

The [handler probes](direct-effects/one-shot/FiniteHandlerSourceProbes.lean) construct Source/Auth
for the same closed request/handler graph and check exact full higher-order
slots, owner distinctions and unavailable modes. Protected selection here is
static mode/family lookup; it does not establish contextual request routing.
Independent review passes 46 exact standard-only reports, fifteen interfaces,
two intended missing-interface failures and 522 actual selected dependencies,
with all 975 parent/eight-library associations before and after. This finite
resume-template increment does not extend the original checker14/16 inventory.
Original handler annotation, contextual CodeChecked/terminal/pending admission,
local-owner retirement, storage and general initial Program remain open.

The [strict capture-origin producer](direct-effects/one-shot/CoreCallableStrictCaptureOrigins.lean)
preserves the same computed physical installation through actual capture and
resume. It derives head membership, selected handler/activation/ticket, complete
captured and outside segments and the current clause front. Original saved
maps/scope and finite kept-prefix checks derive inactive or retained-inside
scope lineage. Its [changed-tail consumer](direct-effects/one-shot/CoreCallableStrictCaptureConsumers.lean)
uses that restored installation to match one actual Core right-return step with
two Raw plug/focus steps. It retains full literal, closing, nonvalue, maps and
PlainData guards while removing the unchanged-original-tail/history guard.

The [connected restoration probes](direct-effects/one-shot/StrictCaptureOriginInterfaces.lean)
add a bound product to the original running graph and preserve its original
Unit result, callback, outer handler and cleanup. Sixteen actual Core edges
from that running start capture pair-left plus an older saved bind. Restoration
retains pair-right, saved bind, outer/intervening handlers, the same selected
spent marker and original completion. Wrong handler, activation, dynamic ticket
and original captured suffix remain distinct negatives. Independent review
passes 35 exact standard-only reports, twelve interfaces, intended RED failure,
541 actual selected dependencies and all 975 parent/eight-library associations.
Standard Classical.choice selects a proved HeadCut receipt; this is proof-level
construction, not an executable capture validator. Outside-active compatibility,
deeper ordinary positions, arbitrary nesting/repeated episodes, disposal,
initial admission and complete callback/C3 execution remain open.

One combined six-leaf integration gate compiles in
9.9 seconds and reuses all 975 unchanged artifacts and logs;
preparation and association checks take
10.4 seconds. The `18d3ecb` coherent assembly has 981 modules and
12,696 ordered standard-only reports, 81 more than `4d2397c`. All six source,
artifact and log associations match their independent reviews. No Rust source
changed or Rust tests were rerun. The unchanged acceptance counts and estimates
measure whole-fragment obligations rather than these proof components.

At that checkpoint, resource runtime execution remained a separate active
increment. The following checkpoint integrates its completed reader connection
with contextual handler admission and compatible outside-active restoration.

The [resource-entry producer](direct-effects/one-shot/CoreCallableComposedResourceEntry.lean)
computes nine actual Core steps from the SAME original initial graph through
the nonliteral initializer and acquisition0. It retains the original saved
resource-body closing, derives the acquired environment and matches acquisition
with exactly three Raw steps, including the synthetic handle binding. The
[runtime reader consumer](direct-effects/one-shot/CoreCallableComposedRuntimeBindings.lean)
adds three actual binding/lambda/return steps, constructs certificate, closing
and ValueRel from executed original checks, and derives the nearest reader12
binding. Its connected pairing consumes both original current and captured-handle
receipts at computed identity0; full opaque contracts, private Family/Plan/Rows,
replacement-indexed Source/Auth and lower storage remain indexed.

The [connected runtime probes](direct-effects/one-shot/ComposedResourceRuntimeOriginProbes.lean)
join those outputs on one twelve-edge path. They derive the cell request row
and support from actual closed code, including cell0 in PlainData. Review caught
an earlier draft that omitted that row; it was corrected before the immutable
checkpoint. Independent replay passes 36 exact standard-only reports, twenty-three
interfaces, three missing-interface failures without an artifact and 591 actual
selected dependencies. All 981 parent/eight-library associations agree before
and after. This is a finite Unit-to-Integer reader lane with explicit closure
and value guards. It does not extend the untyped FrameRel to arbitrary typed Core
or connect the reader to the old generic chronology, higher13 call, full Program,
resource release, cleanup or general C2/C3 execution.

The [contextual handler checker](direct-effects/one-shot/CoreCallableFiniteHandlerAdmission.lean)
executes original Source/Auth checks and constructs Code, CodeChecked, Run and
LocalOwner using the existing exact Cut, TerminalHandler, Pending and retirement
rules. Clause pure prefixes and Bool branches preserve choice and universal full
owner contracts, including resume demand. Actual availability rejects an
ordinary-unavailable operation even when its static protected offer remains.
Its initial checker executes usage, policy, support, accounting evaluation and
budget checks, constructing every Program facet from the same code. Source
requirements stay separate from the computed accounting root.

The [SAME original handler probes](direct-effects/one-shot/FiniteHandlerAdmissionProbes.lean)
produce an accepted Program and structural initial joint judgment for the
four-node request/handler/resume graph. Independent replay passes 26 exact
standard-only reports, ten interfaces, two missing-interface failures without
an artifact and 546 actual selected dependencies, with all 981 parent/eight-library
associations before and after. The public handler BODY is one immediate request
with a pure-plan operand, equal input/answer Contract and one covered declaration.
BODY sequencing/branches, higher-order clauses, cleanup, nested handlers and
general admission remain open. This structural joint does not prove builtin
ABI equality, initial_progress or an actual Core execution. Original checker
coverage remains 14/16. Review harness corrections retain their failed assertions
and reuse the two saved successful compiles; no productive compile was repeated.

The [outside-active head producer](direct-effects/one-shot/CoreCallableStrictOutsideHeadOrigins.lean)
derives caller-specific front misses from the SAME AfterCapture and checks full
original saved owner map and dynamic scope against the selected installation.
Original occurrence/ticket/kept-prefix lineage and unique handler sites then
derive outside restoration, including the inserted spent-marker miss. The
[changed-right consumer](direct-effects/one-shot/CoreCallableStrictOutsideHeadConsumers.lean)
matches one actual Core return with two Raw plug/focus steps and retains the
complete changed physical/lexical tail and history. No desired outside origin,
unchanged-tail equality or successful future path is an input.

The [active-caller probes](direct-effects/one-shot/StrictOutsideHeadInterfaces.lean) use one
Unit-preserving extension of the original nested running graph. Nineteen actual
Core edges retain saved bind, spentK1, liveH0, original caller ticket0 and full
selected installation. Full-map/scope mismatches and inside classification reject.
Independent replay passes 26 exact standard-only reports, twelve interfaces,
two missing-interface failures without an artifact and 542 selected dependencies,
with all 981 parent/eight-library associations before and after. Compatibility
guards can reject otherwise valid callers; arbitrary outside metadata, deeper
ordinary positions, clause-bearing fronts, repeated episodes, disposal, initial
Program and complete callback execution remain open.

One combined eight-leaf gate compiles in
28.6 seconds and reuses all 981 unchanged artifacts and logs;
preparation and association checks take
9.9 seconds. The current coherent assembly has 989 modules and
12,784 ordered standard-only reports, 88 more than `18d3ecb`. All eight source,
artifact and log associations match their independent reviews. No Rust source
changed or Rust tests were rerun. These components advance existing C2/C3
obligations without closing whole-fragment acceptance items or changing estimates.
No normative semantics change. The next bounded assessments address original
handler BODY routing and connecting the computed reader to actual calls through
the existing history carrier. General admission/simulation, deeper saved-anchor
and disposal transport, runtime preparation and integrated C5 remain open.

Packaging review of `f1fc1e4` caught three registrations without compiled output paths.
The corrected commands use warnings as errors and explicit temporary olean
outputs. Replaying those three literal registrations over the audited 908-module
dependency set passes 26 reports with exactly the reviewed artifacts. The prior
missing-import failure was reproduced. This is a registered-tail replay, not a
new uncached run of every module.
These are bounded prototype results
within the existing C2/C3 obligations; the supported fragment, whole-package
inventory and normative semantics are unchanged.

The D4 higher-order case exposes two distinct annotation constraints. A pure
callable can retain a live cell while keeping an empty declared request row;
the current lambda guard instead bounds retention by port resources. Also,
`SourcePlannedTyping.Operations` fixes one rich input/output pair at each exact
operation key. A rich function value contains its body's latent footprint and
structural signature, beyond its declared Core function type. Different closure
bodies can therefore require different annotations at the same declared port.
`OperationRows` fixes decorations for that same rich pair. Downward erasure does
not construct a common authenticated refinement for those payloads.

The same constraint also occurs without operations. A stored higher-order
helper has one rich parameter type; the existing beta theorem substitutes at
that same type. A branch requires both arms to have one rich result, and an
operation result fixes the refinement expected by its resume and caller
continuations. The existing theorems are universally stated over a chosen
refinement, but this does not make a stored callable or continuation parametric
over different refinements. A repair confined to operation inputs would leave
these C2.1 obligations unresolved.

The [retained obstruction](direct-effects/one-shot/CoreHigherOrderSupport.lean)
establishes the unchanged-port failure for the selected cell-retaining closure.
It does not establish impossibility for all translations. A candidate interface
repair must separate declared operation ports from authenticated payload
refinements, including retained support, and transport them through clause
parameters, substitution, receiving scopes and resource exit. Adding a retained
list to a globally fixed input type alone is insufficient. An alternative
normalization must prove that the removed captures and changed callable
structure preserve evaluation, cell observations and cleanup order; purity alone
does not justify removing calls.

Any bounded prototype must first cover two differently structured pure closures
at one operation key and a freshly acquired cell retained through that key. It
must preserve the exact declared signature and reject a dependent payload sent
outside its resource owner. Before generalizing it, check the same closures
through one ordinary apply helper and a branch that returns either closure;
record higher-order result and continuation obligations explicitly. Retain the
prototype only if it supplies these
checks without future-success assumptions and identifies how it reaches the
existing M4 admission boundary. These are proof-interface experiments toward
current Ash semantics, not a language change or a reduction of the task's
higher-order scope.

The first [payload-refinement experiment](direct-effects/one-shot/CorePayloadRefinement.lean)
now supplies the same-port operation, computed retention, actual capture/beta
prefix and selected-receiver checks. It is retained as partial evidence, not as
approval to generalize this interface through M4. The old lambda authentication
and fixed rich operation table remain explicit obstructions. Rust regressions
also exercise ordinary helpers and both branch choices. The subsequent
[helper/branch assessment](direct-effects/one-shot/CoreRefinementJoins.lean)
proves actual helper traces and selected branch support, but also proves that
the current fixed-input and homogeneous-result constructors cannot admit the
unchanged two-body examples. Thus per-payload specialization does not supply
common whole-expression admission. Ordinary callable input/result contracts,
heterogeneous joins and higher-order continuation transport must be addressed
together before generalizing the candidate through M4. The generalization gate
above remains unmet.

The next interface comparison must distinguish public ports from three private
facts: a value's retained support, its actual body plan, and the refinements its
caller or continuation accepts. The current `ValueRows.function` stores one
body decoration; `Auth.app` uses that exact decoration, and `Auth.branch` shares
one result decoration between both arms. Changing only the operation table
therefore cannot supply the required transport. A candidate with static families
must authenticate each body's actual code and allow callers to accept every
refinement admitted by the declared port. Such quantification is a static proof
obligation, never a premise that execution will succeed.

The earlier [callable contracts](direct-effects/one-shot/CallableContracts.lean)
already separate captures from input/result structure and prove substitution.
Their operation clauses require finite port bounds, and the derivation lacks
cleanup and discard constructors. Those lemmas may be reused within their
stated scope, but that historical component does not replace the current M4
invariant. A family-based repair must reach `InitialAdmission.Program` and the
current application, branch, capture, resume, saved-context and resource-exit
preservation boundaries. An observational normalization remains an alternative
only with a proof preserving internal allocation and cleanup as well as returned
values. No shared rewrite or normalization is selected by the negative examples
alone.

The next bounded experiment tests a common callable plan contract while retaining
each actual body plan privately. For the existing `PurePlan` witnesses, it must
construct `SourceAdmission.Code` and its `CodeChecked` evidence at an arbitrary
current context, and transport `Accounting.Run` from the pure contract to the
actual rows with the same root requirements. These are the static certificates
used by M4, rather than a claim that the body will execute successfully. The
Unit, sequenced-Unit and cell-retaining payloads must instantiate the same
contract without changing their code or declared ports; support remains checked
separately. Retain this experiment only if it constructs those certificates from
the existing structural witness. It must expose the remaining lambda, application
and result-interface changes instead of presenting a contract witness as complete
M4 admission. Effectful bodies, higher-order outputs and resource-exit transport
remain obligations of the full repair, even if this bounded comparison passes.

The [bounded certificate result](direct-effects/one-shot/CoreCallablePlanRefinement.lean)
passes independent compilation and review. It constructs the existing actual-row
certificates and preserves the exact accounting root for arbitrary current
contexts. All three payloads instantiate the contract; independent retained
support still rejects the outside receiver. Retain this result as a static
prerequisite. It supplies no lambda/application/result coercion and does not
establish that an arbitrary continuation is admitted. The next interface work
must transport the private body refinement through those judgments and their
preservation boundaries, including retained support at resource exit.

The next bounded implementation separates row refinement from value typing.
A contextual refinement from contract rows to actual body rows must transport
three existing static judgments at the same current context: `Code`,
`CodeChecked` for that transported certificate, and `Accounting.Run` with the
same root requirements. It must quantify over current worlds, installations,
actions, phases and budgets. It must not quantify over successful executions or
take the desired successor invariant as a premise. Identity and composition,
the existing pure-plan family, and insertion of a pure prefix before arbitrary
effectful rows are the first required constructors. The latter case checks that
the interface preserves an actual effectful suffix rather than equating every
body with an empty contract.

The application checkpoint must combine that transport with the selected
payload's existing body derivation and authenticated substitution. Given the
actual receiving context and the contract's current static certificates, it
must construct `SourceAdmission.Admitted` for the substituted body, its checked
certificate and exact-root accounting. The Unit, sequenced-Unit and retaining
payloads must all instantiate it without the refuted old lambda guard. Retain
this interface only if those constructions compile with no future-state premise.
This checkpoint does not admit the pre-beta application or change the fixed
input/result rules: a complete repair must still make callers, branch joins and
saved continuations accept the same declared contract while retaining each
selected witness. Shared source judgments and M4 remain unchanged until those
transport obligations are constructed.

The contextual transport checkpoint now constructs post-beta admission for the
three payloads and passes independent compilation. Its identical-root condition
is useful for pure sequencing, but cannot cover even a choice between two pure
bodies: `Accounting.Run.choice` constructs a choice of the two requirement
trees. At the empty continuation, that tree differs from the pure contract's
empty request. This is a representational restriction of the candidate
interface, not an additional Core effect or owner consumption.

The next bounded checkpoint must transport checked root requirements while
preserving their owner-demand index and the current budget. Given a normal
root, its `RowAnnotation`, and a check of `annotateDisposals` under the current
store, receiver and phases, it must construct corresponding evidence for the
actual root. Choosing between two alternatives checked against the same budget
may concatenate their reported footprints; it must prove the concatenation is
still within that budget rather than assert literal footprint equality.
Require identity, composition, embedding of the existing identical-root
refinement, and a choice constructor for two bodies refining one contract.
Instantiate the choice with the existing Unit and sequenced-Unit bodies at an
arbitrary continuation. Reuse `RowAnnotation.choice`,
`RecursiveRequirements.Checked.choice` and structural disposal annotation.
Retain this result only if it constructs those current certificates without
future-state premises. It remains a prerequisite to changing callable value
typing: common helper admission, returned closures, saved continuations and
retained-resource transport are still open.

The [checked-root result](direct-effects/one-shot/CoreCallableRootRefinement.lean)
passes independent compilation and review for these constructors and both
Unit/sequence and Unit/retaining row choices. It constructs actual normal and
annotated roots, checks and budget bounds under the original current checking
parameters. Retain it as the branch-accounting prerequisite. A row choice is
not yet a common type for a branch returning either closure: the old rich
value and authentication judgments are unchanged. The next design decision
must address those value judgments and substitution, rather than add further
post-beta wrappers to this result.

### Next value-interface experiment

The candidate assigns a callable a common checking contract while keeping
its actual body derivation inside its lambda evidence. The contract's signature
and rows describe what a caller checks; they need not equal the actual body's
signature and rows. Application checks that common contract. Beta must recover
the selected actual body, perform authenticated substitution, and transport the
current certificates using the proved row/root refinement. Retained support is
checked from lexical value evidence and dependencies, independently of the
declared function port. This is a candidate proof judgment, not a new source
annotation or runtime representation. Current elaboration already retains
private control summaries separately from public function types
([Elaboration](../../spec/elaboration.md)).

The alternatives have different obligations. A family of whole legacy source
derivations would still need a common substitution and continuation interface;
quantifying separately over the existing rich types does not construct it.
Normalization would instead need an operational correspondence preserving
allocation, callback order and retained support. The next prototype tests the
contract-based lambda rule directly, because row/root transport supplies its
local beta obligation. Neither alternative is ruled out generally.

Use a separate experimental contract-source judgment first. Its lambda rule
must retain a structural actual-body derivation and a contract-to-body
refinement. Variables, application, binding and branch results use the common
contract, so closed substitution must be proved for that judgment itself.
Independent support substitution must reuse the existing lexical bounds; it
must not reinstate the port-resource capture guard or replace unknown support
with an empty set. Ordinary type erasure must retain the declared ports.

The acceptance gate is a whole-expression derivation for one helper bound once
and called with both Unit and sequenced-Unit closures, followed by the
cell-retaining instance, a branch returning either closure and a returned
callable used by its caller. Require actual beta/bind/branch steps and current
certificate, accounting and support transport for those same derivations.
Reject the prototype if it supplies only ordinary port typing, separate
per-call legacy types, or another after-beta wrapper. Outside-owner receipt of
the retained closure must still fail its actual support check. No desired
successor invariant or successful future execution is an input.

This gate does not by itself replace M4's source invariant. Before changing
shared judgments, map the constructed interface to `ExecutionSite.current`,
`pending` and `coherent`, and the application, capture, resume and resource-exit
preservation boundaries. Exact operation input/output contracts and saved
continuations must then use the same value interface; an operation-input-only
repair is insufficient. `ExecutionSite.certified` is another distinct field:
it certifies the actual declaration plan, whereas the current row refinement
transports `Code`, `CodeChecked` and accounting. The old application exposes
the exact body plan, so its certification can be decomposed at beta. A common
contract no longer supplies that equality. The ordinary prototype examples
must construct certification structurally; private bodies containing handlers must
retain their actual plan and declaration certification, or construct a
certification transport, before they can form the successor execution site.
Row refinement alone does not establish this obligation.

Retain the prototype only with that explicit migration
boundary and its positive compositional substitution evidence. General
higher-order admission remains open until the full invariant is connected.

The separate ordinary prototype now passes its bounded gate. Its recursive
public contract supports compositional substitution while retaining private
lambda witnesses; the examples include one bound helper with both unchanged
bodies, independently checked retained support, common branch results and an
actual returned-callable invocation. Current code/resource certificates and
accounting checks follow those derivations. Ordinary actual-plan certification
is constructed structurally. This evidence retains the candidate for the
migration below; it does not establish effectful or general M4 admission.

### M4 migration boundary

Inspection of the current judgments identifies the following connected changes.
These are obligations of the existing D4 repair, not additional language scope.
The ordinary contract-source prototype does not yet discharge them.

| Boundary | Evidence the migration must retain |
| --- | --- |
| Current expression | `SourceAdmission.Admitted` contains the legacy structural `Expression` and `Auth`, as well as its current `Code` certificate. The new source must supply type, effect, scalar requirement and authentication evidence for the same syntax; ordinary port erasure alone cannot replace these fields. |
| Private callable body | `ExecutionSite.certified` certifies the actual declaration plan under the current outward allowance and resource world. Retain this certification with the actual body evidence, or prove its transport; a public row refinement supplies neither a declaration recipe nor certification of nested handlers. |
| Focus and return | `ExecutionSite.focus` and `plug` transfer one authenticated source into and out of a saved plain frame. The frame and its returned value must share the public contract while preserving each lambda's private evidence. |
| Operation and continuation boundaries | `OperationRows` fixes both operation argument and result rows. `ContractRows` and `PendingRows.live` fix a captured continuation's input and answer rows recursively; `spent` keeps its answer contract. All these boundaries must use the same value interface. |
| Capture, resume and closing | Saved source, its certified declaration plans, lexical support and contextual checks must survive capture and restoration together. Resource receipt and exit must use actual retained support, independently of the declared function port. |
| Initial admission | `Program.source`, `authenticated` and `certified` must construct the migrated current and pending invariant from static source evidence. No constructor may take a desired successor invariant or successful execution. |

The relevant definitions are in
[SourcePlannedSources](direct-effects/one-shot/SourcePlannedSources.lean),
[SourcePlannedChecks](direct-effects/one-shot/SourcePlannedChecks.lean),
[SourceScheduledCleanupInterfaces](direct-effects/one-shot/SourceScheduledCleanupInterfaces.lean)
and [SourceScheduledInitialAdmission](direct-effects/one-shot/SourceScheduledInitialAdmission.lean).
The scalar source requirements and the contextual accounting root are distinct
fields: transporting the latter does not automatically construct the former.

Extending the prototype to effects must first index its source derivation by
exact operation contracts, continuation contracts and execution scope. The
current ordinary judgment has none of these indices; choosing them separately
at each effect constructor would not authenticate one program. Substitution
must preserve the body evidence and these interfaces compositionally. An
implementation may factor shared judgments or introduce an authenticated
companion, but it must connect this full boundary before claiming general
higher-order admission.

### Indexed source checkpoint

The separate
[contract admission judgment](direct-effects/one-shot/CoreCallableContractAdmission.lean)
now fixes exact operation contracts, execution scope, outward allowance and
resource world throughout recursive source evidence. Scalar requirements and
actual declaration plans remain distinct indices. Lambda evidence retains the
private body, scalar outward bound and public-plan certification; actual-plan
certification follows structurally. Substitution preserves these witnesses and
independent retained-support bounds.

Its [effectful examples](direct-effects/one-shot/CoreCallableContractAdmissionExamples.lean)
construct a single helper accepting both unchanged implementations of the same
requesting contract, including the extra-sequencing case. Bind/beta steps and
current-check transport pass independent compilation. The transport takes
current certificates and accounting as inputs; it does not construct an
admitted enclosing handler or prove handler response. Wrong signatures and
false support bounds are rejected. This retains the candidate for migration,
without completing general admission.

That checkpoint retained legacy owner contracts. Common input/answer contracts
must also reach operation results and live/spent pending interfaces. There is
a module dependency boundary:
these experimental modules transitively import `SourceScheduledCleanupInterfaces`.
Importing them back into that file would create a cycle. The next integration
must factor the required definitions or justify a generalized companion
invariant, with concrete current/saved-source preservation and a connection to
M4's existing guarantees. Another conditional beta wrapper would not meet that
acceptance boundary.

The [current/saved-source checkpoint](direct-effects/one-shot/CoreCallableContractExecution.lean)
uses an upper companion importing the existing M4 checking and accounting definitions.
It avoids a back-import into `SourceScheduledCleanupInterfaces`. Its current
site replaces the legacy source/authentication fields for this prototype;
structural saved frames carry the same recursive source, common contracts,
scalar requirements and independent support. A projection to the lower
`SourceTemplates.Expression` is admissible only by construction; that judgment
does not require the function's exact private body signature.

The [concrete acceptance case](direct-effects/one-shot/CoreCallableContractExecutionExamples.lean)
constructs a checked predecessor with live cell0 and a helper suffix. The helper
accepts two Unit-to-Int implementations that read the same cell, one with an
extra Unit bind; both retain actual cell support. Generic focus, exact cell-read
reply, plug and bind transports recover that same suffix with its private
evidence and derive current and pending certificates and accounting from the
predecessor. The example applies all four transports in one actual raw trace.
Both modules pass fresh independent warnings-as-errors compilation; all 18
dependency reports use only standard axioms.

Saved frames accept resources visible at their receiving scope and already in
the current world. The returned value's actual support discharges that bound,
independently of its declared function port. The builtin reply obtains its
result contract from the same exact global operation key and its receiver from
the physical cell update. User-handler replies, callable operation results,
capture/resume/discard execution, cleanup and resource-exit support remain
required subsequent integration work. The full M4 invariant and general
Core admission remain open.

The [owner-source checkpoint](direct-effects/one-shot/CoreCallableContractRegistries.lean)
now supplies an immutable operation/policy registry and common continuation
input/answer contracts. The same experimental source uses owner tables and the
resource world as recursive indices. Resume and discard source rules retain
lexical owner resolution, capabilities and scalar requirements. Structural
substitution, actual-plan certification and lower typing cover both rules;
private callable bodies and common public contracts remain separate.

Two earlier theorem scopes change with these constructors: `erase_at` requires
the actual ticket-scope interpretation, with `erase` retained for empty scope;
`value_demand` proves empty immediate demand for actual values, replacing the
old claim for all expressions. Five affected modules pass independent
warnings-as-errors compilation, with 50 standard-axiom reports. Existing finite
example statements are unchanged. This establishes the registry/source
checkpoint, not handler admission or full M4 preservation.

The next checkpoint extends that same source mutually with clause offers and
declarations, then adds handler/live/spent pending interfaces. Actual clauses
must retain private source evidence under the inserted common owner contract.

The bounded execution gate constructs a checked fixed-world handler request and
its selected clause entry. One callable-result operation contract must admit
both the unchanged Unit callback and a callback retaining cell0, with the same
captured bind-and-invoke caller. The clause successor must follow from that
current request's source, exact cut, checking certificate and saved accounting
root. The lower capture-checking laws can be reused after inversion of the new
source; the legacy `ExecutionSite` wrapper still requires old authentication.
The corresponding outer receiver must reject retained cell support. Full runtime
resume, clause return and changing-world transport remain subsequent gates.

The subsequent resume migration must also reconstruct saved support under the
restored receiving context. In the
[clause-cell result fixture](direct-effects/one-shot/fixtures/core-resume-clause-cell-closure.ash),
capture occurs before any cell exists. The handler clause acquires a cell,
constructs a pure callback retaining it, and resumes with that callback. The
restored caller invokes it while the clause's cell frame remains below the
capture. The current Rust CLI accepts the program and returns `() : Unit`.
Moving that invocation outside the handler in the
[escape fixture](direct-effects/one-shot/fixtures/core-resume-clause-cell-closure-outside.ash)
is rejected with `type.resource-escape`.

This is implementation evidence for the existing operation-result and resource
support obligation. A saved input bound fixed at the pre-capture resource world
cannot simply be copied through this resume. The full invariant must transport
the saved source and support bounds into the actual restored world and receiving
context, while retaining the private body evidence and rejecting the escape.
The fixed-world plain/cell checkpoint above does not yet prove that transport.

## Question

Can one expression language, an ordered stack of interpretations, and separately
checked continuation capabilities explain effects, providers, resources,
disposal, and hooks without computation wrappers or conversions between
computation models?

The candidate uses ordinary values, lexical binding, operation requests, and
handler boundaries. Sequencing pushes a frame. A request captures frames.
Resumption reinstalls them. Ownership checking determines which additional
actions may manipulate a capture. There is no `Comp` type constructor, source
`return` operation, selectable bind, transformer stack, or cross-model `lift`.

The presence of `Bind` in current Core is compatible with this account: it is
the syntax and evaluation of a sequential local binding. An optional
denotational account does not define the operations of this calculus.

## Context and constraints

Current semantic authority is the specification:

- [Bindings](../../spec/dynamic-semantics.md#bindings) evaluate the initializer
  before entering the suffix, with a saved lexical environment.
- [Effects](../../spec/static-semantics.md#effects) use exact parameterized
  identities and exhaustive, result-preserving handlers. The hidden capability
  must be consumed on each normally completing clause path.
- [Handler execution](../../spec/dynamic-semantics.md#effect-handlers-and-completion)
  selects the nearest exact interpretation, moves the segment through its
  boundary, runs the clause outside that segment, and restores it on resume.
- [Resources](../../spec/dynamic-semantics.md#scoped-cell-execution) separate
  duplicable access handles from unique scope completion authority.
- [Cleanup](../../spec/dynamic-semantics.md#scoped-cleanup-actions) distinguishes
  armed actions from running actions and required unfinished completion.
- [Hooks](../../spec/dynamic-semantics.md#synchronous-hook-execution) use ordinary
  handlers and applications, with separate registration owners.

The [Core dialect decision](../decisions/AD-0007-typed-core-dialects.md) requires
typed structure and independent validation. The relevant representation is
`PureComputation::Bind` in [the shared substrate](../../src/core/dialect.rs), and
request, handler, resume, discard, resource, registration, and cleanup nodes in
[Effect Core](../../src/core/effect.rs). The finite control graph in
[capture checking](../../src/core/capture/control.rs) is evidence that current
checking already follows control positions beyond a local operation signature;
it does not establish inference for the proposed extension.

The important pressure from DN-0031 and DN-0032 is mixed control: a request can
capture intervening handlers, owned scopes, and unfinished clause work. A
continuation contract must constrain this entire segment. Properties of just
its returned value or effect row cannot suffice.

Existing evidence transfers within its scope: exact matching and lexical
instantiation in [effect tests](../../tests/effect_runtime.rs); owner movement
and surviving cleanup context in [cleanup interactions](../../tests/cleanup_interactions.rs);
callback order and registration-site context in [hook tests](../../tests/hooks_runtime.rs).
None proves multi-shot, escaping, or asynchronous behavior.

## Candidate directions

The working candidate is a direct handler calculus with one evaluation stack
per running task. The ordered interpretation stack is the projection of
accepting frames from that stack; it is not a second, independently mutable
registry. Suspended tasks and captures retain segments, so extended execution
can have several stacks without changing the expression language.

Compare it with ordinary wrappers around current scopes. Wrappers are a useful
baseline for provision composition, but cannot by themselves introduce the
missing ownership and transfer rules. Indexed families of computation models
remain an optional mathematical comparison, not the source or Core foundation.
Do not insert model-conversion terms to make mixed handlers compose.

## Syntax and binding

This is a small administrative presentation. `x` names an ordinary value, `k`
names a continuation capability, `i` is an exact instantiated effect identity,
`p` is a provider value, and `h` is a fresh dynamic handler activation. Existing
functions, data, matches, and primitive operations are inherited from Core.
Strict operands are displayed as values; a general operand is evaluated once
with an ordinary binding at the same scope position.

The grammar separates the sequential kernel from explicit capability
extensions. `split`, `park`, and `suspend` are candidate administrative forms,
not currently executable Ash syntax. Lexical classes such as `variable`,
`value`, `exact_instance`, `provider`, and `contract` are parameters to this
grammar. The semicolon in the grammar is formal sequencing punctuation,
not a proposal to add semicolons to Ash source.

```ebnf
expression ::= value
  | value "(" value ")"
  | "let" variable "=" expression ";" expression
  | "perform" exact_instance "." operation value
  | "handle" expression "with" provider
  | "resume" continuation value
  | "discard" continuation
  | "resource" identity "," variable "=" provision ";" expression
  | "cleanup" value ";" expression
  | "split" continuation "as" continuation "," continuation ";" expression
  | "park" continuation "in" owner
  | "suspend" ;
provider ::= "handler" exact_instance "under" contract "{" clause { clause } "}" ;
clause ::= operation variable "with" continuation "=>" expression ;
```

A provider is an exhaustive clause closure with its lexical values, type/row
instantiation, and declared control contract. Creating it installs nothing.
Installing it creates `h`; each request creates a fresh `k`. Provider code
identity, exact effect instance, handler activation, and continuation identity
are distinct. A provider containing restricted captured authority is itself
restricted; syntax for a provider value does not imply unrestricted reuse.

For the base calculus, a handler preserves its body's result type `A`. A clause
for `op : P -> Q` receives `x : P` and a capability whose input is `Q` and whose
resumption result is `A`. Normal body return passes its value through. There is
no implicit result transformer or new source return clause.

A provision establishes an access value, an exact identity substitution, an
interpretation, and any completion obligations. The `resource` form abbreviates
that protocol and its scopes; it does not make every provider allocate state.
The resource's formal identity and access variable are bound only in the body.
Setup executes in the preceding scope. A stateless provision can have no
physical allocation and an empty completion action.

Four bindings therefore coexist without four sequencing operators:

| Binding | What it binds | Dynamic significance |
| --- | --- | --- |
| `let x = e; n` | An evaluated value | Saves and later enters the suffix |
| `resource r,x = P; n` | Fresh instance and access | Runs establishment and introduces obligations |
| `handle n with p` | An interpretation boundary | Changes exact request selection inside `n` |
| `op x with k => n` | Operand and captured control authority | Runs a clause outside the captured boundary |

The contextual notation `[r:E, s:F].e` from DN-0032 remains useful for describing
open syntax. Applying it substitutes request instances, types, access values,
evidence, and dependencies together. It is not yet a first-class rank-1 Ash
value. Aliasing reusable access is permitted where its contract allows it;
identifying two independent owners requires a separate structural justification.

## Machine state and stack

Write `M = <S, eta, e, K>`. `eta` contains lexical values and instantiation;
`S` records resource state, continuation records, and ownership; `K` is a stack
with its nearest frame on the left. `S` is mathematical bookkeeping, not a
requirement for a new runtime registry or a universal user-visible state object.

The relevant frames are:

| Frame | Retained information |
| --- | --- |
| `B(x,n,eta)` | A pending value binding and suffix |
| `H(h,i,p)` | Exact accepting interpretation and provider environment |
| `U(g)` | Clause completion group owning its outstanding continuation tickets |
| `O(a,P)` | Resource completion authority and its protocol |
| `F(a,action,phase)` | Cleanup authority: armed or running |
| `Close(z)` | Required completion of an in-progress close |
| `Finish(o,v)` | Required normal provision completion and its saved result |

Strict applications and other Core contexts contribute their ordinary frames.
For the current one-ticket fragment, `U(g)` corresponds to the current clause
boundary with its live/consumed capability. A group is bookkeeping for explicit
splitting; it does not permit copying that boundary freely.

A live continuation record is `S(k) = live(g,Q,A,chi,C,support)`, where `C` is
the cut stack segment, `chi` is its allowed control behavior, and `support`
includes retained access, lexical instantiation, provider dependencies, and
required residual interpretation. Owning edges and non-owning access edges are
different. Recursively owned captures are included in the ownership closure.

The key invariant is that every live completion obligation has exactly one
owning location: active control, one captured segment, a clause group, or an
explicit receiving owner. Access aliases create no owning edges. Capturing a
segment transfers those owning edges without duplicating them.

## Sequential transitions

The following rules suppress unchanged components of `S`. Provider values and
operands have already been evaluated. Fresh names are chosen outside the
support of the current configuration. Ordinary value evaluation resolves
variables and closures through `eta` as in Core.

### Binding and installation

Binding pushes an ordinary frame. Handler entry pushes an accepting frame;
normal return simply removes it. These rules determine sequencing directly.

```sequent
family ordinary-control:
  E-Let :=
    ===>
    <S, eta, let x = m; n, K> -> <S, eta, m, B(x,n,eta) :: K>

  E-Let-Value :=
    ===>
    <S, eta1, v, B(x,n,eta0) :: K> -> <S, eta0[x := v], n, K>

  E-Handle :=
    h fresh
    p interprets exact instance i
    ===>
    <S, eta, handle e with p, K> -> <S, eta, e, H(h,i,p) :: K>

  E-Handle-Value :=
    ===>
    <S, eta, v, H(h,i,p) :: K> -> <S, eta, v, K>
```

### Request and forwarding

Decompose the stack as `L ++ [H(h,i,p)] ++ Kout`, with no frame in `L` accepting
the requested exact instance. This includes builtin accepting boundaries in
the nearest-match test; a nearer builtin is not skipped. The displayed rule
is the source-provider case. Its builtin counterpart retains the specified
authenticated primitive transition.

The request boundary uses the existing structural judgments rather than one
undivided admissibility predicate. `SourceCut(i,K,C,Kout)` identifies the exact
nearest source boundary. `WellFormed(K,Q,R,ambient)` checks ports, support,
ownership uniqueness, names, shape, delimiters and external resources. The
operand-access premise checks that its resources occur in `visible(Kout) ++
ambient`. The selected request must also have the structural
`SourceAdmission.Code.request` derivation for this actual cut, including its
callback, owner-bound, cleanup-budget, selected-clause, retained-continuation
and recursively checked clause-body premises. A separate usage check authorizes
the declared one-shot actions.

```sequent
E-Request :=
  SourceCut(i,K,C,Kout)
  p.op = (x, k_source, e_clause, eta_p, chi)
  C = L ++ [H(h,i,p)]
  WellFormed(K,Q,R,ambient)
  Fits(C,Q,A)
  Fits(Kout,A,R)
  the sound payload annotation for v is a subset of visible(Kout) ++ ambient
  the selected request has a structural Code.request derivation at this cut
  the independent usage check authorizes chi
  k and g fresh
  S1 = S with k owned by g and record live(g,Q,A,chi,C,support(C))
  ===>
  <S, eta, perform i.op v, K> -> <S1, eta_p[x := v, k_source := k], e_clause, U(g) :: Kout>
```

The rule is a mathematical characterization of admitted execution. It does not
propose deferring these premises to a fallible runtime check. The one-shot
[structural boundary](direct-effects/one-shot/StructuralKernel.lean) proves that
`CaptureAdmission`, predecessor well-formedness and ticket freshness construct a
well-formed live boundary with exact owner insertion and outside payload
support. It assumes the payload annotation; expression checking must derive that
annotation separately. The two `Fits` premises are the split produced by
`capture_type_decomposition`. Resumption is proved for the actual well-formed
clause prefix. Disposal separately requires `Discardable` for that prefix and a
fresh close owner. The
source-level `Code.request` judgment and independent usage check remain
necessary; the lower-level capture theorem does not prove all future clause
executions safe.

The selected boundary and all intervening interpretations are absent while
the clause runs. A direct same-instance request in that clause therefore
forwards outward, unless the clause itself installs a nearer interpretation.
No `forward` or `lift` primitive is necessary.

### Resumption and clause return

Each ticket is one-use. Multi-shot behavior will be explicit ticket splitting,
not reactivation of a consumed ticket. `Kc` is the entire current clause
continuation, including work after `resume`. The live record owns a cut stack,
not a copy of `Kc`. The rules below use the structural proof representation of
the clause boundary and saved record: `Kc` contains the live ticket boundary,
and `Kc'` is the same actual prefix after that ticket becomes spent.

```sequent
family resume-control:
  E-Resume :=
    S(k) = live(g,Q,A,chi,C,d)
    local authority to consume k is present
    v has type Q
    Kc = F ++ live(k,Q,A,C,Kout)
    Kc' = F ++ spent(k,A,Kout)
    WellFormed(Kc,A,R,ambient)
    S1 consumes k and transfers C to active control
    ===>
    <S, eta, resume k v, Kc> -> <S1, eta, v, C ++ Kc'>

  E-Clause-Value :=
    g has no outstanding locally owned tickets or unfinished required actions
    ===>
    <S, eta, v, U(g) :: Kout> -> <S, eta, v, Kout>
```

The actual-prefix `WellFormed` premise supplies `Fits`, support, uniqueness,
names, shape and delimiters for the full clause front.
`structural_resume` proves `C ++ Kc'` well formed, the exact owner permutation
and absence of the consumed ticket. For transferred continuations, checking
must also cover the destination interpretation context. Restored execution
eventually returns through `C` into the clause continuation; it does not abandon
the clause suffix. This is deep resumption.

### Disposal

Disposal consumes a live ticket, skips its expression suffix, and executes a
close plan. `close(plan)` walks owned obligations in structural inner-to-outer
order, including recursively owned captures, with each obligation visited once.
It does not traverse access aliases as ownership.

```sequent
E-Discard :=
  S(k) = live(g,Q,A,chi,C,d)
  chi permits disposal
  Kc = F ++ live(k,Q,A,C,Kout)
  Kc' = F ++ spent(k,A,Kout)
  WellFormed(Kc,Unit,R,ambient)
  Discardable(C,Kc',plan)
  z fresh
  S1 consumes k and transfers its owned closure to closing z
  ===>
  <S, eta, discard k, Kc> -> <S1, eta, close(plan), Close(z) :: Kc'>
```

`close(plan)` is internal control, not an ordinary callable capturing `Kc'`.
It finishes with unit, after which `Close(z)` is removed and the original
clause continues. `structural_discard` proves this abstract-plan boundary for
the actual clause prefix. The current lexical runtime separately uses the
structural close certificate retained by `SourceAdmission.Code.request`; an
abstract `Discardable` plan does not establish that runtime admission. Closing
transitions have these requirements:

1. Non-owning expression frames are skipped. Captured source handlers are not
   reinstalled, and abandoned callbacks are not run.
2. A resource or registration owner performs its specified release/removal.
   Still-enclosing builtin resource interpretations remain usable until their
   own closing positions, as in current Ash.
3. An armed cleanup owner changes to running before invoking its action through
   ordinary evaluation. Finishing the action discharges that owner.
4. A running cleanup or unfinished `Close` cannot be abandoned or duplicated.
   It can be captured and resumed once; suspension preserves its obligation.
5. Completion must not skip an outside owner or a scheduled resume on which an
   outside completion depends. Each invoked action must retain the exact
   required interpretation at its closing position.

Initial preparation failure leaves the capability unconsumed. Once actions
start, the calculus does not promise rollback, replay, or eventual completion.
Internal host failure keeps the current specification's weaker guarantee.

The [annotated one-shot kernel](direct-effects/one-shot/KERNEL.md#structural-disposal)
develops this closing obligation as the structural judgments `Closes` and
`Discardable`. It checks each invoked action against the materialized close
suffix, rejects retained structural ticket uses in cleanup closures, and proves
preservation of the annotated control invariant at discard. It also proves
per-invocation interpretation correspondence. The expression layer now derives
retained resource and free-ticket dependencies with substitution proofs.
Residual-request inference and preservation of complete source-derived
admission through arbitrary callback evaluation remain open.

The [expression-bearing machine](direct-effects/one-shot/KERNEL.md#expression-bearing-execution)
now invokes actual cleanup values and projects its transitions to the ownership
kernel. Checked traces cover outward capture during cleanup and disposal that
reads a retained cell before release. This establishes concrete execution and
ownership accounting for those paths. The
[access layer](direct-effects/one-shot/KERNEL.md#expression-and-retained-control-support)
proves joint ledger and expression/control support preservation for every
finite execution satisfying explicit local release, capture, and disposal
checks. For closed executions it excludes completed resource references in
current expressions and retained frames, including dormant captures. Deriving
those checks from source admission remains open. The usage-execution layer
below joins continuation usage to this same admitted execution relation; the
joint layer also combines types and effects for individual transitions and
concrete executions.

## Independent continuation capabilities

A control contract is a set of permitted actions with associated evidence, not
one ordered mode label. The selected provider declares what its clause may do;
the captured segment determines what it can safely support. Admission requires
both. A declaration cannot confer ownership rights that the segment lacks.

| Axis | Permission or obligation |
| --- | --- |
| Resumption | Consume a ticket by reinstating its segment |
| Duplication | Split a ticket using a specified interpretation of the whole capture |
| Abandonment | Finish without running the captured suffix |
| Disposal | Execute the close protocol needed for that abandonment |
| Escape | Transfer the ticket and its obligations beyond the current clause |
| Suspension | Retain owned execution without taking an evaluation step |
| Overlap | Permit simultaneously live branch executions to access shared support |

Linear use means no implicit contraction or weakening of authority. A
resume-only ticket must be resumed on a normally completing local path.
A resume-or-dispose ticket admits zero or one suffix executions while its
authority is still consumed explicitly. An affine source binding can elaborate
an unused ticket to disposal only if a close program is admitted; it cannot
silently forget cleanup. Duplicable but non-discardable authority is possible.

In the one-shot Core target, resume/dispose action flags govern the clause's
explicit expressions. An admitted outer discard can recursively consume live
tickets wholly owned by its capture, even when their clauses only resume.
Their close obligations still have to be discharged. Resume-only syntax alone
therefore does not prohibit indirect abandonment; that stronger restriction
would need a separate capability and an explicit Core semantic comparison.

Suspension is not escape: a task can pause within its owner. Escape is not
duplication: a transferred ticket can remain one-use. Sequential repetition
does not imply overlap safety. Eventual resumption, termination, and successful
native release are not consequences of any of these usage permissions.

### Explicit splitting and multi-shot execution

For the first precise extension, permit pure, total certified splitting.
`split_capture(C,pi)` supplies two segments, an ownership partition, and a
consistent renaming of internal continuation, handler-activation, and owner
identities. Static site identities may remain shared. The certificate `pi`
describes the resource interpretation; it is not arbitrary Rust cloning.

```sequent
E-Split :=
  S(k) = live(g,Q,A,chi,C,d)
  chi permits splitting under pi
  split_capture(S,C,pi) = (S1,C1,C2,d1,d2)
  k1 and k2 fresh
  S2 replaces g's ticket k with live tickets k1 and k2 for C1 and C2
  ===>
  <S, eta, split k as a,b; e, K> -> <S2, eta[a := k1,b := k2], e, K>
```

Both tickets must subsequently be consumed or validly transferred. In this
rule `S1` is the state supplied by the splitter and `S2` extends it; the original
`k` is consumed. Runtime exhaustion is outside its source-total idealization.
Effectful or fallible cloning needs an explicit establishment computation and
failure ownership protocol before it can instantiate a broader split rule.

Structural admissibility is recursive:

| Captured component | Splitting requirement |
| --- | --- |
| Ordinary frame | Its semantically retained values permit duplication |
| Handler frame | Provider environment and interpretation permit repeated installation/execution |
| Live clause group | Every outstanding ticket and its ownership graph can be split consistently |
| External access | Its owner remains live, and the access/protocol permits repeated use |
| Internal resource owner | A specified branch-copy protocol; default is rejection |
| Armed cleanup or registration | An explicit duplication policy; default is rejection |
| Running cleanup or unfinished close | Rejected |

An outer retained cell can be shared by two sequential branches without copying
its owner. An internal cell can instead be copied into two fresh branch
instances if the provider supplies a valid snapshot protocol. Every associated
handle, request identity, saved instantiation, and dependency must be renamed.
Snapshotting cannot proceed if outside references would become stale or
ambiguous; the certificate must rule those out. Neither choice follows merely
from `multi-shot` permission.

Turning an internal owner into one shared owner for several branches would
require a new common owning scope and final completion protocol. That is an
explicit additional interpretation, not an instance of ordinary frame copying.
The initial candidate supports shared owners already outside the cut and
certified branch copies; it does not silently invent shared internal ownership.

## Static judgments

Use `Gamma` for reusable bindings, `Delta` for restricted values and completion
authority, and `Xi` for exact operation contracts, support, and stack/capture
constraints. An expression judgment is:

```text
Gamma ; Delta ; Xi |- e : A ! epsilon => Delta'
```

This states ordinary result typing, required effects, and authority after normal
completion. It is not a computation type or a conversion between models.
The surrounding control judgment relates expression summaries to possible
captured segments. A closure's type/support summary includes its restricted
captures and latent control requirements; ordinary arrows cannot erase them.

For sequencing, authority is threaded through the initializer and suffix. `x`
is placed in the reusable or restricted context according to its value usage.
`CompatibleCuts` checks possible operation captures through the binding frame;
its purpose is to prevent an operation in `m` from repeating or discarding
authority needed by `n`.

```sequent
T-Let :=
  Gamma ; Delta0 ; Xi |- m : A ! epsilon1 => Delta1
  extend(Gamma,Delta1,x:A) ; Xi |- n : B ! epsilon2 => Delta2
  CompatibleCuts(m, B(x,n), Xi)
  epsilon = admissible_union(epsilon1, epsilon2)
  ===>
  Gamma ; Delta0 ; Xi |- let x = m; n : B ! epsilon => Delta2
```

`admissible_union` preserves Ash's row/lacks restrictions. The extra cut
condition is essential: typing both expressions separately and taking row
union is insufficient for control-flow safety.

The [expression proof layer](direct-effects/one-shot/KERNEL.md#expression-dependencies)
proves one necessary part of this condition: an actual cut through a binding
suffix that retains an outside ticket cannot be discarded. The frame's
dependencies come from the suffix syntax, with explicit lexical-closure and
resource-freshness prerequisites for substitution. The separate
[structural usage proof](direct-effects/one-shot/KERNEL.md#structural-continuation-usage)
now derives exactly one permitted consumption on each syntactic path for a
consuming suffix, preserves usage under local expression reduction, and connects
that obligation to cut rejection. Correspondence with full execution traces
and analysis of every reachable cut remain open; these results do not discharge
`CompatibleCuts` as a whole.

The protection component needs an ordered interpretation context with two
incoming capture modes: protected work is absent or present. A live clause
retains the mode of its dormant captured forest. These modes qualify the
existing one-shot capture. If cleanup requests E through
a resume-only handler, and E's clause requests farther outer F before resuming,
F can capture E's live boundary and thereby own the running cleanup. The pending
E use is internally owned, so ticket-use inclusion alone permits that transfer;
closing must still reject the protected work. The
[protection-context proof](direct-effects/one-shot/KERNEL.md#ordered-contexts-and-protection-modes)
establishes exact mode selection for actual cuts and protection transport through
capture and resumption, with this nested counterexample.

The proposed source rule must check each clause in the incoming modes it
supports and propagate the selected mode into its body. A disposal clause may
support only unprotected capture. An inner handler installed before a running
cleanup can receive that mode; rejecting all disposal within callback syntax
would be too strong. A resume-only clause also needs its subsequent outward
requests checked while it owns protected work. Callable contracts must carry
latent protection requirements interpreted at invocation, rather than checking
lambdas only against their creation-site handlers. The complete source judgment
and its preservation are still open; the context proof alone does not establish
these clause or callable contracts.

The [finite protection-contract interface](direct-effects/one-shot/KERNEL.md#finite-protection-contracts-at-invocation)
now checks outward demand summaries against the actual ordered invocation
context. A selected clause supplies a separate outward row for each mode it
supports; its exported requests are checked outside that handler. Each demand
retains its own protection requirement, so a protected incoming capture does
not force requests made after that work completes to remain protected. Existing
outside barriers still apply. These finite contracts have checked composition
and selection laws. Treatment of work executed inside reinstated captures and
authentication against the selected clause's actual policy remain open.

The [callable source component](direct-effects/one-shot/KERNEL.md#source-callable-protection-and-substitution)
now derives latent protection demands from function bodies and preserves exact
contracts and footprints through closed substitution, including higher-order
functions. Beta and bind preserve that check under a fixed supplied context;
cleanup qualifies callback execution with a running barrier.

The [runtime frame bridge](direct-effects/one-shot/KERNEL.md#protection-at-runtime-frames-and-policy-selection)
now derives this context from the actual stack, retains residual requirements
at evaluation frames, and connects local focus/plug and cleanup transitions.
Clause tables take disposal bits directly from the fixed source policy; a
checked request with a protected actual capture therefore selects a policy
that denies disposal. Deriving outward clause rows, authenticating operation
results, and preserving these checks across capture/resume and generative
resource entry remain open. These are component proofs, not complete source
admission or a Core correspondence proof.

The [residual composition theorem](direct-effects/one-shot/KERNEL.md#residual-requirements-across-capture-and-resumption)
now factors a supplied footprint through the captured interpretation prefix.
An actual cut derives an outside residual; restoration checks it against the
waiting caller frames followed by the surviving tail. A concrete check shows
that inserting a handler can invalidate earlier admission, so resumption cannot
reuse the old check without justification. Deriving all retained-code
requirements and authenticating clause rows remain necessary for whole-machine
preservation. This is a law of requirement analysis over the same direct syntax.

The [source clause phase judgment](direct-effects/one-shot/KERNEL.md#source-clause-phases-and-protection-requirements)
now threads available/consumed ticket states through source sequencing and
derives different request qualifications before and after consumption. It
projects to the existing structural usage judgment and preserves exact
requirements through closed substitution. Resume and disposal use the barrier
positions of their actual stack shapes. Captured execution and closing rows
remain inputs, and cleanup's final-phase rule covers normal invocation rather
than abandonment. Whole-machine preservation remains open.

The [offered clause-row certificates](direct-effects/one-shot/KERNEL.md#source-certificates-for-offered-clause-rows)
now require a derivation for the actual selected body, with its operation input
and result contracts, binder policy, and an empty local prefix at entry.
Selection through an actual cut and closed payload binding derive the body's
source requirements and acceptance at the surviving tail. This authenticates
the offered row relative to supplied captured execution and closing contracts;
their provenance and preservation of certificates throughout execution remain
open. The raw capture construction does not yet establish the joint machine
invariant or whole-source admission.

The [disposal requirement derivation](direct-effects/one-shot/KERNEL.md#disposal-requirements-from-executable-plans)
now computes closing footprints from executable plans and actual retained
callback source contracts. Stack induction covers nested captures; each
callback is checked against the complete remaining suffix after plans compose.
The source discard rule, authenticated plan row and runtime ticket resolution
construct an actual discard step with callback readiness and retention in its
successor. A separate bridge derives a checked callback application at the
actual invocation suffix. Preservation through callback execution, contracts
for future cleanup expressions, allocation of all continuation certificates,
and integration with ordinary typing and ownership remain open.

The [cleanup installation and return-phase proofs](direct-effects/one-shot/KERNEL.md#cleanup-installation-and-normal-return-phases)
now derive installed callback contracts from the source and preserve stored
contracts through every raw transition. Source cleanup also derives a separate
invocation certificate for the body's final ticket phase. That certificate
supports a checked callback start at the actual live or spent boundary when
the body returns. A supplied-context example rejects premature invocation
before consumption while admitting invocation afterward. Preservation through
the intervening execution and captured-residual provenance remain open; stored
callback contracts alone do not establish invocation safety or progress.

The [pending source-phase proofs](direct-effects/one-shot/KERNEL.md#pending-contexts-and-source-continuation-phases)
now derive actual evaluation-context certificates from source checking. Frames
retain the child's return phase, full contract, saved environment and exact
remaining requirements. Focus constructs these facts; plug reconstructs the
suffix from the return phase without replaying earlier effects. Bind and beta
preserve exact rows, and branch selection derives an accepted selected-arm row.
Runtime context, port and owner-phase realization remain separate from these
local raw-step proofs and must be joined before claiming whole-machine safety.

The [runtime boundary proofs](direct-effects/one-shot/KERNEL.md#runtime-phase-boundaries-and-joint-capture)
now connect phase contexts to actual live/spent boundaries and completion
history. Focus and plug join the source certificates to existing ownership and
typing preservation on the same named step. Capture shares its selected clause,
fresh owner and successor with the source clause certificate. A concrete
callable-handler execution returns into the clause's pending bind after one
resumption, with the owner recorded as consumed. General captured-row
provenance, source/port contract agreement and whole-program progress remain
open; this does not establish general source admission or Core correspondence.

The [saved frame requirements](direct-effects/one-shot/KERNEL.md#requirements-at-saved-frame-positions)
now derive resumed rows from ordinary frame and cleanup source evidence at each
frame's remaining suffix. Positional checking prevents an exited provider from
satisfying a later request. Capture decomposition and resumption use these
derived rows, with resumption preserving the same ownership/type invariant.
Frames that themselves consume continuations still need phase integration;
the general capture-table scheme and whole-program admission remain unfinished.

The [scheduled owner proofs](direct-effects/one-shot/KERNEL.md#source-phases-and-scheduled-runtime-owners)
connect a consuming source frame to its actual runtime owner through the
existing usage registry and saved scope. Ownership balance rejects duplicate
sequential consumption without rejecting alternative branches or idle scopes
that retain consumed owner names. Dormant captures retain explicit outside
access. Phase-sensitive effect-row composition and whole-source preservation
remain open; owner-demand agreement alone does not prove progress.

The [pending context chains](direct-effects/one-shot/KERNEL.md#phase-and-contract-composition-of-pending-contexts)
now compose matching use phases and full callable contracts by structural
induction. Focus and plug preserve this evidence alongside the existing joint
invariant. The result covers arbitrary finite chains of contiguous plain frames
for one source ticket and a shared analysis environment. Integrating other
frame kinds, saved scope/port agreement and all-transition source preservation
remains necessary before whole-program progress can be claimed.

The [derived owner agreement](direct-effects/one-shot/KERNEL.md#ownership-balance-determines-the-source-owner)
uses runtime ownership balance to identify the unique consuming source use
above a live boundary. Its dormant capture cannot consume that boundary's owner,
so the owner must be consumed by the current expression or pending plain prefix.
Resumption now derives the binder-to-owner equality from these judgments.
Interleaved interpretation frames, source contract/port agreement and full source
preservation still require integration before general admission or progress.

The [neutral source rows](direct-effects/one-shot/KERNEL.md#phase-neutral-source-and-derived-saved-rows)
now derive positional saved-frame requirements from consumed source chains,
retaining latent effects and cleanup protection. Composition through a remaining
interpretation suffix also derives the row of an extended exact capture.
Resumption derives its waiting-prefix check from source evidence and its owner
from ownership balance. Phase-changing interleaved captures, authenticated
handler tables and complete source preservation remain open.

The [capture occurrence interfaces](direct-effects/one-shot/KERNEL.md#interfaces-for-actual-capture-occurrences)
now couple actual saved-frame rows with executable disposal-plan rows or explicit
disposal unavailability. Capture preserves this evidence with the same selected
clause and joint runtime invariant. Two exact cuts at the same clause demonstrate
why the old key alone cannot identify both continuation rows. A uniform source
handler contract across occurrences, full source admission and progress remain
open; the occurrence-specific specialization is not a substitute for them.

The [parametric clause schemas](direct-effects/one-shot/KERNEL.md#parametric-clause-row-schemas)
now make one structural clause derivation reusable across resumption and disposal
rows. Instantiation and abstraction connect the schemas to the existing concrete
source judgment; continuation usage is checked before row substitution. An actual
capture can use the specialized certificate. Uniform ordered interpretation,
capture inference and full source preservation remain unfinished, so this does
not establish whole-program progress.

The [effect-bound correction](direct-effects/one-shot/KERNEL.md#effect-bounds-and-repeated-handling)
now avoids an exact-row admission obstruction for repeated handling. Induction
covers every finite number of pending requests under one shared effect bound;
continuation use and protection remain independently checked. Local capture and
resumption preserve the existing joint runtime invariant under bounded source
premises. A current Core fixture returns two audit actions for two requests,
classifying the obstruction as an experimental admission defect rather than
evidence for a Core change. Full bounded source preservation, progress and
formal Core correspondence remain open.

The [uniform clause-bound proof](direct-effects/one-shot/KERNEL.md#uniform-clause-bounds)
now checks one fixed handler table for multiple covered capture rows. Induction
transports coverage through arbitrary fixed ordered contexts and clause schemas;
actual capture retains its source interface and joint runtime invariant. The
same-table examples include protected captures with unavailable disposal for a
resume-only clause. Shared bounds and capture coverage remain inputs, so complete
source admission, preservation and progress are still unfinished.

The [owned phase-row extension](direct-effects/one-shot/KERNEL.md#captured-segments-with-pending-owner-consumption)
now retains pending ticket consumption with its captured live boundary. Runtime
ownership derives the source chain's owner equations, and the chain must consume
that owner once and return its answer contract. Capture, shared clause checking
and resumption preserve the new rows with the existing joint runtime invariant.
A current Core fixture returns `17` when an outward request captures a pending
inner resume. Open owner segments, intervening interpretation frames and the
complete source invariant remain unfinished; this is not whole-program progress
or formal Core correspondence.

The [outside-owner use interface](direct-effects/one-shot/KERNEL.md#outside-owner-use-interfaces)
now derives a capture's outside obligations from structural usage. Ownership
separation makes an empty interface equivalent to the existing disposal
internal-use check; restoration retains the interface. A raw open-capture resume
preserves usage, while disposal is rejected despite an executable empty plan.
Core accepts the resumptive `let` fixture and rejects its discard variant, but a
direct resume-operand variant exposes `internal.core-build` with cause
`invalid-payload`. That compiler defect is recorded without alignment work.
Open-capture phase/effect rules and complete source preservation remain unfinished.

The [named owner-phase proof](direct-effects/one-shot/KERNEL.md#named-owner-phases-in-ordered-contexts)
now derives consumption and restoration contexts from actual stacks. Structural
induction covers arbitrary intervening frames; historical name uniqueness
identifies the consumed owner and prevents another use after restoration.
Resumption joins the context update to the existing joint runtime invariant;
disposal joins it to ownership preservation under the outside-interface check.
The cleanup example retains protection in the restored capture until cleanup
finishes. Integrating these transitions into the general source phase/effect
judgment, complete preservation and progress remains unfinished. Core is unchanged.

The [open phase-segment proof](direct-effects/one-shot/KERNEL.md#source-segments-with-an-exposed-outside-owner)
now composes pending source code across interpretation and cleanup frames while
exposing one outside owner. Induction gives capture splitting, recomposition and
the owner's exact source demand. Focus, plug and restoration retain these source
certificates with the existing joint runtime invariant. The earlier open capture
is admitted by this source component and remains unsafe to discard. Captured
phase transitions still need general continuation interfaces and clause checking;
interior live-owner groups and complete source preservation remain unfinished.
This is not whole-program progress or formal Core correspondence.

The [captured phase-contract proof](direct-effects/one-shot/KERNEL.md#captured-phase-contracts-and-clause-checking)
now connects an open captured segment to clause checking. Local continuation use
and the outside phase transfer are checked separately; disposal availability
requires no lost outside obligation. Actual capture retains the phase interface
through registry extension and substitutes the selected clause's parameter.
After local consumption, the remaining clause source converts to the preceding
outside-owner judgment. Ordered handler tables still need integration, so
whole-source preservation and progress remain open.
The flat entry-row limitation is experimental evidence, not a Core alignment change.

The [resumption source proof](direct-effects/one-shot/KERNEL.md#resumption-into-open-source)
now connects a clause and arbitrary contiguous plain waiting frames to the actual
restored source configuration. Induction composes both owner states and full
value contracts. The saved segment supplies the outside state expected by the
waiting clause; its actual effect row is checked beneath the advertised bound.
Focus, plug and resume retain source certificates with the same named steps and
joint ownership/type invariant. Interior live-owner groups, multiple outside
owners, general handler tables and whole-source preservation remain unfinished.
Core correspondence remains an assessment obligation; no Core changes are made.

The [shared owner-phase proof](direct-effects/one-shot/KERNEL.md#shared-owner-phase-transitions)
now tracks arbitrary finite owner demands with one inductive transition relation.
Capture derives its outside transition by restriction; resumption updates exactly
its selected owner, including when the restored capture contains other live
owners. These maps agree with actual ordered interpretation and recover the
previous two-state source contract. Disposal preserves the complete outside map.
Actual capture and resume retain these properties with the joint runtime
invariant. The preceding source segment rule excludes a checked interior-owner example;
this motivates the source lift below. Whole-source preservation and progress
remain open.

The [shared-phase source proof](direct-effects/one-shot/KERNEL.md#source-with-shared-owner-phases)
now threads that map through direct expressions, evaluation contexts and all
stack constructors, including interior live-owner boundaries. Induction proves
capture splitting and recomposition with full contracts. Substitution and the
supported ordinary evaluation steps preserve source information; immediate
requests are checked against the actual ordered stack. The previously excluded
interior-owner example now has source certificates before and after resumption.
General continuation-record authentication, handler/resource source rules,
source preservation from authenticated records and complete admission/progress
remain unfinished. This is informative proof evidence, not a Core semantic change.

The [general restoration proof](direct-effects/one-shot/KERNEL.md#general-one-shot-source-restoration)
derives an after-resume source certificate from the before-source and a structural
saved-segment derivation at the actual restored suffix. Induction covers arbitrary
waiting frames and nested live owners. It changes the selected marker only where
that owner's source phase is consumed, retaining the other interpretations in
order. The source transition joins the same named runtime step and full joint
invariant, with the actual restored ownership map. The nested-owner example now
derives its after-source through this theorem. Obtaining the saved derivation
from maintained continuation records remains open, along with capture/disposal
source preservation and the remaining admission/progress work. Core is unchanged.

The [capture provenance proof](direct-effects/one-shot/KERNEL.md#captured-source-contract-provenance)
derives resume-contract fields from the actual source cut and retains their
saved-source evidence through fresh registry insertion. Historical registration
ties the source name to the same runtime allocation. A selected clause's source
derivation and the surviving tail construct the after-capture source; retained
capture evidence supplies the resumption premise after checked interpretation
transport. The nested-owner example connects capture and resume from a source
registry without the fresh owner. A waiting handler can change interpretation,
so transport is not unconditional. Maintained record authentication, coherence
with runtime declaration/port records, closing-plan checks and complete source
admission/progress remain open. This adds informative proof evidence only.

The [closing source proof](direct-effects/one-shot/KERNEL.md#closing-source-and-disposal)
derives the planned source from actual release, callback and retirement entries.
Closing data retains callback source and the check for abandoned outside-owner
obligations; the receiving suffix determines the exported closing row. Disposal
source preservation joins the same runtime step and ownership map. The selected
owner is consumed immediately and nested retirements remain pending. Source
preservation also covers synchronous callback start/finish, retirement, closing
completion and resource release. A callback/retirement/release example retains
source and usage evidence. Maintained record authentication, remaining source
rules and complete admission/progress remain open. Core and the excluded later
continuation capabilities are unchanged.

The [shared source types](direct-effects/one-shot/KERNEL.md#shared-source-types-and-pending-contexts)
give each binding one annotation projected to ordinary ports and protection
contracts. Closed substitution, beta/bind reduction, and pending-context
focus/recomposition preserve the shared derivation. Stored plain-frame metadata
is checked against those annotations. Operation checks and paired registries
retain compatible callable shapes, and the actual request determines the
captured input's shape. Scalar protection still abstracts ordinary atom types;
shape agreement alone does not check latent effects or stored support. Shared
typing of full pending segments, authenticated continuation records, remaining
source rules and complete admission/progress are unfinished. This is evidence
on the experimental direct syntax, with no Core change.

The [shared owner source judgment](direct-effects/one-shot/KERNEL.md#shared-owner-source-contracts)
now connects resume/discard value types to the same owner-phase derivation.
Substitution and fresh-record insertion preserve the shared choices. Its
continuation records agree with the complete runtime port contract, including
resume and close effect lists. Examples distinguish wrong operand types,
repeated owner use and protected disposal from a valid conditional that chooses
resume or discard. This still requires authenticating those fields against
actual saved captures and closing plans, preserving that evidence at receiving
contexts, and completing handler/resource admission and whole-program progress.

The [source reinterpretation proof](direct-effects/one-shot/KERNEL.md#source-reinterpretation-at-receiving-stacks)
retains finite request obligations and their positions before interpreting an
outside stack. Re-evaluation at a changed receiver constructs source expressions,
frames and saved segments with the new row, retaining their owner transitions;
the shared expression result also retains value annotations. A counterexample
proves that a cached residual row alone loses information required at another
caller. The old empty bound can fail after a handler change even when the saved
source is reconstructible there. The source record interface must therefore
retain reinterpretable requirements and specialize them at each resume site.
The existing restoration bridge now uses rechecking in place of equal-context
transport, but still requires coverage by its advertised bound. Referenced rows,
phase indices and all-transition record authentication still require integration.
This identifies a proof-model limitation; it does not request Core alignment.

The [resume-site specialization proof](direct-effects/one-shot/KERNEL.md#resume-site-specialization)
now checks the recomputed row at the actual caller without coverage by the old
cached row. It derives the before-source using a temporary checking view and
restores the original source registry after the owner is consumed. Shared
annotations preserve the runtime port contracts. A conditional join preserves
the same runtime resume and actual ownership map. The changed-handler example
accepts its newly exposed effect at an explicit outside interface and rejects
its absence. Authentication of nested records, shared saved-segment annotations,
and admission maintained across all transitions remain open.

The [recursive capture-source judgment](direct-effects/one-shot/KERNEL.md#recursive-capture-source-authentication)
now checks a historical resume-source certificate at every live capture,
including dormant nested captures. Structural decomposition and recomposition,
all transitions without ticket allocation, and fresh capture from an actual
source cut preserve this component. Selected certificates yield reinterpretable
requirements. A negative example rejects an unregistered nested owner that an
outer certificate and the earlier active-segment judgment miss. Closing
contracts, shared ports, referenced rows and current phase agreement still need
one maintained invariant before complete source admission and progress follow.

The [shared saved-segment proof](direct-effects/one-shot/KERNEL.md#shared-saved-segment-annotations)
now derives ordinary ports, owner-phase source judgments and recursive capture
authentication from the same pending and saved value annotations. Decomposition
and recomposition preserve their agreement. The actual cut determines the
captured answer port, and fresh capture constructs the shared resume record and
pending live boundary while retaining older records. Concrete capture and resume
examples distinguish integer from Boolean and reject incorrect metadata.
Closing obligations, effect-list authentication, dynamic phase/row agreement and
handler/resource source admission remain outside this result; whole-program
preservation and progress are still unfinished.

The [shared closing-plan proof](direct-effects/one-shot/KERNEL.md#shared-closing-plan-source)
now obtains callback types, ordinary outward effects and protected source rows
from the same retained capture and executable plan. Disposal reconstructs the
shared after-source and joins it to the actual named runtime step and owner
phases, with recorded bounds and access checks still explicit. Cleanup start and
completion, close completion, retirement and cell release retain shared source
typing. Ordering examples reject release before a dependent callback, and shared
typing rejects a Boolean-returning cleanup that scalar protection alone admits.
Complete capture-bound authentication, general phase/row preservation and
handler/resource source admission remain prerequisites for whole-program
preservation and progress.

The [phase-sensitive source rechecking proof](direct-effects/one-shot/KERNEL.md#source-rechecking-at-current-owner-phases)
now evaluates finite requirements at the receiving stack and current owner
availability. Sequential checks advance ownership; branch arms start from the
same state and require equal consumption sets. Successful evaluation reconstructs
shared expressions, frames, segments and configurations while retaining nested
historical certificates. Examples distinguish branch alternatives from repeated
sequential use and show protection changing after consumption. Referenced
continuation rows still need recursive specialization and authentication.
Success at every future call, complete source admission and whole-program
preservation/progress do not follow from this conditional reconstruction.

The [shared resumption proof](direct-effects/one-shot/KERNEL.md#shared-resumption-at-current-callers)
now derives restoration from the actual selected historical capture, rechecked
at the caller's current phases. The invocation uses its computed row while
historical records retain their original registry. Ordinary ports agree across
that local view, and a conditional theorem joins source reconstruction with the
same named runtime step and actual owner map. A nested example passes the outer
check and two actual steps, then exposes an inner request rejected by the empty
outside interface. It identifies why recursively authenticated referenced rows
or equivalent maintained call-site evidence are still required. Reachability
from complete initial admission and whole-program progress remain unproved.

The [recursive continuation checker](direct-effects/one-shot/KERNEL.md#recursive-continuation-requirements)
now follows owner/mode references to finite demand-indexed templates. A strict
decrease in demand length proves absence of linked cycles and sufficiency of
the evaluation bound. Its structural judgment is equivalent to successful
execution of the checker and derives one-shot consumption. Ordered prefixes
compose through recursive calls. The nested example now exposes the inner
request before admitting the outer invocation. General source extraction,
template authentication and preservation through execution remain necessary
before this result establishes complete admission or whole-program progress.

The [source-template derivation](direct-effects/one-shot/KERNEL.md#source-derived-continuation-templates)
now constructs recursive requirements and collected resume entries from shared
expressions, frames and saved stacks. Each lookup certificate locates its body
in the actual retained forest and preserves the shared input, answer and demand.
Invocation now requires structural active selection as well as available
ownership. Distinct owned tickets identify its lookup template with the exact
capture execution restores. A checked configuration with a closed resume operand
constructs its raw step and runtime ownership trace without a supplied cut or
additional access premise. Checked current
configurations require owner uniqueness and derive ordinary types and one-shot
consumption from the actual owner map. Contract extension preserves the existing
templates and certificates. The nested example uses this source-derived store
and rejects direct invocation of its dormant inner continuation. Closing
templates, ordinary effect bounds, handler/resource admission, and preservation
of the complete recursive check through stack-changing steps remain
prerequisites for whole-program preservation and progress.

The [recursive transport proof](direct-effects/one-shot/KERNEL.md#recursive-checks-across-consumed-callers)
now preserves the full recursive check when caller contexts agree after consumed
markers are removed and lookups agree for available owners. It connects the
saved body's check to the physical waiting stack and actual successor ownership
map. Removing a consumed owner's templates and permuting entries with distinct
owner/mode keys preserve checking. This store result allows both resume and
disposal entries for one owner and does not commute interpretations. The nested
outer resume now has a constructed, fully checked successor. The following
result supplies general recomposition; preservation for the remaining transition
families is still required before whole-program safety follows.

The [general recomposition proof](direct-effects/one-shot/KERNEL.md#general-resumption-recomposition)
now constructs the restored segment and actual collected store for arbitrary
pending caller prefixes. `resume_step_preserves` covers every raw step from a
checked resume with a closed operand, and `resume_preserves` combines that result
with progress to construct a preserved next step. Both retain the output
annotation and checking footprint and relate the actual runtime owner maps,
with the invoked owner removed from the demand. The nested
case and an effectful bind-prefix case follow from that theorem. This closes
value-operand resumption preservation for the current judgment; fresh capture,
closing-store integration, ordinary context/source-entry steps and whole-program
safety remain open.

The [ordinary recursive reduction proof](direct-effects/one-shot/KERNEL.md#ordinary-recursive-source-reductions)
now preserves complete checked configurations for ready binds, applications and
branches. Closed substitution retains the exact recursive requirements; binds
and applications retain the footprint, while branch selection may remove
requests and permute the alternative's owner demand. That permutation leaves the
pending caller's resulting owner map unchanged. Progress derives lexical
readiness from typing, and every raw step of these ready expressions preserves
the runtime stack with no owner creation or discharge. Examples connect bound
operands and branch selection to nested resumption. The following result supplies
focus/plug integration; fresh capture, closing integration, handler/resource
admission and whole-program safety remain open.

The [recursive context proof](direct-effects/one-shot/KERNEL.md#recursive-evaluation-contexts)
now integrates focus and plugging. All nine pending-context forms preserve the
shared hole annotation and exact recursive checking equation. A plain frame's
neutral interpretation layer preserves continuation selection even through
nested template checks. Focus constructs the runtime frame from the source;
plugging restores its saved scope, and typing supplies lexical closure for the
return step. Both preserve the collected store, demand, footprint and owner map.
The example composes focus, bind reduction, plugging and nested resumption.
Fresh capture, disposal/cleanup, source entry and whole-program safety remain
open.

The [recursive capture proof](direct-effects/one-shot/KERNEL.md#recursive-fresh-capture)
now derives saved and surviving segments, their exact collected stores and
their recursive checks from the selected handler cut. Fresh record construction
retains old templates and adds exactly one owner. For immediate-resume clauses
with a structurally checked reply having no immediate effects, operand
substitution and the derived record construct a complete checked successor.
The example joins actual capture with general resumption preservation, retaining
distinct integer input and Boolean answer annotations. Arbitrary clause
admission, closing contracts, source entry, allocation-history integration and
whole-program safety remain open. This clause class is current proof coverage,
not a restriction of the target calculus.

The [structural clause join](direct-effects/one-shot/KERNEL.md#structural-clauses-and-authenticated-invocation)
now reconstructs recursive checking for sequencing, branches and effects around
continuation actions. A completed resume-only clause derives the exact demand
of its local owner and saved computation. The actual saved requirements supply
its invocation check, and the clause joins the surviving caller at the derived
owner map. An example checks requests before and after alternative resumptions.
Admission of actual handler clauses and their offered table bounds remains open;
ordinary clause port typing alone does not supply this evidence. Disposal
invocations still need authentication from actual closing plans. This is a
source-to-runtime proof join, not a new computation calculus or a restriction
of the full one-shot target.

The [actual dispatch join](direct-effects/one-shot/KERNEL.md#structural-clauses-at-actual-dispatch)
now derives the selected offer and interprets it through the surviving stack.
Capture separates the original footprint into the request, saved computation
and caller. A structurally checked selected clause bounded by the first two
parts yields a checked raw successor after actual argument substitution; its
outside acceptance follows from the original check. The example discharges
these premises for effects around alternative resumptions. The bound covers
demand membership, including protection, while execution order remains in the
source and runtime judgments; list-subsequence bounds would reject some valid
interleavings and repeated branch obligations. This remains conditional on clause admission and its offered bound, which handler installation
must supply generally. Closing integration and whole-program safety remain open;
Core is unchanged.

The [recursive closing construction](direct-effects/one-shot/KERNEL.md#recursive-closing-templates)
now derives a plan template from actual retained callback source and retirement
entries. Its exact checking equation is independent of the continuation store
and retains callback/release order. Materialization joins the surviving caller
at the derived owner map, using that caller's records, and the plan authenticates
a disposal invocation entry. Examples check nested retirement, reject duplicate
retirement and expose the missing-cell obligation after a callback/release
reversal. The closing-record construction below collects these entries from live
captures and derives the abandoned-use check. Recursive consumption below
preserves raw disposal checking; name-history and whole-program safety remain
unproved. Core is unchanged.

The [recursive completion construction](direct-effects/one-shot/KERNEL.md#recursive-cleanup-and-value-completion)
proves progress and recursive-check preservation for all value-state transitions,
including cleanup startup and completion, scope exits and ticket retirement.
Readiness follows from the pending source and recursive check, which reject
return through an unconsumed live continuation. A six-step closing example
reaches the empty caller. This joins materialized plans to their value-completion
steps; transfer to the richer state, full resource/access and name-history
invariants, and handler/resource admission still require integration.

The [closing-record construction](direct-effects/one-shot/KERNEL.md#collected-closing-records)
now collects actual-plan disposal records beside resume records, including
dormant nested captures. Structural record provenance survives capture and
resumption. A richer checked-state judgment retains previously checked states
and derives raw disposal progress; the actual lookup authenticates the declared
retirement demand. Every actual checked disposal cut derives the structural
abandoned-use condition. Examples check both modes for one owner, reject an
incorrect closing demand, and omit disposal for an otherwise constructible plan
that would drop an outside ticket use. The consumption construction below
preserves this richer check for resume and disposal; the remaining
source/invariant joins are still open. Core is unchanged.

The [recursive consumption construction](direct-effects/one-shot/KERNEL.md#recursive-state-preservation-through-consumption)
now proves progress and preservation for both consuming forms with the combined
record store. Resumption removes both modes of the consumed owner. Disposal
checks the actual plan using the surviving caller's records and preserves later
nested retirement ownership. A mixed example resumes a pending bind containing
a nested disposal; a separate actual disposal yields a checked materialized
plan. The [recursive execution construction](direct-effects/one-shot/KERNEL.md#recursive-ordinary-execution-and-completion)
now transfers ordinary expression and value-completion proofs to the combined
record store. It completes the mixed example through all seven steps to unit at
an empty stack, preserving each state's check and the concrete allocation
ledger. Fresh capture is addressed by the construction below. Builtin providers,
source installation and the general combined safety invariants remain
unfinished. Core correspondence is still a status assessment.

The [combined-record capture construction](direct-effects/one-shot/KERNEL.md#fresh-capture-with-combined-records)
now transfers fresh capture to the richer checked state for a structurally
admitted resume-only new clause. Its saved computation can dispose nested
continuations. A nine-step example proceeds from the operation request through
capture, resume, nested disposal and final return, preserving the recursive
check and actual allocation ledger. The construction below adds the new
clause's disposal case with derived balance and actual-plan checks. Complete
handler admission remains open, alongside provider and installation transitions
and the combined safety theorem. Core remains unchanged.

The [two-mode clause construction](direct-effects/one-shot/KERNEL.md#capture-with-either-one-shot-clause-mode)
now proves fresh capture with a clause that can resume or dispose its owner.
It derives ownership balance and evaluates the actual
closing template to authenticate disposal. A six-step example checks both
clause branches and executes disposal through nested retirement to final
return. Reusing existing check decomposition, source provenance and ownership
traces now derives complete ownership balance for every existing checked
state, including arbitrary finite dormant nesting. The proof inducts over the
complete recursive check and the actual capture tree. It adds no balance
premise to the state judgment. Existing source-dependency and ticket-translation
proofs also connect structural internal uses to recursive demands. This bounds
outside-owner use even when checking occurs in an enclosing caller. General
capture now derives and returns mode balance; the example supplies no separate
balance certificate. Source admission, closing-effect admission and clause bounds,
the remaining two transition constructors and the combined safety theorem
remain unfinished. Core is unchanged.

The [cleanup installation construction](direct-effects/one-shot/KERNEL.md#cleanup-installation-with-combined-records)
now derives the installed callback closure, effects and answer annotation from
the existing source. Reusing neutral-frame interpretation preserves the
demand, footprint and both continuation-record collections. Its example
installs fresh cleanup around the existing nested disposal and reuses the
ledger and disposal-preservation proofs. Handler/resource installation remains
open, alongside source admission and combined safety.

The [builtin cell construction](direct-effects/one-shot/KERNEL.md#builtin-cells-with-combined-records)
now preserves the recursive source, both stores and ownership across actual
cell read/write. It reuses request decomposition and requires the selected
operation's canonical builtin port signature. A nine-step execution continues
the previous disposal plan through a cleanup callback's cell read, release and
nested-owner retirement, with no duplicate completion. A write example changes
the cell payload from 17 to 18. These are preservation results for supplied
checked states, not a complete admission theorem.

The [request-progress construction](direct-effects/one-shot/KERNEL.md#request-progress-from-recursive-checks)
now derives the actual interpretation of a closed checked request with a value
operand. It reuses residual admission, owner-phase projection and physical
resolution. Builtin selection yields a preserved successor; existing typed
capture yields a raw handler step at a fresh historical slot. Neither selection
is supplied by the caller. Existing registry-history and fresh-owner proofs
also derive allocation for a named request step and preserve its lifetime
ledger. The same bridge reuses the existing denial of
disposal for protected captures under policy-derived tables. Complete
handler-clause admission, preservation of the extended registry and
initial-source progress remain open.

The [closing-admission construction](direct-effects/one-shot/KERNEL.md#closing-admission-from-structural-effects)
now derives closing-template evaluation from the existing structural
effect-admission judgment and actual ownership. It reuses retirement traces,
plan-owner correspondence and phase projection. General capture now takes the
plan's ordinary residual check and derives its recursive evaluation. The
remaining obligation is to admit those actual closing effects in the surviving
caller; normal completion's context cannot be reused because closing drops
abandoned source handlers. Complete clause admission and combined safety remain
unfinished. A [checked nested-continuation example](direct-effects/one-shot/KERNEL.md#closing-and-resumption-budgets-can-differ)
now shows that structural closing compatibility and hereditary source typing
do not imply containment in the normal resumption row. The local clause
interface uses the exported operation advertisement plus the resumption row
as its closing budget. The actual cut must still justify that combined bound;
the example does not establish a Core mismatch.

The [resource-world transport](direct-effects/one-shot/KERNEL.md#resource-world-extension-with-combined-records)
now carries recursive source, saved captures and actual closing callbacks into
a larger resource world. It reuses existing port-world weakening and keeps
the same continuation stores, requirements and accepted check. This supplies
the retained-state transport needed by acquisition. Historical world membership
alone does not establish current resource access.

The [resource-entry construction](direct-effects/one-shot/KERNEL.md#resource-source-entry-with-combined-records)
now admits resource bodies with enclosing-continuation actions in the recursive
source judgment. A structural discharge relation retains invocation keys, owner
demands and sequencing while removing exact local cell requests. The existing
checker supplies a finite freshness condition for preserving saved invocations
under the new builtin interpreter. Entry derives both the opened body and its
combined continuation-store check; existing ownership-balance and ledger results
continue to apply. Examples initialize/read/close a resource and enter a resource
whose body disposes an enclosing owner with a dormant nested owner. Source handler
installation, complete clause/closing-effect admission, and the combined
initial-source safety theorem remain unfinished.

The [recursive clause connection](direct-effects/one-shot/KERNEL.md#recursive-clause-ownership-and-capture-entry)
now covers those resource bodies at capture entry. Existing checked traces and
source invocation provenance derive the clause's exact ownership balance.
Both clause judgments reuse one factored capture construction. A checked request
captures into a resource clause whose body disposes the fresh continuation.
The general result still requires the clause check, completion and footprint
bound; deriving these and closing effects from handler admission remains open.

The [handler-registration and entry construction](direct-effects/one-shot/KERNEL.md#fresh-handler-registration-and-entry)
now selects an activation fresh for lifetime history, registers its table and
preserves both actual continuation stores, including dormant handlers. The
local entry theorem derives the raw step and combined successor using existing
clause typing, owner-selection and recursive-check proofs. The installation
example reuses the resource/disposal clause. Connecting this construction to
declaration admission remains open. The
[shared computational handler rule](direct-effects/one-shot/KERNEL.md#shared-handler-expressions-and-ordered-resource-discharge)
now derives entry from a combined source check. Resource discharge interprets
nearer handlers before removing builtin requests; order-sensitive regressions
and a resource-then-handler execution are checked. Handler-bearing callable
bodies, table-row and clause admission, and the combined initial-source theorem
remain unfinished.

The [declaration capability connection](direct-effects/one-shot/KERNEL.md#declaration-capabilities-and-table-modes)
now derives selected-clause completion from the existing structural usage
judgment and checked ownership trace. A structural clause/table check also
requires each disposal flag to cover the clause's actual required actions.
Handler installation returns this evidence, and capture connects it to the
selected table entry. Protected capture therefore requires resume-only usage of
that continuation, while nested clauses retain independent rights. Actual clause
checks, outward effect bounds, closing effects and the combined initial-source
invariant remain open.

The [outward-summary proof](direct-effects/one-shot/KERNEL.md#outward-summaries-before-caller-interpretation)
now factors the recursive check of source expressions without an enclosing
continuation through their own ordered interpretations and then the current
caller. This includes computational handlers and scoped resource bodies.
Existing uniform residual coverage checks actual outward rows beneath
advertised bounds. This supplies a prerequisite for handler-bearing callable
bodies; their source typing and substitution still need integration, alongside
complete clause effect admission and initial-source safety.

The [annotated typing layer](direct-effects/one-shot/KERNEL.md#annotated-expression-types-and-frame-ports)
now derives value support, pending-context ports, canonical value forms, and
selected-clause typing for a monomorphic administrative fragment. It connects
typed result support to resource return and typed payload support to the actual
capture boundary. Callable payload support remains separate from effect-instance
identity. A structural close-plan typing judgment checks each scheduled
callback against its disposal effect contract. The
[substitution layer](direct-effects/one-shot/KERNEL.md#closed-substitution-and-local-preservation)
now preserves exact annotated types under closed substitution and derives
joint type, usage, and expression-support preservation for local reduction.
It also types the selected clause expression after operand substitution. The
[dispatch layer](direct-effects/one-shot/KERNEL.md#typed-control-transitions-and-ticket-bindings)
constructs actual capture, resume, and disposal-entry steps with matching
static/runtime ticket ports and state, expression typing and usage, support,
and ownership accounting under explicit local premises. The
[name-history layer](direct-effects/one-shot/KERNEL.md#name-history-across-execution)
preserves recursive name uniqueness alongside ownership and locally admitted
resource support through finite executions. It connects spent ticket bindings
to completion records and excludes later reuse, while recording fresh handler
activations separately. The
[retained-code layer](direct-effects/one-shot/KERNEL.md#typing-retained-code)
checks actual frame expressions, clauses, cleanup functions, and saved results.
It preserves their value types through typed capture construction, resumption,
disposal materialization, and every raw transition starting from a closed value.
The [entry layer](direct-effects/one-shot/KERNEL.md#deriving-administrative-entries)
derives pending-owner translation, lexical closure, and handler/cell/cleanup
annotations from typing. It constructs typed entries and preserves value types
under ordinary computation and the actual builtin integer-cell operations.
The [effect-interface layer](direct-effects/one-shot/KERNEL.md#effect-interfaces-across-the-ordered-stack)
connects retained code to ordered incoming/outward effect bounds and historical
continuation contracts. It proves the corresponding capture, resume, disposal,
entry, ordinary-computation, and closed-value cases, and that current requests
resolve on the active stack or belong to the outward bound. Live boundaries
currently require both effect contracts, and capture uses the same handler
residual for resume and disposal. The joint layer below combines those
interfaces with callback usage, support, ownership, and registry history.
Preservation of complete source-derived admission remains open.

The following are rule schemas for the capability checks. `K(Q,A;chi,d)` is a
static description of a restricted ticket, not a freely copyable function.
Changes to the authority state must also satisfy the surrounding control
judgment, including any outward operation made during resumption or disposal.

```sequent
family capability-typing:
  T-Resume :=
    Delta contains live k : K(Q,A;chi,d)
    v : Q
    chi permits resume
    residual interpretation and support d are available
    restoration has effects epsilon and outgoing authority Delta1
    ===>
    Gamma ; Delta ; Xi |- resume k v : A ! epsilon => Delta1

  T-Discard :=
    Delta contains live k : K(Q,A;chi,d)
    chi permits disposal
    closing k preserves outside and running completion
    checked close has effects epsilon_close and outgoing authority Delta1
    ===>
    Gamma ; Delta ; Xi |- discard k : Unit ! epsilon_close => Delta1
```

Each successful rule consumes the input ticket. Splitting replaces it with two
restricted tickets and checks both continuations of authority. A normally
returning clause has no unexplained local ticket. Pattern alternatives agree
on outgoing authority, or explicitly return a sum carrying the distinct states.

A handler discharges its body's exact target instance and includes all direct
clause effects in the result row. A same-instance request in a clause remains
an outward requirement. Exhaustiveness, operation parameter/result types, and
common handler result type follow current rules. Its additional obligation is
that every reachable request cut supports the clause's declared control use.

The [local demand layer](direct-effects/one-shot/KERNEL.md#scheduled-continuation-demand)
connects pathwise usage to runtime owner identities and decomposes/recomposes
usage through strict contexts. Alternative syntactic occurrences can represent
one scheduled consumption. The
[retained-control usage layer](direct-effects/one-shot/KERNEL.md#continuation-usage-across-retained-control)
now checks demand balance against owned tickets and active accessibility
throughout the control forest. It preserves that invariant through capture,
full-prefix restoration, structurally admitted disposal, and every raw
closed-value transition. The
[usage-execution layer](direct-effects/one-shot/KERNEL.md#usage-preservation-through-execution)
covers the remaining raw transitions and joins usage to ownership, resource
support, name history, and issued-ticket registry-domain correspondence over
the same admitted finite execution. Concrete cleanup capture/resumption and
resource-bearing disposal executions instantiate all premises. The
[joint layer](direct-effects/one-shot/KERNEL.md#joint-contracts-and-transition-preservation)
now records type/effect contracts and usage permissions in one runtime ticket
record, checks each facet independently, and preserves the complete invariant
for each transition family or constructs its typed annotations. A complete
resource-disposal execution carries the same registry through callback
application, cell read, and release; a negative example shows that effect typing
cannot grant a denied disposal permission. Closed annotated expressions also
initialize the invariant from independent checks. Source-derived admission of
all reached cuts and annotations, fresh instantiation, a universal admitted
execution theorem, progress, and Core correspondence remain open. This target
is the one-shot kernel; the other capability extensions require separate proofs
and later integration.

The [admission and progress layer](direct-effects/one-shot/KERNEL.md#derived-admission-and-progress-cases)
now derives release, focus, and ordinary-step access checks. Structural open
closing certificates supply actual plan existence and preserve interpretation
agreement under a shared current caller. Closed joint states supply their
outside interfaces. A checked administrative counterexample shows why plan
existence cannot follow from the six-field invariant alone: a dormant running
cleanup has no legal disposal plan. This does not establish a source-reachable
failure or inconsistency. General callable payloads remain admissible through
their actual outside type boundary; the stronger signature-support shortcut
is optional.

Value states now have a checked progress theorem: empty control or an actual
step preserving the joint invariant. Ready resumption also derives its live
boundary and steps with preservation. These results do not assume the desired
transition exists. Closed disposal also steps when a structural retained-control
judgment supplies certificates for live records that permit disposal. The proof
derives plan existence, compatibility, and a fresh close owner and preserves the
joint invariant. The
[prepared-execution layer](direct-effects/one-shot/KERNEL.md#preservation-of-prepared-captures)
now preserves retained certificates through every raw transition under an
explicit local certificate check for a newly captured ticket. Stronger value,
ready-resumption, and closed-disposal progress theorems preserve both the joint
invariant and retained readiness. Capture exposes its actual transition and
valid chosen contract unconditionally; only successor readiness depends on
the new certificate at that contract's effect bound.
The certificate judgment admits resume-only captures of running cleanup.
Source-derived readiness, its preservation, general progress, and Core
correspondence remain open.

The [fresh-instantiation counterexample](direct-effects/one-shot/KERNEL.md#fresh-instantiation-counterexample-and-core-judgment)
now demonstrates a non-value `Ready` state with no fresh named step after two
calls to the same resource-acquiring lambda in the uninstantiated syntax.
Current Core already specifies distinct activations per execution, and its
focused repeated-acquisition runtime test passes. The comparison judgment is
to repair the model's source/runtime instantiation, preserving bound metadata
and older closures, rather than change Core semantics or restrict repeated
calls. This is a diagnosed mismatch, not a completed correspondence theorem.

The [metadata instantiation foundation](direct-effects/one-shot/KERNEL.md#lexical-metadata-instantiation-foundation)
now distinguishes source resource binders from opaque runtime activation atoms.
It proves existence and uniqueness from lexical lookup availability, preservation
of older realized metadata under rebinding, transport of resource support, and
fresh-key preparation compatible with the ownership ledger. Aliases remain
possible. A checked unit-operand request selects the older exact handler across
a newer activation using only its retained effect metadata. This adds no second
computation calculus. Source-expression and closure integration, signature
transport, and Core's fallible preparation remain open; the administrative
repeated-call counterexample is not yet repaired by these metadata proofs.

The [scoped-code layer](direct-effects/one-shot/KERNEL.md#scoped-code-instantiation-and-substitution)
now traverses the same expression grammar while deferring each resource body's
local binder until acquisition. It proves exact free-name accounting, the
lexical coverage condition for closing, stability of resource-closed code, and
commutation with substitution of such code. A prepared acquisition resolves its
body's local name while preserving older inserted activations. These results
connect metadata instantiation to code binding. The operational layer below
now executes that representation; joint preservation and Core simulation
remain to be connected.

The [scoped execution layer](direct-effects/one-shot/KERNEL.md#scoped-execution-with-fresh-acquisitions)
now instantiates a resource body at each acquisition while retaining unallocated
templates in callable code. Every transition family preserves the ownership
ledger and resource-name closure, including code in dormant captures and
cleanup actions. The same lambda's resource template executes twice with
distinct completed activations; a generic fresh cell-read execution also
connects instantiated metadata and operands to actual builtin dispatch.
This repairs the diagnosed repeated-call behavior in the scoped model. It does
not transfer the administrative layer's full joint invariant or establish
general progress and Core correspondence. The following layer adds live support
and handler-name history; typing, usage, and source-derived disposal admission
remain separate integration obligations.

The [scoped naming and access layer](direct-effects/one-shot/KERNEL.md#scoped-naming-dependencies-and-live-support)
now connects lifetime name history and live support to resource-name closure
and ownership in the same execution. It preserves all four facets under explicit
local release, capture-payload, and structural disposal checks. Exited handler
activations cannot be reused, consumed tickets cannot become available again,
and closed admitted executions cannot retain completed resources. A fresh cell
read supplies concrete positive evidence; a name-resolved but dangling return
fails release admission. Deriving the local checks from source typing and
continuation capabilities remains open, as do general progress and Core simulation.

The [scoped usage connection](direct-effects/one-shot/KERNEL.md#scoped-structural-usage)
now reuses the structural one-shot checker while retaining the full sequencing
and ticket syntax. Resource instantiation leaves usage unchanged, ordinary
substitution preserves it, and actual evaluation contexts split and recompose
usage. Exact free-ticket lists and scheduled consumption connect this result to
runtime owner translation. The projection forgets resource metadata only for
usage checking; an explicit unresolved-reference example rules out treating it
as operational simulation.

The [scoped retained-control usage layer](direct-effects/one-shot/KERNEL.md#scoped-retained-control-and-execution-usage)
now preserves scheduled consumption and active ticket access through every
scoped transition, including fresh acquisition and materialized disposal.
One finite-execution theorem connects usage and registry history to ownership,
resource-name closure, lifetime names, and live support. Actual fresh cell and
capture/resume executions inhabit that result. Registry history does not
authenticate source permissions. Internal retirement is delegated by an owning
discard, separately from an inner ticket's explicit disposal flag, as formalized
in the retirement layer below. Universal source-admitted joint
preservation, general progress, and Core correspondence remain open.

The [scoped signature layer](direct-effects/one-shot/KERNEL.md#scoped-type-instantiation-and-signature-coherence)
now realizes full type metadata and finite user-operation descriptors while
keeping previously realized ports fixed. Its decidable coherence check accepts
exactly when one signature can respect all supplied entries, including aliases.
Coherent table extension preserves old lookups, but freshness alone does not
establish coherence. Descriptor consistency is distinct from authentication
against current effect declarations; complete authentication and joint scoped
type preservation remain open. Declaration-table permutation does not change the ordered
interpretation-stack semantics.

The [declaration-derived signature layer](direct-effects/one-shot/KERNEL.md#declaration-derived-resource-signatures)
now derives port determinacy and coherent table extension from a fixed
declaration registry for resource parameters. Exact positional arguments bind
the template's declared names; family and operation lookup determine both
ports. It rejects forged ports and the earlier same-key callable conflict
when its required argument is omitted. This models part of current Core's
declaration rule; registry extraction, general kinds and type arguments,
and the full correspondence theorem remain open.

The [generative scoped typing layer](direct-effects/one-shot/KERNEL.md#generative-scoped-expression-typing)
now types actual scoped expressions. Resource bodies check at every fresh
activation, with result and outward residual resources confined to the
preceding world. Typing derives resource closure, bounds value dependencies,
and decomposes and recomposes actual focus contexts. A typed resource entry
with a returned integer initializer has a fresh execution step, a typed opened
body, and a preserved ownership ledger. Historical name formation remains
separate from live access. The later scoped joint layer connects local
type/effect preservation to those checks. Derivation of the universal opening
premise from finite source checking remains open. Generic user operations also need declaration-based
signature lookup or coherent extension across fresh openings; a finite table
of exact instances alone cannot supply the universal rule. These results
establish bounded resource-entry progress, not general progress or simulation.

The [scoped substitution layer](direct-effects/one-shot/KERNEL.md#scoped-typed-substitution-and-ordinary-execution)
now preserves exact expression and clause types, including closure support,
under closed ordinary substitution. The resource case commutes substitution
with every fresh opening and preserves the replacement's older activation
atoms. Consequences type actual binding and beta successors and the selected
handler clause after operand substitution. Those substitution results keep
lexical readiness explicit; the next layer derives it for empty ordinary
environments. The following retained and effect layers connect these results
to stack interfaces; complete joint preservation remains open.

The [lexical readiness layer](direct-effects/one-shot/KERNEL.md#lexical-readiness-and-bounded-scoped-progress)
now derives closed runtime values and binding-suffix readiness from typing.
It constructs actual typed successors for value-form binding, application,
branching, and resource acquisition. Structural correspondence between static
and runtime ticket names makes pending translation total and supplies typed
retained frames at actual strict focus positions. This checks names, not
dynamic-owner existence, permissions, or ports. General progress still needs
the complete configuration invariant and its dispatch, continuation, and
cleanup cases; full source admission and Core simulation remain open.

The [scoped retained typing layer](direct-effects/one-shot/KERNEL.md#scoped-retained-typing-and-configuration-transitions)
now checks actual retained code and captured stacks. Exact capture, full-prefix
resumption, disposal materialization, all transitions from current values,
ordinary steps with value operands, and given strict focus positions preserve
or construct value-type composition.
Fresh resource entry extends typing through the retained world and preserves
its ownership ledger. A concrete cleanup trace applies the callback and
restores its saved integer, with every configuration typed. This layer still
keeps immediate rows existential: an explicit unhandled-request example shows
that consistent value types alone do not provide an interpreter. Connected
effect, ownership, capability, and source-admission judgments remain necessary
for general progress and Core correspondence.

The [scoped connected-effect layer](direct-effects/one-shot/KERNEL.md#scoped-entries-and-connected-request-progress)
now derives handler/cleanup entries and exact source/builtin selections, and
connects request rows through actual retained code and captured stacks.
Capture, full-prefix resumption, builtin operations, binding, beta reduction,
and closed-value transitions preserve connected typing. Relative progress for
a request with a value operand derives an actual typed step or an outward
observation with no local interpreter. The nested-handler execution reinstalls
the inner interpretation and reaches the outer effect in its resumed suffix.
The historical ticket-slot freshness premise and the conservative shared
resume/closing residual do not establish ownership freshness, disposal
readiness, or permission. The following layer adds scoped entry/disposal
interfaces; joint source admission and preservation, general progress, and
Core correspondence still require integration.

The [scoped structural-closing layer](direct-effects/one-shot/KERNEL.md#scoped-effect-entry-and-structural-closing-readiness)
now checks connected entry interfaces and fresh resource-world growth.
Structural readiness of the actual capture constructs a cleanup plan and
checks callback requests against their remaining suffix. At a supplied live
boundary, it derives a disposal step with a fresh close owner, connected
successor typing, and ownership preservation. An eleven-step callback/read/
release execution checks every configuration's value/effect interface.
Readiness and effect availability still do not imply interpreter agreement:
a checked example loses a source override during disposal and fails
`SameRequests`. The [scoped joint layer](direct-effects/one-shot/KERNEL.md#scoped-joint-invariants-and-derived-progress)
now joins the local effect constructions with ownership, naming, support,
usage, registry history, and resource closure. It derives value completion and
resumption steps, including lexical ticket resolution and the active boundary.
All four states of a fresh acquisition/read/release execution satisfy the joined
judgment. Capture/disposal access checks remain explicit; source establishment
and preservation of future readiness, general
admitted progress, and Core correspondence remain open.

The [scoped progress layer](direct-effects/one-shot/KERNEL.md#scoped-progress-for-every-expression-form)
now covers every expression form under structural prestate access and closing
checks. It derives a terminal value, an actually unmatched outward operation,
or a step preserving all joined invariants and every old ticket record. With
an empty outgoing row, only terminal or stepping outcomes remain. Closing
readiness is required only for disposal-authorized tickets; protected
resume-only captures remain admissible to that structural check. The theorem
does not assume successful execution, but its conclusion does not preserve the
readiness premises. Source establishment and preservation of those premises
and Core simulation remain separate obligations. Conditional retirement
authority is proved in the delegated-retirement layer below.

The [scoped readiness-preservation layer](direct-effects/one-shot/KERNEL.md#scoped-preservation-of-closing-readiness)
now preserves existing closing interfaces through every transition, with one
explicit structural obligation for a newly captured ticket. Non-request
progress preserves the stronger joined readiness judgment and the exact
registry. A source-prefix example shows why initial checks alone are insufficient:
granting disposal to a resume-only clause creates an impossible closing obligation
when it captures running cleanup. The same code preserves readiness under
resume-only rights. Current Core accepts the resume case and rejects actual
unsafe discard; its existing cleanup tests pass. This evidence calls for a
correct mapping of inferred continuation actions into the calculus, rather than
a Core semantic change. Source derivation of new-capture certificates, future
access checks, and simulation remain open.

The [least-action layer](direct-effects/one-shot/KERNEL.md#least-enclosing-continuation-actions)
now computes the least enclosing-ticket resume/dispose bound for the structural
usage checker. Necessity and repermission are proved with nested policy fixed;
value substitution and resource instantiation preserve the bound. This derives
the resume-only contract needed by the running-cleanup example. It does not
infer disposal safety. A checked binder-reuse example also shows why a general
source mapping must distinguish clause identities: joining requirements at a
shared administrative binder number can grant excess authority. That mapping,
new-capture certificates, future access checks, and Core
simulation remain open.

The [policy-synthesis layer](direct-effects/one-shot/KERNEL.md#synthesized-clause-action-policies)
now collects every contained clause's requirements and proves that its computed
policy is sufficient and pointwise least for an existing usage derivation.
Coherent keys give exact local action contracts; identical copies are allowed.
Instantiation preserves the policy exactly, while substitution preserves profile
membership and coherence under an explicit combined-profile premise. The
running-cleanup example now uses the entire source expression's computed policy
through actual capture. Execution must retain that source policy; the following
layer proves coverage across current and retained code. Extracting Core
identities and checking external callable inputs remain unproved, as do capture
safety, future access and simulation.

The [runtime provenance layer](direct-effects/one-shot/KERNEL.md#source-contract-provenance-through-execution)
now preserves clause-contract membership through every represented raw
transition and finite execution, including current code, retained frames,
cleanup callbacks and saved captures. A fixed coherent source policy therefore
gives exact local permissions at actual ticket allocation. Type-directed capture
records those permissions and leaves only the capture-specific closing
certificate conditional on disposal being required. This closes action-profile
transport for the current machine; external callable inputs need separate
compatibility checks. Authenticated Core identity mapping, closing safety,
future access and formal simulation remain unproved.

The [delegated-retirement layer](direct-effects/one-shot/KERNEL.md#delegated-internal-retirement)
now proves that a plan retires exactly its recursively owned live tickets and
that a retirement reached from empty control originates in a prior owning
discard. Initial usage, fresh allocation history and the existing per-step
access checks derive permission at that selected discard. Inner direct-dispose
permission is unnecessary; current Core tests accept owned resume-only clauses
closed by an outer discard. Fresh creation history and the ledger prevent
duplicate completion.
These are conditional execution results. Source establishment of access and
closing certificates, general progress and Core simulation remain open.

The [fixed-port counterexample](direct-effects/one-shot/KERNEL.md#fixed-declaration-ports-and-callable-support)
now proves a source-typing correspondence gap. The current annotation model
cannot type a closure retaining a freshly acquired resource when it is sent to
a handler still inside that resource's lifetime in the parameterless `Send`
example: all fresh openings share one operation input type, including its
retained-resource list. Lean proves the
failure for every fixed signature, while current Core runs the corresponding
fixture successfully and rejects moving the handler outside the owner. This
requires repairing the model, not restricting Core. Declared operation ports
must be separated from value support, and the affected support-preservation
proofs must be rebuilt before source admission and simulation can be claimed.

The [port/support repair](direct-effects/one-shot/KERNEL.md#declared-ports-and-independent-value-support)
now supplies separate declared-port typing and lexical value support for the
existing scoped grammar. All old typed terms preserve their declared ports;
the counterexample additionally types under one fixed `Send` signature at
every fresh opening. Its callable still retains the opened resource, and the
existing access judgment rejects the outside-owner ordering. Closed typed
substitution has been rebuilt through all expression and clause constructors,
with actual bind/beta and selected-clause consequences. Independent support
bounds survive the same parameter substitution, including a returned callable
wrapper. The runtime port layer below continues that migration; `Ready`/progress, source
support inference, closing safety and Core simulation remain open.

The [runtime port layer](direct-effects/one-shot/KERNEL.md#runtime-port-typing-and-capture-preservation)
now derives strict frames and lexical readiness and checks actual retained
code, historical ticket ports and recursively captured stacks. Exact capture,
full clause-prefix resumption, completion and disposal preserve that port
typing. Old retained typing erases into it on the same runtime objects. Capture
and resumption also preserve ownership and independently checked live support
for the same constructed event. Port equality does not recover old raw type
equality, and declared callable ports cannot justify resource release: an
explicit negative example is rejected by the separate access check.

The [ordered port/effect interfaces](direct-effects/one-shot/KERNEL.md#ordered-effect-interfaces-with-declared-ports)
now check the same actual forest against one historical record's declared ports
and resume/closing rows. Exact cuts preserve those interfaces, and full-prefix
resumption preserves connected typing together with ownership and independently
checked support. Lookup derives a local interpretation or outgoing allowance;
an outward observation additionally requires actual lookup failure. The safe
callable fixture has connected source, request, capture and resume states. A
negative example retains the unsafe-release rejection even with connected
typing.

The [connected capture and completion layer](direct-effects/one-shot/KERNEL.md#connected-capture-entry-and-structural-completion)
now constructs capture with its selected historical contract, proves actual
value-operand request progress, and preserves connected typing through ordinary
and closed-value transitions. Focus and handler/cleanup entry derive their
metadata; fresh resource entry preserves the ledger and connected typing in the
larger resource world. Structural closing readiness constructs the actual ordered
plan, with each callback checked against its remaining providers and closing
row. Materialized disposal preserves connected typing and has relative progress
at an explicitly ready live boundary. The callback disposal trace and adversarial
ordering/override cases use the new judgment. The following layer connects
joined validity and conditional progress; source-derived future access and
closing conditions, source-to-execution general progress and Core simulation
remain unproved. A checked
counterexample also combines connected typing with current live support while
rejecting release. The stronger value-progress theorem therefore needs separate,
preserved returned-value support bounds; adding a current-release premise does
not establish future source safety.

The [joined port invariant and progress layer](direct-effects/one-shot/KERNEL.md#joined-port-invariants-and-conditional-progress)
now links declared ports/effects and one-shot permissions through one historical
record, alongside ownership, names, live support, usage and resource-name closure.
Capture inserts one matching record; all local transition families preserve the
joined state. Conditional progress covers every current expression form under
actual access checks and structural closing interfaces, deriving an actual
successor or terminal/outward observation without assuming one. A stronger
counterexample satisfies the whole joined invariant while a value has no admitted
next step because release is unsafe. The theorem's access premise therefore
cannot be dropped. Source result-support and closing analysis, preservation of
future readiness and authenticated Core simulation remain required.

The [port readiness-preservation layer](direct-effects/one-shot/KERNEL.md#preserved-closing-readiness-with-declared-ports)
now preserves existing closing interfaces through every raw transition under
an explicit structural obligation for each new capture. Non-request progress
preserves the exact registry and joined readiness under current access checks.
Capture derives the successor and exposes its remaining closing condition at
the selected record's row. A ready value can still have no admitted next step:
closing readiness does not supply normal-return safety.

The [independent result-summary component](direct-effects/one-shot/KERNEL.md#independent-storage-and-result-summaries)
now separates a callable's stored captures from its result structure over the
same expression grammar. Capture-avoiding summary substitution and structural
analysis preserve parameter scope; an actual closed value's analyzed storage
matches its syntactic resource dependencies. A concrete retaining-closure
beta/bind execution returns an ordinary integer. Checked factory examples show
why analysis correspondence requires more than syntactic equality or current
support equality. Actual-value realization, general result soundness, source
closing analysis and authenticated Core simulation remain unproved. This is
analysis metadata, not another computation calculus or a change to current Core.

The [result-substitution correspondence layer](direct-effects/one-shot/KERNEL.md#substitution-correspondence-for-result-summaries)
now compares callable captures after every parameter substitution while
preserving result and application structure. Concrete closed-value substitution
expands code and clause dependencies exactly; analysis of that substitution
corresponds to analysis in the extended environment. General bind and beta
lemmas attach the metadata correspondence to their actual raw reducts. Beta
uses one explicit known-call unfolding. These results close substitution
transport for the current analyzer; they do not establish general returned-value
realization, control-sensitive result inference or Core simulation.

The [canonical return-bound layer](direct-effects/one-shot/KERNEL.md#canonical-return-bounds-and-the-unfolding-limit)
now derives exact actual support for typed first-order values. Unit return
therefore justifies release independently of unknown result metadata. Current
value progress can derive its access checks from a structural cell-answer
certificate, and the fixed-signature callable example completes an access-checked
seven-step execution with ownership conserved. Its retaining payload still
requires its own handler-boundary check. A further checked counterexample shows
that the current summary comparison cannot justify observations that unfold
captured applications. Higher-order inference needs a stronger comparison and
returned-value realization; this is an analysis requirement, not a Core change.

The [normalized capture/result layer](direct-effects/one-shot/KERNEL.md#normalized-capture-and-result-views)
now repairs that information loss. Capture normalization flattens stored values
while retaining complete result views inside application operands. The stronger
comparison survives substitution and explicit known-call unfolding, distinguishes
the captured-application counterexample, and again supports concrete closed-value
substitution plus actual bind/beta correspondence. Checked representation round
trips supply constructive result-view equality. These results preserve the
information needed for stronger inference; application-aware support observation,
precise returned-value realization and source-to-Core simulation remain unproved.

The [conservative normal-result theorem](direct-effects/one-shot/KERNEL.md#conservative-normal-result-soundness)
now connects the existing support observer to every actual raw machine
transition and finite execution. A finite source bound contains the actual
stored resource dependencies of a closed returned value when execution starts
and ends with an empty stack.
Branches include both alternatives; bindings can ignore an initializer's
returned support while the actual execution still evaluates it strictly.
Applications and control results remain unknown. This is partial correctness,
not termination, intermediate access safety, or resource liveness. The theorem
does not supply individual resource-return or operation-payload checks, and
does not realize the more precise normalized result views. Those admission
and inference obligations, general source progress and authenticated Core
correspondence remain open. The conservative analysis limit implies no change
to current Core.

The [resource-return invariant](direct-effects/one-shot/KERNEL.md#preserved-resource-return-obligations)
now carries individual return checks through active and recursively saved
control. Actual capture, full resumption, disposal and completion preserve
them; only newly allocated resources require local entry evidence. Existing
source typing supplies that evidence for first-order answers. Value progress
derives release checks and preserves both return evidence and the existing
joint or readiness invariant. Higher-order entry checking must account for the
freshly instantiated body: a checked counterexample shows that an unopened
template can hide the new resource's capture. This is an analysis obligation,
not a current Core defect. General source-derived acquisition, payload,
disposal and closing checks, precise result inference and Core correspondence
remain open.

The [finite source-bound construction](direct-effects/one-shot/KERNEL.md#finite-source-bounds-across-resource-opening)
now retains unresolved resource names and proves that inference commutes with
opening a resource binder. On resource-closed code it agrees with the runtime
observer. A finite Boolean check characterizes a sufficient source bound and
constructs the actual fresh-world entry event with its local return certificate,
including function-valued answers. World membership does not prove live
ownership, and this construction does not supply issuance-history freshness
or full access admission. It also exposes a precision gap: Core accepts closures
retaining copied integers, while this observer still treats the read result as
unknown. That gap calls for stronger model analysis, not a Core semantic change.
General source admission, precise operation/application/control results and
Core correspondence remain open.

The [template substitution result](direct-effects/one-shot/KERNEL.md#template-certificates-through-value-substitution)
now transports those local certificates through ordinary replacement by actual
closed values. Each replacement's stored support must fit its variable's
inferred bound. The construction commutes replacement with resource opening
and proves that the original finite template check remains successful after
replacement. Opening with an identity outside the supplied world leaves that
check unchanged; resource closure connects it to the opened body's runtime
support bound. This connects an actual strict bind to the following resource
entry, deriving that entry's return certificate. It uses conservative storage comparison,
not known-call unfolding, and does not infer a pending operation's result
from its eventual value. These are proofs over the proposed calculus's `Code`
grammar; they do not yet connect an Ash surface program or current compiler
Core to a fully admitted execution. General calculus admission and Core
correspondence remain required.

The [continuation-input construction](direct-effects/one-shot/KERNEL.md#declared-input-bounds-through-capture-and-resumption)
now checks saved return obligations at their declared input bounds. First-order
ports bound actual stored support; callable ports remain unknown. Typed capture
derives the saved annotation from the operation signature, and typed resumption
uses the same historical ticket lookup to check the actual supplied value.
Both construct actual successors with typing and return checks preserved.
Every raw transition preserves the revised return invariant under current
typing and local entry evidence, and value progress retains it alongside
joint or readiness validity. A typed capture/resume example preserves a scope
returning a closure of a copied integer; an untyped raw resumption with a
handle demonstrates why input checking is necessary. The positive example
uses a generic integer-producing operation and a declared input bound, not
initial-term inference or builtin cell-read admission. Those analysis and
admission connections, and Core correspondence, remain open. The analogous
Ash fixture returns `42 : Int` through current Core; that observed agreement
does not substitute for the missing translation and simulation proofs.

The [signature-aware result analysis](direct-effects/one-shot/KERNEL.md#signature-aware-operation-result-analysis)
now propagates declared operation-result bounds through ordinary bindings and
proves closed-value storage, substitution and context correspondence. The
opened copied-read closure receives an empty bound, while a closure retaining
the handle to read later keeps that dependency. The analogous builtin-read
Ash fixture returns `41 : Int` through current Core. A checked counterexample shows that finite request bounds require the raw
capture's input annotation to agree with the operation signature.
[Signature-aware return-check preservation](direct-effects/one-shot/KERNEL.md#signature-aware-return-check-preservation)
now covers every actual raw transition under current typing, fixed builtin
signatures, explicit capture agreement and a local new-cell return certificate.
The typed capture constructor derives the saved bound from the current request
check and constructs the same event's agreement, typing and return checks.
Current-value progress preserves these checks with existing joint validity or
readiness. The pending integer-producing request now passes the new invariant;
negative examples reject wrong ports even when their storage bounds coincide.
These are local return-check and current-value progress results.

[Declaration-derived template entry](direct-effects/one-shot/KERNEL.md#declaration-derived-template-entry)
now supplies the new-cell return certificate before allocation in the existing
resource-parameter declaration fragment. It reuses ordered parameters and
validated operation templates, proves that declared result bounds commute with
opening, and compiles the matching runtime signature with fixed cell operations.
The finite template checker agrees with the runtime observer after opening.
Resource-entry progress uses the actual event's issuance freshness and preserves
joint validity and return checks for the same named step. A copied-read closure
has a concrete typed initial configuration exercising this result; a declared
reference result retains its resource dependency and rejects escape of its owner.
These results do not authenticate all Core declaration forms or prove complete
execution of that example. [Ordinary closed-value substitution](direct-effects/one-shot/KERNEL.md#declaration-template-substitution)
now preserves the same finite checker under structural binding bounds. An actual
named bind followed by fresh resource entry preserves joint validity and return
checks at both states, with ordinary lexical premises derived from current
typing. A concrete typed initial term exercises both events. This does not
infer arbitrary pending computation results or establish closing readiness,
nested-template admission, general calculus admission or formal Core
correspondence.

[Symbolic template worlds](direct-effects/one-shot/KERNEL.md#symbolic-template-worlds-and-shadowing)
now transport those checks through lexical opening. Saved outer support is
resolved before an inner binder masks its body environment, preserving the
distinction between an outer alias and a direct inner reference that share a
binder numeral. Realized symbolic worlds may alias resources and form a subset
of the issued world. The resulting local entry theorem preserves joint validity
and return checks; actual lexical-value bounds remain separate premises.
Examples include a checked outer-retaining value bound before raw inner entry.
Deriving this metadata recursively from initial calculus terms and proving
whole nested executions remain open.

[Generative result derivations](direct-effects/one-shot/KERNEL.md#generative-result-derivations)
now give nested resource expressions a stable outward bound by checking their
bodies at every fresh opening. Strict-child derivations prevent an ignored
unsafe initializer from being hidden by a finite final-result check. Certified
substitution preserves the recursive judgment. A current value bind derives its
replacement bound from the initializer's derivation and preserves joint validity
while retaining the justified analysis environment. A consecutive cell-frame
certificate retains the bound through actual entry and return, and a nested
closure example completes both owners. Its Core fixture returns `17 : Int`;
this exposes an old observer precision limitation rather than a Core defect.
The result judgment remains separate from typing and latent-body safety.
[Ordinary frames and saved captures](direct-effects/one-shot/KERNEL.md#generative-results-through-frames-and-captures)
now carry those bounds with each frame's saved analysis environment. Actual
capture retains its forest certificate; resumption checks the actual input port
under the same compiled declarations and requires an explicit match between
the saved output and waiting prefix input bounds. An eight-step nested-resource
example preserves these certificates through both ordinary binds, and its Core
fixture also returns `17 : Int`. This is a local result-support component:
clause results, callable input support, request payloads, cleanup certificates,
full initial-term admission, whole-execution progress and Core simulation remain
open. Multishot, escaping continuations and suspension remain separate targets.

[The current progress join](direct-effects/one-shot/KERNEL.md#generative-results-joined-with-current-progress)
now derives current access checks from these result certificates and preserves
the result certificates with joint validity and closing interfaces on the same
normal or builtin step.
It uses actual issued-history freshness and an explicit boundary excluding
ready requests selected by source handlers. A checked counterexample shows
that plugging can expose such a request while preserving the result certificate;
the boundary is not a preserved initial-program property. Clause and payload
admission, callable support, cleanup integration, whole-execution progress and
Core correspondence therefore remain required one-shot work.

[Lexical clause-result checks](direct-effects/one-shot/KERNEL.md#lexical-continuation-results-and-clause-checking)
now distinguish continuation input and answer support without adding computation
syntax. Handler bodies and clauses share an outward bound, and each clause
receives its own lexical ticket contract. Substitution preserves these checks;
actual capture binds the operand using the same compiled declaration as typing,
and actual resume uses the checked operand with matching saved/prefix bounds.
A nested-clause program has independent result, type and one-shot checks, plus
a thirteen-step execution and ledger ending at `17`, matching its Core fixture.
Result information does not grant repeated continuation use.

[Retained result contracts](direct-effects/one-shot/KERNEL.md#retained-continuation-result-contracts)
now carry these checks through actual contexts and handlers. Historical result
records connect each lexical scope and saved capture to the same runtime owner.
Capture derives the selected clauses and result interfaces from the ordered
stack; resume derives saved-output/prefix-input compatibility from one shared
record. All fourteen states of the nested-clause run have result certificates.
[Joint continuation records](direct-effects/one-shot/KERNEL.md#joint-continuation-records-and-ownership)
now connect finite result inputs to the same historical owner record as type,
effect and one-shot usage checks. Capture and resume preserve the combined
invariant on the same actual event, and issued history supplies result-registry
freshness. A five-step handler execution reaches `17` with the combined checks
at every state; the record survives consumption but cannot authorize another
resume. Arguments with empty finite support derive their payload access check.
[Declared payload boundaries](direct-effects/one-shot/KERNEL.md#declared-payloads-across-capture-boundaries)
now derive capture access for the represented finite-port declarations,
including nonempty argument support. Actual typed operand resources fit the
requested effect instance, whose selected handler is supported by the outside
tail. A six-step combined execution passes an outer cell handle while capturing
an inner cell, resumes, and releases both cells; its starting state already owns
them. Callable payload contracts, disposal/cleanup and closing interfaces,
complete admission, whole-execution progress and Core simulation remain open.

[Evaluated request and resume progress](direct-effects/one-shot/KERNEL.md#evaluated-request-and-resume-progress)
now derives the actual next event from the combined invariant. Requests follow
ordered resolution to a builtin, source handler, or permitted outward row;
resumes derive their live boundary from usage. The successor retains result
support and the joint ownership invariant, with no separate access or closing
premise. This theorem covers evaluated requests and resumes; the following
construction joins the other current forms admitted by the result rules.

[Repeatable progress](direct-effects/one-shot/KERNEL.md#repeatable-progress-for-the-current-result-fragment)
now connects every current form admitted by the structural result rules,
including sequencing, branches, handlers and fresh cell entry. A single combined
invariant constructs a successor with that invariant, an ordinary terminal, or
an explicitly allowed outward request. For closed computations, any finite
step budget yields a certified prefix or earlier termination. Terminal owners
are completed exactly once and returned resource support fits the admitted
bound. These results do not yet admit callable application or disposal/cleanup,
or prove safety for arbitrary raw annotation choices; the full one-shot
admission and universal safety target remains open.

[Capture annotation checking](direct-effects/one-shot/KERNEL.md#checking-the-supplied-capture-annotation)
now proves preservation for every supplied capture in the finite-port fragment
whose continuation input agrees with the declared operation result. A checked
model counterexample shows that raw capture can preserve ownership and access
while a wrong input annotation makes its successor untypable. The local
declaration check excludes that case without assuming successor validity.
This is an obligation in the proof model, not evidence of a Core defect.

[Entry annotation checking](direct-effects/one-shot/KERNEL.md#checking-supplied-entry-annotations)
now supplies structural checks for focus frames, handler answers and resource
answers. Current typing constructs these annotations, while every supplied
checked entry with fresh identities preserves the same combined invariant.
The premises inspect current code and existing continuation interfaces;
successor typing and validity are derived.

[Finite checked-run preservation](direct-effects/one-shot/KERNEL.md#supplied-capture-records-and-finite-checked-runs)
now combines these events with annotation-free execution and supplied capture
records. Local checks use the same record at each shared endpoint. The run
judgment contains no intermediate-validity premises; one initial combined
invariant derives all of them along every supplied finite checked run. Closed
endpoints have ordinary progress, and terminal endpoints account for issued
owners and returned resource support.

[Checked endpoint progress](direct-effects/one-shot/KERNEL.md#progress-extending-the-checked-run)
now constructs the next checked step from the current invariant, including its
fresh identities and annotations. Every supplied checked run from an initial
calculus term satisfying the four structural judgments preserves the combined
invariant and either finishes or extends by another checked step. Intermediate
validity and next-step witnesses are derived. This closes checked-step coverage
for the current fragment; callable application, disposal/cleanup and complete
executable admission remain open.
Core correspondence remains a status assessment; alignment is outside scope.

[Callable body contracts](direct-effects/one-shot/KERNEL.md#callable-body-contracts-and-the-actual-beta-step)
now separate a closure's captured storage from its argument storage and the
result bound of its actual lambda body. World growth and closed substitution
preserve the contracts. Current joint validity, a checked body, a bounded value
argument and the retained result interface construct the exact beta event with
combined successor validity. Two storage-empty factories show why the returned
closure's support cannot be inferred from the factory's captures. This is a
local application bridge: callable behavior still needs transport through
general values and saved control, and the body judgment still excludes nested
application and disposal/cleanup. It does not extend the whole-run theorem yet.

[Full callable-contract substitution](direct-effects/one-shot/KERNEL.md#callable-contracts-through-binding-and-substitution)
now preserves argument and result behavior through ordinary variables, binding,
higher-order arguments and returned functions in the same expression syntax.
Only physical capture checks project contracts to storage. The structural
judgment includes nested application, handlers, operations, resumption and
generative resources, and substitution preserves it through clause binders and
fresh opening. Actual beta and value-binding events preserve these expression
contracts. This is not yet combined machine preservation: saved frames and
historical continuation records still require integration with full contracts.
Callable operation ports, disposal/cleanup and executable admission remain open.

[Retained callable contracts](direct-effects/one-shot/KERNEL.md#callable-contracts-on-retained-control)
now survive saved evaluation frames, exact stack composition, actual capture
and full-prefix resumption. The selected handler supplies its complete answer
contract; the declared finite output supplies the capture's input. A checked
trace resumes under pending clause binding, returns a function and invokes it
outside the handler to obtain `17`. These are contract-component results on
the existing raw machine. That component leaves its contract world and records
abstract; the joined layer below connects them to issued history, ownership,
ports/effects and one-shot authority. The subsequent progress layer extends
finite checked-run safety to callable contracts; disposal/cleanup integration
remains open.

[Joined callable preservation](direct-effects/one-shot/KERNEL.md#joining-callable-contracts-to-the-machine-invariant)
now connects full callable contracts to actual issued-resource history and one
shared continuation record. Capture, resumption, beta/binding, value returns
and annotation-checked entry preserve contracts together with ownership,
support, ports/effects, usage and names on the same event. Current retained
clauses and declaration typing derive capture payload access. A closed program
establishes the combined invariant, captures a callable answer, resumes under
pending clause work and invokes the returned function to obtain `17`, consuming
its single issued ticket. The following result extends progress and finite-run
preservation; callable operation contracts, disposal/cleanup and executable
admission remain open.

[Callable progress and checked-run safety](direct-effects/one-shot/KERNEL.md#progress-and-checked-runs-with-callable-contracts)
now follow from the combined invariant. Every admitted closed nonterminal state
constructs a checked next event, including application and callable-answer
capture. Supplied capture records are authenticated against before-state
interfaces; runs retain exact registry updates and assume no intermediate
validity. Every finite checked run from the four initial structural judgments
preserves the invariant and either finishes or admits a checked extension.
Terminal runs account for all issued owners and bound actual result storage.
This remains the calculus fragment with finite operation-result storage bounds,
finite handled-clause input bounds and no disposal/cleanup. Executable admission and general Core correspondence are
unproved; Core alignment is outside the work.

[Cleanup and disposal result preservation](direct-effects/one-shot/KERNEL.md#cleanup-and-disposal-with-full-result-contracts)
now covers structural expression admission, substitution, armed/running
cleanup, generated closing control and the full saved result contract. Local
joined proofs connect those contracts to the same ownership, usage, support,
port/effect and history checks. A checked initial program runs cleanup and
invokes its returned function to obtain `17`. A separate raw disposal trace
closes an armed callback and a resource before returning a callable; it is not
a joined source-admission proof. Disposal still requires independent plan,
typing, access and freshness evidence. Deriving safe closing admission for each
new capture and extending finite checked-run safety remain open. Result
contracts alone do not establish callback `Unit → Unit` types or disposal
permission.

The [hereditary request-capture join](direct-effects/one-shot/KERNEL.md#request-capture-from-one-checked-source-state)
now derives the selected payload, clause, capability and effect evidence from
one checked request state. Existing protection classification and capture proofs
supply preserved capture for protected cuts without an extra closing certificate.
For unprotected cuts, outside-owner restrictions, callback compatibility and
closing-effect bounds remain source-admission obligations. The general
initial-source theorem remains open.

The [capture-sensitive owner check](direct-effects/one-shot/KERNEL.md#capture-sensitive-outside-owner-checking)
now connects the existing internal-use checker to a selected handler capability.
It rejects disposal that skips an outside owner's pending work and permits the
ownership check when a larger capture includes that owner. Its composition law
checks both segments against the combined owned region. Ordinary effect/protection
checking does not imply this check; source summaries still need to establish it
for possible future captures.

The [ordered owner-use summary](direct-effects/one-shot/KERNEL.md#ordered-owner-use-summaries)
now preserves the existing interpretation selection and records the exact
captured owners and pending work. Existing capture preservation consumes its
check, and existing source focusing derives a pending-use entry from the
syntactic evaluation context. Deriving and preserving the required checks
through calls and future captures remains open.

The [source grouping refinement](direct-effects/one-shot/KERNEL.md#source-grouping-is-lost-by-flattening)
now derives explicit grouping from source constructors while reusing the
existing effect evaluator and owner-phase proof. Two concrete source nestings
produce identical flattened requirements but different ownership decisions at
actual handler cuts. The new structural relation rejects swapping their
groupings. This establishes why the old requirement index needs retained source
information; latent callable expansion and preserved source admission remain
open.

The [callable grouping and selected-table extension](direct-effects/one-shot/KERNEL.md#callable-grouping-and-selected-clause-tables)
now retains grouped bodies through existing callable conversion and closed
substitution. Actual argument instantiation exposes the body while preserving
its established effect evaluation. Source sites also retain their ordered
clause tables and select the actual operation capability for the owner check.
Preservation of the owner and closing checks throughout execution remains open.

The [caller-owner composition theorem](direct-effects/one-shot/KERNEL.md#locally-closed-prefixes-and-caller-owner-checks)
now shows that a locally closed callee prefix leaves an outward request's
caller owner check unchanged. It derives separation from existing structural
usage and unique ownership, then reuses the capture-composition proof. The
function-execution invariant that supplies this local interface is still open;
an empty latent effect row alone does not supply it.

The [source-owner closure projection](direct-effects/one-shot/KERNEL.md#source-entry-and-local-owner-closure)
now derives initial usage from a body typed with continuation scope `none`.
The established checked finite-run theorem supplies its later closed local
interface and hence the caller owner-check equality. Existing full resumption
preservation and value-scope transport now also reconstruct local ownership
usage when the outside caller resumes with a value. The strengthened existing
finite-run theorem supplies full usage at that resume and preservation of old
ticket registrations through an arbitrary access-checked caller run.
[Saved capture identity](direct-effects/one-shot/KERNEL.md#saved-capture-identity-through-caller-execution)
now derives the endpoint's local-prefix decomposition from the original ticket,
allocation freshness and existing capture uniqueness. Deriving the run's access
checks from source remains part of initial-source admission.

The [hereditary callback connection](direct-effects/one-shot/KERNEL.md#hereditary-callbacks-at-their-closing-positions)
now checks the actual closing footprint against the surviving interpretations
and a combined budget, then derives the callback's substituted source body and
requirement check at its protected closing position. This uses existing
retirement, substitution and outward-evaluation proofs. Initial-source
admission of these concrete checks remains open.

The [non-disposing capture theorem](direct-effects/one-shot/KERNEL.md#capture-without-disposal-admission)
now covers a selected clause that denies disposal even when a raw closing plan
exists and fails admission. Existing allocation, clause certificates,
substitution and ownership accounting construct its checked successor. A
checked source regression distinguishes capture from permission to run cleanup.
Disposal-enabled source admission and the combined initial-source theorem
remain open.

The [actual capture-budget connection](direct-effects/one-shot/KERNEL.md#checking-the-actual-capture-budget)
now obtains the resumption row from the source cut before allocation. Successful
finite checking against the exported operation row plus that resumption row
constructs the checked successor directly. It reuses the existing allocation
and capture proofs. Structural disposal success and source-wide admission of
these checks remain open obligations.

The [hereditary resource-return connection](direct-effects/one-shot/KERNEL.md#hereditary-source-and-resource-return-admission)
now reuses the finite template-support check to construct resource entry with
both source and return evidence. Preserved return bounds supply actual value
release checks. The retaining-own-resource example also has hereditary source
typing, so its rejected support check remains necessary for initial-source
admission. The existing template-substitution theorem now also preserves that
support check across a source bind when the actual value passes a finite
captured-resource check. An alias example completes bind, acquisition and
release with hereditary source evidence. Deriving these checks for arbitrary
source bindings remains open. No product Core or resource semantics changes
follow from this proof connection.

The [structural completion-contract connection](direct-effects/one-shot/KERNEL.md#hereditary-source-with-structural-completion-contracts)
now reuses full higher-order result contracts, including their existing cleanup
and disposal rules, with hereditary source states. It covers bind, beta,
resource entry and release, resumption and disposal recomposition. An application
returning a resource-retaining function is admitted when its structural result
bound excludes the inner resource, even when finite template inference is
unknown. The actual source-capture successor now also preserves the structural
result contract under the same fresh owner, with the operation's input-bound
evidence retained. Both capture paths now allocate the existing shared runtime
record, proving full continuation port agreement and storing the actual clause's
permissions. The disposing path preserves the actual closing export and its
combined budget when the structural disposal and finite closing checks succeed.
The allocation proofs already contained the required input equality; their
strengthened interfaces retain it, and one shared record construction serves
both paths. Structural source and result checks now also establish the full
runtime invariant at the initial empty machine, with a finite check excluding
unissued resource references. The [combined execution invariant](direct-effects/one-shot/KERNEL.md#execution-with-structural-effect-checking)
retains actual source/effect checking alongside the existing runtime ownership,
support, usage and result evidence. Non-disposing capture derives fresh
allocation and payload access and preserves all those facets; resumption
preserves them through recomposition. This uses the source's checked requirement
tree directly and does not assume its erasure to the older pending-stack effect
annotation. Admission of disposing captures, remaining transition coverage and
initial-source execution induction remain open. The invariant now also survives
all returned-value transitions, ordinary computation, focus and resource,
cleanup and handler installation. Resource-release checks and fresh allocation
are derived from current structural contracts and histories. Cell read/write
now preserve this invariant too, including through cleanup frames. Closed
request checking derives the physical builtin step or nearest source-handler
cut. Disposal now preserves the combined invariant using an earlier structural
closing certificate and a successful current footprint check, after an
arbitrary checked caller execution. Existing capture identity and current
support supply the saved plan's current resource-access evidence. Current source
checking and runtime name history now derive the actual cleanup footprint's
successful check and physical request resolution at disposal. The connection
reuses existing template evaluation, retirement separation and ownership traces.
The historical certificate still needs to be established at permitted captures
and connected to its declared-request interface. A checked regression reuses
the pure-callback example to show why an accepted source footprint alone cannot
supply structural closing compatibility: conservative request annotations may
mention an interpretation that closing removes. A stronger
[current-state counterexample](direct-effects/one-shot/KERNEL.md#current-state-disposal-admission-gap)
now satisfies every field of the combined `Valid` invariant while admitting no
access-checked disposal step. Its raw disposal step does exist; no execution
from an admitted initial program to this state is claimed. This proves that
`Valid` alone cannot support the intended progress theorem. The existing scoped
declared-request judgment rejects the state and, together with a retained
structural closing certificate, supplies a checked local disposal connection.
The [retained closing-invariant connection](direct-effects/one-shot/KERNEL.md#retained-structural-closing-invariant)
now carries concrete closing certificates and scoped declared-request typing
alongside the current invariant. It constructs the initial state and preserves
the strengthened state through disposal, resumption and returned-value
transitions. Old certificates survive every raw transition by the existing
capture-provenance theorem. An independently checked action registry now retains
the selected clause's least enclosing requirements through every transition
with the existing usage checks, while runtime permissions and nested-clause policy remain unchanged. Certificate
obligations follow those action requirements: a resume-only selected clause
needs no closing certificate merely because its policy also permits disposal.
The retained effect-interface judgment now follows the same action bounds:
a boundary needs its saved executable interface only for resumption and its
closing interface only for disposal. A checked source declaration and local
resumption regression show that the older unconditional interface judgment
rejects an unused closing interface unnecessarily. The replacement reuses
expression, frame, value, port and plan proofs, with structural transport for
the changed live-boundary rule. The main strengthened-state proofs now use it
and still exclude the disposal counterexample. Disposing captures still need
source-derived certificates, and capture must establish the interfaces its
selected actions actually require. Complete source establishment and capture
integration remain open. The source footprint judgment cannot replace them. A source-handler cut still needs
capability-specific capture admission. The
builtin result transport extends the existing frame induction for completion
frames; the selection, disposal, source and runtime connections reuse existing
lemmas.

The [deterministic interface-progress connection](direct-effects/one-shot/KERNEL.md#deterministic-computation-and-entry-annotations)
now retains the strengthened invariant through ready bind, beta reduction,
branches and builtin cell read/write, reusing the existing source/runtime steps.
Request selection preserves that invariant for builtins or identifies the nearest
handler cut still requiring capture admission. Its exact cut decomposition
also exposes the captured and surviving interfaces needed for capture admission.
An entry regression distinguishes raw metadata choice from a compatible typed
choice: the same pure cleanup code permits both a request annotation unsupported
by its caller and an empty annotation with a connected successor. Progress can
choose the latter. The remaining entry proofs must retain source and interface
evidence for that same choice; arbitrary raw entry preservation is too strong.

The [current-form and capture-retention connection](direct-effects/one-shot/KERNEL.md#current-form-classification-and-source-capture-retention)
now derives general resumption progress from current usage and classifies every
strengthened state as terminal, able to take a preserving step, or one of the
three remaining entry/capture forms. That explicit last branch prevents treating
classification as full progress. At non-disposing capture, the selected source
declaration now supplies the fresh owner's action guard; existing usage,
ownership and capture-provenance proofs preserve all older closing certificates.
The new owner needs no certificate, independently of broader runtime permissions.
The source/runtime and certificate proofs now describe the same access-checked
successor and coherent record. Capture still needs that successor's effect
interfaces. Disposing captures still require source-derived closing evidence.
The [installation connection](direct-effects/one-shot/KERNEL.md#resource-and-handler-installation)
now preserves the strengthened state through resource and handler entry. Existing
stack annotations determine the same result port for the source-chosen frame
and independent effect proof. The classification accounts for the actual
handler-table update and leaves focus, cleanup entry and capture unresolved.

The [shared source-annotation connection](direct-effects/one-shot/KERNEL.md#shared-source-annotations-for-entry)
now uses the actual current source derivation's allowed effect list as the caller
interface. The original initial-source premises establish this structural
witness, and source-directed focus and cleanup entries preserve it for the
same chosen frame. Existing decomposition and evaluation proofs supply both
entries. The `Run` invariant now retains that witness with runtime validity,
independent action history and closing certificates. The same initial-source
premises establish it; access-checked focus, cleanup entry and ready computation
preserve it by reusing existing runtime, substitution and ownership proofs.
The existing value-summary transport now recovers the shared witness at values,
connecting resumption, disposal, builtins and value-to-value steps to `Run`.
Callback start also preserves `Run`, retaining the callback's source-selected
request annotation and reusing the existing running-frame and runtime proofs.
Resource and handler installation now also preserve `Run`: the opened body
retains its bound by the new cell and caller, while handler installation keeps
one residual row across the body, declarations and installed frame. Both use
the same source-chosen fresh identity for the runtime step. Disposal still
requires the certificate retained at capture. Context plugging and capture
need further shared-witness preservation proofs.

The [structural stored-segment refinement](direct-effects/one-shot/KERNEL.md#structural-source-and-interpretation-segments)
now keeps each plain context's source annotation with its caller interface and
each handler's declarations with its residual row. Initial source establishes
the judgment, focus stores it, and plugging preserves it using the existing
context and value proofs. Actual focus and plug steps preserve the corresponding
runtime invariant. The [preservation connections](direct-effects/one-shot/KERNEL.md#preserving-the-structural-segment)
now retain this same invariant through ordinary computation, all returned-value
forms, and resource, handler and cleanup installation. One structural transport
proof covers world, contract, action and handler-table changes. Resumption now
retains the exact saved derivation selected by the independent resume capability
and consumes one owner. Builtin cell operations retain that same invariant and
reduce the requirement row. Disposal and capture still need the stronger segment connection;
source admission must also establish disposal certificates at capture.
The [source-derived capture interfaces](direct-effects/one-shot/KERNEL.md#source-derived-capture-interfaces)
now revise the experimental offer rule: a used resume or disposal bound equals
the declaring handler's residual row; unused bounds remain independent. The
actual cut retains that shared row on the capture and caller, and the selected
clause supplies compatible interfaces for a concrete live boundary. Joining
that boundary to the complete source/store/runtime capture transition remains
open, as does source-derived disposal admission. Core correspondence follows
the proof target and does not require retaining inadequate experimental source
judgments. Current Core and normative Ash semantics are unchanged by this
experiment.

The [closing-route separation](direct-effects/one-shot/KERNEL.md#closing-requires-interpretation-agreement)
now has both shared source checking and a connected normal interface. Its plan
is effect-typed with the complete callback row, yet no outward row can preserve
the callback's selected local handler after the plan removes it. Widening the
closing row therefore cannot repair that fixed capture. This reuses the pure
callback with a conservative annotation; it neither proves initial reachability
nor rules out choosing a compatible annotation at source entry. Its selected
clause only resumes. General progress and source admission of disposing captures
remain open.

### What independent checking means

The judgments are separate but communicate constraints:

1. Value/row checking establishes types and exact requirements.
2. Clause checking infers or verifies which actions it uses on its ticket.
3. Capture checking establishes that those actions are admissible for every
   segment that can reach that interpretation.
4. Completion and support checking establish that resulting ownership transfers,
   closing positions, and retained access remain valid.

An exported function cannot hide control-sensitive requirements behind a bare
effect row. It needs a qualified summary relating operation behavior to retained
authority, or checking must specialize it at each admissible installation.
The syntax, inference, and separate-compilation representation of these
summaries remain open. `CompatibleCuts` is a named proof obligation with the
structural cases above, not a claimed complete local inference rule.

## Worked mixed-handler derivations

The examples below use the administrative syntax and ordinary integer
primitives. They are design examples, not current executable Ash programs.
All providers have an `Int` handler result in the first two examples.

### Forwarding and work after resumption

Suppose an outer provider handles `E.ask` by `resume k 10`. The inner provider's
clause is:

```text
ask x with k =>
    let y = perform E.ask x;
    let z = resume k (y + 1);
    z + 100
```

Evaluate `handle (handle (let a = perform E.ask (); a * 2) with inner) with outer`.

1. The inner request captures `[B(a,a*2), H_inner]`.
2. Its clause forwards outside `H_inner`. The outer request captures the
   inner clause's pending `y` binding and its live clause group, through
   `H_outer`.
3. The outer provider resumes once with `10`, restoring that clause group.
4. The inner clause resumes its original capture with `11`. Its body produces
   `22`, which returns to the binding for `z` in the clause.
5. The clause returns `122`.

This is a derivation of nesting and forwarding using one binding rule. If the
outer provider attempted to split at step 2, the live inner ticket would also
need splitting permission. Its one-shot declaration blocks that operation.

### Multi-shot outside a one-shot interpretation

Let `Coin.pick : Unit -> Bool`. Its provider uses:

```text
pick ignored with k =>
    split k as left,right;
    let a = resume left true;
    let b = resume right false;
    a + b
```

Let `Ask.read : Unit -> Int` be interpreted by `resume k 10`. Evaluate:

```text
handle (
    handle (
        let b = perform Coin.pick ();
        let n = perform Ask.read ();
        if b then n else n + 1
    ) with ask_once
) with coin_twice
```

The `Coin` cut contains the pending suffix and the `Ask` interpretation. The
`Ask` provider has an unrestricted environment, and there is no live `Ask`
ticket yet. Splitting can therefore produce two handler activations. Each
branch later creates and resumes its own one-shot `Ask` ticket. Results are
`10` and `11`, and the enclosing clause returns `21`.

Thus a one-shot clause contract does not prohibit repeated installation of
reusable provider code. Conversely, capturing an already live one-shot ticket,
as in the preceding example, does prohibit duplicating that ticket.

### State placement and replay

Use a suffix which increments a cell initially containing zero and returns its
new value. The choice prefix is evaluated once; only the captured suffix repeats.

| Placement at choice capture | Ownership interpretation | Branch results |
| --- | --- | --- |
| Cell owner outside the choice boundary | Shared sequential access to one live cell | `1`, then `2` |
| Cell owner inside the captured segment | Default unique-owner rule | Split rejected |
| Cell owner inside, with certified fresh snapshot splitting | Two cells copied from zero before either branch runs | `1`, then `1` |

These are different specified behaviors. Moving a resource boundary through
the capture point changes the interpretation and is not ordinary reassociation.
Even a shared external owner can reject repetition if its protocol admits only
one transition; copying an access handle does not prove protocol replay safety.

### Disposal and the exact interpreter

Capture an armed cleanup action whose required logging interpretation lies
inside the cut. Discard does not reinstall that interpretation. The close is
rejected unless the action has an admissible surviving interpretation with the
required selection relationship. A same-signature or same-instance fallback
does not by itself prove that an overridden interpretation may be substituted.

If an enclosing cell remains available to an inner cleanup at its closing
position, the cleanup can use it and the cell closes afterward. If the cleanup
has already started, neither its invocation nor the unfinished close can be
discarded. These are current constraints retained by the proposed calculus.

## Provision and resource composition

Provision establishment is a typed protocol. Success produces a fresh identity
`a`, access value `v`, interpretation `p_a`, and obligation package `o`. Its
successful entry installs ownership outside interpretation:

```text
O(a,P) :: K                         owns establishment's completion
H(h,E<a>,p_a) :: O(a,P) :: K        additionally interprets its body's requests
```

The top frame is shown first. A request to that interpretation captures `H`,
but leaves its owner outside; the provider clause can access its own state.
An outward request may capture both. This decomposition is a model of roles;
it does not require splitting current fused builtin frames in the implementation.

Normal return through `O` checks that the result retains no disallowed local
access, saves the result, completes `o`, and returns the saved value. A selected
failure result from establishment never enters the body. Particular providers
define their result wrappers: current cells have internal acquisition failure,
whereas native buffers expose an ordinary `Outcome`. A general provision must
not flatten or conflate those behaviors.

Partial establishment must already own any acquired obligations through its
own checked scopes. No general rollback or destructor guarantee is inferred.

More explicitly, `Init(r,x,n,eta0,P)` saves the resource body while the
provider's establishment expression runs. `Ready(a,v,p_a,o)` is an internal
successful protocol result, not a freely forgeable source constructor.
`finish(o)` performs normal completion and returns unit to `Finish(o,v)`, which
then returns the saved body value; this active completion cannot be abandoned.
`Freshen` substitutes the new exact
identity throughout the body's lexical instantiation and binds its access value.

```sequent
family provision-control:
  E-Provision-Start :=
    ===>
    <S, eta, resource r,x = P; n, K> -> <S, eta, establish(P), Init(r,x,n,eta,P) :: K>

  E-Provision-Ready :=
    establishment has produced fresh a and authority o in S
    eta1 = Freshen(eta0,r,a)[x := v]
    h fresh
    ===>
    <S, eta, Ready(a,v,p_a,o), Init(r,x,n,eta0,P) :: K> -> <S, eta1, n, H(h,E<a>,p_a) :: O(a,P,o) :: K>

  E-Provision-Value :=
    support(v) contains no access forbidden to escape a
    normal completion of o is admitted in K
    S1 moves o into required normal completion
    ===>
    <S, eta, v, O(a,P,o) :: K> -> <S1, eta, finish(o), Finish(o,v) :: K>

  E-Provision-Finished :=
    normal completion of o has finished
    S1 discharges o
    ===>
    <S, eta, (), Finish(o,v) :: K> -> <S1, eta, v, K>
```

`Finish` has the same non-abandonment and non-duplication restrictions as
`Close`; an outward request can capture and resume it once. The owner notation
`O(a,P,o)` makes the obligation package explicit; earlier
`O(a,P)` suppresses it. An establishment failure removes `Init` and produces
the provider's specified failure outcome without installing `H` or entering
`n`. For a fused builtin boundary these abstract roles must simulate its
authenticated primitive transitions, including its specified failure channel.

For open fragments with compatible, distinct formal provision contexts, define
composition by syntax and substitution:

```text
(R; x => e) followed by (S; y => n)
    := (R,S; x => let y = e; n)
```

This combines requirements without executing establishment. Free occurrences
are embedded by capture-avoiding renaming. A frame theorem must establish that
the additional context preserves exact dispatch, support, and permitted cuts.
Merely mentioning no additional resource name is not sufficient: an extra
boundary can change capture or closing behavior.

Dependent provision uses ordinary sequence: evaluate a result, establish the
next provision from it, then enter its body. It need not fit an independent
product of provision parameters. Scope fusion and moving establishment earlier
remain separate contextual-equivalence theorems. Observable acquisition failure
or cleanup supplies immediate counterexamples to unconditional movement.

## Suspension and escape

These extend ownership transitions without adding another expression calculus.
The first suspension model is cooperative: a task yields between ordinary
machine steps; no source stack, owner, or interpretation is copied or released.
`suspend` saves the same task configuration with `()` as its next expression.
Rescheduling restores it once. A suspended required cleanup remains required.
No fairness or eventual resumption follows from the suspension permission.

For escape, use explicit transfer to an existing owning scope `q`. The initial
candidate supports an owned inbox for homogeneous tickets; it does not require
returning unrestricted continuation values or adding existential source types.
`park k in q` transfers a ticket to that inbox and returns unit. The receiving
scope fixes input `Q`, answer `A`, admissible support, interpretation context,
and its completion policy.

The transfer must preserve the ownership graph and make the destination
responsible for resumption or admitted disposal. `TransferOK` checks that all
external support outlives the inbox's use, no owning cycle is created, and the
resumption context preserves required exact interpretation and completion.

```sequent
E-Park :=
  S(k) = live(g,Q,A,chi,C,d)
  chi permits transfer to q
  TransferOK(k,q,d)
  S1 moves k from g to q without copying C
  ===>
  <S, eta, park k in q, K> -> <S1, eta, (), K>
```

The local clause may finish after transfer. Later the inbox moves the ticket to
a checked consumer, which supplies a `Q`; resumed execution produces an `A`
for that consumer. It does not return into the finished original clause.

Capturing `C` does not capture `Kout`. A dependency on an outside resource or
interpretation must therefore remain protected by `q` or be rejected. This
candidate forbids unrestricted replacement of missing interpreters at resume.
Lifetime extension alone does not make an interpretation available.

For example, a scope `q` can surround a local handler whose `pause` clause parks
an otherwise self-contained ticket and returns unit. After that handler call
returns, a consumer still inside `q` takes the ticket and resumes it once.
The captured local handler returns as part of the segment, while the answer
goes to the consumer. Moving the consumer outside `q`, or closing an external
cell on which the segment depends, is rejected.

General continuation packaging, answer-type polymorphism, arbitrary heap
escape, and mobile reinterpretation need further type and support rules. They
are not claimed by this bounded escape construction.

## Hooks and asynchronous execution

### Synchronous hooks

Current hook roots and registrations are an encoding in the sequential kernel.
The root resumes with its payload. A registration keeps its owner outside a
generated handler whose clause forwards to the older chain, applies its saved
callback, and resumes with the transformed value. For outer `A` and inner `B`,
the result is `B(A(payload))`.

The callback runs with the registration-surrounding interpretation context;
publication-only inner handlers remain in captured control. A closure alone
does not store a handler stack. Registration ownership and saved lexical values
must not be mistaken for captured interpretation. Owned abandonment removes
registrations without invoking pending transformations.

### One concrete asynchronous candidate

Use a distinct asynchronous publication API with
`publish : Payload -> EnqueueResult`, where `EnqueueResult` is `Accepted | Closed`.
It cannot keep the synchronous endomorphism's result contract when publication
returns before transformations finish. A future awaited API can return a result
through explicit joining; it is a separate contract. Internal preparation
failure remains outside this ordinary result, unless a particular provider
explicitly exposes an additional failure case.

The candidate has structured task groups, registration-site interpretation,
selection at publication, and drain-on-close. These are choices for comparison,
not current Ash behavior or consequences of an effect row.

1. Publication selects the current ordered subscribers and prepares delivery
   items. It checks payload sharing/copying and all callback support before
   committing the batch. Enqueue order follows registration order.
2. The task group owns every queued item. Starting one moves its obligation
   from queued to running, rather than deleting the obligation.
3. Each callback evaluates with a retained, checked registration-site
   interpretation context. Sharing provider closures/instances requires an
   explicit task-context admissibility check. Surrounding expression frames,
   live continuation tickets, and completion owners are not blindly copied.
4. Publication returns `Accepted` after enqueueing, not after callback completion.
   Callback result is unit; typed failures are retained in the group's chosen
   report instead of becoming implicit exceptions.
5. Deregistration stops future selection. Already selected items retain their
   callback and support until completion. A registration or supporting resource
   cannot finish closing while those items still need it.
6. Normal group close disables new publication into the closing group and
   drains its selected work before releasing support. A publication attempted
   after this point returns `Closed` and enqueues nothing. The exact
   interpretation remains available to retained work until draining finishes.

A draining callback cannot wait for the very scope whose close is waiting for
it without risking deadlock; reject known dependency
cycles, and do not infer general deadlock freedom from effect typing.

An asynchronously retained handler may itself capture restricted provider state.
Registration-site interpretation cannot be obtained just by saving names or
effect rows. If the context cannot be retained/shared lawfully, registration
is rejected or the caller must supply a different explicit task context.

The scheduler extends a state to owned queued/suspended/running tasks and
selects one ready machine step. Starting work, yielding, and finishing are
distinct transitions. For one work item, the order is:

```text
select < enqueue < start < finish < release-required-support
```

For precision, write scheduler state as `<S,T>`, where `T` maps task identities
to local configurations and lifecycle states. A local step may read/update the
shared provider state `S`; the scheduler never executes two such steps at once
in this interleaving model. `Done(t)` records the unit result or explicit typed
report and discharges that task's work obligation only after its local owned
completion has finished.

```sequent
family scheduler-control:
  E-Schedule :=
    T(t) = ready(eta,e,K)
    <S,eta,e,K> -> <S1,eta1,e1,K1>
    ===>
    <S,T> -> <S1,T[t := ready(eta1,e1,K1)]>

  E-Suspend :=
    T(t) = ready(eta,suspend,K)
    retaining this task's support is admitted
    ===>
    <S,T> -> <S,T[t := suspended(eta,(),K)]>

  E-Wake :=
    T(t) = suspended(eta,e,K)
    the selected scheduler policy authorizes waking t
    ===>
    <S,T> -> <S,T[t := ready(eta,e,K)]>

  E-Task-Done :=
    T(t) = ready(eta,(),[])
    t has no outstanding local obligations
    S1 = Done(t,S)
    ===>
    <S,T> -> <S1,T without t>
```

Enqueue and start additionally perform the checked task-context construction
described above. Their provider-specific retention proof remains an extension
obligation, rather than being hidden in an assumption that closures capture
dynamic handlers. Scheduler lifecycle transitions are unavailable to ordinary
source code except through the chosen typed scheduling provider.

Different items can interleave even on one thread. FIFO enqueue does not imply
FIFO completion. Safety proofs quantify over all admitted schedules; eventual
draining additionally requires fairness, terminating callbacks, and the stated
environment assumptions. Cost observes queue length and retained support
separately from publication latency.

Cancellation is a separate optional protocol. Cancelling queued work must
dispose its retained authority; cancelling running work needs an admitted cut.
A running cleanup remains non-cancellable under the base completion rules.
Detached callbacks and automatic cancellation are not part of this first model.

Fan-out creates separate callback executions, each normally once. Multi-shot
replays a captured computation. If that computation includes publication,
replay can enqueue another batch. An exactly-once delivery claim needs an
additional identity/deduplication protocol and is not supplied by either feature.

## Laws, propositions, and checking

Use three relations: alpha/definitional equality of syntax, derivability from
an effect/provider theory, and contextual equivalence of execution. The last
observes results, termination/divergence, specified failures, and ordered
external events. Async observation additionally distinguishes blocking and
allowed schedules; trace sets alone are not a chosen complete equivalence.
Allocation, identities, and timing enter observations when exposed by a contract.

The basic binding equations are direct substitution/frame equations. For a
value `v`, `let x = v; e` agrees with capture-avoiding `e[v/x]` under the same
usage conditions. Reassociation of nested lets with fresh binders has the same
evaluation order and corresponding pending frames. A proof for extended control
must show that the corresponding frames have the same admissible cuts; it may
not move a handler, resource, or cleanup boundary in the process.

| Proposition | Required argument and checking boundary |
| --- | --- |
| Alpha/substitution coherence | Simultaneous substitution preserves term, type, row, evidence, and dependency identities |
| Nearest exact dispatch | Stack decomposition is unique for an instantiated request |
| Provider clause typing | Exhaustiveness, operand/resumption types, common result, residual row, declared capability use |
| Capture admissibility | Every permitted clause action is supported by each reachable segment, including retained restricted values |
| Authority conservation | Each transition preserves unique owning locations or a certified split/transfer relation |
| Preservation | Typed expressions, stack segments, state, support, and protocols remain jointly well typed after a step |
| Relative progress | A closed admitted sequential state returns, steps, or exhibits a specified external/internal outcome; scheduler blocking has separate rules |
| Completion safety | No obligation is silently lost, resumed twice, or closed twice; started cleanup is not abandoned |
| Provider theory soundness | Claimed operation equations hold for the chosen state/trace interpretation |
| Split correctness | Branch identities and ownership satisfy the selected sharing/copying policy, including external protocol use |
| Frame property | Adding unused requirements preserves matching, cuts, interpretation, and completion under stated premises |
| Ordered fragment composition | Identity and associativity follow from substitution, frame coherence, and direct sequencing |
| Exchange or scope fusion | A contextual simulation preserves capture extent, establishment/close events, support, and multiplicity |
| Suspension/transfer safety | Retained support and interpretation remain available and completion responsibility is transferred |
| Async safety | Queue/task/group ownership is conserved under every allowed interleaving |
| Async liveness | Fairness and termination/environment premises suffice for the particular claimed progress property |
| Conservative extension | Current validated programs retain current results, traces, capture, and close behavior |
| Elaboration correctness | Candidate surface bindings and provider syntax simulate the administrative calculus and preserve validated Core contracts |

The one-shot target must prove progress. Its comparison with current Core may
also identify changes needed in Core: a failed correspondence proof requires a
counterexample and judgment about whether the calculus is wrong, the
implementation violates the specification, or the language needs a semantic
improvement. The current work assesses that status and records counterexamples;
it does not bring Core into alignment. Any later semantic delta requires an
explicit proposal.
Correspondence claims must state the resulting common fragment and observations.

The first checking boundary uses ordinary types, usage dataflow, and capture
analysis. Provider equations and rewrite theorems need proof certificates,
restricted decision procedures, or externally established lemmas. Existing
interface evidence is not automatically evidence for these propositions.
Do not promise general automatic discovery of semantic equivalence.

Duplicating a capture is a specified operation, not an equation asserting that
one execution equals two. Likewise, checked effectful disposal is not silent
weakening. Commutativity, idempotence, and deduplication require separate laws.

## Research grounding and transfer limits

| Source | Used here | Limit |
| --- | --- | --- |
| Plotkin and Pretnar, [Handling Algebraic Effects](https://arxiv.org/html/1312.1399), sections 2, 4–6 | Typed operations, interpretation clauses, and provider-equation obligations | Their theory does not prove this combined ownership and scheduler calculus; general handler correctness is not decidable |
| Matache et al., [Scoped Effects, Scoped Operations, and Parameterized Algebraic Theories](https://www.cs.ox.ac.uk/people/samuel.staton/papers/2025toplas.pdf), sections 2.3, 3–4 | Ordered scope parameters, binding, and scoped equations | Scope parameters are not ordinary access handles; unrestricted computation substitution cannot copy Ash obligations |
| Benton, [A Mixed Linear and Non-Linear Logic](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-352.html) | Separate reusable and restricted authority | Does not supply escape, scheduling, or effectful close rules |
| Tang, Hillerström, Lindley and Morris, [Soundly Handling Linearity](https://arxiv.org/html/2307.09383), sections 2–3, 5 | Control-flow use must agree with captured value/resource use; qualified control requirements | Additional research beyond DN-0032's original list; its soundness does not cover the proposed disposal, branch-copy, and task protocols |
| Bauer and Pretnar, [Programming with Algebraic Effects and Handlers](https://arxiv.org/abs/1203.1539) | Direct programming with operation instances and handlers, including scheduling examples | Programming examples do not establish resource-safe asynchronous hooks |
| Atkey, [Parameterised Notions of Computation](https://bentnib.org/paramnotions-jfp.pdf) | Comparison for input/output resource descriptions and frame structure | No computation-model indexing or conversion term is imported into this calculus |
| Wadler, [Propositions as Sessions](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf) | Comparison for typed connection, substitution, and scope movement | Neither a session-process language nor a deadlock-freedom theorem is imported |

The direct small-step and capability design is this note's synthesis. The
research supplies specific structures and warnings, not a theorem for the
combination.

## Evidence and experiments

The first evidence should be formal derivations and counterexamples, before
runtime representation choices. Compare the direct rules against current
specification derivations for exact forwarding, deep resume, owned discard,
resource activation, and synchronous registration. Require matching results,
selected instances, ownership transfers, and completion order.

Then check these extension cases:

| Case | Expected distinction |
| --- | --- |
| Two instances of one API, aliases, repeated acquisition site | Exact selection and fresh activations remain distinct |
| Multi-shot cut through reusable one-shot provider code | Admitted when no restricted live authority is duplicated |
| Multi-shot cut through a live one-shot clause ticket | Rejected |
| Shared cell versus fresh branch copies | `1,2` versus `1,1`, with corresponding release counts |
| Restricted value used only in a pending suffix | Its use still constrains an earlier operation's control contract |
| Discard requiring a removed source interpreter | Rejected at its closing position |
| Cleanup performing an outward effect | One-shot capture/resume allowed; abandonment of running close rejected |
| Park beyond a local handler into an enclosing inbox | Admitted only with retained support and checked residual interpretation |
| Park beyond a required resource owner | Rejected |
| Async publication followed immediately by deregistration | Selected work remains owned; future selection stops |
| Async callback under a publication-only override | Registration context remains selected, or retention is rejected |
| Fan-out of restricted payload; replayed publication | Copy/share evidence required; replay can enqueue another batch |
| Failed establishment and partial setup | No body entry; existing partial obligations remain accounted for |

The user-authorized [one-shot formalization](direct-effects/one-shot/README.md)
is a bounded proof experiment. It tests whether structural capture, restoration,
support, and closing judgments preserve recursively owned one-shot control,
including outside pending consumption and running completion. It compares
against the current exact-dispatch, nested-capture, resource-support, and cleanup
obligations cited above. Retain checked definitions, proofs, and counterexamples
as design evidence; remove abandoned encodings. The experiment authorizes no
product evaluator, source syntax, or inference change. Model checking finite
examples can find counterexamples but does not replace preservation or
simulation proofs for the unbounded language.

## Open questions

- What minimal qualified summary permits separate compilation of control-sensitive
  helpers without exposing their implementation or losing useful composition?
- Which resource protocols can supply pure total branch copying, and which need
  explicit effectful/fallible fork computations?
- How should source syntax expose provider result types and continuation
  contracts while preserving the intended rank restrictions?
- Can effectful disposal remain fully structural, or do some providers require
  an explicitly supplied surviving interpretation package?
- What proof language and trusted boundary can check provider equations and
  contextual rewrite certificates?
- Which retained interpretation contexts can be shared by async work, and how
  much ordering must be stated by their resource protocols?
- Which fairness-sensitive equivalence should govern async rewrites?

These gaps limit the combined calculus. They do not require replacing direct
sequencing with a monadic language or introducing transformer conversions.
