# One-shot control formalization

This is proof evidence governed by [DN-0033](../../DN-0033-direct-effects-and-continuation-capabilities.md).
It defines a candidate annotated control kernel, not current Ash source
semantics. It is in progress. No complete safety or compiler-correctness theorem
is claimed.

The [mathematical companion](KERNEL.md) explains the structural judgments,
proof dependencies, and what a full consistency claim would require.

The schematic request boundary is backed by the existing structural judgments.
The
[structural capture and restoration boundary](KERNEL.md#structural-capture-and-restoration-boundary)
checks the exact cut, outside payload support and well-formed control, then
proves capture, actual-prefix resumption, separately admitted disposal and
finite ownership accounting. Selected-clause source admission and independent
one-shot permissions remain additional premises.

## Current proof status

For the current lexical `InstallationState`, M0 structural resource admission,
M1's 32 individual transition families and M2 initial source admission are
complete. See [complete capture-state construction](KERNEL.md#complete-capture-state-construction)
and [initial source admission](KERNEL.md#initial-source-admission). M3 now gives
[combined constructive preservation](KERNEL.md#combined-constructive-preservation):
every applicable request has a valid successor using source-selected metadata.
M4 derives a terminal state or an applicable request from every valid snapshot,
provided the immutable operation environment satisfies the admitted builtin
cell-signature law. M3 then constructs the preserving event. Fuel-bounded
execution retains a valid endpoint and either exhausts its fuel or terminates;
raw event traces separately preserve exact owner accounting from an initial
ledger. This is not preservation for arbitrary raw annotation choices or a
claim that arbitrary raw execution retains source typing.
[Admitted-program finite execution](SourceScheduledM4.lean) is exposed by
`InitialAdmission.Program.finite_prefix`; the closed handled-discard fixture is
checked by `Examples.handled_discard_finite_prefix`.

The table below records separate evidence from earlier and adjacent models,
including their original limits. Statements there that initial admission or
whole-program progress remained open describe those narrower boundaries; they
do not qualify the current annotated-state M0–M4 result above.

| Work | Status |
| --- | --- |
| Structural capture, full-prefix resumption and ownership accounting | Checked within the annotated control and scoped execution models; the evidence below states each theorem's premises. |
| Combined progress and preservation for the current result fragment | Progress, preservation along every finite checked run, and checked extension of every closed nonterminal endpoint are proved. See the [checked-progress account](KERNEL.md#progress-extending-the-checked-run). |
| Callable application | Full contracts now participate in [progress and preservation along every finite checked run](KERNEL.md#progress-and-checked-runs-with-callable-contracts). Callable operation payload/result contracts remain open. |
| Disposal/cleanup | Runtime disposal, cleanup and capture are connected to the retained invariant. [Contextual effectful-cleanup admission](KERNEL.md#contextual-cleanup-clause-admission) generates selected bodies from original retained evidence and primitive conditions. Uniform consuming declaration admission and complete initial admission remain open. [Handler interference during closing](KERNEL.md#exact-handler-interference-during-closing) now has an exact finite structural check. |
| Declaration continuation capabilities | [Structural usage and table modes](KERNEL.md#declaration-capabilities-and-table-modes) derive selected-clause completion and constrain disposal. Retained provider requirements supply capture compatibility for the current recipe grammar, including resources, pure cleanup and internally handled request prefixes. General handler-bearing and effectful-cleanup recipes remain open. |
| Earlier source state with retained plans | Reuse evidence: [universal preservation for retained events](KERNEL.md#universal-preservation-for-retained-events) covers stable computation, checked raw disposal and six focus forms. The annotated runtime below supplies the broader current event interface. |
| Annotated runtime state | [Shared runtime integration](KERNEL.md#annotated-runtime-integration) retains the actual annotated code, saved continuations and closing callbacks under one owner, name, access, usage and completion invariant. All ten focus forms, ordinary computation, all eight return forms, resumption, builtin replies, both capture branches, disposal and resource/handler/cleanup entry are connected. [Exhaustive progress and finite execution](KERNEL.md#annotated-progress-and-finite-execution) construct actual successors and finite prefixes, with exact terminal ownership accounting. [Checked annotated events](KERNEL.md#checked-annotated-events) have universal preservation and finite-trace safety, including dynamic registry updates and exact annotated disposal, for every transition family. Progress in that same relation now yields an event at every nonterminal admitted state and every finite trace endpoint. Complete declaration/initial admission remains open. |
| Declaration-policy integration | [Explicit policies in the shared state](KERNEL.md#declaration-policies-in-the-shared-state) now pass through initial assembly, all ten focus forms, ordinary computation, all eight value-return forms, builtin replies, resumption, disposal, and resource/cleanup/handler entry, reusing existing ownership and completion proofs. Handler entry requires a proved source-evidence retention law; the recipe instance reuses its signature-transport proof. Capture now connects contextual source admission to the typed allocator with admitted snapshots and installed packets. Deriving contextual admission at every reachable request and integrating the broader policy into finite execution remain open. |
| Complete initial-term admission | Initial requirement evaluation, row acceptance and resource support use one executable check. [Recursive capability annotations](KERNEL.md#recursive-continuation-capability-annotations) derive scheduling and connect to initial runtime assembly and finite safety. Closed operation interfaces remain a specialization. General consuming declarations and complete source/completion/support admission remain open. “Initial term” means [scoped calculus code](KERNEL.md#initial-calculus-terms-and-core-programs). |
| Core correspondence | [Evidence and gap assessment](KERNEL.md#current-core-correspondence-status), with no general simulation proved and no alignment work authorized. |

These are separate obligations, not equally sized units of work. Completion of
the finite-result fragment does not estimate completion of the full one-shot
target. Multishot, escaping continuations and suspension are excluded from it.
Within handler admission, closing interference and installed-handler operation
requirements have exact finite checks. Selection retains the actual captured
and waiting pieces. Mutual compilation of
[structural source adaptations](KERNEL.md#structural-source-adaptation-and-mutual-compilation)
now covers every local plan constructor and retained-frame form, reusing the
existing capture and owner proofs. Invocation compatibility follows from the
recursive retained checks. General declaration rules still need to construct
these derivations for handler-bearing and effectful-cleanup consuming clauses.
[Direct source-interface compilation](KERNEL.md#direct-callback-and-initial-scheduling-admission)
now constructs callback checks from structural annotations, including internal
handlers that dispose their own empty captures. Free continuation uses still
require their separate capability derivations.
[Retained invocation interfaces](KERNEL.md#retained-operation-interfaces-at-invocation)
now derive normal and closing schedules at actual owner cuts from structural
annotations and finite operation checks. They admit a local clause that installs
a handler and effectful cleanup around resumption.
[Recursive capability annotations](KERNEL.md#recursive-continuation-capability-annotations)
now also handle free continuation uses in retained code, with separate rights
and phase validation after consumption. General declaration admission must still
generate these annotations and retain them through selection and runtime use.
[Annotation rewriting and substitution](KERNEL.md#annotation-rewriting-substitution-and-selection)
now preserve validation, exact saved-plan registry agreement and selected offered
plans across closed substitution. General declaration generation and its runtime
integration remain open.
[Concrete capture annotations](KERNEL.md#concrete-capture-annotations)
now supply typed clause allocation from one actual cut, selected plan and
independently validated code annotation. Exact cut and selection uniqueness
derive the previous universal body premise. A handler-bearing clause example
passes this check while failing the old recipe grammar. This does not yet
derive the annotation from handler installation.
[Declaration policies and handler installation](KERNEL.md#declaration-policies-and-handler-installation)
separate declaration evidence from planned and retained scheduling checks. The
existing judgments and runtime entry retain their current defaults; generic
entry carries the selected evidence into the actual typed handler frame.
Recursive capability annotations now also compile under supplied declaration
policies, using declaration-only compatibility laws and the same scheduling
proof. Pointwise policy transport reuses the existing operation interfaces.
Constructing the broader declaration judgment and carrying it through the full
execution invariant remain open.
[Consuming-clause annotation generation](KERNEL.md#consuming-clause-annotation-generation)
now constructs capture annotations from source derivations for sequencing,
choice, nested handlers, fresh resources and effectful cleanup around one-shot
consumption.
Selection retains the derivation for the actual offered clause. Independent
structural checks are equivalent to validation of the generated annotation;
authentication of captured-interface bounds and full runtime integration remain
open.
[Finite continuation operation bounds](KERNEL.md#finite-continuation-operation-bounds)
now derive concrete capture checks from clause-local checking of declared
resume/close requirements, original retained checks and independent disposal
protection. Authenticating those bounds at installation and retaining them
through execution remain open.
[Structural consuming-declaration admission](KERNEL.md#structural-consuming-declaration-admission)
now derives clause-local checks from source rules and finite outer operation
requirements for any captured prefix. Admission survives selection, resource
world extension and value substitution. The concrete source evidence can be
installed in the existing typed handler frame; the full execution invariant
still uses the earlier declaration policy.
[Explicit capture-bound authentication](KERNEL.md#explicit-capture-bound-authentication)
now ties finite interface checks to the bounds stored for the selected offered
mode. Source admission and a successful bound check derive the concrete capture
annotation and feed the existing typed allocator. Request typing and execution
preservation must still guarantee that check at every capture.
[Recursive resumption bounds](KERNEL.md#recursive-resumption-bounds) now cover
arbitrary-depth chains of captured continuation calls. An induction separates
their finite operation requirements from owner permissions and consumption.
[All existing consuming-clause constructors](KERNEL.md#consuming-clauses-over-recursive-captures)
now generate capture certificates for those chains, including disposal and
fresh-resource cleanup. The canonical bounded allocator accepts the recursive
source input and preserves the same stored packet. General recursive retained
source shapes and retention through the full runtime remain open.
[Exact bound retention](KERNEL.md#source-bound-retention-and-installation)
now connects consuming-source generation, recursive annotation rewriting and
closed substitution to installation of the recorded runtime packet. Missing
metadata cannot supply a bounded installation. The existing full-state
resumption proof also preserves these packets on the same successor and owner
trace. Carrying source metadata through every transition and deriving every
reachable bound check remain open.
[Structural declaration transport](KERNEL.md#structural-declaration-transport-to-actual-clauses)
now derives admission of actual clause plans from an admitted checking
declaration with the same signature, retaining its recorded mode bounds.
Installation reuses that proof for the actual handler packet.
[Structural snapshot admission](KERNEL.md#structural-admission-of-persistent-bounds)
now retains evidence for the exact recorded bounds through the 17 connected
runtime rules. Handler entry still needs to join its actual source witness and
installed packet to that invariant.
[Queued source bounds](KERNEL.md#bounds-at-source-focus)
now separate immutable plan metadata from continuation-specific capability
cuts. All ten focus positions retain the exact child and pending-code bounds
alongside the shared runtime preservation result. The same plan metadata can
supply handler installation.
[Persistent bound snapshots](KERNEL.md#persistent-bound-snapshots-and-returned-contexts)
now retain current and queued metadata through focus and returned-context
recomposition under a refinement of the shared state indexed by its checking
plan. [Ordinary computation](KERNEL.md#persistent-bounds-through-ordinary-computation)
retains the selected packet through bind, beta reduction and both branches,
including progress and preservation in the combined execution invariant.
[Combined focus and return](KERNEL.md#combined-snapshots-through-focus-and-context-return)
now retain these snapshots alongside the same owner, name, access and completion
checks. Focus guards and value closedness follow from existing source proofs.
[All returned-value transitions](KERNEL.md#snapshots-through-all-returned-value-transitions)
now preserve the same snapshots through boundary exits, cleanup execution and
retirement, reusing the existing owner-consumption proofs.
[Builtin replies and cleanup entry](KERNEL.md#snapshots-through-builtin-replies-and-cleanup-entry)
now retain those snapshots too. Read/write keeps the original pending data;
cleanup entry queues the original callback annotation while its body runs.
[Resource entry](KERNEL.md#snapshots-through-fresh-resource-entry) selects the
original fresh-body annotation and transports queued metadata into the larger
resource world. Its progress proof derives the initializer and answer port
from the checked source.
[Handler entry](KERNEL.md#admitted-snapshots-and-packets-through-handler-entry)
now retains the actual clause witness and joins the admitted snapshot and
installed handler packets on the same runtime successor, including source-derived
progress. [Exact packet source typing](KERNEL.md#source-typing-at-the-installed-packets-exact-plan)
now retains the original structural declaration derivation at the installed
packet's actual clause plan.
[Joint packet/source typing](KERNEL.md#joint-source-typing-at-stored-packets)
now pairs that source with each runtime frame's rich interface, including dormant
segments. Capture splitting derives the selected packet's declaration source;
contract/world transport, suffix rechecking, registry updates and recomposition
preserve the pairing. [Joint runtime handler entry](KERNEL.md#joint-packet-source-through-runtime-handler-entry)
now constructs that pairing in the stronger execution invariant, with admitted
snapshots, actual installed packets and progress. It can start from an already
checked empty-stack state.
[Joint capture preservation](KERNEL.md#joint-packet-source-through-capture-allocation-and-execution)
now carries the exact saved and waiting packets through both allocator branches,
closing certificates and the combined execution successor. Inherited-route
snapshot admission and fresh-owner progress are proved.
[Generated bounded annotations](KERNEL.md#generated-bounded-annotations-on-the-joint-capture-successor)
now reach the same successor and admitted snapshot under a finite capture-input
check paired with its action/source witness. Deriving that check from initial
source admission remains open.
[Joint resumption](KERNEL.md#joint-packet-source-through-one-shot-resumption)
now restores the exact saved packets above the waiting caller, preserves
snapshot admission and consumes the selected owner. Its progress proof derives
the live cut from existing source usage.
[Joint disposal](KERNEL.md#joint-packet-source-through-disposal)
now materializes the actual closing packets, retains the original caller
packets and preserves the admitted execution successor, including progress.
[Ordinary computation](KERNEL.md#joint-packet-source-through-ordinary-computation)
now preserves the same stronger invariant through bind, beta and both branches,
with admitted-snapshot progress.
[Focus and all eight returns](KERNEL.md#joint-packet-source-through-focus-and-returns),
[resource and cleanup entry](KERNEL.md#joint-packet-source-through-resource-and-cleanup-entry),
and [builtin cell operations](KERNEL.md#joint-packet-source-through-builtin-cell-operations)
now retain the same joint source and actual packets. Local preservation covers
all 21 raw constructors; bounded capture retains its finite input-check premise.
[Common events and finite executions](KERNEL.md#joint-source-preservation-over-actual-finite-events)
now preserve joint source and packet typing under the existing recipe policy,
with reachable-state progress, finite-prefix construction and terminal owner
accounting. Extending this result to the broader consuming-declaration policy
and admitted bound annotations remains open, together with complete initial
admission and derivation of every reachable capture check.
[General annotation reconstruction](KERNEL.md#reconstruction-and-transport-of-general-capability-annotations)
now derives validated annotations from every current structural scheduling
constructor and extracts both pieces at an actual capture cut. Recomposition
and receiver adaptation reuse existing proofs. This removes the reconstruction
restriction to resumption chains; the bounded capture-input generator and
preservation of admitted bound metadata still require integration.
[Capability phase transport](KERNEL.md#capability-phases-preserve-the-actual-annotations)
preserves the same annotations and their bound fields across fresh allocation
and spending of an absent outer owner. Receiver adaptation now supports the
stated broader declaration policies; retaining bounds while changing the
receiving forest remains a separate obligation.
[Independent capture-bound construction](KERNEL.md#capture-bounds-independent-of-source-scheduling)
now generates an admitted snapshot for arbitrary captured forests from the
selected declaration and actual cut. This removes the need to preserve every
capability-annotation field merely to construct capture bounds. Connecting that
construction to general capture scheduling remains open.
[Certified runtime capture](KERNEL.md#certified-capture-with-independent-bound-snapshots)
now carries a validated general capture certificate and independent bounds to
the actual source successor, admitted snapshot and installed packets. It retains
ownership balance and row inclusion. The certificate compiler and raw allocation
proofs now accept declaration-policy parameters and their static laws, reusing
the existing substitution and ownership proofs.
[Concrete consuming declaration policies](KERNEL.md#concrete-consuming-declaration-policies)
now supply those static laws at every finite layer of declaration evidence.
Policy inclusion retains exact bounds, and a handler-wrapped clause rejected by
the old recipe grammar enters the source scheduler. The general structural
certificate now reaches the combined execution invariant, with its admitted
snapshot and actual packets, through shared ownership and completion proofs.
Its validation stays paired with the same current action/source witness.
Deriving that validation from initial source and integrating common finite
execution remain open.
[Direct consuming clauses over general captures](KERNEL.md#direct-consuming-clauses-over-general-captures)
now derive a capture certificate from the current request, whole retained source
and structural declaration admission. The captured forest may branch and invoke
owners in its waiting tail. The clause may use operation prefixes, choices
and builtin resource scopes before resuming or disposing. Pure cleanup wrappers
are also admitted when the callback checking plan is `.pure` and its dependency
list is empty. Resource allocation
uses the existing provider-insertion proof, now parameterized by declaration
policies. This generator does not yet cover handler or effectful-cleanup wrappers around
consumption. It also reuses neutral transport, fresh-owner phase transport and
exact source cuts. The earlier chain generator continues to cover the remaining
wrappers only for its restricted captured-source form.
[The general handler boundary](KERNEL.md#handler-boundary-obligation-for-general-captured-source)
now has a checked obstruction: a caller handler can preserve operation
availability while invalidating a later disposing capture's callback route.
The old operation-interface generator rejects this input. Extending to general
source needs additional boundary evidence; the existing finite interference
summary supplies an exact closing check and a sufficient declared-bound rule.
[Boundary composition and consumption](KERNEL.md#callback-boundary-composition-and-consumption)
now split those bounds at actual handler cuts and preserve them through resume
and disposal at actual owner cuts, including dormant captures. The proofs reuse
the existing structural shielding judgment. Integration into general annotation
generation and preservation through all execution families remain open.
[Effectful cleanup insertion](KERNEL.md#effectful-cleanup-insertion-and-closing-routes)
now has an exact closing-route condition and a connection to existing runtime
ownership proofs. A checked example shows why separate validity of the original
request and callback is insufficient; a surviving builtin permits the full
callback schedule. The general conditional generation result is described below.
[Cleanup plan transport](KERNEL.md#exact-cleanup-plans-through-cuts-and-pending-sites)
now retains the actual callback through handler and owner cuts, closing,
resumption and disposal. Pending-site decomposition accounts explicitly for the
new callback code. Recomposition reuses existing checks, but general local
transport and callback admission still need to supply its premises.
[Callback schedules from closing routes](KERNEL.md#callback-schedules-from-closing-routes)
now derive the closing callback checks from their normal operation interfaces,
structural coverage by declared effect needs, and the existing capture-route
guard. This includes dormant captures and arbitrary discarded plain code. The
selected-request annotation and direct consuming-clause capture generator use
that derivation without a prechecked closing schedule. General cleanup transport
must still retain these source interfaces and derive the guards at every
reachable request; handler and effectful-cleanup clause generation remain open.
[Cleanup source-interface transport](KERNEL.md#cleanup-source-interfaces-through-capture-and-consumption)
now preserves callback declarations, effect coverage and normal operation checks
through insertion, handler cuts, owner cuts, resumption, disposal and closing.
The selected-request branch generates its new annotation using the original
interfaces and an explicit finite closing-route condition.
[General cleanup annotation generation](KERNEL.md#general-cleanup-annotation-generation)
now covers every existing expression and retained-frame constructor by mutual
induction, including recursive continuation uses. It returns a target annotation
and a structural tree of additional operation and closing-route checks. Passing
those checks preserves validity and derives scheduling from the original source.
[Contextual cleanup clause admission](KERNEL.md#contextual-cleanup-clause-admission)
now incorporates these primitive conditions into structural rules for clauses
with sequencing, choices, effectful cleanup and resource scopes. Original retained
evidence and admitted conditions generate the selected body at a fresh capture
and its existing scheduling judgment. Callback dependency coverage and consumed
owner rejection have separate checked examples. This is admission at an actual
capture; uniform declaration admission, deriving the conditions at every reachable
capture, and retention of admitted bound metadata remain open.
[New interception from original source](KERNEL.md#new-interception-from-original-source)
now derives a newly selected disposer's closing schedule from the original whole
callback metadata, its normal operation checks, the new capture guard and the
separate pending-owner bound. The original request needs no disposal schedule.
The proof supplies the existing adaptation compiler's fresh-request branch and
preserves the original owner partition.
[Structural source rechecking and handler admission](KERNEL.md#structural-source-rechecking-and-handler-admission)
now derive target capability annotations by mutual induction over source
rechecking rules, including callbacks that invoke outside continuations.
Contextual handler admission uses those rules and composes with cleanup and
resource admission. Checked examples cover a nonempty saved request whose
interpretation changes, and two handlers around cleanup and a fresh resource.
[Explicit cleanup admission](KERNEL.md#explicit-cleanup-admission-and-annotation-witnesses)
also uses structural rechecking directly. It avoids relying on an existentially
chosen conditional check tree being usable. A rule for alternative annotation
witnesses at the same physical receiver preserves admission when their caller
interfaces agree; it cannot exchange scopes or interpretations.
The rechecking derivations remain explicit inputs at actual captures.
[Cleanup admission from receiver plans](KERNEL.md#cleanup-admission-from-receiver-plans)
now reuses the full mutual cleanup generator to derive structural rechecking.
A retained receiver plan exposes primitive operation and closing conditions;
when they hold, it constructs the existing receiver judgment and cleanup
admission rule, with exact bound retention through the existing compiler.
This does not establish that an arbitrary chosen check tree succeeds or that
initial admission supplies its conditions at every reachable context.
[Structural admission descent](KERNEL.md#structural-admission-descent-and-entry)
now extracts child admission and finite checks through handlers, structural cleanup
and fresh resources. Existing snapshot entry relations retain those exact
child bounds. A composed example descends through two handlers, cleanup, a fresh
resource and both consumption branches. Finite bound checks also survive world
extension and unrelated owner changes. Arbitrary intervening execution still
needs preservation of contextual admission: a saved outside-owner invocation
can reject a phase change that the finite clause-bound check does not observe.
[Contextual admission phase preservation](KERNEL.md#contextual-admission-phase-preservation)
now retains the exact annotations, structural rechecking and consuming admission
when availability is preserved for the actual retained live owners. Existing
scope realization and live-owner inclusion derive that condition from the same
runtime stack.
[Contextual admission world preservation](KERNEL.md#contextual-admission-world-preservation)
now transports exact source annotations, rechecking and admission through
resource-world growth, with composition and exact bound-data preservation.
Cleanup admission uses explicit structural rechecking; the conditional generator
remains separate evidence.
[Joint contextual admission transport](KERNEL.md#joint-contextual-admission-transport)
now connects permission extension and composes all three changes while retaining
exact source bounds. Existing permission entries keep their rights. Physical
receiver changes and retention through every reachable request remain open.
[Receiver generation with retained current bounds](KERNEL.md#receiver-generation-with-retained-current-bounds)
now strengthens the existing structural rechecking compiler to preserve the
current expression's exact bound projection. Neutral stack expansion also
derives target code directly from original admission and finite checks, retaining
those bounds. Its selected-source bridge reaches the existing typed allocator,
actual capture step, admitted snapshots and exact fresh-owner accounting.
This does not yet derive successor structural admission.
[Retained metadata through recomposition](KERNEL.md#retained-metadata-through-recomposition)
now preserves the exact input snapshots when retained annotations are joined.
The rechecking compiler also produces structural provenance for retained bounds
and preserves their admission, including dormant-branch closing. Connecting
these results to every reachable source admission remains open.
[Exact source metadata at capture](KERNEL.md#exact-source-metadata-at-capture)
now connects valid source splitting to the actual captured snapshot and the
request context's resumption evidence. Neutral receiver expansion preserves the
saved metadata, including callbacks and dormant branches. Original source and
snapshot agreement is an explicit premise. Canonical closing is now connected
through the structural request source below; general reachable admission remains open.
[Structural closing with canonical metadata](KERNEL.md#structural-closing-with-canonical-metadata)
now derives closing annotations from original source and structural callback
rechecking, with exact equality to the runtime closing projection. The resulting
capture context supplies matching admitted capture and disposal snapshots.
The request path now requires this structural derivation on its original saved
source. Scheduling-only reconstruction is no longer its closing interface.
[Receiver rechecking and metadata agreement](KERNEL.md#receiver-rechecking-and-metadata-agreement)
now supplies structural receiver changes that preserve the complete retained
snapshot and constructs contexts with exact saved/closing/waiting agreement.
Counterexamples show why the earlier `sameReceiver` rule and current-expression
bounds alone do not establish that guarantee. The admission integration below
now adopts the stronger interface, and generated-source correspondence below
connects it to emitted retained fields.
[Resource entry retaining source metadata](KERNEL.md#resource-entry-retaining-source-metadata)
now updates the actual resource context constructor to preserve saved, closing
and waiting snapshots in the extended world. Neutral expansion and provider
insertion share the generalized retention proof; canonical closing commutes
with world extension.
[Admission retaining receiver metadata](KERNEL.md#admission-retaining-receiver-metadata)
now uses receiver-only rechecking in the actual handler/cleanup constructors and
requires exact retained agreement in `sameReceiver`. Phase, permission and world
transport, their composition, and structural descent remain proved. Existing
examples with arbitrary initial annotations retain their scope through proofs
that their particular forests have fixed metadata.
[Generated clause and retained-source correspondence](KERNEL.md#generated-clause-and-retained-source-correspondence)
now strengthens the existing generation induction: emitted resume/dispose fields
match the context's saved/closing/waiting projections through every clause
constructor and fresh resource. Selected-clause capture shares the actual source
split with an admitted runtime snapshot when the input source and snapshot agree.
[Structural request source and canonical disposal](KERNEL.md#structural-request-source-and-canonical-disposal)
now supplies canonical closing to the actual request context and selected-clause
capture theorem. It uses the structural capture guard, original source split and
recursive closing derivation, with no future request/closing-validity premise.
Permission, phase and world transport preserve this evidence. A disposal-enabled
example retains explicit callback bounds on both sides of the cut. Deriving this
source evidence at every reachable request remains open.
[Contextual source preservation for ordinary computation](KERNEL.md#contextual-source-preservation-for-ordinary-computation)
now covers bind, beta and both Boolean reductions. The actual bound-selection
event determines the successor source subtree; original admission derives its
contextual judgment, finite checks and nested declaration evidence. The shared
runtime theorem retains the same action witness and reuses existing ownership,
access and completion proofs.
[Queued source admission at focus and return](KERNEL.md#queued-source-admission-at-focus-and-return)
now retains the original consuming source derivation beside the queued bounds
and reconstructs it on plain return. It covers the existing focus splits,
distinguishes consuming work that remains current under a pure frame, and reuses
the runtime ownership proofs. Permission, phase and world transport preserve
the queued record at a fixed receiver.
[Queued records through capture and restoration](KERNEL.md#queued-records-through-capture-and-restoration)
now transports the original records through the exact ordered capture and
resumption cuts, including dormant branches. The typed capture and resumption
theorems retain those records alongside their existing ownership conclusions.
Record movement preserves the original context.
[Source reconstruction at changed receivers](KERNEL.md#source-reconstruction-at-changed-receivers)
now derives admission at a new caller from the original source and explicit
structural receiver checks, with independent operation/phase checks and exact
continuation metadata. The typed return consumes the reconstructed record.
Examples activate a record recovered after capture/resumption. Deriving those
checks from every actual runtime change and retaining source coverage throughout
prefix execution remain open.
[Derived receiver checks for saved frames without code](KERNEL.md#derived-receiver-checks-for-saved-frames-without-code)
now removes the extra receiver-check premise for saved forests without pending
code, callbacks or handler requirements, including actual handler delimiters.
The consuming source retains its full grammar. Under a pure focus frame, the
entire source record and finite checks are derived from the original record.
Context construction and finite-check transport also cover nonempty saved code;
[general neutral source admission](KERNEL.md#neutral-source-admission-with-saved-code)
now supplies the full focused source record for arbitrary saved code, callbacks
and handler requirements. The source rule retains the original derivation and
exact continuation metadata; generation reuses induction on that derivation.
Child descent and phase, permission and resource-world transport include the new
rule. [Neutral waiting-tail admission and generation](KERNEL.md#neutral-waiting-tail-generation)
now constructs full source admission and valid clause code when the waiting
forest changes, preserving saved bounds exactly and tail metadata structurally.
An actual capture/resumption/return snapshot example reuses its recovered source
record at the changed tail, then supports source descent, return, computation
and further focus. Typed return integration reuses the existing ownership proof.
The restoration API derives the caller interface and its finite-check equality
from the original record and structural expansions.
[Non-neutral waiting reconstruction](KERNEL.md#non-neutral-waiting-reconstruction)
also constructs the context and source record from explicit structural
rechecking. A saved operation can change to a disposing interpretation;
an interpretation missing that operation is rejected despite valid owner checks.
Deriving these rechecking obligations from every actual restoration and retaining
source coverage throughout execution remain open.
[Source-derived bypass rechecking](KERNEL.md#source-derived-bypass-rechecking)
now derives the selected-request case when a newly inserted handler is bypassed.
The original capture supplies its callback bound, closing erases the inserted
handler, and existing proofs retain callback code and owner bounds. Fresh
interception remains a separate case. Waiting-suffix rechecking now derives
the unchanged selection and guard, leaving only recursive rechecking of the
original closing source.
[Rechecking requests at non-disposing interpretations](KERNEL.md#rechecking-requests-at-non-disposing-interpretations)
also handles an originally selected disposer changing to a builtin or resumptive
handler. The existing compiler retains bounds and independent owner checks.
Two successive non-neutral waiting reconstructions now generate a complete
source record through a resumptive-to-disposing-to-resumptive interpretation
change, reusing the actual first generated context. This remains source/context
evidence; general reachable-source admission is still open.
[Fresh capture from structural closing](KERNEL.md#fresh-capture-from-structural-closing)
now reuses the original prefix's closing derivation for a newly intercepting
handler. Operation-only annotations may change their requirement list when a
new structural footprint of the same syntax justifies it. A mixed-callback
example retains an effectful callback and an outside continuation invocation,
even when closing removes a handler that supplied a conservative requirement.
The general recursive derivation of closing obligations remains open.
[Separate ownership bounds for disposal callbacks](KERNEL.md#separate-ownership-bounds-for-disposal-callbacks)
identify a necessary source condition: ordinary pending code uses captured
owners, while callbacks scheduled by disposal use surviving receiver owners.
The existing request judgment implies both bounds at its actual cut. A checked
counterexample passes normal validity, the capture guard and the pending-code
bound but fails callback ownership; no valid target request annotation exists.
Structural closing preserves actual outside-owner selections, including their
saved bodies and tails. Original active selection, surviving-owner membership
and the existing uniqueness invariant now derive the selection after closing.
These results do not yet derive all closing obligations from initial admission.
Closing compilation now also preserves the exact callback metadata through
retirement of captured owners. It reuses annotation phase transport at the
surviving receiver. A checked example discards ordinary code that becomes
invalid after retirement while retaining valid resource and outside-owner
callbacks. This does not require the discarded normal source to remain valid.
[Protected-mode request rechecking](KERNEL.md#protected-mode-request-rechecking)
now derives the request case across a running callback from its actual selected
protected mode. Such a capture cannot dispose, so it needs no new recursive
closing annotation. The local rule permits an absent ordinary mode while the
reusable operation capability still requires both modes. Compilation and
permission, phase and world transport preserve the original source bounds.
[Requests selected inside an unchanged prefix](KERNEL.md#requests-selected-inside-an-unchanged-prefix)
now recover the local cut from the actual whole-source selection and retain the
exact capture when the outside receiver changes. Operation-only requests derive
their precise capability from the original footprint. Selected disposing
requests reuse their original guard and owner bound, leaving recursive receiver
rechecking of the original closing source. A nested example combines this case
with a callback using the protected-only outer interpretation.
[Partial caller closing](KERNEL.md#partial-caller-closing-during-continuation-invocation)
now reconstructs the closing prefix of an original caller while preserving its
suffix, including the disposal running marker. Resumption and disposal share
the traversal and reuse the original outside selection. The proof preserves
surviving owners and caller metadata admission; examples retain exact saved-body
and closing-body metadata. A negative case excludes every target annotation when
the saved body actually requests an erased handler. Initial admission must
prevent that case; general recursive derivation remains open.
[Canonical partial closing and caller decomposition](KERNEL.md#canonical-partial-closing-and-original-caller-decomposition)
now recover the original source children at an arbitrary outside owner cut,
preserve the exact split/close/append snapshot, and carry original callback and
suffix payloads in order. Both boundary forms have checked canonical snapshots;
a concrete payload example drops pending prefix source while retaining the
original dormant callback and pending suffix. Broader runtime adoption remains
open.
[Independent recursive admission checks](KERNEL.md#independent-recursive-admission-checks)
now factor the full annotated source validator into interpretation checks and
continuation permission/consumption checks. Their conjunction is equivalent to
the original validator, and the existing source compiler accepts the separately
proved factors. Nested-owner examples distinguish missing effects from missing
or consumed continuation permissions. Receiver transformation still requires
its own preservation proof.
[Source-only recomposition](KERNEL.md#source-only-recomposition-and-independent-checks)
now constructs one joined annotation before validation, preserves both factors
in both directions, and retains the exact original metadata append. The
rechecking, closing and partial-caller compilers use that constructor for dormant
closing joins. Failed effect or continuation checks remain rejected.
[Rechecking compilation before full validation](KERNEL.md#rechecking-compilation-before-full-validation)
now constructs one target annotation with independent interpretation and control
preservation implications and retained metadata. The old compiler API follows
from this stronger result. Contextual transformation evidence remains an input;
deriving it from initial admission is still open.
[Original source at fresh interception](KERNEL.md#original-source-at-fresh-interception)
now recovers the normal captured prefix and its validity from whole original
source. Recovery from an actual source join retains the original child
annotations, allowing existing callback closing proofs to be reused. Examples
cover both an effect request and a callback invoking an outside continuation.
Capture guards, pending-owner bounds and recursive closing still need evidence;
this does not complete the general initial-source derivation.
[Handler admission from original operation interfaces](KERNEL.md#handler-admission-from-original-operation-interfaces)
now extracts operation interfaces from compact or expanded retained source and
derives handler-entry receiver changes from finite intercepted-operation checks.
The source traversal covers callbacks and dormant branches, and extraction is
complete for this structural view. The richer rules remain necessary for
selected disposing requests and retained code that invokes outside owners.
Explicit handler, cleanup and resource successors now retain these source views
and the exact continuation metadata, including resource-world extension. The
existing admission compiler accepts them through metadata transport. An
induction covers arbitrary finite nesting of the supplied resumptive table,
including saved callbacks. Examples compose that nesting with an unrelated
disposing table, effectful cleanup entry and a fresh resource with a builtin read.
[Initial interface admission at continuation use](KERNEL.md#initial-interface-admission-at-continuation-use)
now generates source directly from structural admission and original saved/closing
views, checking requirements at consumption. This admits a proved temporary
masking case rejected by intermediate interface checks. Arbitrary waiting
annotations retain their exact bounds, including through resource allocation.
The selected stored clause reaches the existing capture-certificate and canonical
snapshot boundary. Richer saved-source derivation and full execution integration
remain open.
[Rich source rechecking at continuation use](KERNEL.md#rich-source-rechecking-at-continuation-use)
now supplies a structural compiler for full captured annotations, reusing the
existing receiver rechecking and metadata proofs at consuming leaves. Examples
cover outside-owner invocation, a continuation-using closing callback, fresh
resources and a fresh disposing interpretation. Stored-clause capture reuses
the same certificate and snapshot boundary. The structural leaf derivations
remain explicit obligations; deriving them at every reachable request and
retaining them across all runtime transitions remain open.
A checked counterexample now rules out deriving them from clause-local
`Admitted` evidence alone: an understated continuation interface can pass that
check while its actual captured code cannot run under the clause's handler.
The existing checker rejects the example with the actual captured requirement.
Authentication of the captured contract is therefore a necessary premise of
the initial-source argument.
[Queued consumption-time source at focus and return](KERNEL.md#queued-consumption-time-source-at-focus-and-return)
now separates original captured source from the current caller in retained
records. Actual typed focus and return reuse existing ownership and completion
proofs. Canonical-index adapters reconstruct source on return, and generic
capture/resumption preserves the original payload. Permission, phase and world
transport now retain these records. An explicit neutral receiver path lets
restored records participate in typed focus and return under added spent
markers or pure frames. Source-directed handler entry now derives the child
record at the actual typed packet-installation successor, including an
intermediate masking handler. Ordinary computation retains these records in
full execution; cleanup and resource entry now retain their derived child
records through full execution too. Fresh capture retains the selected clause's
source record, exact resumption bounds and canonical disposal snapshots at the
actual typed and full-execution successor, reusing the existing allocator and
ownership proofs. Source evidence at that request remains an explicit premise.
Resumption and disposal now activate retained source at their exact typed and
full-execution successors, sharing the original action witness and deriving the
actual spent phase map. Disposal also moves all recursive payloads through the
ordered callback filter. The runtime theorems now take the combined source and
metadata record described below, including its neutral receiver movement.
Deriving usable records throughout execution and full initial-source admission
remain open.
[Consuming source with actual metadata provenance](KERNEL.md#consuming-source-with-actual-metadata-provenance)
now pairs the source record with its exact original saved/closing metadata and
structural movement to the actual pending bounds. Capture initializes this
record; computation, focus/plain return, handler/cleanup/resource entry and
permission/phase/world transport preserve the local correspondence. The receiver
expansion is derived from the metadata record. A separate strengthened neutral
transport theorem constructs source at a supplied destination's exact bounds.
Actual resumption/disposal now preserve that metadata movement and use the
strengthened theorem to activate source at the exact runtime successor. Existing
typed and full-execution connections now carry the combined record for capture,
computation, focus/plain return and handler/cleanup/resource entry. Valid
retained source now supplies concrete code records for every pending body,
callback and dormant saved branch, checked at their exact receiving suffixes.
Fresh capture carries these records under the new permissions and phase;
resumption and disposal construct complete records at their actual successors.
The runtime's existing schedule and positioned records reconstruct full retained
source with exact bound metadata. Preservation of this coverage through every
transition and derivation of later contextual request-site judgments remain
open; current code validity does not imply those later judgments. Current code
and complete pending records now also form one coverage judgment preserved by
ordinary computation, all focus forms and plain return. The typed runtime
connections derive successor coverage from the original code records; return
does not require separate admission of the restored queued body.
[Finite requirements at a surviving interpretation boundary](KERNEL.md#finite-requirements-at-a-surviving-interpretation-boundary)
now derive operation-only receiver checks from the surviving outside and retained
cells. A finite bound on exposed requests supports arbitrary closing prefixes;
examples cover ordinary code, callbacks and dormant bodies. Protected-only
requests separately derive their capture guard from the selected contract's
fields. The general initial-source derivation and runtime adoption remain open.
[Canonical source annotations before rechecking](KERNEL.md#canonical-source-annotations-before-rechecking)
now resolve a proved representation obstruction: compact bounds can forbid
rechecking a compound computation when an operation changes to a disposing
interpretation. Mutual normalization preserves original validity and bound
observations, yields exact canonical metadata, and separately proves that all
current and retained source branches are expanded. Rechecking the actual
generated source returns an expanded target too; idempotence keeps canonical
indices stable. Normalized snapshots preserve admission and commute
with capture, resumption and disposal metadata movement. Queued records now
retain their original source payloads at canonical indices through capture and
resumption; actual queued derivations generate expanded code on return at their
recorded contexts. Adoption by the broader execution invariant remains open.
[Contextual capture from selected source](KERNEL.md#contextual-capture-from-selected-source)
now selects the actual stored clause annotation, retains its source bounds during
compilation, and derives a capture certificate from the original request and
retained source. The existing typed allocator accepts that source admission and
preserves the admitted snapshot, installed packets and exact owner increment.
Deriving contextual admission at every reachable request and integrating the
broader policy into finite execution remain open.
[Recursive nested-bound admission](KERNEL.md#recursive-admission-of-nested-handler-bounds)
checks the bounds recorded inside every offered consuming clause. World extension,
value substitution and stable-signature transport preserve that check. The same
selected clause now generates both valid code and admitted bound metadata;
bounded capture now retains that generated annotation on its actual successor,
under the finite capture-input check.
[Exact capture data and snapshots](KERNEL.md#exact-selected-plan-data-and-capture-snapshots)
now retain that annotation at the typed allocator's selected plan and split the
original pending metadata into saved and waiting parts. Contract refinement and
payload substitution keep the same plan, and reuse the raw capture ownership
proof. [Runtime clause evidence](KERNEL.md#exact-clause-evidence-through-runtime-capture)
now survives both allocation branches and reaches the actual `AtPlan` successor
in the runtime and combined execution proofs. Bounded source generation now
joins the stronger `AtPackets` interface under its finite input check, retaining
packet/source agreement through the actual successor.
[Inherited capture](KERNEL.md#admitted-inherited-snapshots-through-capture)
now joins an admitted snapshot and the exact retained packet stack to the
combined successor, with progress from a fresh ledger owner. Its current
annotation is justified by the actual recipe-derived clause check.
[Resumption](KERNEL.md#admitted-snapshots-and-packets-through-resumption)
now joins the exact saved/caller annotation rearrangement, admitted installed
packets and one-shot owner consumption on the same successor. Its progress
proof locates the live cut from the existing source invariant.
[Disposal](KERNEL.md#admitted-snapshots-and-packets-through-disposal) now carries
the original callback annotations and caller packets through the actual stored
closing plan, including preservation and source-derived progress.
This connects 20 raw constructors and the inherited-recipe case of capture to
the stronger snapshot proof. General bounded capture, complete source admission
and the complete finite-execution connection remain open. Installed packet
admission must also join the other 17 snapshot transitions in that final interface.
The [source-context data layer](KERNEL.md#source-contexts-before-declaration-checking)
now exposes actual plans and sites before recipe checking. A generic local
composition and a rejection example establish that newly installed handlers
must be allowed to supply operations unavailable before their entry.
A [consuming declaration rule](KERNEL.md#internally-handled-request-recipes) now
admits that prefix and compiles it through declaration selection and capture,
including a nested handler for the same effect instance.
[Source-local requirement templates](KERNEL.md#source-local-requirement-templates)
now describe every caller context before the runtime capture is known, with an
exact instantiation theorem and a compiler for their primitive obligations.

The remaining focus-annotation problem now has an
[admitted-program counterexample and finite hint checks](KERNEL.md#source-type-choices-and-finite-hints).
The same raw binding code and plan can admit different initializer ports.
Explicit lexical type hints distinguish them, with checked source/frame
agreement and preservation of realized resource identities.
[Finite annotated nodes](KERNEL.md#finite-annotated-nodes-and-transport) now cover
the full scoped syntax, with substitution/instantiation erasure laws and all ten
focus positions. [Metadata closure](KERNEL.md#metadata-closure-and-full-tree-commutation)
now gives full-tree substitution/instantiation commutation while allowing local
resource scopes. [Annotated source checking](KERNEL.md#annotated-source-checking-and-focus)
now authenticates the same rich type choices at recursive source nodes and
checks finite metadata closure. Its erasure reuses the existing source proofs;
all ten focus positions retain the checked child and annotated context, and
frame preparation produces a successful finite port guard. Both binding choices
establish the existing initial runtime invariant, and a local-resource example
checks every fresh opening. [Annotated substitution and ordinary reduction](KERNEL.md#annotated-substitution-and-ordinary-reduction)
now preserve that source judgment through closed substitution, binding, function
application and branch selection. The proofs reuse existing source transports,
resource-opening laws, requirement evaluation and owner accounting.
[Context recomposition and runtime retention](KERNEL.md#annotated-runtime-retention-and-focus)
now preserve this evidence in annotated current code and recursively saved
frames. All ten focus forms preserve that stronger scheduled state using the
actual child hint and stack ports. The [annotated runtime integration](KERNEL.md#annotated-runtime-integration) now
lifts all ten forms into the shared runtime invariant. The older finite
retained-event theorem covers six; the common annotated event relation now covers all ten.
[Annotated resumption](KERNEL.md#annotated-capture-splitting-and-resumption) now
covers every raw resume step; capture splitting retains the actual handler
declarations and both source segments. [Annotated allocation components](KERNEL.md#annotated-clause-selection-and-allocation-components)
now preserve the selected body through substitution and rebuild the live segment
under the fresh contract and saved-plan entry. [Annotated closing records](KERNEL.md#annotated-closing-sources-and-stored-records)
now retain callback sources through existing transitions and materialize the
selected closing control. [Capture preservation](KERNEL.md#annotated-capture-preservation)
now connects clause effects and owner accounting to the complete successor
source state in both allocation branches. [Annotated disposal](KERNEL.md#annotated-disposal-preservation)
now joins cleanup and caller source with record consumption and owner accounting;
the [shared runtime](KERNEL.md#annotated-runtime-integration) now derives its typed-plan
interface from the retained certificate. The same runtime also derives capture
resource support and registry freshness. Entry witnesses and builtin replies
now join the same runtime invariant. [Combined progress](KERNEL.md#annotated-progress-and-finite-execution)
covers every typed current form and constructs finite execution prefixes.
[Checked annotated events](KERNEL.md#checked-annotated-events) now prove universal
preservation and finite-trace safety for focus, ordinary reduction, all returns,
resumption, builtin replies, entry, capture and exact annotated disposal.
[Common-event progress](SourceAnnotatedEventProgress.lean) now proves that every
admitted nonterminal state has an event in that same relation, including every
endpoint of a finite supplied trace. General structural declaration admission
and complete initial-program admission remain open.
The [closing-plan identity example](SourceAnnotatedClosingIdentity.lean) proves
that equal erased certificates alone cannot identify the actual annotations.
Certificates now retain the actual capture and closing-plan construction;
[annotated capture identity](SourceAnnotatedCaptureIdentity.lean) preserves that
connection through stack transformations.
[Annotated return preservation](KERNEL.md#annotated-returns-and-retirement) now
covers every raw value-return step, including retirement and exact owner-demand
consumption. Current Core already retains structural node types,
so this is a representation gap in the experiment rather than an identified
absence of Core metadata.

## Objective and boundary

Replace the one-shot kernel's named admissibility predicates with structural
judgments and prove capture/recomposition plus ownership preservation. The
kernel must include recursively live clause captures, exact interpretation
selection including builtin blockers, retained resource access, outside pending
ticket consumption, armed cleanup, and protected running completion.

Multishot continuations, escaping continuations, suspension and asynchronous
execution remain later extensions. Ordinary expression typing remains a
required proof layer within the one-shot target. The
[Core correspondence assessment](KERNEL.md#current-core-correspondence-status)
records agreement, proof gaps and mismatches; alignment changes are outside the
current work. Any use
of annotated frames must be explicit about the obligation to derive their
annotations from expressions.

## Proof construction

1. Define a recursive control forest, exact cut constructors, and typed stack
   composition. Prove decomposition, recomposition, and ownership accounting
   for arbitrary finite control forests, without bounding nesting depth.
2. Define accessible support separately from recursively owned resources.
   Replace capture/restoration admissibility with structural support judgments
   and prove support transport.
3. Define pending ticket consumption and structural close-plan generation.
   Check each cleanup action against ordered interpretation at its closing
   position. Prove no loss of outside scheduled consumption in the supplied
   annotations, exact accounting of closed owners, and protection of running
   completion.
4. Define raw one-shot machine transitions and their structural well-formedness
   judgment. Prove ownership preservation across the kernel transitions, rather
   than assuming safety in each transition's premise.
5. Check positive and negative examples from current semantic obligations,
   audit theorem assumptions, and reconcile the mathematical presentation in
   DN-0033 with the proved definitions.

## Checked evidence

The control theorem names below are in namespace `Ash.OneShot` in
[OneShot.lean](OneShot.lean). The proofs cover arbitrary finite control forests,
including recursively owned live captures.

| Result | Checked theorem or judgment |
| --- | --- |
| Unique nearest exact cut and its decomposition | `cut_unique`, `cut_decompose`, `SourceCut` |
| Typed capture and full clause-prefix restoration | `capture_type_decomposition`, `resume_full_type_recomposition` |
| Preserved accessible support and private payload exclusion | `capture_preserves_support`, `resume_preserves_support`, `captured_private_access_cannot_cross` |
| Capture/resume/discard preserve all fields of the annotated control invariant | `capture_wellFormed`, `resume_wellFormed`, `discard_wellFormed` |
| Resource-bearing instances satisfy preservation premises | `Examples.capture_and_resume_are_inhabited`, `Examples.resource_discard_wellFormed` |
| Recursive close accounts for owners and excludes protected completion | `close_owner_accounting`, `close_plan_unique`, `close_excludes_protected` |
| Every invoked cleanup has no retained structural ticket uses | `close_actions_ticket_closed` |
| Discard cannot erase annotations requiring an outside ticket | `discard_preserves_outside_consumption` |
| Materialized close control preserves accessible support | `close_plan_preserves_support`, `discard_control_preserves_support` |
| Each planned invocation retains its original exact request interpretation | `close_plan_preserves_interpretation`, `discard_invocation_preserves_interpretation` |
| Admitted discard constructs a raw step preserving ledger and support jointly | `admitted_discard_joint_preservation` |
| Each raw ownership event conserves created, live, and discharged owners | `flow_accounting` |
| Every finite event sequence preserves the lifetime ledger | `steps_preserve_ledger` |
| No duplicate completion event or live/completed alias | `ledger_no_double_completion`, `ledger_no_live_completed_alias` |

[Expressions.lean](Expressions.lean) adds administrative expressions and
syntax-derived retained dependencies in namespace `Ash.OneShot.Syntax`.

| Result | Checked theorem |
| --- | --- |
| Closed-value substitution bounds resource dependencies and preserves free ticket membership | `binding_substitution_support`, `binding_substitution_pending` |
| Binding return preserves support and resolves an otherwise closed lexical environment | `binding_return_preserves_support_and_environment` |
| A fresh resource binder cannot hide an inserted resource dependency at a free variable occurrence | `Expr.subst_retains_inserted_resource` |
| A cut through a suffix retaining an outside ticket cannot be discarded | `pending_suffix_blocks_discard` |
| A closed cleanup value has no free structural-ticket annotation | `cleanup_frame_ticket_barrier` |
| Local expression reductions introduce no new retained dependencies | `local_step_dependencies` |

These are dependency membership and support results, not pathwise ticket-use
checking or full expression preservation. Binding-frame use requires lexical
values to have been substituted, leaving only the initializer parameter free.
Local substitution steps also check that resource binders cannot capture the
inserted value's resource identities. Automatic freshening remains unproved.
Tagged effect arguments retain nested resource identities; they do not model
the complete Core kind and type system.

[Usage.lean](Usage.lean) adds structural one-shot usage in the same namespace.
Resume and disposal permissions are independent fields. Sequential forms thread
availability, branches require equal outputs, function bodies receive no
enclosing ticket, and each nested clause must consume its own ticket.

| Result | Checked theorem or judgment |
| --- | --- |
| Structural usage and clause completion | `Uses`, `ClausesUse` |
| A consumed state cannot become available again | `use_state_monotone` |
| Substituting a usage-checked value preserves usage | `usage_substitution` |
| Local expression reduction preserves usage | `local_step_preserves_usage` |
| Every syntactic explicit-use path satisfies the independent one-shot protocol | `usage_path_sound` |
| A consuming path has exactly one event of a permitted kind | `consuming_paths_exactly_once` |
| Usage output is unique | `usage_output_unique` |
| A suffix required to consume an outside ticket blocks disposal across its binding frame | `consuming_suffix_blocks_discard` |

`SyntaxPath` describes strict children and a choice of conditional arm. It does
not expand function calls, operation dispatch, or nested clauses. The latter
have their own usage derivations. These path theorems therefore establish the
structural discipline, not exactly-once use along complete execution traces.
Permissions are supplied for administrative ticket binders. The dispatch layer
below connects them to individual runtime capture and consumption steps. The
usage-execution layer preserves the discipline through all locally admitted
transitions; source-derived admission remains open. Disposal permission
alone does not establish that a capture can be closed.

[Execution.lean](Execution.lean) adds an expression-bearing administrative
machine in namespace `Ash.OneShot.Execution`. Its control retains pending
expressions, handler clauses, cell payloads, cleanup values, saved results, and
lexical ticket scopes. `Scope.translate` fails for an unresolved free ticket;
a source binder cannot silently become an unrelated dynamic owner.

| Result | Checked theorem or judgment |
| --- | --- |
| Concrete capture preserves the actual pending syntax and projects to the exact abstract cut | `handler_cut_reconstructs`, `handler_cut_erases` |
| Concrete close control projects to the proved raw close plan | `make_plan_erases`, `close_control_erases` |
| Every raw expression transition projects to an ownership event | `raw_step_erases` |
| Every finite execution with fresh allocation preserves the lifetime ledger | `run_steps_preserve_ledger` |
| Cleanup start retains both action access and saved-result access | `start_cleanup_preserves_retained_support` |
| An actual callback request captures and resumes running cleanup before returning its saved result | `Examples.cleanup_outward_capture_execution` |
| Admitted disposal executes a callback that reads a retained cell before its release | `Examples.cell_cleanup_disposal_is_admitted`, `Examples.disposal_reads_cell_before_release` |

The machine uses substituted lexical values and already-instantiated resource
names. Fresh source instantiation, handler-activation uniqueness, whole-stack
expression typing, request-summary inference, and joint usage/support admission
remain unproved. Context-port derivation is established in the typing layer
below. Builtin operation keys `0` and `1` denote read and write only within
this prototype; correspondence with authenticated Core operations is separate.

[Access.lean](Access.lean) combines current-expression dependencies with retained
control support. `AccessChecks` inspects the pre-configuration: a released
resource must be absent from the returned value; a captured operand must be
supported outside the selected segment; disposal must satisfy `Discardable`
for the actual materialized plan and surviving control. These are explicit
local premises, not a source admission algorithm.

| Result | Checked theorem or judgment |
| --- | --- |
| Each raw expression step satisfying the local checks preserves expression and retained-control support | `raw_step_preserves_access` |
| Every finite locally admitted execution preserves support and the lifetime ledger jointly | `access_run_joint_preservation` |
| A closed locally admitted execution cannot retain a completed resource in its current expression | `access_run_no_completed_reference` |
| The same exclusion holds for retained frames, including dormant captures and saved cleanup results | `access_run_no_completed_retained_reference` |
| The raw dangling-reference release is rejected, and its final state is unreachable from supported initial configurations | `Examples.dangling_reference_release_rejected`, `Examples.dangling_reference_result_unreachable` |
| Outward capture and resumption during cleanup satisfy the local access checks throughout execution | `Examples.cleanup_outward_capture_joint_execution` |
| Releasing an inner resource can return a reference to a still-live outer resource | `Examples.outer_reference_joint_invariant` |
| Acquisition and release of a resource have a locally admitted execution | `Examples.scope_releases_unit_joint_execution` |

`AccessRunSteps` retains an independent raw execution and requires the local
checks at each reached pre-configuration. The theorem does not establish that
checking only the initial source expression supplies those checks. The
no-completed-reference corollaries use empty ambient support; a nonempty ambient
list is an external support assumption, not proof of a resource lifetime.

[Typing.lean](Typing.lean) adds annotated monomorphic expression typing,
operation-clause coverage, and syntax-derived context ports. The proof
fragment's `Ty` now includes cell references and functions with latent requests
and retained-resource annotations. These are internal proof annotations, not
new source syntax or a change to Core's type representation.

| Result | Checked theorem or judgment |
| --- | --- |
| Actual value dependencies are bounded by the annotated type, including closure captures | `typed_value_support` |
| Typed resource returns satisfy the local no-escape check | `typed_return_excludes_resource` |
| A typed payload with supported type annotations satisfies outward boundary support | `typed_payload_at_boundary` |
| Instance-bounded signatures provide a restricted sufficient shortcut for payload support | `typed_payload_crosses_cut` |
| Typed focus derives child typing and context input/output ports | `typed_focus_decomposition` |
| Plugging a correctly typed child reconstructs a typed expression | `context_plug_typed` |
| Focus constructs an actual machine frame whose ports compose with the typed outer stack | `focus_constructs_typed_frame` |
| Typed values have the expected unit, boolean, integer, reference, or function form | `typed_unit_value`, `typed_boolean_value`, `typed_integer_value`, `typed_reference_value`, `typed_function_value` |
| Handler coverage provides an actual clause selection with checked operand, resumption, and answer types | `covered_operation_selects_clause`, `selected_clause_typed` |
| Every scheduled disposal callback has a unit application derivation in its local effect context | `disposal_invocation_typed` |
| Every invocation request is outward or resolves to an actual retained builtin in its remaining suffix | `plan_request_is_outward_or_interpreted` |
| Cell-reading disposal has empty outward effects when the cell remains until after the callback | `Examples.pure_cell_disposal_typed` |

`Typed` checks all administrative expression forms, but type/effect preservation
for their complete execution remains unproved. Immediate and latent effect lists
are membership bounds; they are not the full Core row/lacks calculus. Resource
scopes exclude their identity from both result annotations and residual effects.
Closure support includes dependencies of retained lexical values. Source
instantiation, polymorphism, and environment realization remain necessary.
Closed typed substitution is established in the layer below.

`SignatureSupported` is a restricted sufficient condition, not a universal law
of Core signatures. Callable payloads may retain resources absent from their
effect instance. `typed_payload_at_boundary` covers that case when their
annotated support is available at the actual boundary. A positive callable
example and a rejection of the shortcut demonstrate the distinction.

Ticket types carry separate resume and disposal effect contracts. `PlanTyped`
checks each actual close-plan invocation against its declared function type,
the builtin cells in its remaining materialized suffix, and the outward close
bound. A callback cell request need not be an outward effect of the complete
close: the cell-reading example has an empty outward bound. A missing cell or
release before invocation rejects that bound. `DisposalTyped` joins these checks
with raw plan construction and structural `Discardable`. This supplies local
invocation typing and suffix interpretation, not yet preservation
of effects during arbitrary callbacks or proof that all reachable captures
satisfy the ticket contracts.

[Substitution.lean](Substitution.lean) connects the annotated typing judgments
to closed substitution and the existing local reduction relation.

| Result | Checked theorem |
| --- | --- |
| Changing irrelevant environment entries preserves expression and clause typing | `typed_environment_congr`, `clauses_environment_congr` |
| A closed typed value can be checked under another ordinary environment | `closed_value_environment_transport` |
| Substitution converts a variable's lexical support into actual syntax support without enlarging the annotation | `substitution_support_bound` |
| Closed typed substitution preserves the exact annotated expression and clause types | `typed_substitution`, `clauses_typed_substitution` |
| Binding return, beta reduction, branch selection, and local contexts preserve result types and immediate effect bounds | `local_step_preserves_types` |
| Local reduction preserves types, structural usage, and available resource support jointly | `local_step_preserves_joint` |
| The selected operation clause is typed after installing its closed operand | `selected_clause_substitution_typed` |

The proof handles ordinary binder shadowing and preserves closure support lists
exactly. Positive examples substitute a resource handle into a capturing
closure, drop a shadowed handle from an identity closure, and instantiate the
cleanup example's selected clause. A counterexample has a typed substitution
whose `ResourceFresh` condition fails. Typing preservation therefore does not
replace administrative resource-name hygiene.

`LocalStep` covers local expression reduction, including handler-body contexts;
it does not perform operation dispatch, capture, resumption, disposal, scope
entry/exit, or cleanup-owner completion. The joint theorem here does not extend
the finite machine ledger theorem to full type/usage preservation. A complete
machine invariant must preserve the correspondence between static clause
binders and dynamic ticket owners and derive all reachable-cut admissions.

[Dispatch.lean](Dispatch.lean) connects those local results to capture,
resumption, and entry into disposal on the actual expression-bearing machine.

| Result | Checked theorem or judgment |
| --- | --- |
| Exact handler selection fixes the captured segment's answer port | `handler_cut_ports` |
| Selected clause substitution preserves its independent usage check | `selected_clause_substitution_usage` |
| Static type/use scopes and the runtime scope name the same lexical binder | `ScopeAgreement` |
| A live or spent active clause occurrence matches the static ticket's state and ports | `TicketBinding` |
| Distinct ticket names make the binding state unique and exclude reuse of a spent owner | `ticket_binding_state_unique`, `spent_binding_blocks_available` |
| Covered dispatch constructs a fresh capture with typed/used clause entry, matching ticket binding, ports, support, and ledger | `typed_capture_step` |
| Checked resumption restores the capture and clause prefix, consumes the binding, and preserves operand typing, usage, ports, support, and ledger | `typed_resume_step` |
| Checked disposal enters the actual close plan with a spent binding, typed unit, usage, ports, support, and ledger | `typed_discard_step` |
| Running cleanup has a checked capture/resume pair with distinct lexical and runtime ticket identities | `DispatchExamples.cleanup_capture_resume_checked` |
| Cell-reading cleanup has checked disposal entry with an empty outward close bound | `DispatchExamples.cell_discard_entry_checked` |

These constructions derive the operation-result annotation from the signature
and the answer port from the selected handler. They do not prove preservation
from a fully typed source configuration: retained stack expressions, old lexical
environments, request availability, and future continuation effects still need
a shared invariant. `TicketBinding` describes an active occurrence with matching
ports; it does not establish uniqueness of names, nearest-owner lookup, or the
saved continuation's declared effects. A spent occurrence checks its answer
port; input, effects, and permissions remain historical annotations. The
existing distinct-name invariant makes the state unique. A checked
counterexample shows why the ledger alone cannot replace that invariant: the
same stack can contain live and spent occurrences of one name without
duplicating live ownership. `Fits` checks supplied ports, not the
typing of every retained expression. Capture still requires administrative
hygiene and operand-type support at the actual outside boundary.

Disposal uses the existing structural `DisposalTyped` judgment for the actual
capture and surviving prefix. Its theorem concerns entry into closing, before
callbacks run. `PlanTyped` establishes callback types and local effect bounds;
it does not establish their independent usage checks or preservation throughout
callback execution. Negative examples reject a mismatched capture input port
and disagreement between the static type and usage binders.

[Names.lean](Names.lean) preserves ticket-name and handler-activation history
across finite executions, including spent markers and dormant captures.

| Result | Checked theorem or judgment |
| --- | --- |
| Every raw transition bounds name multiplicity by prior names and actual allocations | `raw_step_name_bounds` |
| Raw disposal cannot invent ticket names | `raw_plan_ticket_name_bound` |
| Allocation-history bounds and the ownership ledger establish recursive distinct names | `NameHistory`, `history_gives_distinct_names` |
| Finite execution preserves name history and the ownership ledger | `NamedSteps`, `named_steps_preserve` |
| Reachable ticket bindings have one state per owner | `named_execution_has_unique_ticket_state` |
| Owned ticket occurrences and true spent markers account for all retained ticket names | `ticket_name_count_accounting` |
| A spent binding appears in the completion record | `spent_binding_was_discharged` |
| A consumed binding cannot become available in any later execution | `consumed_binding_never_available` |
| Previously allocated handler activations cannot be allocated again | `named_execution_never_reallocates` |
| One execution preserves name history, ledger, and locally admitted resource support together | `NamedAccessSteps`, `named_access_steps_preserve` |
| Running cleanup completes along a trace carrying those joint checks | `NameExamples.cleanup_execution_has_joint_checks`, `NameExamples.cleanup_final_joint_invariant` |

`NamedStep` records fresh handler activations alongside the existing fresh owner
events. The activation classifier records actual handler entry; restoring a
captured handler does not allocate it again. Freshness is checked against the
entire history, including exited activations. A raw reentry with a previously
used activation is exhibited and rejected by that check. The conflicting
live/spent example from the dispatch layer fails the name-history bounds.

True spent markers exclude retirement frames, which still own tickets awaiting
discharge. Combining their count with the name and ownership histories places
each spent binding in the completion record. Monotone completion then excludes
a later available binding even after the spent frame disappears. The theorem
assumes valid initial histories; it does not reconstruct events preceding an
arbitrary initial state. The complete cleanup example starts with empty records.

These proofs require fresh allocation; they do not establish a source
instantiator or allocator that supplies it. The combined access theorem still
requires the existing local access checks at each reached pre-configuration.
The usage-execution layer below joins continuation usage to these same
executions. Joint expression/stack typing, effect interpretation, and
source-derived admission remain open.

[Retained.lean](Retained.lean) checks the actual code stored in frames and
captures. Its historical ticket table records input and answer types; it grants
no ownership or continuation permission. Immediate effect bounds remain
existential in this layer, so it does not establish effect availability.

| Result | Checked theorem or judgment |
| --- | --- |
| Actual contexts, clauses, cleanup functions, and saved results have type derivations | `FrameTyped`, `StackTyped`, `ConfigurationTyped` |
| Handler cuts preserve typing of the selected handler, capture, and outside stack | `handler_cut_retains_typing` |
| Every raw transition starting from a closed value preserves configuration typing | `raw_value_step_preserves_typing` |
| Resumption restores typed captured code above the complete clause prefix | `resume_preserves_configuration_typing` |
| A typed request and retained handler construct a typed capture with an extended ticket table | `capture_constructs_typed_configuration` |
| A table backed by allocation history has no entry for a fresh ticket owner | `fresh_owner_has_no_ticket_signature` |
| Disposal preserves types of materialized callbacks and retirement frames | `make_plan_retains_types`, `discard_preserves_configuration_typing` |
| A typed cell return excludes its local resource identity | `typed_cell_return_excludes_identity` |

Checked examples type capture, resumption, and completion of running cleanup,
and materialization of a disposal callback that reads a retained cell. Negative
examples show that matching ports alone can admit a non-callable cleanup or a
saved result of the wrong type. These are rejected by `FrameTyped`.

This layer does not prove preservation for every raw transition. Non-value
entry rules permit arbitrary administrative annotations. The following layer
constructs valid entries. The joint layer below connects their types to effects,
usage, resource support, and name history through those constructed events.

[Entries.lean](Entries.lean) derives administrative entry annotations and lexical
premises from expression and retained-code typing. It also proves preservation
for ordinary computation and the fixed builtin integer-cell protocol.

| Result | Checked theorem or judgment |
| --- | --- |
| Free ticket uses name the current static binder; typed clauses have no free outer tickets | `typed_tickets_scoped`, `typed_clauses_have_barrier` |
| Checked dependency names translate to actual runtime owners | `scope_translates_scoped_dependencies` |
| Free ordinary variables are bound by the typing environment | `typed_variables_bound`, `typed_clauses_variables_bound` |
| Typed values in the empty environment are closed; typed parameter bodies satisfy lexical substitution hygiene | `typed_value_is_closed`, `typed_body_is_closed_except` |
| Focus constructs its actual frame, deriving ports and pending owner translation | `focus_constructs_typed_configuration` |
| Handler, cell, and cleanup entry derive answer ports, clause barriers, and cleanup request annotations | `handler_entry_constructs_typed_configuration`, `cell_entry_constructs_typed_configuration`, `cleanup_entry_constructs_typed_configuration` |
| Bind and application construct actual typed steps under resource-name freshness | `bind_constructs_typed_step`, `beta_constructs_typed_step` |
| Branch selection preserves configuration typing | `branch_preserves_configuration_typing` |
| Source and retained-handler typing derive capture's lexical premises | `typed_capture_lexical_admission` |
| Exact cell updates preserve retained-code types, and builtin reads/writes preserve configuration typing | `cell_update_preserves_stack_typing`, `cell_read_preserves_configuration_typing`, `cell_write_preserves_configuration_typing` |

The handler-entry result records the chosen activation explicitly, so a later
allocation proof can use its freshness. A positive focus example retains a
pending use of runtime owner 3 from lexical binder 9. Negative examples reject
a different free ticket and exhibit why arbitrary raw handler annotations and
arbitrary builtin signatures cannot satisfy a general preservation theorem.

These are type-directed constructions and value-type preservation results.
They do not establish the shared effect/usage invariant, fresh resource
instantiation, relative progress, or correspondence to full Core. Source
checking must supply those additional facts without assuming future safety.

[Effects.lean](Effects.lean) connects retained-code types to incoming and outward
effect bounds on the same ordered stack. Historical continuation contracts
record separate resume and disposal bounds. `EffectScope` requires the actual
runtime owner and the static ticket to agree on these bounds as well as types.

| Result | Checked theorem or judgment |
| --- | --- |
| Actual frame code checks against its incoming/outward effect interface | `EffectFrame`, `EffectStack`, `EffectConfigurationTyped` |
| Ordered segments compose and decompose at a common effect bound | `effect_stack_append`, `effect_stack_decompose` |
| The selected handler determines the capture's outward interface | `handler_cut_effect_decomposition` |
| Capture constructs a typed configuration and a fresh historical effect contract | `capture_constructs_effect_configuration` |
| Resumption preserves connected types/effects through the entire clause prefix | `resume_preserves_effect_configuration` |
| A typed close plan materializes its local builtin providers and outward requirements | `close_plan_has_effect_interface` |
| Disposal with the matching plan contract preserves connected types/effects | `discard_preserves_effect_configuration` |
| Every raw closed-value transition preserves the type/effect judgment | `raw_value_step_preserves_effect_configuration` |
| Focus and handler/cell/cleanup entry construct type/effect-checked frames | `focus_constructs_effect_configuration`, `handler_entry_constructs_effect_configuration`, `cell_entry_constructs_effect_configuration`, `cleanup_entry_constructs_effect_configuration` |
| Ordinary computation and fixed builtin cell operations preserve connected types/effects | `bind_preserves_effect_configuration`, `beta_preserves_effect_configuration`, `branch_preserves_effect_configuration`, `cell_read_preserves_effect_configuration`, `cell_write_preserves_effect_configuration` |
| Every current request resolves on the active stack or belongs to the outward bound | `current_request_is_interpreted_or_exported`, `current_request_has_interpretation` |

A nested-handler example captures a suffix requiring a second effect, resumes,
and reaches its outer interpretation through the inner handler and spent ticket.
Its raw trace records capture and consumption of the same owner. Another example
admits a matching dormant handler with no current effect requirement, but rejects
using that handler to satisfy an active request. Cell-reading disposal retains
its local builtin while exporting an empty closing row.

Live boundaries currently require both declared resume and disposal bounds,
irrespective of usage permissions. Capture assigns both fields the handler's
residual because `ClausesTyped` uses that contract. These are sufficient bounds;
distinct minimal contract inference is not proved. Exact instance resolution
does not establish operation-level progress. Effect-checked disposal still needs
the independent `Discardable` judgment. The joint layer below combines these
transition results with support, ownership, and usage. Complete source-derived
admission and Core correspondence remain open.

[Demand.lean](Demand.lean) derives local scheduled consumption from usage proofs.
`ContextUses`, `focus_decomposes_usage`, and `context_plug_preserves_usage` split
and recompose the usage of actual strict contexts. `CodeDemand` connects lexical
usage rights to a runtime owner table; `translated_demand_membership` proves that
its demand has the same owner membership as translated free-ticket dependencies.
This is a membership theorem, not a multiplicity theorem: alternative branches
can contain two occurrences while demanding one consumption per path. Examples
accept resume/dispose alternatives and reject sequential double consumption.
Latent function bodies and nested clauses remain usage checked even when the
current fragment has no outer demand.

Local code demands do not establish whole-control accounting or accessibility.
The following layer supplies those separate judgments.

[ControlUsage.lean](ControlUsage.lean) checks scheduled consumption across current
and retained code. `FrameDemand` checks actual contexts, clauses, callbacks, and
saved values. `StackUsage` checks active accessibility recursively, including
inside dormant captures. `ConfigurationUsage` requires current and retained
demands to be a permutation of uniquely owned tickets. Historical scope mappings
remain available after consumption; only actual demands require live access.

| Result | Checked theorem or judgment |
| --- | --- |
| Retained code checks usage and active accessibility | `FrameDemand`, `StackUsage`, `ConfigurationUsage` |
| Structural ticket ownership projects to the existing ownership inventory | `owned_tickets_project`, `owned_tickets_unique` |
| Stack segments compose and decompose with their external ticket interface | `stack_usage_append`, `stack_usage_decompose`, `handler_cut_usage_decomposition` |
| Removing an external name requires its absence from all subtree demands | `stack_usage_remove_unused_external` |
| Capture preserves usage with fresh registry insertion and the selected clause's permissions | `capture_preserves_configuration_usage` |
| Full-prefix restoration preserves demand balance and active accessibility | `resume_preserves_configuration_usage` |
| Actual close plans retain checked callbacks and registered retirement owners | `make_plan_retains_usage`, `close_control_usage` |
| Disposal preserves configuration usage under structural internal-use checking | `discard_preserves_configuration_usage` |
| A value cannot return through a live, unconsumed clause boundary | `live_clause_cannot_return_unconsumed` |
| Every raw closed-value transition preserves configuration usage | `raw_value_step_preserves_configuration_usage` |

Retirement contributes one consumption while exposing no active ticket. Disposal
uses demand-to-dependency membership, internal-use checking, active accessibility,
and uniqueness to derive that captured demands are exactly the captured owned
tickets. It then replaces those demands with the actual plan's retirement
demands. Callback usage remains checked when its outer demand is empty.

Examples restore a nested live prefix whose dormant capture retains an outside
owner's demand, reject a current resume hidden inside a dormant capture despite
balanced counts, and check existing cleanup-capture and cell-disposal states.
The nested resumption constructs an actual raw step and uses distinct handler
activation identities. Another example disposes an internally live ticket,
replaces its pending resume with retirement, and preserves usage through the
retirement step. These are administrative configurations, not a source-admission
or full-trace theorem.

Disposal in this layer requires actual `makePlan` and structural `InternalUses`;
resource support, exact closing interpretations, and effect contracts remain
independent obligations. The following layer joins usage to the existing
allocation and access checks for finite executions.

[UsageExecution.lean](UsageExecution.lean) covers every raw transition, including
focus, ordinary computation, entries, and builtin cell reads and writes. Its
registry update is a function of ordinary event and configuration data. Capture
installs the selected clause binder's permissions under a fresh ticket identity;
other steps retain the table. `UsageRegistryHistory` states that the table's
domain is exactly the historically issued tickets, including consumed tickets.
This is domain correspondence, not agreement with the separate type/effect tables.

| Result | Checked theorem or judgment |
| --- | --- |
| Every raw transition preserves usage under structural allocation/disposal premises | `raw_step_preserves_configuration_usage` |
| Historical allocation and existing access checks supply those premises | `usage_checks_from_allocation_and_access` |
| Registry updates preserve correspondence with issued ticket history | `raw_step_preserves_usage_registry_history` |
| The same admitted finite execution preserves ledger, names, support, usage, and registry history | `named_access_steps_joint_usage` |
| Cleanup capture/resumption instantiates the joint theorem from empty histories | `UsageExecutionExamples.cleanup_execution_joint_usage` |
| Disposal runs a callback that reads its retained cell before release, satisfying the joint theorem | `UsageExecutionExamples.cell_disposal_joint_usage` |

The first execution starts with a source-shaped expression and empty control,
ownership history, activation history, and registry. The second starts at an
explicitly checked administrative disposal state with an existing live ticket,
armed cleanup, and owned cell. It checks actual close-plan support and exact
builtin selection, invokes the callback, reads the cell, and then discharges
cleanup, resource, and close obligations. Both examples establish all initial
premises and the actual `NamedAccessSteps`; neither assumes future usage safety.

Every reached `AccessChecks` remains an explicit execution premise. The next
layer joins type/effect and usage contracts for individual transitions and
concrete executions. Deriving all boundary checks from source admission,
constructing fresh source instantiation, proving progress, and establishing
Core correspondence remain open. The existential final registry has a concrete
update at each step; it does not supply an executable allocator.

[Joint.lean](Joint.lean) stores one `TicketRecord` per runtime owner. Its effect
contract and consumption permissions have separate projections and independent
checking judgments. `Valid` combines the ledger, name history, resource support,
expression/stack types and effects, continuation usage, and exact registry-domain
history for one configuration. Capture allocates both projections together for
the actual selected clause, recording its type/effect contract and its declared
usage permissions. Consumed tickets retain their historical records.

| Result | Checked theorem or judgment |
| --- | --- |
| One ticket record supports independent contract and usage checking | `Joint.Registry`, `Joint.Valid`, `Joint.effects_insert`, `Joint.usage_insert` |
| Closed annotated expressions initialize the complete invariant from independent checks | `Joint.initial_configuration_valid` |
| Type-directed capture preserves the complete invariant along the same named/access-checked event | `Joint.capture_constructs_joint_configuration` |
| Resumption and structurally admitted, effect-checked disposal preserve that invariant | `Joint.resume_preserves_joint_configuration`, `Joint.discard_preserves_joint_configuration` |
| Every actual closed-value transition preserves all facets | `Joint.closed_value_preserves_joint_configuration` |
| Ordinary computation and exact builtin operations preserve all facets | `Joint.ordinary_step_preserves_joint_configuration` |
| Focus and entry construct annotations that preserve all facets | `Joint.focus_constructs_joint_configuration`, `Joint.handler_entry_constructs_joint_configuration`, `Joint.cell_entry_constructs_joint_configuration`, `Joint.cleanup_entry_constructs_joint_configuration` |
| One registry and one actual execution retain the complete invariant through resource-bearing disposal and callback evaluation | `Joint.Examples.resource_disposal_joint_execution` |
| A resource scope enters and releases from a checked expression with empty histories | `Joint.Examples.source_cell_scope_joint_execution` |
| Type/effect contracts cannot confer a denied disposal permission | `Joint.Examples.disposal_effects_do_not_confer_permission` |

The disposal example begins at a fully checked administrative live capture. It
runs cleanup application, ordinary reduction, type-directed focus, a builtin
read of cell 4 containing 17, and release. The final state has no outstanding
owner and retains the same historical registry. The separate source-shaped
resource example starts from empty control and histories. A negative example
keeps the effect contract unchanged but removes disposal permission; effect
typing still holds while `Valid` is impossible.

These results cover each transition family by preservation or type-directed
construction. They do not prove preservation for arbitrary annotations selected
by `RawStep`, nor yet define a complete admitted execution relation whose
annotation and boundary premises follow from source checking. Capture still
requires current cut access and substitution hygiene; disposal also requires
actual close-plan support and its registered effect bound. Fresh allocation
remains explicit. The initialization theorem checks a closed annotated
expression; it does not certify every future captured cut. Progress and Core
correspondence remain unproved. General theorems parameterize ambient resources
and outward requests; the two concrete executions use empty ambient and outward
interfaces.

[Admission.lean](Admission.lean) derives several previously explicit local
access checks. Result typing justifies resource release; expression shape
justifies focus and ordinary computation. A selected request can check its
operand type's resource support against the actual outside boundary.
`SignatureSupported` is a restricted sufficient shortcut, not a mandatory
condition: a checked callable payload retains an outside cell even though its
effect instance does not name that cell.

Disposal needs more than the six fields of `Joint.Valid`. A checked
administrative state can contain a running cleanup inside its dormant capture,
for which `makePlan` returns `none`. This is a counterexample to plan existence
following from that invariant, not a source-reachable counterexample or an
inconsistency result. The existing `AccessChecks.discard` field is conditional
on a successful plan; it does not itself supply plan existence.

`OpenCloses` and `OpenRequests` structurally check a plan against an outside
resource/request interface. Each callback uses either the same local target in
the original and materialized prefixes, or a request unresolved in both
prefixes and declared outward. `PreparedDisposal` combines an actual successful
plan, its effect typing, this closing judgment, and internal ticket-use evidence.
Its outside resources are computed from retained dependencies minus captured
ownership. For a closed joint state, existing support and effect checks supply
the outside interface at the actual live boundary. The certificate therefore
materializes disposal compatibility even with additional clause control.

The comparison uses the same current caller on both sides. Added caller
control can change an outward interpreter; the theorem does not freeze its
capture-time identity. These certificates are sufficient structural evidence;
completeness, source inference, and their propagation through future capture
are not proved. Certificates contain code and proofs, not authority to execute
without the unique live owner. Positive examples check both a cell retained in
the plan suffix and a genuinely external cell. The protected running capture
cannot have a `PreparedDisposal` certificate.

`PreparedCaptures` stores these certificates structurally throughout retained
control, requiring one only when the live owner's record permits disposal.
Together with the closed joint invariant it derives the current discard's
access checks. It accepts a resume-only capture of running cleanup without
requiring a disposal plan, and rejects that capture when disposal is permitted.
Source establishment remains open. The execution layer below now proves local
preservation, with a new certificate check at each new capture.

| Result | Checked theorem or judgment |
| --- | --- |
| Release, focus, and ordinary steps derive their access checks | `Admission.value_access_checks`, `Admission.focus_access_checks`, `Admission.ordinary_access_checks` |
| General callable payloads use the actual outside type boundary | `Admission.selected_type_boundary_access_checks`, `Admission.Examples.general_callable_payload_is_admitted` |
| Open closing certificates materialize under a supplied outside interface | `Admission.open_closes_materialize` |
| Closed joint states supply a prepared disposal plan's outside interface | `Admission.prepared_disposal_at_live_boundary` |
| The current joint invariant does not imply plan existence | `Admission.DisposalGap.joint_invariant_does_not_establish_disposal_readiness` |
| Retained certificates derive access checks for a closed current discard | `Admission.PreparedCaptures`, `Admission.prepared_discard_access_checks` |

[Progress.lean](Progress.lean) proves completion and resumption progress directly
from the existing invariant. A value state either has empty control or takes an
actual named/access-checked step preserving `Joint.Valid`. Canonical forms
establish unit values for cleanup completion, close completion, and retirement.
Usage balance and unique ownership rule out returning through a live boundary:
neither its saved capture nor its caller can consume that boundary's outstanding
ticket. A resume with a value operand derives lexical resolution and an actual
live boundary from current usage and active accessibility, then restores the
whole clause prefix. Neither theorem assumes a next transition or an explicit
access check.

For a closed state with `PreparedCaptures`, `prepared_discard_progress` also
derives the live boundary, actual plan, outside compatibility, and a fresh close
owner from finite history. It constructs an admitted step preserving
`Joint.Valid`; its conclusion does not include `PreparedCaptures`. The next
layer strengthens this result. A resource-bearing example inhabits both
preconditions.

| Result | Checked theorem |
| --- | --- |
| A valid value state returns or steps with joint preservation | `Progress.value_progress` |
| A value cannot return through an unconsumed live continuation | `Progress.value_cannot_return_through_live` |
| Empty control has discharged every issued owner exactly once | `Progress.terminal_ledger_settled` |
| Ready resumption derives the actual live boundary and steps with joint preservation | `Progress.resume_value_progress` |
| Structurally prepared disposal steps with joint preservation | `Progress.prepared_discard_progress`, `Progress.Examples.resource_disposal_progress` |

These are progress cases, not the general progress theorem. Value and resumption
allow ambient/outward parameters; prepared disposal requires closed interfaces.
They do not prove termination. General
capture, disposal, allocation, and source-instantiation readiness still need
to follow from a preserved source admission judgment.

[PreparedExecution.lean](PreparedExecution.lean) preserves `PreparedCaptures`
through every raw transition. Immutable registry extension preserves old
records and their certificates. `AllocationPrepared` checks a new capture's
concrete plan only when its record permits disposal; transitions allocating no
ticket need no new certificate. The proof decomposes and recomposes actual
control, retains certificates inside dormant captures, and covers active cell
updates and close-plan materialization. It does not assume the desired
post-state readiness.

`Ready` combines `Joint.Valid` and `PreparedCaptures`. The stronger value,
ready-resumption, and closed-disposal progress theorems now return a `Ready`
successor. Ordinary steps preserve it too. Type-directed capture exposes its
actual named transition and valid chosen contract unconditionally, then
establishes successor readiness from a certificate at that precise contract's
closing effect bound. This is a local capture obligation, not a requirement to
support every possible stronger effect bound.

| Result | Checked theorem or judgment |
| --- | --- |
| Every actual transition preserves retained certificates under the stated local allocation check | `PreparedExecution.raw_step_preserves_prepared`, `PreparedExecution.AllocationPrepared` |
| Closed checked expressions initialize the combined state judgment | `PreparedExecution.ready_initial_configuration` |
| Value, ready resumption, and prepared disposal progress preserve readiness | `PreparedExecution.ready_value_progress`, `PreparedExecution.ready_resume_value_progress`, `PreparedExecution.ready_discard_progress` |
| Ordinary computation and exact builtins preserve readiness | `PreparedExecution.ready_ordinary_step` |
| Actual capture validates its new certificate at the chosen contract | `PreparedExecution.ready_capture_constructs` |
| Concrete capture and resource disposal inhabit the stronger conclusions | `PreparedExecution.Examples.pure_capture_preserves_ready`, `PreparedExecution.Examples.resource_disposal_preserves_ready` |

The new examples start at checked administrative states. They do not claim
source reachability. Initializing `Ready` also does not check future capture
compatibility: deriving every new certificate, payload boundary check, and
substitution/freshness premise from source checking remains open. No general
progress, universal joint execution-safety, or Core correspondence theorem is
claimed.

[FreshnessGap.lean](FreshnessGap.lean) gives a concrete remaining obstruction to
general progress. A single lambda acquires resource identity 4, returns unit,
and is called twice. An eight-event `RunSteps` prefix performs and releases the
first acquisition. The second call reaches a non-value `Ready` state with
identity 4 already in issued history. Its only possible entry rule would reuse
that identity, so no `NamedStep` exists. Both endpoints satisfy `Ready`; the
prefix theorem is a `RunSteps` result, not a full source-admitted or
access/type-preserved execution theorem.

The [Core comparison judgment](KERNEL.md#fresh-instantiation-counterexample-and-core-judgment)
classifies this as missing source/runtime instantiation in the prototype.
Current Core already requires fresh activations for repeated execution of the
same source site, and its focused repeated-acquisition test passes. The repair
must instantiate bound identities and their metadata consistently while keeping
older closures' activations intact. Reusing a historical owner or forbidding
repeated calls would not satisfy the target semantics.

[Instantiation.lean](Instantiation.lean) establishes the metadata foundation
for that repair. Source resource binders and runtime activation atoms have
distinct constructors. An immutable lexical environment realizes exact effect
instances, nested type arguments, function ports, latent rows, and retained
resource support. Realization exists when each source name has a binding and
is unique. Freezing already-realized metadata into activation atoms preserves
it under every later environment. Different source names may alias the same
activation; no global injectivity premise is imposed.

| Result | Checked theorem or judgment |
| --- | --- |
| Bound metadata has a unique realization | `Instantiation.effect_realization_exists`, `Instantiation.type_realization_exists`, `Instantiation.effect_realization_unique`, `Instantiation.type_realization_unique` |
| Earlier realized metadata cannot be rebound | `Instantiation.frozen_effect_cannot_change`, `Instantiation.frozen_type_cannot_change` |
| Resource support follows realization through every metadata position | `Instantiation.type_resources_realize`, `Instantiation.realized_type_support` |
| Fresh acquisition preserves lexical issuance history | `Instantiation.acquisition_preserves_environment_history`, `Instantiation.acquired_activation_differs_from_earlier_bindings` |
| Entry with an already-realized body preserves the ownership ledger | `Instantiation.prepared_cell_entry_preserves_ledger` |
| Same-site rebinding preserves older request selection even with a unit operand | `Instantiation.Examples.metadata_only_request_captures_outer` |

Examples distinguish two acquisitions of source slot 4, retain old metadata
through rebinding, and allow two aliases for one activation. The dispatch
example constructs the exact outer `HandlerCut` and an actual `RawStep`; it is
not a source-reachability or joint-preservation theorem. Issuance history and
metadata lookup provide no live access or ownership authority. Unbounded
natural-number freshness also does not model Core's fallible preparation.
Source-body instantiation, lexical closures, substitution, saved code, and
signature transport remain to be integrated. The earlier `FreshnessGap`
counterexample still applies to the unchanged administrative machine. See the
[integration boundary](KERNEL.md#lexical-metadata-instantiation-foundation).

[ScopedExpressions.lean](ScopedExpressions.lean) now supplies binding-aware
instantiation for the same expression grammar. Resource references and operation
metadata distinguish source names from runtime atoms. Traversal realizes free
names in lambdas, sequencing, handler clauses, and cleanup code. A resource
declaration's initializer uses the preceding environment; its body masks the
new binder until acquisition. Resource-closed code has no free source resource
names but may still contain deferred local acquisition sites.

| Result | Checked theorem |
| --- | --- |
| Instantiation leaves exactly the free source names whose lookups are missing | `ScopedExpressions.Code.instantiation_free` |
| Closing succeeds exactly when the environment covers those names | `ScopedExpressions.Code.instantiation_closes_iff` |
| Resource-closed code is unchanged under later instantiation | `ScopedExpressions.Code.closed_instantiation_identity` |
| Inserting resource-closed code commutes with instantiation | `ScopedExpressions.Code.instantiation_subst` |
| Acquisition resolves a closed declaration's body with its prepared fresh binding | `ScopedExpressions.acquisition_closes_body` |
| Executable effect instantiation agrees with structural metadata realization | `ScopedExpressions.effect_instantiation_realizes` |

Examples check nested same-name scopes with an outer-dependent initializer,
closed lambdas with deferred acquisition sites, and old closures inserted
under a newer binding. The substitution result concerns resource instantiation;
it does not establish ordinary-variable hygiene, type/usage preservation, or
when evaluation captures a lexical environment. The operational layer below
now executes this representation; it does not yet establish a simulation or
transfer the administrative machine's joint typing and admission theorems.
The repeated-call `FreshnessGap` remains valid for the old machine.
The [scoped-code boundary](KERNEL.md#scoped-code-instantiation-and-substitution)
identifies the remaining integration obligations.

[ScopedExecution.lean](ScopedExecution.lean) gives the scoped representation
the full set of one-shot transition families. Retained contexts, handler
clauses, callbacks, saved values, and dormant captures carry scoped code.
Acquisition distinguishes its source binder from the runtime identity, requires
the declaration's free lexical resource names to be resolved, and instantiates
the body after the initializer returns an integer. Lifetime freshness applies
to the created runtime owner. Runtime activation dependencies survive a source
binder with the same numeral; unresolved source names cannot be erased into
exact runtime requests.

Every raw transition projects to the existing `Flow` ownership calculus.
Finite executions preserve the ledger and exclude duplicate completion.
`resource_entry_progress` constructs a fresh key and an actual successor with
resource-name closure and ledger preservation. It is a bounded progress case,
not a type/usage/support or general progress theorem.

The repeated-call program now completes in this layer: one retained lambda
template acquires and releases keys 0 and 1, and source slot 4 never enters
ownership history. The old administrative counterexample remains true; the
scoped rules supply the diagnosed model repair without weakening freshness.

[ScopedClosure.lean](ScopedClosure.lean) preserves resource-name closure of
executing and retained code through every raw transition, recursively including
dormant captures. The finite-execution result combines that invariant with the
ledger. A generic cell-read trace additionally connects acquisition to actual
builtin dispatch: both request metadata and operand receive the selected fresh
key, the active cell supplies its payload, and return releases it.

| Result | Checked theorem |
| --- | --- |
| All scoped transitions project to ownership events | `ScopedExecution.raw_step_erases` |
| Finite scoped executions preserve the ledger and exclude double completion | `ScopedExecution.run_steps_preserve_ledger`, `ScopedExecution.run_no_double_completion` |
| Resource entry constructs a fresh step and preserves closure and ledger | `ScopedExecution.resource_entry_progress` |
| The same callable resource template executes twice with distinct completed activations | `ScopedExecution.Examples.repeated_calls_complete_distinct_activations` |
| Every raw transition preserves resource-name closure of current and retained code | `ScopedExecution.raw_step_preserves_resource_closure` |
| Finite executions preserve resource-name closure and ownership together | `ScopedExecution.scoped_execution_preserves_closure_and_ledger` |
| Fresh acquisition, exact builtin read, and release form an actual execution | `ScopedExecution.Examples.fresh_scoped_cell_read` |

These scoped execution results do not inherit `Joint.Valid` by erasure.
The naming and access layers below now add handler-name history and live
support; later scoped layers add usage, value/effect typing, and local joint
preservation. Source-derived disposal admission, general progress, and Core
simulation remain open. The
[operational integration boundary](KERNEL.md#scoped-execution-with-fresh-acquisitions)
separates the completed model repair from those outstanding obligations.

[ScopedNames.lean](ScopedNames.lean) preserves lifetime ticket and handler
counts through all scoped transitions. Named execution allocates fresh handler
activations alongside fresh owned identities. Counts include dormant captures,
spent boundaries, and still-owned retirement markers. Combined with the ledger,
they establish unique ticket protocol states, completion of retained spent
markers, and non-revival of consumed tickets. `TicketBinding` supplies structural
occurrence and port correspondence; it does not validate permissions or effect
rows. A concrete sequential-handler execution installs the same source
expression with activations 0 and 1 and retains both in history after exit.

[ScopedDependencies.lean](ScopedDependencies.lean) proves dependency transport
for ordinary substitution and lexical instantiation. Instantiation introduces
only runtime atoms supplied by its environment. A resource-body instantiation
can therefore introduce only the acquired key. Source binder masking never
removes an older activation atom. Frozen effect metadata has exactly the
runtime instance's resource support.

[ScopedAccess.lean](ScopedAccess.lean) preserves live support of the current
expression and retained control through every raw transition under explicit
local access checks. The three checks concern release, the selected request's
operand, and the actual structural disposal plan. They inspect the pre-state;
they do not assume successor support. Resource entry uses the instantiation
dependency theorem to support its new key through the new cell boundary.
Finite named, access-checked executions preserve resource-name closure,
ownership, name history, and live support together. Closed executions cannot
retain completed resources in the current expression or dormant control.

| Result | Checked theorem |
| --- | --- |
| Scoped execution preserves fresh naming and resource-name closure with the ledger | `ScopedExecution.named_execution_preserves_closure_ledger_and_history` |
| A consumed ticket cannot later become available | `ScopedExecution.consumed_binding_never_available` |
| Exited handler activations remain unavailable for reallocation | `ScopedExecution.NameExamples.exited_handler_cannot_be_reallocated` |
| Acquisition introduces only its selected runtime key | `ScopedExpressions.acquisition_dependency_bound` |
| All scoped transitions preserve live support under local checks | `ScopedExecution.raw_step_preserves_access` |
| Named access-checked executions preserve all four connected invariants | `ScopedExecution.scoped_named_access_preserves_invariants` |
| Current and retained code cannot reference a completed resource in a closed admitted execution | `ScopedExecution.access_run_no_completed_reference`, `ScopedExecution.access_run_no_completed_retained_reference` |
| Fresh acquisition/read/release inhabits the execution preserving all four invariants | `ScopedExecution.AccessExamples.fresh_read_all_four_invariants` |

A negative example is resource-name closed but fails release admission because
its returned reference retains the owner being released. Name resolution does
not grant lifetime access. These results still assume each local access check;
deriving them from source typing and structural continuation capabilities is
unfinished. The [integration boundary](KERNEL.md#scoped-naming-dependencies-and-live-support)
keeps these four connected facets separate from full joint safety and progress.

[ScopedUsage.lean](ScopedUsage.lean) connects scoped expressions to the existing
structural one-shot usage judgment. `usageShape` retains sequencing, branches,
functions, handlers, clauses, and ticket binders while forgetting resource and
interpretation metadata. This projection is used only for usage checking.
Instantiation leaves it unchanged, and ordinary substitution commutes with it.
The exact free-ticket list and its lexical-to-runtime translation are preserved.

| Result | Checked theorem |
| --- | --- |
| Instantiation preserves and reflects structural usage | `ScopedExpressions.instantiation_preserves_usage_iff` |
| Substituting a usage-checked value preserves usage | `ScopedExpressions.usage_substitution` |
| The projection preserves exact free-ticket lists | `ScopedExpressions.Code.usage_shape_tickets` |
| Actual scoped focus splits usage and recomposition restores it | `ScopedExecution.focus_decomposes_usage`, `ScopedExecution.context_plug_preserves_usage` |
| Focus divides the scheduled consumption between child and frame | `ScopedExecution.focus_splits_code_demand` |
| Acquisition preserves scheduled consumption through instantiation | `ScopedExecution.acquisition_preserves_code_demand` |
| Translation to runtime ticket owners agrees with scoped dependencies | `ScopedExecution.usage_shape_scope_translation` |

The positive example interleaves acquisition, a builtin request, ordinary
sequencing, and resume/dispose alternatives. Negative examples reject double
consumption, an outer ticket captured by a function, and a nested clause using
an outer ticket. A separate counterexample passes usage while retaining an
unresolved resource name: this is not an operational or resource-safety erasure.
Syntactic path laws do not expand function calls or dispatch into nested clauses;
those bodies have their own checks. The expression-level
[integration boundary](KERNEL.md#scoped-structural-usage) records the projection's
limits.

[ScopedControlUsage.lean](ScopedControlUsage.lean) extends that judgment to
actual scoped frames and stacks. Active ticket access is checked separately
from recursive ownership and scheduled consumption. Capture decomposes the
selected stack, resumption restores the full prefix, and disposal replaces
internally owned demands with a concrete plan's retirement demands. Nested
examples preserve a dormant capture's demand for an outside ticket and reject
using a ticket available only in dormant control.

[ScopedUsageExecution.lean](ScopedUsageExecution.lean) proves usage preservation
for every scoped raw transition. Acquisition instantiates the body before
preserving its demand. Owner-history freshness and the existing access checks
derive the local usage checks. The registry update follows the actual capture
event and selected clause binder; its domain remains exactly the issued ticket
history, including consumed tickets.

| Result | Checked theorem |
| --- | --- |
| Actual scoped capture splits retained usage | `ScopedExecution.handler_cut_usage_decomposition` |
| Resumption restores all pending demand without reviving the consumed ticket | `ScopedExecution.resume_preserves_configuration_usage` |
| A concrete disposal plan preserves balanced consumption through retirement | `ScopedExecution.discard_preserves_configuration_usage` |
| A value cannot return through an unconsumed live clause | `ScopedExecution.live_clause_cannot_return_unconsumed` |
| Every scoped transition preserves usage under derived local checks | `ScopedExecution.raw_step_preserves_configuration_usage` |
| The same finite execution preserves closure, ownership, names, support, usage, and registry history | `ScopedExecution.scoped_named_access_steps_joint_usage` |
| Actual fresh cell execution and capture/resume execution inhabit the combined theorem | `ScopedExecution.UsageExecutionExamples.fresh_cell_execution_joint_usage`, `ScopedExecution.UsageExecutionExamples.capture_resume_joint_usage` |

These results do not establish value/effect typing or derive source admission.
Disposal still requires an actual plan. Internal retirement checks registered
ownership, not an inner ticket's explicit disposal permission; stronger contracts
against indirect abandonment require a separate admission rule. The
[retained-control integration boundary](KERNEL.md#scoped-retained-control-and-execution-usage)
records these limits.

[ScopedSignatures.lean](ScopedSignatures.lean) supplies the next typing
prerequisite. Executable type instantiation agrees with structural realization
and traverses input/output ports, latent rows, and retained support. Realized
types and operation descriptors cannot be rebound by a later environment.
Finite user-operation tables have a decidable coherence check: entries at the
same exact instance and operation must have identical complete ports.

| Result | Checked theorem |
| --- | --- |
| Executable type instantiation agrees with realization | `Instantiation.type_instantiation_realizes` |
| Already-realized type metadata stays fixed under later bindings | `Instantiation.realized_type_cannot_be_rebound` |
| Coherence checking is equivalent to existence of a signature respecting all entries | `Instantiation.check_coherent_complete` |
| Coherent tables provide every realized declaration's ports | `Instantiation.realized_operation_lookup` |
| Permuting coherent declaration entries preserves signature lookup | `Instantiation.coherent_signature_permutation` |
| Table extension requires both local coherence and agreement across the boundary | `Instantiation.coherent_append_iff` |
| Coherent extension preserves existing successful lookups | `Instantiation.coherent_extension_preserves_lookup` |

Consistent aliases pass; conflicting aliases realize successfully but admit no
single signature. Callable ports may retain resources absent from the effect
instance, so no global `SignatureSupported` restriction is imposed. Another
counterexample shows that fresh resource atoms alone do not establish coherent
table extension. These are abstract descriptor checks, not authenticated Core
declarations. Builtin cell signatures remain fixed separately. The
[signature integration boundary](KERNEL.md#scoped-type-instantiation-and-signature-coherence)
connects this evidence to the remaining expression-typing and Core obligations.

[DeclaredSignatures.lean](DeclaredSignatures.lean) derives coherence from a
fixed declaration registry for the resource-parameter fragment. A structural
family check requires unique parameters, a nonempty operation vector, and
resource names bound by those parameters. Exact positional arguments determine
the realization environment; the selected operation template determines both
ports. No independent table-coherence premise is needed for these entries.

| Result | Checked theorem |
| --- | --- |
| Family checking reflects the structural declaration conditions | `Instantiation.check_family_iff` |
| Exact argument binding supplies every declared resource parameter | `Instantiation.parameter_environment_binds` |
| A selected valid declaration and argument vector yield operation ports | `Instantiation.declared_operation_exists` |
| Entries derived from the same registry and key have equal ports | `Instantiation.declared_operation_ports_unique` |
| Declaration-derived tables are coherent | `Instantiation.declared_table_coherent` |
| Preserving old declarations permits coherent table extension | `Instantiation.declared_extension_coherent` |
| The extension preserves existing successful lookups | `Instantiation.declared_extension_preserves_lookup` |

Examples admit aliases and fresh callable ports with their declared resource
arguments. They reject conflicting result types, missing arguments, unknown
families and operations, duplicate parameters, and literal activation atoms in
declarations. The [declaration integration boundary](KERNEL.md#declaration-derived-resource-signatures)
distinguishes this checked fragment from complete Core authentication, general
kinds and type arguments, and expression typing. An explicit counterexample
passes its resource-scope check with an unknown latent effect family; full
referenced-type and effect-instance validation remains separate.

[ScopedTyping.lean](ScopedTyping.lean) adds expression typing for the actual
scoped machine syntax. Resource bodies check at every identity fresh for a
finite world, with result and outward residual resources confined to the
preceding world. The execution connection uses issued resource history as the
world; live access remains a separate judgment.

| Result | Checked theorem |
| --- | --- |
| Result types are formed in the world | `ScopedTyping.typed_result_in_world` |
| Typing survives world extension | `ScopedTyping.typed_world_weaken` |
| Typing derives resource-name closure | `ScopedTyping.typed_resource_closed` |
| Typed values bound their resource dependencies | `ScopedTyping.typed_value_support` |
| Actual focus contexts decompose and recompose typing | `ScopedTyping.typed_focus_decomposition`, `ScopedTyping.context_plug_typed` |
| Every actual fresh allocation yields a typed opened body without result or row escape | `ScopedTyping.resource_body_typed_at_fresh` |
| Typed resource entry has a fresh execution step, typed body, and preserved ledger | `ScopedTyping.typed_resource_entry_progress` |

Examples check a typed resource-read acquisition and initial typing of the
repeated-call program. Negative derivations reject fresh-reference escape and
unresolved references; historical typing alone does not grant live access.
The [scoped typing boundary](KERNEL.md#generative-scoped-expression-typing)
records the remaining signature-schema, joint preservation,
and source-checking obligations. The universal fresh-body premise is a
declarative rule, not yet a decidable source checker. This layer proves bounded
resource-entry progress, not general progress or Core correspondence.

[ScopedSubstitution.lean](ScopedSubstitution.lean) proves typed substitution
for scoped expressions and clauses. Closed values preserve their older
activation atoms when inserted beneath resource binders; exact closure support
annotations survive replacement of lexical values by runtime syntax.

| Result | Checked theorem |
| --- | --- |
| Typing depends only on retained ordinary variable bindings | `ScopedTyping.typed_environment_congr` |
| Substitution accounts for the inserted value's actual support | `ScopedTyping.substitution_support_bound` |
| Closed substitution preserves expression and clause typing | `ScopedTyping.typed_substitution`, `ScopedTyping.clauses_typed_substitution` |
| Immediate row widening and empty-ticket transport preserve latent contracts | `ScopedTyping.typed_effect_weaken`, `ScopedTyping.typed_none_ticket_transport` |
| The selected clause keeps its declared ports after operand substitution | `ScopedTyping.selected_clause_substitution_typed` |
| Actual binding and beta steps have typed successor expressions | `ScopedTyping.typed_bind_step`, `ScopedTyping.typed_beta_step` |

Examples preserve an older reference under a same-numbered resource site and
retain a closure's support annotation. An actual repeated-acquisition function
call has a typed beta successor. These results keep raw lexical readiness
premises explicit and do not establish full configuration preservation. The
[substitution boundary](KERNEL.md#scoped-typed-substitution-and-ordinary-execution)
records the remaining source-admission and machine integration obligations.

[ScopedReadiness.lean](ScopedReadiness.lean) derives lexical runtime readiness
from typing. Free variables belong to the ordinary environment and free
tickets to the static ticket scope. This judgment deliberately leaves resource
access and ownership to the separate invariants.

| Result | Checked theorem |
| --- | --- |
| Resource opening cannot hide an existing dependency | `ScopedExpressions.Code.instantiation_keeps_dependencies` |
| Typing bounds free ordinary variables and tickets | `ScopedTyping.typed_lexical_dependencies` |
| Empty-environment typing closes actual values | `ScopedTyping.typed_value_closed` |
| Singleton-environment typing supplies binding-suffix readiness | `ScopedTyping.typed_suffix_ready` |
| Value-form binding, application, and branching have actual typed successors | `ScopedTyping.typed_bind_value_progress`, `ScopedTyping.typed_application_value_progress`, `ScopedTyping.typed_branch_value_progress` |
| Typed value-form resource initializers take a fresh step preserving the ledger | `ScopedTyping.typed_resource_value_progress` |
| Structural scope-name correspondence makes pending-ticket translation total | `ScopedTyping.lexical_translation_total` |
| An actual focus position gets its retained frame and ports from typing | `ScopedTyping.typed_focus_progress` |

Examples derive closure and binding readiness for the repeated-acquisition
program and a focus frame containing the actual translated ticket owner.
Negative cases reject missing ordinary bindings, unavailable static tickets,
and mismatched runtime binders. These are bounded progress cases. The
[readiness boundary](KERNEL.md#lexical-readiness-and-bounded-scoped-progress)
separates them from general progress, full source admission, live resource
support, and runtime-owner/frame correspondence.

[ScopedRetained.lean](ScopedRetained.lean) extends value typing to current
scoped code, retained frames, callback values and saved results, and dormant
captured stacks. Historical ticket ports connect static and runtime scopes;
they do not grant a live capability. The world grows through every retained
payload when a resource is acquired.

| Result | Checked theorem |
| --- | --- |
| Exact handler cuts retain typed code and ports | `ScopedTyping.handler_cut_retains_typing` |
| Resumption restores capture above the entire clause prefix | `ScopedTyping.resume_preserves_configuration_typing` |
| Capture derives lexical readiness and a typed extended-ticket configuration | `ScopedTyping.capture_constructs_typed_configuration` |
| Actual disposal plans retain typed contents and compose with the outside stack | `ScopedTyping.make_plan_retains_types`, `ScopedTyping.discard_preserves_configuration_typing` |
| All raw transitions from value-form expressions preserve configuration value typing | `ScopedTyping.raw_value_step_typed` |
| World extension preserves current and dormant retained typing | `ScopedTyping.configuration_world_weaken` |
| Typed cell returns supply the resource-release dependency exclusion | `ScopedTyping.typed_cell_return_excludes_identity` |
| Given focus positions and value-form bind, application, and branch steps construct typed configuration successors | `ScopedTyping.configuration_focus_progress`, `ScopedTyping.configuration_bind_value_progress`, `ScopedTyping.configuration_application_value_progress`, `ScopedTyping.configuration_branch_value_progress` |
| Fresh resource entry preserves configuration value typing and the ledger | `ScopedTyping.configuration_resource_value_progress` |

Examples check typed capture, resumption with nonempty clause work, and fresh
resource entry. A three-step cleanup execution has all four configurations
typed and preserves its ownership ledger. A negative example has consistent
value types but no interpreter for its request, so this layer alone cannot
prove general machine-step progress. The
[retained typing boundary](KERNEL.md#scoped-retained-typing-and-configuration-transitions)
records the remaining effect, ownership, source-admission, and Core obligations.

[ScopedEntries.lean](ScopedEntries.lean) constructs handler and cleanup entries
with annotations derived from typing. It derives builtin operand shapes and
reconstructs actual source/builtin selections from nearest active lookup.
[ScopedEffects.lean](ScopedEffects.lean) then checks connected effect interfaces
through actual scoped frames and dormant captures.

| Result | Checked theorem |
| --- | --- |
| Handler and cleanup entries derive stored code checks and ports | `configuration_handler_entry_progress`, `configuration_cleanup_entry_progress` |
| Exact lookup constructs executable selection | `handler_selection_of_resolution`, `cell_selection_of_resolution` |
| Typed builtin requests with exact lookup have a read/write step | `configuration_builtin_progress` |
| Captured and recomposed effect interfaces follow actual stack order | `handler_cut_effect_decomposition`, `resume_effect_recomposition` |
| Capture constructs a connected typed successor and extends old contracts | `capture_constructs_effect_configuration` |
| Resumption and all raw closed-value transitions preserve connected typing | `resume_preserves_effect_configuration`, `raw_value_step_preserves_effect_configuration` |
| A request with a value operand takes a typed step or is observably outward | `request_effect_progress`, `closed_request_effect_progress` |

These theorem names are in `ScopedTyping`. Request progress permits an outward
observation only when lookup finds no local interpreter. Its capture branch
uses a fresh historical ticket slot; ownership freshness and disposal
permissions remain separate. Examples check nested capture and resumption
reaching an outer effect, concrete typed reads/writes, and rejection of
unhandled or dormant-only interpretation under a closed interface. The
[connected request boundary](KERNEL.md#scoped-entries-and-connected-request-progress)
records the remaining admission, disposal, general progress, and Core work.

[ScopedEffectCompletion.lean](ScopedEffectCompletion.lean) checks the remaining
local entry/effect cases and constructs disposal plans from structural
readiness of the actual captured stack.

| Result | Checked theorem |
| --- | --- |
| Connected interfaces survive resource-world growth | `effect_configuration_world_weaken`, `effect_stack_world_weaken` |
| Focus, handler and cleanup entry derive connected typed successors | `focus_constructs_effect_configuration`, `handler_entry_constructs_effect_configuration`, `cleanup_entry_constructs_effect_configuration` |
| Fresh resource entry preserves connected typing and ownership | `resource_entry_effect_progress` |
| Callback requests use their actual remaining plan suffix | `plan_invocation_contract`, `plan_request_is_outward_or_interpreted` |
| Structural readiness constructs an executable, effect-typed plan | `close_ready_constructs_plan` |
| Disposal preserves connected typing and derives a fresh ledger-preserving step | `discard_preserves_effect_configuration`, `ready_disposal_effect_progress` |
| Eleven-step disposal/cleanup trace has twelve connected typed configurations | `CompletionExamples.disposal_trace_configurations_typed` |
| Effect readiness does not imply unchanged interpretation | `CompletionExamples.readiness_does_not_imply_interpretation_agreement` |

These names are in `ScopedTyping`. The disposal progress result requires a
supplied live boundary, runtime resolution, historical contract, readiness,
and ledger. It constructs the plan and fresh close owner. It does not supply
access, interpreter agreement, or disposal permissions. The
[structural closing boundary](KERNEL.md#scoped-effect-entry-and-structural-closing-readiness)
records the remaining joint admission, general progress, and Core obligations.

[ScopedJoint.lean](ScopedJoint.lean) joins connected scoped typing with the
ownership ledger, name history, live support, structural usage, registry history,
and resource-name closure. One ticket record supplies separate effect-contract
and permission projections.

| Result | Checked theorem in `ScopedJoint` |
| --- | --- |
| Independent closed-expression checks initialize all seven facets | `initial_configuration_valid` |
| Type-directed capture constructs one coherent registry entry | `capture_constructs_joint_configuration` |
| Resumption and prepared disposal preserve all facets | `resume_preserves_joint_configuration`, `ready_disposal_constructs_joint_configuration` |
| Ordinary computation and all current-value events preserve the joint invariant | `ordinary_step_preserves_joint_configuration`, `value_event_constructs_joint_step` |
| Focus and handler/cleanup/resource entry construct joined successors | `focus_constructs_joint_configuration`, `handler_entry_constructs_joint_configuration`, `cleanup_entry_constructs_joint_configuration`, `resource_entry_constructs_joint_configuration` |
| Value completion and resumption derive the next step without a supplied boundary or access certificate | `value_progress`, `resume_value_progress` |
| Empty control has discharged each issued owner exactly once | `terminal_ledger_settled` |
| Every state of a three-step fresh-read execution has all seven facets | `Examples.fresh_read_all_states_valid` |
| Nested capture and usage-derived resumption inhabit the joined judgment | `Examples.nested_capture_constructed`, `Examples.nested_resume_constructed` |

Capture/disposal still need their structural access checks. Disposal additionally
needs closing readiness at the supplied live boundary. The nested fixture starts
with existing handler activations. The
[scoped joint boundary](KERNEL.md#scoped-joint-invariants-and-derived-progress)
distinguishes these results from general source-admitted progress, preserved
future readiness, internal retirement permission, and Core correspondence.

[ScopedProgress.lean](ScopedProgress.lean) covers every current expression form
under structural access and closing checks. Those checks concern the prestate;
they contain no next-step or successor-validity requirement.

| Result | Checked theorem or judgment in `ScopedProgress` |
| --- | --- |
| Typed current expressions have an exhaustive value/focus/head classification | `CurrentForm`, `typed_current_form` |
| Finite histories supply fresh owner and handler identities | `fresh_owner_exists`, `fresh_activation_exists` |
| Existing captures require a closing plan only when disposal is permitted | `ClosingInterfaces`, `closing_interface_at_live` |
| Discard derives the permitted owner and its active boundary | `discard_demand_supplies_authority`, `discard_progress` |
| Requests dispatch locally or expose an actually unmatched outward request | `request_progress` |
| Every expression returns, exposes an outward request, or steps with all seven facets and unchanged old ticket records | `current_progress` |
| An empty outgoing row removes the observation alternative | `closed_current_progress` |
| Independent closed-expression checks derive an initial value or first step | `initial_progress` |
| Fresh source entry, nested resumption, outward observation, and conditional protected-capture checks are inhabited | `Examples.source_resource_progress`, `Examples.nested_resumption_progress`, `Examples.permitted_outward_request_is_observed`, `Examples.protected_resume_only_has_closing_interfaces`, `Examples.protected_dispose_permission_rejects_closing_interfaces` |

These results preserve `ScopedJoint.Valid` and old registry records. Their
conclusions do not preserve access checks or closing interfaces. The
[all-expression progress boundary](KERNEL.md#scoped-progress-for-every-expression-form)
records the remaining source establishment, readiness preservation, and Core
simulation obligations. Initial progress is a first-step result; “closed” in
`closed_current_progress` means an empty outgoing effect row.

[ScopedPrepared.lean](ScopedPrepared.lean) preserves existing closing interfaces
through actual scoped execution and isolates the certificate needed by each new
capture. It includes resource-world growth and immutable historical records.

| Result | Checked theorem or judgment in `ScopedPrepared` |
| --- | --- |
| Closing interfaces survive registry extension and world growth | `closing_interfaces_extension`, `closing_interfaces_world_weaken` |
| Capture decomposition, full resumption and disposal preserve existing interfaces | `closing_interfaces_decompose`, `closing_interfaces_resume`, `closing_interfaces_discard` |
| Every raw transition preserves interfaces under the new-capture obligation | `AllocationClosing`, `raw_step_preserves_closing_interfaces` |
| Non-request progress preserves the joined invariant, closing interfaces, and exact registry | `Ready`, `nonrequest_ready_progress` |
| Current values derive progress without a supplied access certificate | `ready_value_progress` |
| Type-directed capture exposes only its new conditional closing obligation | `capture_constructs_ready_obligation` |
| Initial readiness does not establish readiness of a new capture under arbitrary granted rights | `Examples.initial_ready_does_not_establish_new_capture_readiness` |
| The same running-cleanup capture preserves readiness with resume-only rights | `Examples.resume_only_capture_preserves_ready` |

The counterexample includes a four-step source prefix and an actual capture.
Its policy grants unused disposal authority; current Core checks actual discard
and permits the corresponding resume-only control. The
[scoped readiness-preservation boundary](KERNEL.md#scoped-preservation-of-closing-readiness)
records that model-policy judgment, the passing current-Core cleanup tests,
and the remaining source contract, access, retirement, and simulation work.

[ScopedActions.lean](ScopedActions.lean) computes the least enclosing-ticket
action bound for the structural usage checker, keeping nested clause policy fixed.

| Result | Checked theorem or judgment |
| --- | --- |
| Every usage derivation requires the computed permissions | `ActionRequirements.usage_requires_actions` |
| Any sufficient enclosing permission bound preserves a valid usage derivation | `ActionRequirements.usage_repermission` |
| The computed bound is least for the same binder, states and nested policy | `ActionRequirements.least_enclosing_actions`, `scoped_least_enclosing_actions` |
| Value substitution and fresh instantiation preserve the bound exactly | `Code.substitution_required_actions`, `Code.instantiation_required_actions` |
| Both branch arms count; nested clauses retain independent checks | `ActionExamples.mixed_clause_needs_both`, `nested_clause_checked`, `insufficient_nested_policy` |
| Flags alone do not validate scope, single consumption or function barriers | `ActionExamples.wrong_binder_still_rejected`, `double_completion_still_rejected`, `function_capture_still_rejected` |
| Reused binder numbers can force unnecessary shared grants | `ActionExamples.shared_binder_outer_requirement`, `shared_binder_policy_needs_both`, `shared_binder_both_checked` |
| The running-cleanup example's derived resume-only bound permits its actual capture | `ActionExamples.derived_resume_contract_preserves_ready` |

The scoped theorem and example names are in `ScopedExpressions`.
The [least-action boundary](KERNEL.md#least-enclosing-continuation-actions)
distinguishes structural minimality from reachable actions, requires a prior
usage derivation for sufficiency, and records the still-unproved mapping from
source clause occurrences to independent policy entries. Action inference does
not establish capture-specific closing safety or Core simulation.

[ScopedPolicies.lean](ScopedPolicies.lean) synthesizes a policy from every clause
declaration contained in the expression, including functions and nested clauses.

| Result | Checked theorem or judgment |
| --- | --- |
| Valid usage covers every collected clause requirement | `ActionPolicies.usage_covers_profile` |
| A covering policy reconstructs usage, including nested clause checks | `ActionPolicies.usage_change_policy` |
| The computed policy supports usage and is pointwise least | `ActionPolicies.least_whole_policy`, `scoped_least_whole_policy` |
| Coherent keys give exact local action contracts; distinct keys suffice | `ActionPolicies.inferred_exact`, `distinct_keys_coherent` |
| Substitution bounds profile membership and preserves combined coherence | `ActionPolicies.substitution_profile_bound`, `substitution_preserves_profile_coherence` |
| Instantiation preserves the profile and inferred policy exactly | `Code.instantiation_action_profile`, `Code.instantiation_inferred_policy` |
| Synthesized usage joins initial typing and empty runtime resource support | `initial_ready_with_synthesized_policy` |
| Copied functions retain exact contracts despite repeated keys | `PolicyExamples.copied_profile_coherent`, `copied_profile_not_unique`, `copied_policy_exact`, `copied_functions_checked` |
| Conflicting key reuse joins authority and fails coherence | `PolicyExamples.collision_joins_authority`, `collision_not_coherent` |
| Whole-source policy synthesis supports the running-cleanup capture | `PolicyExamples.running_capture_with_synthesized_policy` |

Unqualified scoped names and `PolicyExamples` are in `ScopedExpressions`.
The [policy-synthesis boundary](KERNEL.md#synthesized-clause-action-policies)
keeps enclosing scope fixed, distinguishes action coherence from authenticated
identity, and explains why execution must retain the initial policy. The next
layer proves coverage of current and retained code. Extraction from Core,
compatibility of external callable inputs, capture safety, and formal simulation
remain open.

[ScopedProfiles.lean](ScopedProfiles.lean) proves provenance of runtime clause
contracts through all represented transition families, keeping the source policy
fixed. The profile includes current code, retained frames and saved captures.

| Result | Checked theorem in `ScopedProfiles` |
| --- | --- |
| Contexts, exact handler cuts and selected clauses retain their profile entries | `context_profile_membership`, `handler_cut_profile`, `selected_clause_profile` |
| Generated and materialized cleanup plans retain existing callback profiles | `make_plan_profile`, `close_control_profile` |
| Every raw step preserves profile membership, without additional safety premises | `raw_step_profile` |
| Finite raw, named and access-checked execution preserves provenance | `raw_trace_profile`, `named_steps_profile`, `named_access_steps_profile` |
| Reached runtime profiles belong to the original source profile | `source_profile_provenance` |
| The fixed source policy covers runtime entries and preserves coherent contracts | `source_profile_coverage`, `source_profile_coherence`, `source_contract_exact` |
| Actual selected clauses and newly allocated tickets receive exact local contracts | `selected_contract_exact`, `named_ticket_contract_exact` |
| Type-directed capture records required permissions and exposes only the remaining closing certificate | `source_capture_constructs_ready_obligation` |
| Actual beta duplication preserves membership while increasing multiplicity | `Examples.duplicate_beta`, `duplicate_profiles`, `duplication_preserves_provenance` |
| Cleanup retains nested clauses; dropping current code must not erase source policy | `Examples.cleanup_plan_retains_clause_profiles`, `branch_drops_current_profile` |
| Running-cleanup capture records disposal-disabled permissions and preserves readiness | `Examples.running_contract_record` |

The [provenance boundary](KERNEL.md#source-contract-provenance-through-execution)
separates fixed source contracts from historical registry records and records
the limitations for external callable inputs and future code-bearing stores.
Capture safety, future access, authenticated Core
identity mapping and simulation remain open.

[ScopedRetirement.lean](ScopedRetirement.lean) proves structural provenance and
conditional authority for internal ticket retirement, distinguishing it from
explicit clause action permissions.

| Result | Checked theorem or judgment in `ScopedRetirement` |
| --- | --- |
| A close plan schedules exactly its recursively live captured tickets | `plan_retires_exact_live_tickets` |
| Unique owned tickets retire uniquely; outside tickets receive no plan authority | `plan_retirement_unique`, `plan_retires_no_outside_ticket` |
| Every new scheduled retirement originates in an owning discard | `Delegates`, `raw_scheduled_origin` |
| Recorded executions retain actual intermediate configurations | `RecordedTrace`, `RecordedTrace.raw`, `trace_has_recording` |
| A retirement reached from empty control has a prior delegating event | `retirement_has_prior_delegation` |
| Current usage proves permission at the selected discard | `delegated_discard_requires_permission` |
| Initial usage, fresh history and per-step access derive permission at the prior event | `source_retirement_has_permitted_delegation` |
| Fresh recorded execution cannot complete an owner twice | `recorded_no_double_completion` |
| An administrative inner resume-only ticket retires after an authorized outer discard | `Examples.before_usage`, `scheduled_usage`, `retirement_executes_without_inner_dispose_permission` |

The [retirement boundary](KERNEL.md#delegated-internal-retirement) grounds this
distinction in current Core and 11 passing discard tests. The formal fixture
starts with supplied captures and records; source-derived allocation is not
claimed for it. Per-step access checks remain explicit in the trace theorem,
so complete source admission, general progress and simulation remain open.

Positive and negative derivations check builtin dispatch blockers, removed
source overrides, protected running cleanup, dormant resource visibility,
pending outside consumption, duplicate identities, and an explicit
capture/resume/release execution. A raw close plan that loses pending outside
consumption is deliberately exhibited: ownership conservation alone is weaker
than admissibility. Further counterexamples require checking the materialized
suffix rather than the original active spine, and rejecting cleanup closures
that retain even an internally owned ticket. A nested-cleanup positive example
checks support and exact lookup of a still-enclosing cell across materialization.
Expression examples check resource-retaining closures, structural-ticket
barriers, handler-local binding, resource arguments, unresolved lexical values,
and resource-name capture. The raw substitution counterexample demonstrates why a dependency
upper bound alone is insufficient: hiding an inserted dependency also satisfies
an upper bound. The fresh-substitution theorem provides the corresponding lower
bound.
Usage examples accept mixed resume/dispose branches and independent nested
clauses. They reject missing or repeated consumption, incomplete branches,
missing permissions, consumption in a resume operand, and capture through a
function or nested-clause barrier. A closed-dependency value containing an
illegal function capture inside its local handler clause is rejected too:
dependency closure alone cannot establish structural usage.

`WellFormed` currently checks ports, support, ownership, names, frame shapes,
capture delimiters, and ambient separation. It does not yet incorporate the
expression dependency results or establish a complete annotation judgment.
The raw ownership events alone do not establish callback evaluation. The new
machine invokes callbacks by ordinary application and requires a returned unit
before discharging their running owner. Its raw ledger projection alone omits
current-expression support: an explicit raw trace can return a dangling
resource reference while conserving ownership. The access layer rejects that
trace and preserves support under the stated local checks. Generated-plan
support and lookup are proved, but `CompatibleCuts`, full type/usage/support
admission and its joint preservation through arbitrary cleanup expression steps,
relative progress, and simulation of current Core remain unproved. The full
calculus goal remains open.

Core correspondence is a comparison obligation. A mismatch may identify a
calculus error, an implementation defect against the specification, or a
justified semantic change needed in Core and the specification. The
[proof programme](KERNEL.md#remaining-proof-construction) requires explicit
counterexamples and judgment at that boundary. Progress remains a required
theorem for the one-shot calculus.

[ScopedSignatureGap.lean](ScopedSignatureGap.lean) identifies a source-typing
correspondence defect, explained in the
[fixed-port comparison](KERNEL.md#fixed-declaration-ports-and-callable-support).
The existing fixed support-annotated operation types reject a callable retaining
a fresh resource even when its selected handler stays inside that resource's
lifetime. Current Core accepts the corresponding source. The model must separate
declared ports from per-value support; this is not a reason to restrict Core.

| Result | Checked theorem |
| --- | --- |
| Two fresh openings confine fixed support to the old world | `two_openings_confine_support`, `all_openings_confine_support` |
| The confinement applies to fixed operation ports | `request_ports_in_world`, `generative_request_ports_confined` |
| No fixed signature types the accepted source shape | `Examples.safe_source_has_no_fixed_signature_typing` |
| The source is closed and satisfies one-shot usage | `Examples.program_resource_closed`, `Examples.program_has_no_initial_resource_atoms`, `Examples.program_uses_one_shot` |
| Its actual cut supports the retained payload | `Examples.actual_boundary_supports_payload` |
| The raw machine completes the source with fresh owners | `Examples.source_executes`, `Examples.source_execution_has_fresh_owners` |

[ScopedPortTyping.lean](ScopedPortTyping.lean) and
[ScopedPortSubstitution.lean](ScopedPortSubstitution.lean) begin that repair.
They check the existing expression grammar with fixed declared ports and
independent callable support. The
[port/support account](KERNEL.md#declared-ports-and-independent-value-support)
states the remaining runtime and source-analysis obligations.

| Result | Checked theorem |
| --- | --- |
| Old expression typing preserves its declared types and effect bounds | `typed_erasure` |
| One fixed signature types every fresh opening of the safe fixture | `Examples.generative_source_port_typed` |
| The same callable port coexists with different actual resource support | `Examples.fresh_payload_same_port_with_actual_support` |
| Access checking rejects the unsafe boundary despite successful port typing | `Examples.outside_source_port_typed`, `Examples.outside_capture_rejected` |
| Independently bounded support survives ordinary value substitution | `Support.substitution_support_bound` |
| Closed substitution preserves ports through the full scoped grammar | `typed_substitution`, `clauses_typed_substitution` |
| Actual bind and beta steps preserve expression ports | `typed_bind_step`, `typed_beta_step` |
| The actual selected clause preserves ports and supplied support bounds together | `selected_clause_binding_preserves_ports_and_support` |
| A returned callable wrapper retains the inserted payload's cell | `SubstitutionExamples.higher_order_parameter_transport`, `SubstitutionExamples.higher_order_result_still_retains` |

These theorems use namespace `Ash.OneShot.ScopedPorts`. Support calculation is
not general result-support inference. The runtime layer below migrates retained
port typing; the following effect layer connects lookup and resumption.
`Ready`/progress still require migration.

[ScopedPortReadiness.lean](ScopedPortReadiness.lean) and
[ScopedPortRetained.lean](ScopedPortRetained.lean) connect the replacement ports
to actual strict frames, historical ticket records and captured forests.
The [runtime account](KERNEL.md#runtime-port-typing-and-capture-preservation)
states which old invariants remain separate.

| Result | Checked theorem |
| --- | --- |
| Runtime annotations recover their inferred declared ports | `erase_embed_port`, `embedded_declared_resources` |
| Typing supplies closed values, suffix readiness and actual focus frames | `typed_value_closed`, `typed_suffix_ready`, `typed_focus_progress` |
| Old retained typing embeds into the new judgment on the same configuration | `frame_erasure`, `stack_erasure`, `configuration_erasure` |
| Exact capture and full-prefix resumption preserve runtime ports | `handler_cut_retains_typing`, `capture_constructs_typed_configuration`, `resume_preserves_configuration_typing` |
| Closed-value completion and disposal preserve runtime ports | `raw_value_step_preserves_typing`, `discard_preserves_configuration_typing` |
| The same capture/resume event preserves ports, ownership and checked support | `capture_constructs_ports_ledger_support`, `resume_preserves_ports_ledger_support` |
| The safe callable trace has port-typed capture, resume and return states | `RetainedExamples.source_entries_typed`, `RetainedExamples.captured_typed`, `RetainedExamples.completion_states_typed` |
| Declared callback ports cannot justify unsafe cell release | `RetainedExamples.escaping_return_has_ports`, `RetainedExamples.escaping_return_access_rejected` |

These results also use `Ash.OneShot.ScopedPorts`. Erased port equality does not
recover old raw type equality. These port results do not by themselves provide
connected effects, complete joint validity, source support inference or general
progress.

[ScopedPortEffects.lean](ScopedPortEffects.lean) connects incoming/outgoing effect
interfaces to the same historical port records. The
[ordered interface account](KERNEL.md#ordered-effect-interfaces-with-declared-ports)
explains the separate effect and runtime-port projections.

| Result | Checked theorem or judgment |
| --- | --- |
| Actual frame and dormant-capture effects connect through one ordered forest | `EffectFrame`, `EffectStack`, `EffectConfigurationTyped` |
| Exact cuts preserve selected, captured and outside effect interfaces | `handler_cut_effect_decomposition` |
| A current request has an interpretation or an outgoing-row allowance | `current_request_is_interpreted_or_exported` |
| Actual lookup failure requires outgoing allowance; empty outgoing rows give local lookup | `unhandled_current_request_is_exported`, `current_request_has_interpretation` |
| Full-prefix resumption preserves connected ports and effect interfaces | `resume_effect_recomposition`, `resume_preserves_effect_configuration` |
| The same resume event preserves connected typing, ledger and checked support | `resume_preserves_effects_ledger_support` |
| The safe generative fixture has connected source/request/capture/resume states | `EffectExamples.source_entries_connected`, `EffectExamples.request_connected`, `EffectExamples.captured_connected`, `EffectExamples.resumed_connected` |
| Connected typing still cannot justify unsafe resource release | `EffectExamples.connected_typing_does_not_imply_release` |

These results use `Ash.OneShot.ScopedPorts`. Outgoing-row membership alone does
not imply failed lookup. Effect connectivity alone does not supply disposal
permission, a closing plan or resource support. The following layer supplies
connected capture, completion/disposal and entry constructions.

[ScopedPortSteps.lean](ScopedPortSteps.lean) and
[ScopedPortCompletion.lean](ScopedPortCompletion.lean) migrate the local connected
transition proofs and structural closing effect judgment. The
[capture and completion account](KERNEL.md#connected-capture-entry-and-structural-completion)
states their remaining admission premises.

| Result | Checked theorem or judgment |
| --- | --- |
| Actual capture constructs a connected successor and immutable extension | `capture_constructs_effect_configuration` |
| The same capture event preserves connected typing, ledger and checked support | `capture_constructs_effects_ledger_support` |
| Exact builtin selection supplies typed read/write steps | `builtin_effect_progress` |
| Value-operand requests step or have an actual unhandled outward observation | `request_effect_progress`, `closed_request_effect_progress` |
| Closed-value transitions and bind/beta preserve connected typing | `raw_value_step_preserves_effect_configuration`, `bind_preserves_effect_configuration`, `beta_preserves_effect_configuration` |
| Focus, handler and cleanup entry derive actual metadata | `focus_constructs_effect_configuration`, `handler_entry_constructs_effect_configuration`, `cleanup_entry_constructs_effect_configuration` |
| Fresh entry preserves connected typing in the larger resource world and the ledger | `resource_entry_effect_progress` |
| Structural closing readiness constructs the actual ordered plan | `CloseReady`, `close_ready_constructs_plan`, `plan_invocation_contract` |
| Actual materialization preserves connected typing and gives relative disposal progress | `discard_preserves_effect_configuration`, `ready_disposal_effect_progress` |
| Safe callable capture and completion inhabit the connected conclusions | `StepExamples.capture_has_connected_successor`, `StepExamples.completion_states_connected`, `CompletionExamples.fresh_safe_callable_entry` |
| The callback disposal trace has connected typing at every listed state | `CompletionExamples.disposal_callback_trace`, `CompletionExamples.disposal_trace_configurations_typed` |
| Early provider release and closing a running callback are rejected | `CompletionExamples.release_before_callback_rejected`, `CompletionExamples.running_cleanup_rejected` |
| Closing readiness does not guarantee exact interpreter agreement | `CompletionExamples.readiness_does_not_imply_interpretation_agreement` |
| Connected typing and current live support do not justify release | `CompletionExamples.live_support_does_not_supply_release` |

These results use `Ash.OneShot.ScopedPorts`. The combined request theorem assumes
an unused historical ticket slot, which only source capture uses. The disposal
theorem assumes structural closing readiness at the actual live boundary.
The following layer joins the current-state invariants and conditional progress.

[ScopedPortJoint.lean](ScopedPortJoint.lean) and
[ScopedPortProgress.lean](ScopedPortProgress.lean) use one historical record for
the independent port/effect and permission projections. The
[joined progress account](KERNEL.md#joined-port-invariants-and-conditional-progress)
distinguishes current-state progress from source-to-execution safety.

| Result | Checked theorem or judgment |
| --- | --- |
| One record connects ports/effects, permissions and issued history | `ScopedPortJoint.TicketRecord`, `RegistryHistory`, `effects_insert`, `usage_insert` |
| Seven independent fields describe the same actual state and resource world | `ScopedPortJoint.Valid` |
| Capture derives its successor and inserts one matching contract/permission record | `ScopedPortJoint.capture_constructs_joint_configuration` |
| Resume, disposal, ordinary steps and fresh entry preserve the joined invariant | `ScopedPortJoint.resume_preserves_joint_configuration`, `discard_preserves_joint_configuration`, `ordinary_step_preserves_joint_configuration`, `resource_entry_constructs_joint_configuration` |
| Value progress preserves all fields under explicit current access checks | `ScopedPortJoint.checked_value_progress` |
| Whole joined validity can hold while a value has no admitted next step | `ScopedPortJoint.Examples.joint_valid_value_can_lack_admitted_step` |
| Structural closing checks and usage choose the same owner, rights and closing row | `ScopedPortProgress.ClosingInterfaces`, `discard_demand_supplies_authority`, `discard_progress` |
| Every current expression form progresses under actual access and closing checks | `ScopedPortProgress.current_progress`, `closed_current_progress` |
| The repaired generative source starts with one fixed signature | `ScopedPortJoint.Examples.safe_entry_constructed`, `ScopedPortProgress.Examples.safe_source_first_step` |
| Closing interfaces do not replace result-support safety | `ScopedPortProgress.Examples.closing_interfaces_do_not_supply_release` |

The new namespaces are `Ash.OneShot.ScopedPortJoint` and
`Ash.OneShot.ScopedPortProgress`. No current progress premise assumes a step or
successor validity. The theorem does not preserve or derive future access and
closing checks. The following layer preserves closing readiness with an explicit
new-capture obligation; source derivation of future access and closing safety
and Core simulation remain open.

[ScopedPortPrepared.lean](ScopedPortPrepared.lean) migrates preservation of
closing readiness to the same declared ports and historical records. The
[readiness account](KERNEL.md#preserved-closing-readiness-with-declared-ports)
explains why current access checks remain explicit.

| Result | Checked theorem or judgment |
| --- | --- |
| Joined validity and actual historical closing interfaces | `ScopedPortPrepared.Ready` |
| Existing closing interfaces survive every raw transition under the new allocation obligation | `raw_step_preserves_closing_interfaces`, `AllocationClosing` |
| Non-request progress preserves readiness and the exact registry under current access checks | `nonrequest_ready_progress`, `checked_ready_value_progress` |
| Capture constructs the joined successor and exposes the selected record's remaining closing obligation | `capture_constructs_ready_obligation` |
| The fixed-signature source establishes readiness and preserves it at first entry | `Examples.safe_source_ready`, `Examples.safe_first_entry_preserves_ready` |
| Readiness still allows a value with no admitted next step | `Examples.ready_value_can_lack_admitted_step` |

These results use `Ash.OneShot.ScopedPortPrepared`. They preserve existing
closing interfaces; they do not infer future access checks or new-capture
closing safety from source admission.

[ResultSummaries.lean](ResultSummaries.lean) adds independent analysis metadata
over the same expressions. The [result-summary account](KERNEL.md#independent-storage-and-result-summaries)
separates proved storage facts from the pending computation-result theorem.

| Result | Checked theorem or judgment |
| --- | --- |
| Captures and result bodies have different binder scopes | `Summary`, `Summary.Scoped`, `Summary.substitute` |
| Renaming, substitution and analysis preserve summary scope | `rename_preserves_scope`, `substitute_preserves_scope`, `analyze_preserves_scope` |
| Instantiating a returned callable retains its argument's structure and support | `returned_callable_instantiation`, `returned_callable_retains_argument_support` |
| Unknown support is distinct from resource-free support | `unresolved_support_is_not_empty` |
| An actual closed value's analyzed storage matches its syntactic resource dependencies | `closed_value_storage_sound` |
| A resource-retaining closure has a scalar result summary and a concrete beta/bind execution | `Examples.constant_capture_and_result_differ`, `Examples.retaining_constant_beta_bind` |
| Factory substitution needs a comparison weaker than syntactic summary equality | `Examples.factory_beta_summary_is_not_syntactic_equality`, `Examples.factory_beta_summaries_agree_on_storage` |
| Current support equality is insufficient for substitution transport | `Examples.current_support_equality_is_not_stable` |

These results use `Ash.OneShot.ResultSummaries`. `Scoped` describes metadata
binding, not actual-value realization. `callResult` is one unfolding, not a
proved evaluator; the analyzer keeps applications symbolic and control-sensitive
forms unknown. The following layer establishes a substitution-stable comparison
and concrete substitution correspondence. Realization of inferred computation
results remains to be proved before these summaries can justify resource release.

[ResultTransport.lean](ResultTransport.lean) and
[ResultCodeSubstitution.lean](ResultCodeSubstitution.lean) connect that comparison
to closed-value substitution in the existing execution syntax. The
[substitution account](KERNEL.md#substitution-correspondence-for-result-summaries)
separates these results from the pending computation-result theorem.

| Result | Checked theorem or judgment |
| --- | --- |
| Capture storage agrees after every summary substitution | `StorageEq`, `StorageEq.substitute_congr` |
| Result and application structure survives related substitutions and known-call unfolding | `ResultEq`, `ResultEq.substitute_congr`, `ResultEq.call_result` |
| Related environments yield related analysis | `analyze_result_congr` |
| Analysis commutes exactly with summary renaming and substitution through its environment | `analyze_rename`, `analyze_substitute` |
| An actual closed value's analysis is independent of its surrounding environment | `closed_value_analysis_environment_independent` |
| Actual code and clause substitution expand dependencies exactly in place | `code_substitution_dependencies`, `clauses_substitution_dependencies` |
| Concrete substitution and environment extension have corresponding capture and result metadata | `code_capture_substitution`, `analyze_code_substitution` |
| One known-lambda unfolding agrees with analysis under parameter extension | `known_lambda_result` |
| Actual bind and beta events carry metadata correspondence for their reducts | `bind_constructs_summary_correspondence`, `beta_constructs_summary_correspondence` |
| A retaining factory and ordinary shadowing use the general substitution theorem | `Examples.retaining_factory_beta_correspondence`, `Examples.shadowed_parameter_substitution_correspondence` |
| The comparison distinguishes unresolved parameters and callable results | `Examples.distinct_parameters_not_storage_equivalent`, `Examples.unknown_not_parameter_equivalent`, `Examples.equal_storage_does_not_equate_callable_results` |

These results use `Ash.OneShot.ResultSummaries`. `StorageEq` compares ordered
support lists after arbitrary substitutions; `ResultEq` uses it only for
callable captures. Neither relation realizes an actual value by itself. The
concrete substitution theorem covers all syntax constructors, but forms already
analyzed as unknown remain unknown. Beta explicitly unfolds `callResult`;
`ResultEq` does not erase the analyzer's symbolic application node. General
result soundness, branch approximation, control-sensitive result rules and
preserved resource-boundary exclusion remain to be established.

[ResultBounds.lean](ResultBounds.lean) derives actual return-support bounds from
canonical declared-port shapes and checks the comparison's unfolding limit. The
[return-bound account](KERNEL.md#canonical-return-bounds-and-the-unfolding-limit)
explains the current-value and inference boundaries.

| Result | Checked theorem or judgment |
| --- | --- |
| First-order ports contain no function component | `ScopedPorts.Port.FirstOrder` |
| An actual typed first-order value has exactly its port's explicit resource support | `typed_first_order_value_support` |
| Unit values have empty actual support; first-order cell answers exclude their closing identity | `typed_unit_value_has_empty_support`, `typed_first_order_cell_return_excludes_identity` |
| A structural current-frame certificate derives value access checks and joined/ready progress | `FirstOrderRelease`, `first_order_value_access_checks`, `first_order_value_progress`, `first_order_ready_value_progress` |
| An identity-free callable port still permits stored resource dependencies | `BoundExamples.empty_port_resources_do_not_bound_callable_storage` |
| The retaining payload passes its actual boundary check and its Unit result safely releases the cell | `BoundExamples.callable_request_checks`, `BoundExamples.callable_source_access_trace` |
| The complete seven-step example adds owner freshness and preserves ledger/live support | `BoundExamples.callable_source_admitted_execution`, `BoundExamples.callable_source_final_ledger_and_support` |
| Closed pending applications can be storage equivalent while their unfolded supports differ | `ResultSummaries.ObservationGap.closed_pending_applications`, `pending_applications_storage_equivalent`, `unfolded_pending_support_differs` |
| Current comparison does not justify application-aware capture observations | `ResultSummaries.ObservationGap.current_comparison_does_not_justify_unfolding` |

Canonical-bound results use `Ash.OneShot.ScopedPorts`; observation limits use
`Ash.OneShot.ResultSummaries`. The first-order certificate is sufficient for
the current value step, not a source restriction or a preserved future-release
condition. The example proves `AccessRunSteps` with ledger/live-support
preservation, not all joined fields at every state. Unknown metadata stays
unknown. The existing summary comparisons remain valid for their current
observer. The following layer strengthens comparison and concrete substitution
transport; application-aware observation and actual-value realization remain
required.

[CaptureViews.lean](CaptureViews.lean) and
[CaptureViewSubstitution.lean](CaptureViewSubstitution.lean) preserve full result
structure inside captured applications. The [normalized-view account](KERNEL.md#normalized-capture-and-result-views)
explains the stronger comparison and its limits.

| Result | Checked theorem or judgment |
| --- | --- |
| Capture positions and application operands retain different information | `View`, `Atom`, `View.capture`, `normalize` |
| Normalization commutes with renaming, substitution and one known-call unfolding | `normalize_rename`, `normalize_substitute`, `normalize_call_result` |
| Stronger capture and result equivalence survive related replacements | `SameCapture.substitute_congr`, `Related.substitute_congr` |
| Equal captured applications have related operands and known-call unfoldings | `Related.captured_application_operands`, `Related.captured_application_call_result` |
| Every result view and capture atom has a checked summary representative | `normalize_encode`, `normalize_encode_atom`, `encode_injective` |
| View substitution has identity and composition laws | `view_substitute_identity`, `view_substitute_comp` |
| The stronger comparison distinguishes the captured-application counterexample | `Examples.pending_applications_distinguished`, `Examples.enclosing_callables_distinguished` |
| Equal replacement storage alone cannot justify substitution into an application | `Examples.replacement_capture_equality_is_insufficient` |
| An actual closed value's normalized captures are its exact resource atoms | `closed_value_capture_view` |
| Concrete capture and analyzer substitution preserve the stronger comparison | `code_capture_substitution`, `analyze_code_substitution` |
| Actual bind/beta reducts carry the stronger correspondence | `bind_constructs_summary_correspondence`, `beta_constructs_summary_correspondence` |
| Retaining factories and ordinary shadowing use the general stronger theorem | `Examples.retaining_factory_beta_correspondence`, `Examples.shadowed_parameter_substitution_correspondence` |

These results use `Ash.OneShot.CaptureViews`. Constructive result-view equality
uses its injective encoding into the existing summary syntax. The round trip
is from View through Summary back to View; it does not reconstruct an original
unnormalized summary. Normalization preserves application structure without
executing it. Precise actual-value realization and application-aware support soundness
remain unproved, as do control-sensitive result inference and source-derived
future release/closing checks. The next layer proves conservative support
soundness while applications remain unknown.

[ReturnSupport.lean](ReturnSupport.lean) bounds actual normally returned values
using the existing conservative observer. The [normal-result account](KERNEL.md#conservative-normal-result-soundness)
explains its full transition coverage and limited analysis precision.

| Result | Checked theorem or judgment |
| --- | --- |
| Finite support containment with unknown as the upper bound | `Below`, `Below.trans`, `Below.join_left`, `Below.join_right` |
| Capture and source-result analysis are monotone under environment support bounds | `captured_monotone`, `analyze_monotone` |
| Plain-frame analysis agrees with actual plugging and is monotone | `context_result_plug`, `context_result_monotone` |
| Ordered stack observation composes through actual cuts and cell updates | `stack_result_append`, `cut_result`, `cell_update_result` |
| Every actual raw transition refines the conservative result observation | `raw_step_result` |
| Actual finite executions preserve that approximation | `run_steps_result`, `raw_trace_result` |
| A finite source bound contains a normally returned closed value's actual resource dependencies | `returned_value_support`, `returned_value_excludes` |
| A branch returns one retaining closure within the bound of both alternatives | `Examples.actual_branch_return` |
| An ignored application is actually executed before an empty-support return | `Examples.ignored_call_trace`, `Examples.ignored_call_return_support` |
| Unknown is not finite, and the storage order does not justify application unfolding | `Examples.unknown_has_no_finite_bound`, `Examples.storage_order_does_not_justify_unfolding` |

These results use `Ash.OneShot.ReturnSupport`. The returned-value theorem is
partial correctness for executions from an empty stack to a closed value at
an empty stack. It assumes a finite source bound, which the conservative
observer cannot supply for unknown result forms. It proves no normal
termination, intermediate access safety, or retained-resource liveness.
Applications and control results stay unknown. The next layer supplies
preserved individual resource-return obligations; precise result-view
realization and general source-derived admission still need further proofs.

[ReturnBoundaries.lean](ReturnBoundaries.lean) preserves resource-return checks
through active and saved control. The [resource-return account](KERNEL.md#preserved-resource-return-obligations)
separates local allocation evidence from general source admission.

| Result | Checked theorem or judgment |
| --- | --- |
| Inferred support or canonical first-order shape can justify a cell's return | `Excludes`, `CellBound` |
| Active and recursively saved cells carry transformed incoming result checks | `Checked`, `ConfigurationChecked` |
| More precise inputs preserve checks; stack decomposition uses transformed tail inputs | `checked_monotone`, `checked_append` |
| Exact capture and full-prefix resumption preserve saved return evidence | `checked_cut`, `checked_resume` |
| Unit-answer closing releases and disposal preserve return checks | `close_control_checked`, `checked_discard` |
| Only an actual new resource needs a local entry certificate | `AllocationReturn` |
| Existing source typing derives first-order fresh-entry certificates and pairs them with actual entry | `typed_first_order_entry_certificate`, `typed_first_order_entry_constructs` |
| Every raw transition preserves return checks under local entry admission | `raw_step_preserves_checked` |
| Finite entry-certified executions erase to actual runs and preserve the invariant | `EntriesChecked`, `entries_checked_execute`, `run_steps_preserve_checked` |
| Actual typed values derive release exclusion and current access checks | `typed_cell_return_excludes`, `value_access_checks` |
| Value progress preserves both joint/readiness validity and the return invariant | `checked_value_progress`, `checked_ready_value_progress` |
| An outer-resource capture may return; the closing resource's own capture may not | `Examples.outer_capture_may_return`, `Examples.own_capture_cannot_return` |
| Applying the runtime observer to an unopened template can hide the newly acquired resource | `Examples.template_bound_does_not_admit_opening` |
| Actual capture/resume preserves a function-valued return certificate | `Examples.capture_resume_preserves_function_return` |

These results use `Ash.OneShot.ReturnBoundaries`. Value progress derives its
release check from preserved structural evidence and actual typing. General
fresh-entry admission remains explicit, with a source-derived route proved
for first-order answers. The next layer adds finite inferred source bounds
for some function-valued answers. Payload and disposal checks, closing
certificates and precise control/application result inference remain separate.
The function-return example establishes raw events and
return checks, not complete typed or access-admitted execution. No Core
semantic change follows from the template-analysis counterexample.

[TemplateDependencies.lean](TemplateDependencies.lean) and
[TemplateSupport.lean](TemplateSupport.lean) derive finite source return bounds
that survive resource opening. The [source-bound account](KERNEL.md#finite-source-bounds-across-resource-opening)
explains binding, the executable check and its precision limits.

| Result | Checked theorem or judgment |
| --- | --- |
| Source dependency lists retain bound resource names and distinguish binder namespaces | `Dep`, `dependencies`, `clauseDependencies` |
| Lexical opening transports exact ordered dependency lists | `dependencies_instantiate`, `clauses_instantiate` |
| Projections recover runtime dependencies and free resource names | `runtime_dependencies`, `runtime_clauses`, `bound_dependencies`, `bound_clauses` |
| Resource-closed code has no unresolved resource dependency | `closed_dependencies_have_no_bound` |
| Finite source support inference commutes with resource opening and mapped ordinary environments | `infer_instantiate` |
| Source inference agrees with the runtime observer on resource-closed code | `runtime_agreement` |
| A finite Boolean check characterizes the sufficient source certificate | `SourceBound`, `check`, `check_iff_source_bound` |
| A world-fresh opening leaves the finite check unchanged | `infer_runtime_instantiate`, `available_fresh_opening`, `check_fresh_opening` |
| Resource closure connects the template certificate with the runtime support bound | `source_bound_runtime_iff`, `fresh_opening_runtime_iff` |
| Source bounds contain the actual opened body's runtime support | `opened_source_bound` |
| Successful checking constructs actual entry and its local return certificate | `source_entry_certificate`, `source_entry_constructs`, `checked_source_entry` |
| Resource shadowing excludes the initializer and never binds an allocated identity | `Examples.nested_resource_shadows_its_own_name`, `Examples.initializer_remains_outside_new_binding`, `Examples.equal_numeric_activation_is_not_shadowed` |
| Aliases and nested operation metadata retain unresolved resource dependencies | `Examples.alias_capture_rejected`, `Examples.nested_operation_metadata_retains_bound_name` |
| A function-valued answer receives an inferred entry certificate | `Examples.function_return_entry` |
| A copied-read closure accepted by Core remains unknown to this observer | `Examples.copied_read_closure_is_still_unknown` |
| Without freshness or resource closure, opening or runtime projection can change the evidence | `Examples.nonfresh_opening_can_change_the_check`, `Examples.unresolved_capture_has_misleading_runtime_projection` |

These results use `Ash.OneShot.TemplateDependencies` and
`Ash.OneShot.TemplateSupport`. Completeness of the Boolean check is relative
to `SourceBound`, not all safe or Core-accepted programs. The supplied world
does not prove liveness, and the constructed raw event does not prove
issuance-history freshness or joint access admission. The analysis still
returns unknown for applications and control results. Its copied-read gap
requires type-informed result analysis; it does not establish a Core defect.
General source progress and Core correspondence remain required.

[TemplateSubstitution.lean](TemplateSubstitution.lean) carries template return
certificates through replacement by actual closed values. The
[substitution account](KERNEL.md#template-certificates-through-value-substitution)
distinguishes stored-support bounds, ordered substitutions and actual bind
execution.

| Result | Checked theorem or judgment |
| --- | --- |
| A closed-value replacement within a variable's support bound preserves conservative result support | `substitution_below` |
| Each replacement checks actual closure and stored support against the fixed environment | `BindingsChecked` |
| Canonical first-order typing can supply a check for an actual value | `typed_first_order_binding` |
| Ordered closed-value substitutions preserve support bounds and resource closure | `replaceAll`, `replacements_below`, `replacements_resource_closed` |
| Those substitutions commute with resource opening | `replacements_instantiate` |
| Earlier template bounds contain the actual opened and substituted body's result support | `opened_replacements_bound` |
| Checked replacements preserve both the template certificate and the original finite check | `source_bound_replacements`, `checked_replacements_preserve_check` |
| The finite check and checked replacements construct actual resource entry and its local return certificate | `replaced_entry_certificate`, `checked_replaced_entry` |
| Actual strict binding leads to entry of the same substituted body | `bind_then_entry`, `Examples.actual_alias_bind_and_entry` |
| A retaining function can fit an outer-resource bound but cannot fit an empty bound | `Examples.outer_function_checked`, `Examples.empty_bound_rejects_retaining_value` |
| Substitution of a retaining function preserves acceptance of its enclosing template | `Examples.substituted_function_template_checked` |
| Sequential substitution is not the evaluation of nested bindings with repeated names | `Examples.repeated_names_do_not_overwrite_inserted_values` |

These results use `Ash.OneShot.TemplateSubstitution`. Storage comparison does
not justify unfolding calls. First-order typing is used only after a value
exists, so the pending copied-read analysis gap remains. Reflection through
a world-fresh opening proves preservation of the original finite checker
on the substituted template. Its fresh witness is used only in the proof,
not as a runtime allocation. The entry theorem applies the original entry
construction to that preserved check. Raw bind and entry
events do not supply live ownership, issuance history or joint access
admission. General calculus admission and Core correspondence remain open.

[ContinuationBounds.lean](ContinuationBounds.lean) retains declared input
bounds in saved continuations. The [continuation-bound account](KERNEL.md#declared-input-bounds-through-capture-and-resumption)
explains their connection to actual typed operands and the remaining
expression-analysis boundary.

| Result | Checked theorem or judgment |
| --- | --- |
| Declared input bounds are finite exactly for first-order ports | `portBound`, `port_bound_finite`, `first_order_port_bound` |
| Actual typed values fit those bounds | `typed_value_below_port` |
| The same historical ticket lookup connects a resumed operand to the actual saved input | `resume_operand_bound` |
| Saved return checks use their input ports; previous certificates remain sufficient | `Checked`, `ConfigurationChecked`, `old_checked_suffices` |
| Exact stack decomposition, capture and full restoration preserve return bounds | `checked_append`, `checked_cut`, `checked_capture`, `checked_resume` |
| The operation signature supplies the actual capture annotation and typed checked successor | `capture_constructs_typed_checked` |
| Disposal materialization and cell updates preserve checks | `close_control_checked`, `checked_discard`, `cell_update_checked` |
| Every raw transition preserves checks under current typing and local resource-entry evidence | `raw_step_preserves_checked` |
| Actual typed resumption preserves typing and return checks together | `typed_resume_constructs_checked` |
| Actual value returns derive release exclusion and access checks | `typed_cell_return_excludes`, `value_access_checks` |
| Value progress retains joint/readiness validity and the revised return invariant | `checked_value_progress`, `checked_ready_value_progress` |
| An integer-producing request captures and resumes a scope returning a closure of the copied integer | `Examples.typed_capture_and_resume` |
| The old saved-unknown check rejects this capture; callable input ports remain unknown | `Examples.old_unknown_capture_rejected`, `Examples.callable_input_stays_unknown` |
| Without input typing, a raw resume can violate its saved return bound | `Examples.raw_resume_without_input_typing_can_break_the_bound` |

These results use `Ash.OneShot.ContinuationBounds`. All-step preservation
proves the return invariant, while the typed constructors separately supply
successor typing. The positive example begins with the stack checked at the
operation's integer result bound. It does not supply the current expression
analyzer's check for the requesting configuration, an initial-term admission
proof or a builtin cell-read execution. General typed result inference,
calculus admission and Core correspondence remain open.

[OperationResults.lean](OperationResults.lean) uses exact operation signatures
in stored-result analysis. The [operation-result account](KERNEL.md#signature-aware-operation-result-analysis)
separates its substitution and context results from the remaining machine
preservation proof.

| Result | Checked theorem or judgment |
| --- | --- |
| Decoding a frozen instance preserves every argument and its exact key | `decode_frozen_argument`, `decode_frozen_arguments`, `decode_frozen_effect` |
| A known operation uses its declared result port's support bound | `operationBound`, `operation_bound_known`, `analyze_perform_known` |
| Support analysis respects equal or bounded environments | `captured_support_congr`, `analyze_support_congr`, `analyze_monotone` |
| Actual closed values retain their exact resource support | `closed_value_storage_sound`, `closed_value_old_support`, `closed_value_environment_support` |
| Concrete closed-value substitution agrees with extended-environment analysis | `capture_substitution_support`, `analyze_substitution_support` |
| The new observer refines the old support bounds | `analyze_refines_old` |
| Context analysis agrees with actual plugging and is monotone | `context_result_plug`, `context_result_monotone` |
| Actual typed values and resumed operands fit their declared bounds | `typed_value_below_port`, `resumed_value_below_input` |
| Actual bind steps carry support correspondence | `bind_constructs_support_correspondence` |
| Actual builtin read/write steps preserve their head-expression result summary | `read_constructs_result`, `write_constructs_result` |
| The opened copied-read closure now has empty support while a closure reading later retains its owner | `Examples.copied_read_closure_has_empty_bound`, `Examples.copied_template_opening_has_empty_bound`, `Examples.stored_read_still_retains_its_owner` |
| Unknown keys, callable results and pending applications remain unknown | `Examples.unresolved_operation_key_is_unknown`, `Examples.callable_result_keeps_unknown_storage`, `Examples.known_application_remains_unknown` |
| Runtime projection cannot replace unopened-template checking | `Examples.unopened_capture_requires_template_analysis` |
| Finite request bounds require signature agreement for raw capture annotations | `Examples.finite_result_requires_capture_annotation_agreement` |

These results use `Ash.OneShot.OperationResults`. The decoder theorem proves
`decode(freeze(instance)) = some instance`, not both inverse directions.
The analyzer's closed-value support theorem requires resource closure.
Substitution and refinement observe storage without unfolding calls. The
following module integrates whole-stack return-check preservation with
signature-constrained capture annotations; current expression typing alone
does not constrain an arbitrary raw capture. Initial-term admission and Core correspondence remain
open.

[OperationReturns.lean](OperationReturns.lean) integrates the signature-aware
observer with active and saved return checks on the existing execution stack.

| Result | Checked theorem or judgment |
| --- | --- |
| Signature-aware frames preserve bounds; actual capture cuts reconstruct checked stacks | `frame_result_monotone`, `checked_monotone`, `checked_append`, `cut_result`, `cut_cap_result`, `checked_cut` |
| Saved stacks retain their input bounds through capture and actual recomposition | `checked_capture`, `checked_resume` |
| Capture checks the actual operation's declared result against the saved input port | `CaptureInput`, `capture_input_known` |
| Every actual raw transition preserves return checks under current typing, fixed cell signatures and local capture/allocation conditions | `raw_step_preserves_checked` |
| Current request checking constructs an actual capture with signature agreement, table extension, successor typing and return checks | `capture_constructs_typed_checked`, `typed_capture_constructs_checked` |
| Typed resumption constructs the actual step with successor typing and return checks | `typed_resume_constructs_checked` |
| Generated disposal and cell updates preserve return checks | `close_control_checked`, `checked_discard`, `cell_update_checked` |
| Actual typed value returns exclude the closing owner and supply release access checks | `typed_cell_return_excludes`, `value_access_checks` |
| Current values require no new allocation or capture annotation | `value_allocation_return`, `value_capture_input` |
| Value execution and progress preserve the new return checks with existing joint validity or readiness | `run_value_preserves_checked`, `named_value_preserves_checked`, `checked_value_progress`, `checked_ready_value_progress` |
| A pending integer-producing request and its actual capture/resume pass return checking | `Examples.requesting_checked`, `Examples.capture_agreement`, `Examples.capture_and_resume_checked` |
| Reference and Unit annotations for an Int-producing operation are rejected, even when storage bounds coincide | `Examples.wrong_capture_input_rejected`, `Examples.scalar_mismatch_rejected` |
| An actual builtin read preserves return checks throughout its enclosing stack | `Examples.builtin_read_preserves_whole_stack` |

These results use `Ash.OneShot.OperationReturns`. The all-step theorem proves
return-check preservation, not arbitrary raw successor typing. Its value
progress wrappers require `withCellSignatures users`. Allocation certificates
use the actual opened body's new runtime summary. The following modules supply
those certificates from declaration-derived template checks; general
initial-term admission remains open. The examples do not prove complete joint
execution or Core simulation. See the
[proof account](KERNEL.md#signature-aware-return-check-preservation) for the
premises and remaining construction.

[DeclarationResults.lean](DeclarationResults.lean) derives symbolic and runtime
result bounds from the existing validated resource-parameter declarations.

| Result | Checked theorem or judgment |
| --- | --- |
| Positional resource arguments bind before opening and agree with runtime binding after freezing | `namedParameters`, `named_parameters_open`, `named_parameters_frozen` |
| Declared first-order result bounds commute with opening and agree with structural type realization | `name_bound_open`, `type_bound_open`, `name_bound_realizes`, `type_bound_realizes` |
| Exact declaration lookup commutes with opening | `operation_bound_open` |
| Runtime decoding preserves frozen and realized type metadata | `mapM_frozen_effects`, `mapM_frozen_names`, `decode_frozen_type`, `decode_realized_type` |
| The compiled signature and bound agree with existing declaration judgments | `declared_signature_known`, `declared_operation_bound` |
| Successful and failed source/runtime result lookups agree | `operation_bound_runtime`, `closed_operation_bound_runtime` |
| Resource-closed argument trees and effects have exact frozen forms | `closed_argument_frozen`, `closed_arguments_frozen`, `closed_effect_frozen` |
| Alias positions survive; wrong arity, nominal/application arguments and malformed declarations reject | `Examples.positional_aliases_preserved`, `Examples.wrong_arity_rejected`, `Examples.nonresource_argument_rejected`, `Examples.nested_resource_argument_rejected`, `Examples.invalid_declarations_rejected` |
| Missing lookups stay unknown, fresh instances derive their corresponding ports, and cells keep fixed signatures | `Examples.unknown_family_and_operation_rejected`, `Examples.same_declaration_at_distinct_activations`, `Examples.builtins_ignore_user_registry` |
| An invalid input declaration rejects even when its output is scalar | `Examples.malformed_input_rejected_before_result_analysis` |

These results use `Ash.OneShot.DeclarationResults`. They authenticate lookup
within `FamilyValid`'s existing resource-parameter fragment, not all Core
parameters, kinds, declaration provenance or visibility. Callable result
support remains unknown. No arbitrary signature-equivariance premise is used.

[DeclarationTemplates.lean](DeclarationTemplates.lean) uses those declarations
to check resource bodies before allocation and derive their local return bounds.

| Result | Checked theorem or judgment |
| --- | --- |
| Template inference commutes with opening and agrees with the signature-aware runtime observer on resource-closed code | `infer_instantiate`, `runtime_agreement`, `infer_runtime_instantiate` |
| The finite checker characterizes its support certificate and the bound after fresh opening | `check_iff_source_bound`, `check_fresh_opening`, `source_bound_runtime_iff`, `fresh_opening_runtime_iff`, `opened_source_bound` |
| A checked template supplies the actual opened body's allocation-return certificate and raw entry | `source_entry_certificate`, `source_entry_constructs`, `checked_source_entry` |
| Named entry uses actual issuance freshness and preserves return checks with joint validity | `resource_named_preserves_checked`, `checked_resource_entry_progress` |
| A copied-read closure checks before opening and obtains an entry certificate for every identity | `Examples.copied_read_template_checked`, `Examples.copied_template_entry` |
| Retained readers and declared reference captures reject; copied integer and outer-reference captures pass | `Examples.retained_reader_rejected`, `Examples.declared_reference_capture_rejected`, `Examples.declared_outer_reference_capture_accepted`, `Examples.generic_copied_integer_checked` |
| Callable results and unknown calls stay unknown; unopened captured names remain visible | `Examples.callable_result_remains_unknown`, `Examples.unknown_call_remains_unknown`, `Examples.unopened_capture_not_erased` |
| A concrete copied-read initial term is typed and jointly valid, and has a fresh named allocation preserving both joint validity and return checks | `Examples.copied_initial_typed`, `Examples.copied_initial_valid`, `Examples.copied_initial_joint_entry` |

These results use `Ash.OneShot.DeclarationTemplates`. The joined progress result
covers resource entry from a currently valid state. The following module
supplies ordinary-substitution preservation under
structural closed-value bounds. General initial-term admission, complete
execution/release of the example and Core correspondence remain open. See the
[declaration/template proof account](KERNEL.md#declaration-derived-template-entry).

[DeclarationSubstitution.lean](DeclarationSubstitution.lean) preserves the
new template checks under actual closed-value substitution and connects them
to a bind followed by fresh resource entry.

| Result | Checked theorem or judgment |
| --- | --- |
| Existing structural binding certificates also bound the new analyzer on actual closed values | `closed_value_bound_iff` |
| Substitution and ordered replacements preserve stored-result bounds | `substitution_below`, `replacements_below` |
| Bounds survive opening and reflect back to the same finite template checker | `opened_replacements_bound`, `source_bound_replacements`, `checked_replacements_preserve_check` |
| Replaced templates supply actual raw entry and its local allocation certificate | `replaced_entry_certificate`, `checked_replaced_entry`, `bind_then_entry` |
| Current typing derives ordinary bind closure and resource closure | `typed_bind_ready` |
| An actual named bind followed by fresh entry preserves joint validity and return checks at both states | `checked_bind_resource_progress` |
| A template with a pending read passes the new check and remains checked after certified integer replacement | `Examples.earlier_template_checked`, `Examples.copied_integer_binding`, `Examples.substituted_template_checked` |
| Actual first-order typing supplies the same binding certificate | `Examples.typed_integer_supplies_same_binding` |
| A certified outer-retaining function preserves the template check; an uncertified hidden handle breaks it | `Examples.retained_outer_function_preserves_template`, `Examples.unchecked_function_replacement_breaks_check` |
| Repeated replacement names retain their existing order | `Examples.repeated_names_keep_order` |
| A concrete typed initial term exercises both named steps with their joint invariants | `Examples.initial_typed`, `Examples.initial_valid`, `Examples.actual_bind_then_joint_entry` |

These results use `Ash.OneShot.DeclarationSubstitution`. They reuse the existing
binding and replacement grammar. The two-step theorem takes current `Valid`,
return checks, an actual value's support bound and a checked resource body; it
derives the ordinary lexical premises from typing. It proves neither `Ready`
preservation nor the example's later read/release. Nested-template admission,
bounds for arbitrary pending computations, general execution admission and
Core correspondence remain open. See the
[substitution proof account](KERNEL.md#declaration-template-substitution).

[SymbolicTemplates.lean](SymbolicTemplates.lean) transports finite template
checks through lexical opening and preserves saved outer aliases across a
shadowing resource binder.

| Result | Checked theorem or judgment |
| --- | --- |
| Symbolic membership characterizes a finite support bound and permits world enlargement | `check_iff_bound`, `check_world_mono` |
| Opening transports code, support metadata and worlds to the existing runtime checker | `check_transport`, `available_iff_subset`, `runtime_world_check`, `realized_world_map`, `realized_check`, `realized_check_in_world` |
| Initializer inference commutes with snapshotting its binding; fully realized snapshots remain stable | `snapshot_binding`, `snapshot_runtime_stable`, `realized_snapshot_stable` |
| Actual entry masks the body environment and preserves joint validity and return checks using a realized subworld | `masked_binder_missing`, `symbolic_entry_certificate`, `symbolic_resource_entry_progress` |
| Saved outer aliases pass where retained inner references fail; unsnapshotted conflation has no masked realization | `Examples.saved_alias_passes_inner_reference_fails`, `Examples.unsnapshotted_membership_conflates_scopes`, `Examples.masked_shadow_has_no_realization`, `Examples.distinct_acquisitions_cannot_share_one_name` |
| Initializers use outer scope, snapshots survive inner opening, and unknown bounds stay unknown | `Examples.initializer_uses_outer_body_masks_it`, `Examples.inner_opening_keeps_saved_outer_identity`, `Examples.snapshot_unknown_stays_unknown` |
| Several symbolic aliases may denote one resource and check in a larger issued world | `Examples.noninjective_outer_aliases`, `Examples.aliased_world_checks_in_larger_issued_world` |
| A checked actual outer-retaining value can be bound before raw inner entry with its allocation-return certificate | `Examples.actual_outer_alias_replacement`, `Examples.actual_outer_alias_bind_then_inner_entry` |

These results use `Ash.OneShot.SymbolicTemplates`. Environment realization
relates support metadata; actual value bounds remain separate structural
premises. The raw examples do not prove the outer acquisition or complete
nested execution. Recursively deriving these environments from initial terms,
general progress and Core correspondence remain open. See the
[symbolic-world proof account](KERNEL.md#symbolic-template-worlds-and-shadowing).

[GenerativeResults.lean](GenerativeResults.lean) derives finite results through
nested resources, using recursive premises at every fresh body opening.

| Result | Checked theorem or judgment |
| --- | --- |
| Strict children and generative bodies have structural derivations; finite storage lists have exact summaries | `Derives`, `summary_support` |
| Derivations supply resource closure and bound actual closed-value storage | `resource_closed`, `finite_check_value_support`, `value_support` |
| Certified ordinary substitution preserves recursive derivations, including fresh openings and ordinary shadowing | `checked_substitution`, `value_substitution_shape`, `leaf_substitution_shape`, `substitution` |
| Derivations transport to larger worlds | `world_mono` |
| An actual initializer supplies its own replacement bound; a named bind retains the justified environment and preserves joint validity with the cell-spine certificate | `value_below_summary`, `bind_value_derivation`, `bind_preserves_spine_and_joint` |
| Actual entry exposes its recursive body bound and excludes the new owner | `resource_entry` |
| An unchanged outward bound survives consecutive actual cell entries and returns | `CellSpine`, `resource_entry_preserves_spine`, `value_return_access`, `cell_return_preserves_spine` |
| The same value-return event also preserves current joint validity | `cell_return_preserves_joint` |
| Returning an owned reference is rejected even when an enclosing bind ignores it | `owned_reference_return_rejected`, `Examples.ignored_unsafe_initializer_rejected` |
| Nested resources have a finite closure-result derivation where the old observer reports unknown | `Examples.inner_bound`, `Examples.program_bound`, `Examples.old_observer_loses_nested_result` |
| Both entries and returns retain result/spine evidence; the actual run completes both owners | `Examples.outer_entry_keeps_recursive_bound`, `Examples.inner_entry_keeps_recursive_bound`, `Examples.inner_return_keeps_bound`, `Examples.outer_return_keeps_bound`, `Examples.nested_trace`, `Examples.nested_execution`, `Examples.nested_ownership_complete` |
| Actual integer substitution and a preceding bind join the nested example | `Examples.pending_program_bound`, `Examples.integer_substitution_preserves_nested_derivation`, `Examples.preceding_bind_retains_initializer_derivation`, `Examples.actual_bind_then_nested_execution` |
| A concrete typed initial bind exercises the joined theorem without an extra replacement-bound premise | `Examples.preceding_bind_typed`, `Examples.before_bind_valid`, `Examples.actual_joint_bind_derives_replacement_bound` |
| The nested initial term is typed and jointly valid; applying its returned closure produces 17 | `Examples.inner_typed`, `Examples.program_typed`, `Examples.initial_joint_valid`, `Examples.returned_callback_application` |

These results use `Ash.OneShot.GenerativeResults`. The declarative result
judgment is independent of typing and latent-body safety; it is not a complete
admission checker. The spine certificate in this module covers consecutive cell frames. The
current value bind retains its justified extended analysis environment. The next
module adds ordinary-frame and saved-capture transport; full admission, all-step
preservation and Core correspondence remain open. See the [generative-result proof account](KERNEL.md#generative-result-derivations).

[GenerativeFrames.lean](GenerativeFrames.lean) carries recursive result bounds
through saved ordinary environments, actual contexts and captured forests.

| Result | Checked theorem or judgment |
| --- | --- |
| Actual closed-value support transfers to the waiting frame's environment | `closed_value_check`, `returned_value_rebind` |
| Actual focus decomposes a supported expression, and plugging reconstructs it | `ContextReturns`, `focus_decompose`, `context_plug`, `context_plug_returned_value` |
| Stack transformations compose and decompose at matching support bounds | `StackReturns`, `stack_append`, `stack_decompose`, `cell_spine_embeds` |
| Context and stack certificates transport to larger worlds | `context_world_mono`, `stack_world_mono` |
| Actual capture preserves the saved certificate; resumption requires explicit prefix compatibility | `capture_certificate`, `resume_recomposition` |
| The actual saved input port bounds the resumed value under the same declaration-compiled signature | `ResumeBound`, `resumed_value_derivation`, `resume_step` |
| Local focus, plugging, value binding, entry and normal returns preserve result certificates | `ConfigurationReturns`, `focus_step`, `plug_step`, `bind_step`, `resource_step`, `cell_return_step`, `handler_return_step` |
| An eight-step nested-resource execution retains the waiting bind's environment and preserves its ledger | `Examples.ordinary_frame_nested_trace`, `Examples.ordinary_frame_nested_execution`, `Examples.ordinary_frame_nested_ledger`, `Examples.restored_waiting_environment`, `Examples.initial_joint_valid` |
| Concrete capture and resume certificates use compiled declarations; a nonempty prefix composes changing bounds | `Examples.actual_capture_keeps_certificate`, `Examples.declared_capture_state_typed`, `Examples.actual_resume_restores_certificate`, `Examples.nonempty_prefix_recomposition` |
| A callable port cannot erase stored dependencies or supply a finite resume-input bound | `Examples.callable_port_does_not_erase_retained_support`, `Examples.callable_resume_port_remains_unknown` |

These results use `Ash.OneShot.GenerativeFrames`. Saved-capture output and
prefix-input bounds match explicitly; type equality alone is insufficient.
The nonempty-prefix example proves certificate composition, not a full typed
execution. Handler clause results, callable input support, request payloads,
cleanup and full initial-program checking remain open. These are one-shot
integration obligations. See the
[frame and capture proof account](KERNEL.md#generative-results-through-frames-and-captures).

[GenerativeProgress.lean](GenerativeProgress.lean) joins result certificates
with the scoped joint invariant and current closing interfaces.

| Result | Checked theorem or judgment |
| --- | --- |
| The local boundary excludes ready requests selected by actual source-handler cuts | `NoSourceRequest`, `nonrequest_boundary`, `value_boundary`, `builtin_boundary` |
| Current result derivations identify their supported outer forms | `SupportedHead`, `supported_head` |
| Cell updates and larger worlds retain result certificates | `cell_update_preserves_results`, `configuration_world_mono` |
| Actual returned-value support derives release checks; the boundary excludes source capture | `return_access_checks` |
| Every compatible raw step preserves results using actual issued freshness | `raw_preserves_results`, `named_preserves_results` |
| No ticket allocation preserves the registry and historical closing interfaces | `boundary_allocates_no_ticket`, `boundary_named_registry_unchanged`, `boundary_preserves_closing` |
| Current progress constructs the same step with joint readiness and result certificates | `current_progress`, `nonrequest_progress`, `value_progress`, `closed_progress` |
| Initial typing, usage and result checks establish the first joined step | `initial_progress`, `Examples.ordinary_initial_progress` |
| An actual builtin read retains the waiting continuation's certificate | `Examples.reading_returns`, `Examples.builtin_read_results` |
| A plug can expose a source request while preserving results; freshness cannot be removed | `Examples.ready_source_request_rejected`, `Examples.boundary_need_not_survive_plug`, `Examples.freshness_is_necessary` |

These results use `Ash.OneShot.GenerativeProgress`. The successor retains
`Ready` and `ConfigurationReturns`, but need not retain `NoSourceRequest`.
The result judgment still lacks application, handler, resumption, discard and
cleanup constructors. The theorem therefore does not establish whole-execution
progress or full initial-program checking. See the
[progress join account](KERNEL.md#generative-results-joined-with-current-progress).

[ClauseResults.lean](ClauseResults.lean) checks lexical continuation results
and handler clauses over the existing expression grammar.

| Result | Checked theorem or judgment |
| --- | --- |
| Handler bodies and clauses share an answer bound; each clause has its own lexical ticket | `TicketBound`, `PortBound`, `Derives`, `ClausesDerive` |
| Resource closure and actual stored-value support follow from result derivations | `resource_closed`, `actual_value_derivation`, `value_support` |
| Larger worlds and ordinary substitution preserve expression and clause derivations | `world_mono`, `clauses_world_mono`, `replacement_under_binding`, `substitution`, `clauses_substitution` |
| An actual selected clause receives its declared parameter bound from the same lookup as operand typing | `selected_clause`, `selected_clause_substitution` |
| Actual handler clauses and saved interfaces construct a raw capture and active clause result | `HandlerResults`, `capture_result`, `Examples.actual_capture_checks_clause` |
| Source-derived operand support and matching saved/prefix bounds construct actual resume results | `resume_inversion`, `resume_result`, `Examples.actual_clause_resume` |
| Nested handler source has independent result, typing and one-shot checks, establishing initial readiness | `Examples.nested_handlers_checked`, `Examples.nested_handlers_typed`, `Examples.nested_handlers_use_one_shot`, `Examples.nested_initial_ready` |
| Thirteen actual steps reach 17 and preserve the ticket ledger | `Examples.nested_trace`, `Examples.nested_execution`, `Examples.nested_ledger` |
| Result information grants neither repeated use nor access to another lexical ticket; callable ports remain unknown | `Examples.result_bounds_do_not_grant_reuse`, `Examples.wrong_clause_ticket_rejected`, `Examples.callable_parameter_bound_unknown` |

These results use `Ash.OneShot.ClauseResults`. Capture's payload access and
joint validity remain separate obligations. The nested trace installs its inner
handler after consuming the outer ticket, and does not prove readiness at every
state. The following module supplies generalized result-frame transport;
callable behavior, payload and cleanup integration, full progress and Core
correspondence remain open. See the
[clause-result proof account](KERNEL.md#lexical-continuation-results-and-clause-checking).

[ClauseFrames.lean](ClauseFrames.lean) retains the generalized expression
judgments and lexical continuation contracts in actual runtime frames.

| Result | Checked theorem or judgment |
| --- | --- |
| Historical result metadata links lexical scopes to runtime owners without granting use | `ResultRecord`, `Registry`, `ScopeBound`, `scope_resolves` |
| Existing contexts embed; focus and plug preserve the generalized result component | `ContextReturns`, `context_embeds`, `focus_decompose`, `context_plug`, `focus_step`, `plug_step` |
| Closed returned values restore saved environments with a justified larger support bound | `returned_value_rebind`, `context_plug_returned_value` |
| Stack interfaces compose, decompose and accept smaller inputs while retaining saved expectations | `StackReturns`, `stack_input_weaken`, `stack_append`, `stack_decompose` |
| Worlds and historical registry extensions transport frame certificates | `context_world_mono`, `insert_extends`, `scope_extends`, `stack_registry_extends`, `stack_world_mono` |
| Actual handler cuts recover selected clauses and interfaces; declared output support fits the captured input | `handler_cut_certificate`, `perform_check`, `declared_output_included` |
| Capture constructs fresh result metadata and the successor certificate from the actual checked request and stack | `capture_step` |
| One shared record derives saved-output/prefix-input compatibility and the actual resume result | `resume_recomposition`, `resume_step` |
| Sequencing, handler and clause returns, and resource entry/return preserve results; cell return derives release access | `bind_step`, `handler_entry_step`, `handler_return_step`, `clause_return_step`, `resource_step`, `cell_return_step` |
| The existing resource-owning capture/resume retains its cell and ordinary context under the generalized judgments | `Examples.resource_request_results`, `Examples.resource_capture_resume_results` |
| All fourteen states of the existing nested-clause run carry result certificates | `Examples.initial_results`, `Examples.outer_request_typed`, `Examples.inner_request_typed`, `Examples.nested_results` |
| Conflicting historical answers and resource erasure are rejected; conservative saved inputs accept smaller closed values | `Examples.wrong_historical_answer_rejected`, `Examples.resource_support_cannot_be_erased`, `Examples.smaller_closed_value_restores_saved_environment` |

These results use `Ash.OneShot.ClauseFrames`. Within this module, the result
registry is separate and capture freshness is a result-registry premise. The
following joint construction connects its finite input records to issued history. Payload access, callable behavior, disposal and cleanup,
complete initial-term checking, whole-execution progress and Core correspondence
remain open. Intermediate result checking is not intermediate joint readiness.
See the [retained-contract proof account](KERNEL.md#retained-continuation-result-contracts).

[ClauseJoint.lean](ClauseJoint.lean) combines result bounds with the existing
ownership, type/effect and one-shot usage invariant on the same execution.

| Result | Checked theorem or judgment |
| --- | --- |
| One record supplies both projections and authenticates the finite continuation input | `TicketRecord`, `Registry.joint`, `Registry.results`, `joint_insert`, `results_insert`, `active_input_bound` |
| Exact issued history supplies combined/result registry freshness | `recorded_history`, `registry_fresh`, `result_registry_fresh` |
| Historical records remain unchanged under fresh insertion and composed extensions | `RegistryExtends`, `registry_extends_refl`, `registry_insert_extends`, `registry_extends_trans` |
| Independent initial checks establish the combined state invariant | `Valid`, `initial_configuration_valid` |
| One selected clause, operation output, owner and successor preserve every component on capture | `capture_preserves` |
| Actual typed arguments with empty support derive outward payload access | `empty_payload_access_checks` |
| Resume derives closure and access, preserves the ledger and result bounds, and keeps the same registry | `resume_access_checks`, `resume_preserves` |
| Handler entry exposes its actual metadata and preserves the combined judgment | `named_raw_step`, `handler_entry_results`, `handler_entry_shape`, `handler_entry_preserves` |
| Handler, clause and cell returns preserve the combined invariant; cell release uses actual result exclusion | `current_closed_value`, `value_access_checks`, `handler_return_preserves`, `clause_return_preserves`, `cell_return_preserves` |
| Certified traces retain every state invariant and all historical records | `CertifiedSteps`, `certified_execution`, `certified_final`, `certified_registry_extension` |
| A five-step checked handler execution returns 17 with ticket 5 issued and consumed once | `Examples.initial_valid`, `Examples.single_handler_execution`, `Examples.single_handler_ledger` |
| Historical records remain after consumption but cannot authorize another resume; callable input support stays unknown | `Examples.completed_record_remains`, `Examples.consumed_ticket_cannot_resume`, `Examples.callable_input_is_not_silently_empty` |

These results use `Ash.OneShot.ClauseJoint`. The combined record currently
requires a canonical finite continuation input bound. Its capture theorem
retains an access premise; the following declaration-boundary construction
derives it for the represented finite-port fragment. Callable contracts, disposal/cleanup and closing
interfaces, full initial-term checking, whole-execution progress and Core
correspondence remain open. `Valid` is not full `Ready`, and certified traces
are not general progress or preservation from initial validity alone. The
five-step example has no cell. See the [joint-record proof account](KERNEL.md#joint-continuation-records-and-ownership).

[PayloadBoundary.lean](PayloadBoundary.lean) derives capture payload access
from declared argument resources and the actual selected handler's support.

| Result | Checked theorem or judgment |
| --- | --- |
| Parameter lookup ranges over the actual resource arguments, including aliases | `parameter_environment_range`, `Examples.parameter_aliases_preserved` |
| Realized declared types and erased operation ports mention only effect-instance arguments | `realized_declared_support`, `declared_operation_resources`, `signature_resources` |
| Actual typed finite payload support fits the selected outside tail | `typed_payload_bound`, `payload_crosses_selected_handler` |
| The actual retained clause supplies the finite input bound and derives current request access | `current_payload_access`, `request_access_checks` |
| The same capture and combined successor are constructed without an access-check premise | `capture_without_payload_premise` |
| The nonempty outer-handle example has an actual cut, compiled port, clause coverage, and checked control | `Examples.operation_known`, `Examples.selected_cut`, `Examples.clause_types`, `Examples.coverage`, `Examples.control_effects`, `Examples.control_types` |
| The runtime boundary owns both cells and has the complete combined invariant | `Examples.request_results`, `Examples.initial_valid`, `Examples.nonempty_payload_crosses`, `Examples.capture_checks_are_derived` |
| Six actual steps capture/resume and release both cells with every state checked | `Examples.resource_capture_release_execution`, `Examples.resource_capture_final_ledger` |
| The inner handle cannot cross that boundary; hidden declaration atoms are rejected | `Examples.captured_inner_handle_rejected`, `Examples.hidden_declaration_atom_rejected` |

These results use `Ash.OneShot.PayloadBoundary`. They apply to the represented
resource-parameter declarations and finite argument support. Callable ports
still do not bound stored captures. The example begins with already-owned cells
and proves normal release after resume; initial acquisition and discard/cleanup
are not established by that trace. The inner-handle negative also has an
ordinary port mismatch, so it does not isolate escape checking. Full initial-term checking, whole-execution
progress and Core correspondence remain open. See the
[payload-boundary proof account](KERNEL.md#declared-payloads-across-capture-boundaries).

[ClauseProgress.lean](ClauseProgress.lean) joins evaluated request and resume
progress to the combined result and ownership invariant.

| Result | Checked theorem |
| --- | --- |
| The selected cell update preserves retained clause-result frames | `cell_update_preserves_results` |
| Actual builtin reads and writes preserve the configuration result certificate | `builtin_request_preserves_results` |
| Ordered resolution yields an allowed outward request or a step preserving combined validity and old records | `request_progress` |
| A selected interpreter or empty outgoing row guarantees a step | `interpreted_request_progress`, `closed_request_progress` |
| Usage locates the live boundary; resume steps with the same registry and combined invariant | `resume_progress` |

These results use `Ash.OneShot.ClauseProgress`. They require a value operand
and the current combined invariant, with no separate access, closing, capture
cut, fresh-owner or live-boundary premise. The following proof joins the other
current forms admitted by the result rules. Full initial admission and universal
execution safety remain open. See the
[progress proof account](KERNEL.md#evaluated-request-and-resume-progress).
Core correspondence is currently an evidence and gap assessment; changing
Core to align with this calculus is outside this work.

[ClauseExecution.lean](ClauseExecution.lean) connects progress across all
current heads admitted by the structural result judgment.

| Result | Checked theorem or judgment |
| --- | --- |
| Result admission excludes application, discard and cleanup heads | `SupportedHead`, `supported_head` |
| Focus supplies its local boundary; result bounds derive return access | `focus_boundary`, `return_access_checks` |
| Branches and all admitted non-capture events preserve result certificates | `branch_results`, `raw_preserves_results`, `named_preserves_results` |
| The same actual event carries joint validity and result preservation | `join_non_capture` |
| Current combined validity suffices for terminal, allowed outward request, or an invariant-preserving step | `current_progress`, `closed_progress` |
| Initial structural premises and certified endpoints support progress | `initial_progress`, `certified_endpoint_progress` |
| Existing machine steps have an explicit length | `CountedSteps`, `counted_execution` |
| One shared sequence carries both the step count and all state certificates | `CertifiedPrefix`, `prefix_counted`, `prefix_certified` |
| One current or initial invariant constructs a checked prefix for any finite budget, or reaches a terminal earlier | `finite_prefix`, `initial_finite_prefix` |
| Terminal execution accounts for every issued owner exactly once and bounds returned resource support | `terminal_accounting`, `terminal_result_support` |

These results use `Ash.OneShot.ClauseExecution`. The public progress theorem
has no separate access, closing or source-request-boundary premise. Its
successor retains the same combined judgment, allowing repeated application.
The finite-prefix theorem is existential over actual named executions; it
does not prove preservation for arbitrary raw annotation choices. Callable
application and disposal/cleanup admission remain open, as do the complete
checker and full one-shot execution-safety theorem. Finite checked-run
preservation is established by the later `CheckedEvents` layer. See the
[repeatable-progress proof account](KERNEL.md#repeatable-progress-for-the-current-result-fragment).

[CaptureAnnotations.lean](CaptureAnnotations.lean) proves preservation for a
supplied capture whose input annotation agrees with the declaration.

| Result | Checked theorem or judgment |
| --- | --- |
| Actual clause selection determines its parameter, ticket binder and body | `clause_selection_unique` |
| An annotation erasing to a finite port is its canonical embedding | `first_order_annotation`, `finite_annotation` |
| The selected retained clause supplies the finite output bound | `selected_output_bound` |
| Every supplied capture with the declared result annotation preserves the combined invariant | `selected_capture_preserves` |
| Local declaration checking refines the same raw capture and preserves its exact successor | `DeclaredCapture`, `declared_capture_executes`, `declared_capture_preserves` |
| The matching annotation is admitted and the mismatched annotation is rejected | `Examples.matching_capture_declared`, `Examples.mismatched_capture_not_declared` |
| A wrongly annotated capture can execute with access and ownership preserved | `Examples.mismatched_capture_executes`, `Examples.mismatched_capture_has_access`, `Examples.mismatched_capture_preserves_ownership` |
| No ticket registry makes that successor port-typed or combined-valid | `Examples.mismatched_capture_not_typed`, `Examples.mismatched_capture_not_valid` |

These results use `Ash.OneShot.CaptureAnnotations`. The annotation condition
inspects the selected operation's declaration, not successor validity. The
counterexample shows why unrestricted raw annotation choices cannot support
universal type preservation. This module closes the capture case in the current
finite-port fragment; other annotation-producing events and the complete
admission theorem remain open. It establishes no mismatch in validated Core.
See the [capture-annotation proof account](KERNEL.md#checking-the-supplied-capture-annotation).

[EntryAnnotations.lean](EntryAnnotations.lean) checks supplied focus, handler
and resource annotations and derives them from current typing.

| Result | Checked theorem or judgment |
| --- | --- |
| Local code, context and existing-tail interfaces check the supplied annotation | `EntryTyping` |
| Checked entries are exact raw events and supply the non-capture boundary | `entry_executes`, `entry_boundary` |
| These events leave the usage-registry update unchanged | `entry_registry_unchanged` |
| Supplied annotations and fresh resource identities produce typed successor interfaces | `entry_effects` |
| The same actual event preserves the combined invariant with derived access | `entry_preserves` |
| Current typing constructs focus ports and pending translations | `focus_annotations_exist` |
| Current typing constructs handler/resource answer annotations for supplied identities | `handler_annotations_exist`, `resource_annotations_exist` |

These results use `Ash.OneShot.EntryAnnotations`. The entry judgment contains
no successor-validity premise; its construction theorems derive witnesses
from current typing. The preservation theorem additionally requires ordinary
fresh owner/activation histories. Together with declaration-checked capture,
it covers annotation-producing events in the current result fragment. The following layer joins
these events into finite checked-run preservation. Callable and
disposal/cleanup admission remain open. See the
[entry-annotation proof account](KERNEL.md#checking-supplied-entry-annotations).

[CaptureRecords.lean](CaptureRecords.lean) checks each supplied capture record
against the current cut, clause and retained interfaces.

| Result | Checked theorem or judgment |
| --- | --- |
| The actual capture checks one supplied record without successor-validity premises | `CheckedCapture` |
| Checked records project to the same raw and declaration-checked capture | `checked_capture_executes`, `checked_capture_declared` |
| The exact supplied record insertion preserves combined validity and old records | `checked_capture_preserves` |
| Current validity and declaration agreement construct a checked record | `checked_capture_exists` |

These results use `Ash.OneShot.CaptureRecords`. A run must use the same record
at a shared endpoint; independently chosen existential witnesses do not suffice.

[CheckedEvents.lean](CheckedEvents.lean) composes the events using exact registry
updates and derives validity along any supplied finite checked run.

| Result | Checked theorem or judgment |
| --- | --- |
| Annotation-free events provide raw execution, a request boundary and preserved effects | `StableEvent`, `stable_executes`, `stable_boundary`, `stable_effects` |
| Annotation-free events preserve the combined invariant with derived access | `stable_preserves` |
| Checked events specify exact registry updates and preserve the combined invariant | `CheckedEvent`, `checked_executes`, `checked_preserves` |
| Freshness-checked steps compose without intermediate-validity premises | `CheckedStep`, `CheckedRun`, `step_preserves` |
| One initial invariant derives every certificate along the supplied run | `run_certified` |
| Every finite checked run preserves combined validity and old records on the actual execution | `run_preserves` |
| Closed endpoints are terminal or have an actual invariant-preserving next event | `run_closed_progress` |
| Terminal endpoints complete issued owners exactly once and satisfy the result bound | `run_terminal_accounting`, `run_terminal_result_support` |

These results use `Ash.OneShot.CheckedEvents`. Universal preservation applies to
checked runs in the current result fragment. The endpoint progress theorem
constructs a named event; the following layer establishes checked next-event
coverage. Callable
application, disposal/cleanup integration and a complete executable admission
checker remain open. No Core alignment or correspondence theorem is claimed.
See the [finite-run proof account](KERNEL.md#supplied-capture-records-and-finite-checked-runs).

[CheckedProgress.lean](CheckedProgress.lean) derives checked next steps from
current structural validity and extends the same supplied checked run.

| Result | Checked theorem |
| --- | --- |
| Stable and actual value events have checked-step witnesses | `stable_step`, `named_value_checked` |
| Current handler typing constructs a declaration-checked capture | `declared_capture_exists` |
| Ordered requests and value resumption construct checked events from the current invariant | `request_progress`, `resume_progress` |
| Every admitted current form is terminal, an allowed outward request, or has a checked next step | `current_progress`, `closed_progress` |
| The constructed step preserves the combined invariant on the same actual event | `checked_progress_preserves` |
| Checked runs compose without validity premises | `run_append` |
| Every nonterminal closed endpoint extends its supplied checked run | `run_progress` |
| Four initial structural judgments suffice for preserved validity and checked endpoint progress along every supplied run | `initial_run_safety` |

These results use `Ash.OneShot.CheckedProgress`. They close checked-step coverage
for the current result fragment. Initial terms are scoped calculus code, not Ash
surface or validated Core programs. Callable application, disposal/cleanup and a
complete executable admission checker remain open; no termination or Core
correspondence theorem is claimed. See the
[checked-progress proof account](KERNEL.md#progress-extending-the-checked-run).

[CallableBodies.lean](CallableBodies.lean) separates function storage, argument
storage and the actual lambda body's result contract.

| Result | Checked theorem or judgment |
| --- | --- |
| Unsubstituted bodies are checked under their saved environment and no inherited ticket | `BodyChecked` |
| Stored function metadata pairs independent storage and body checks | `StoredFunction` |
| World growth and closed substitution preserve body and storage contracts | `body_world_mono`, `body_substitution`, `stored_world_mono`, `stored_substitution` |
| Actual closure support fits its stored capture bound | `stored_support` |
| Actual argument support supplies parameter rebinding and body-result substitution | `argument_rebinding`, `body_application`, `body_application_bounded` |
| Current joint validity plus body, argument and tail contracts gives the exact beta event and combined successor validity | `beta_preserves` |
| A lambda cannot inherit a direct lexical resume from its caller | `body_cannot_inherit_resume` |
| Storage-empty factories can differ in returned closure captures | `Examples.retaining_factory_checked`, `Examples.constant_factory_checked`, `Examples.same_factory_storage` |
| An empty capture bound does not establish an empty callable result bound | `Examples.retaining_result_not_empty`, `Examples.storage_does_not_supply_body` |
| A typed identity application executes to `17` with combined validity | `Examples.identity_call_typed`, `Examples.identity_call_joint`, `Examples.identity_call_body`, `Examples.identity_call_executes` |
| An effectful application enters a handler, resumes once and completes at `17` with the recorded ticket | `Examples.effectful_call_typed`, `Examples.effectful_call_joint`, `Examples.effectful_call_executes`, `Examples.effectful_call_completes` |

These results use `Ash.OneShot.CallableBodies`. The beta bridge checks the exact
runtime lambda and keeps both projections of the same continuation registry.
Its body fragment still excludes applications and disposal/cleanup. General
callable behavior must survive bindings, argument passing, returned functions
and retained frames before application can enter the whole-run safety theorem.
See the [callable-body proof account](KERNEL.md#callable-body-contracts-and-the-actual-beta-step).

[CallableContracts.lean](CallableContracts.lean) retains full callable contracts
through the same expression syntax. Physical capture checking alone projects
those contracts to storage bounds.

| Result | Checked theorem or judgment |
| --- | --- |
| Structural contracts distinguish stored resources, pairs and callable domains/results | `Contract`, `Derives`, `ClausesDerive`, `Captures` |
| Actual value support and resource closure follow from the contract derivation | `captures_iff`, `captured_resources`, `value_support`, `resource_closed` |
| Environment agreement follows relevant syntax dependencies, binders and fresh opening | `agree_left`, `agree_right`, `agree_extend`, `agree_without_ticket`, `opened_environment_agree` |
| World growth, relevant environment changes and closed-value ticket changes preserve checking | `captures_environment`, `world_mono`, `environment_congr`, `clauses_environment_congr`, `closed_value_environment`, `value_ticket_transport` |
| Actual closed substitution preserves capture bounds | `captures_closed`, `captures_expand`, `captures_substitution` |
| Shadowing and distinct extensions preserve the assigned full contracts | `Environment.extend_shadow`, `Environment.extend_commute` |
| Expression and handler-clause substitution preserve full result contracts | `substitution`, `clauses_substitution` |
| An evaluated callable contract exposes the actual lambda and checked body | `function_value` |
| Beta and value binding preserve the substituted result contract on the exact raw event | `beta_result`, `bind_result`, `beta_step`, `bind_step` |
| Identity, higher-order application, bound invocation and a returned callable have full contracts | `Examples.identity_checked`, `Examples.higher_order_checked`, `Examples.bound_call_checked`, `Examples.factory_checked` |
| A storage-only binding cannot be invoked through a callable contract | `Examples.opaque_binding_cannot_be_called` |
| Higher-order beta and bound invocation retain callable behavior in their actual reducts | `Examples.bound_call_preserves_function`, `Examples.higher_order_beta_preserves` |

These results use `Ash.OneShot.CallableContracts`. The judgment includes nested
application, handlers, operations, resumption and generative resources. Request
outputs and handled-clause parameter/resume inputs use finite port-derived
storage bounds; operand-port compatibility remains an independent typing check.
The beta and bind results
preserve this new expression contract, not the older `ClauseJoint.Valid`
invariant. Saved-frame and continuation-record integration, callable operation
ports, disposal/cleanup and executable admission remain open. See the
[full-contract proof account](KERNEL.md#callable-contracts-through-binding-and-substitution).

[CallableFrames.lean](CallableFrames.lean) carries full input and answer contracts
on the existing evaluation contexts and retained control forest. Frame
composition matches complete contracts, including callable behavior.

| Result | Checked theorem or judgment |
| --- | --- |
| Historical records and resolved lexical scopes retain complete input/answer contracts | `ResultRecord`, `ScopeBound`, `insert_extends`, `scope_extends`, `scope_resolves` |
| Clause checks and saved evaluation contexts survive world growth | `clauses_world_mono`, `context_world_mono` |
| Context plugging, closed-value restoration and focus decomposition preserve full contracts, including both application positions | `ContextReturns`, `context_plug`, `returned_value_rebind`, `focus_decompose` |
| Arbitrarily nested saved control composes and decomposes at complete contracts | `StackReturns`, `stack_append`, `stack_decompose` |
| Registry extension and world growth preserve retained contract derivations | `stack_registry_extends`, `stack_world_mono` |
| An actual handler cut supplies its saved clause and full answer contracts | `handler_cut_certificate` |
| The same recorded input/answer restores the entire captured stack above pending clause work | `resume_recomposition`, `resume_step` |
| Actual focus, plug, beta and bind events preserve the configuration's full result contract | `ConfigurationReturns`, `focus_step`, `plug_step`, `beta_step`, `bind_step` |
| Handler/clause returns and fresh resource entry/return preserve contracts; cell return excludes the released identity from actual result storage | `handler_entry_step`, `handler_return_step`, `clause_return_step`, `resource_step`, `cell_return_step` |
| Declared finite ports supply actual value contracts and selected-clause substitution | `selected_clause`, `typed_value_storage_contract`, `selected_clause_substitution`, `declared_output_contract` |
| Actual typed capture constructs an extended full-contract record and successor contract | `capture_step` |
| A concrete request has independently checked ports, callable answer clauses and a selected cut | `Examples.identity_contract`, `Examples.clauses_contract`, `Examples.request_contract`, `Examples.request_typed`, `Examples.selected_cut` |
| Capture/resumption returns a function through pending clause binding and invokes it outside the handler, reaching `17` | `Examples.capture_returns_callable`, `Examples.identity_closed`, `Examples.continue_after_capture`, `Examples.captured_callable_is_invoked` |
| A storage-only result cannot fill the saved callable position | `Examples.storage_cannot_fill_callable_frame` |

These results use `Ash.OneShot.CallableFrames`. They preserve the full contract
component on actual raw events, not the combined machine invariant. Its abstract
world is not yet linked to issued history, and registry absence does not prove
lifetime owner freshness. Raw frame type annotations and ticket authority remain
independent obligations. No contract subsumption, general progress, or
disposal/cleanup integration is claimed. The example starts at an evaluated
request under installed frames. See the
[retained-contract proof account](KERNEL.md#callable-contracts-on-retained-control).

[CallableJoint.lean](CallableJoint.lean) joins full callable contracts to the
existing ownership, support, type/effect, usage and name-history invariant.
Both continuation projections use one historical owner record, and the
contract world is the issued-resource history.

| Result | Checked theorem or judgment |
| --- | --- |
| One record links the resumed input contract to its declared finite port | `TicketRecord`, `Valid`, `active_input_contract` |
| Insertion preserves both projections and prior records | `joint_insert`, `results_insert`, `registry_extends_refl`, `registry_extends_trans`, `registry_insert_extends` |
| Both record domains agree with issued tickets; lifetime freshness supplies registry absence | `recorded_history`, `registry_fresh`, `result_registry_fresh` |
| Four structural initial judgments establish the full joined invariant | `initial_configuration_valid` |
| Actual resumption preserves all projections on the same named event | `resume_access_checks`, `resume_preserves` |
| Selected capture constructs one record and one successor for contracts, ports/effects, usage, ownership and names | `capture_preserves` |
| Current declared payload typing and retained handler checks derive capture access | `current_payload_access`, `request_access_checks`, `capture_without_payload_premise` |
| Current typing supplies actual closure; non-cell value states receive access checks | `current_closed_value`, `value_access_checks` |
| Beta, binding, plugging and handler/clause/cell returns preserve the joined invariant | `beta_preserves`, `bind_preserves`, `plug_preserves`, `handler_return_preserves`, `clause_return_preserves`, `cell_return_preserves` |
| Pre-state annotation checks preserve contracts and all joint fields through focus, handler entry and resource entry | `entry_access_checks`, `entry_results`, `entry_preserves` |
| Current typing and an actual focus construct its annotation and joined successor | `focus_preserves` |
| Named executions compose | `execution_append` |
| A closed higher-order application establishes initial validity and preserves it through two beta steps to `17` | `Examples.higher_order_typed`, `Examples.higher_order_usage`, `Examples.higher_order_initial`, `Examples.higher_order_executes` |
| A closed program installs a handler with a callable answer under independent type and usage checks | `CaptureExample.identity_typed`, `CaptureExample.clauses_typed`, `CaptureExample.handled_typed`, `CaptureExample.initial_valid`, `CaptureExample.source_enters_request` |
| Capture, nonempty-prefix resumption and outside invocation preserve the full invariant from initial code to `17`, with one issued and completed ticket | `CaptureExample.capture_valid`, `CaptureExample.continue_captured_callable`, `CaptureExample.callable_handler_execution` |

These results use `Ash.OneShot.CallableJoint`. They remove the earlier separation
between abstract contract worlds/records and actual machine history for the
listed transition families. The concrete handler execution establishes the
joined invariant at its initial state and propagates it through each event.
The following layers add general next-step coverage and finite checked-run
preservation. Callable operation contracts, disposal/cleanup and executable
admission remain open. See the [joined proof account](KERNEL.md#joining-callable-contracts-to-the-machine-invariant).

[CallableProgress.lean](CallableProgress.lean) derives next-step progress from
`CallableJoint.Valid`, including application and callable handler answers.

| Result | Checked theorem |
| --- | --- |
| Builtin reads and writes preserve exact callable interfaces on saved control | `cell_update_preserves_results`, `request_storage_contract`, `builtin_request_preserves_results` |
| Current validity derives request selection, capture access, fresh ownership and full resumption | `request_progress`, `interpreted_request_progress`, `closed_request_progress`, `resume_progress` |
| Admitted heads exclude disposal/cleanup; non-capture cases derive access and preserve exact result contracts | `supported_head`, `focus_boundary`, `return_access_checks`, `branch_results`, `raw_preserves_results`, `named_preserves_results`, `join_non_capture` |
| Every admitted current state finishes, reaches an allowed outward operation, or steps preserving the joined invariant | `current_progress`, `closed_progress`, `initial_progress` |
| Terminal states complete exactly their issued owners and bound physical result support | `terminal_accounting`, `terminal_result_support` |

These results use `Ash.OneShot.CallableProgress`. Closed progress excludes
outward requests. It does not assert termination or preservation for arbitrary
unchecked frame annotations.

[CallableRuns.lean](CallableRuns.lean) checks supplied events against current
code and retained interfaces. Exact before/after registries index the run;
there are no intermediate-validity premises in its constructors.

| Result | Checked theorem or judgment |
| --- | --- |
| A supplied capture record carries the declared storage input and full handler answer, authenticated against the actual cut and retained interfaces | `CheckedCapture`, `checked_capture_executes`, `checked_capture_declared`, `checked_capture_preserves`, `checked_capture_exists` |
| Stable events preserve the joint invariant, including actual beta reduction | `StableEvent`, `stable_executes`, `stable_boundary`, `stable_effects`, `stable_preserves` |
| Checked events and steps preserve their exact registry updates | `CheckedEvent`, `CheckedStep`, `checked_executes`, `checked_preserves`, `step_preserves` |
| Every supplied finite checked run preserves the invariant from its starting validity alone | `CheckedRun`, `run_preserves`, `run_closed_progress` |
| Terminal checked runs discharge exactly the issued owners and bound actual returned storage | `run_terminal_accounting`, `run_terminal_result_support` |
| Current validity constructs checked events, with no supplied successor certificate | `stable_step`, `named_value_checked`, `declared_capture_exists`, `request_progress`, `resume_progress`, `current_progress`, `closed_progress`, `checked_progress_preserves` |
| Checked runs compose at the same registry and every closed nonterminal endpoint admits a checked extension | `run_append`, `run_progress` |
| Four initial structural judgments imply preservation and endpoint progress for every checked run | `initial_run_safety` |
| A closed higher-order application has a two-beta checked run to `17` | `Examples.higher_order_run`, `Examples.higher_order_safety` |
| Initial code installs a handler and captures a callable answer through checked events | `CaptureExample.source_enters_request`, `CaptureExample.capture_run` |

These results use `Ash.OneShot.CallableRuns`. The proof extends the earlier
finite-result run theorem to the admitted callable fragment. Operation results
still require declared finite storage bounds, and handled clauses require
finite input bounds as well. Disposal/cleanup and complete executable
initial-term admission remain open. This proves neither general Core
correspondence nor termination. See the
[callable progress and run account](KERNEL.md#progress-and-checked-runs-with-callable-contracts).

[CompletionContracts.lean](CompletionContracts.lean) extends the structural
result judgment with cleanup and disposal, reusing full callable contracts and
the same expression syntax.

| Result | Checked theorem or judgment |
| --- | --- |
| Cleanup retains the body's full result and checks its callback behavior; disposal returns empty storage under its lexical ticket | `Derives`, `ClausesDerive`, `cleanup_contract`, `discard_contract` |
| Actual returned storage and resource closure remain structurally bounded | `value_support`, `resource_closed` |
| World/environment changes and closed-value ticket transport preserve contracts | `world_mono`, `environment_congr`, `clauses_environment_congr`, `closed_value_environment`, `value_ticket_transport` |
| Full substitution through cleanup, disposal, clauses and fresh resource bodies preserves callable behavior | `substitution`, `clauses_substitution`, `function_value`, `beta_result`, `bind_result`, `beta_step`, `bind_step` |
| Earlier callable derivations embed in the extended judgment | `callable_derivation_included`, `callable_clauses_included` |
| Cleanup and code sequenced after disposal can return callables; an unbound ticket or opaque callback is rejected | `Examples.callback_contract`, `Examples.callable_cleanup`, `Examples.disposal_then_callable`, `Examples.disposal_needs_bound_ticket`, `Examples.storage_callback_is_insufficient` |
| Empty input/result storage does not establish a Unit result type | `Examples.scalar_result_is_not_unit_typing` |

These results use `Ash.OneShot.CompletionContracts`. A callback's resource
contract has empty input/result storage bounds. Independent port typing must
establish `Unit → Unit`. A bound result-ticket index does not grant disposal
permission or prove that a capture can close.

[CompletionFrames.lean](CompletionFrames.lean) extends retained result contracts
to armed, running, closing and retiring frames.

| Result | Checked theorem or judgment |
| --- | --- |
| Contexts retain contracts through focus, plugging and world growth | `ContextReturns`, `clauses_world_mono`, `context_plug`, `returned_value_rebind`, `context_world_mono`, `focus_decompose` |
| Exact stack composition, registry/world extension, selected capture and full resumption preserve saved values and callback behavior | `StackReturns`, `stack_append`, `stack_decompose`, `stack_registry_extends`, `stack_world_mono`, `handler_cut_certificate`, `resume_recomposition` |
| Ordinary, entry/return, resource and continuation transitions preserve full result contracts on the existing raw machine | `ConfigurationReturns`, `focus_step`, `plug_step`, `beta_step`, `bind_step`, `resume_step`, `handler_entry_step`, `handler_return_step`, `clause_return_step`, `resource_step`, `cell_return_step`, `capture_step` |
| Selected clauses use declared finite inputs and actual substituted operands | `selected_clause`, `typed_value_storage_contract`, `selected_clause_substitution`, `declared_output_contract` |
| Cleanup saves the full body contract, invokes the callback, then restores the same body value | `cleanup_entry_step`, `cleanup_start_step`, `cleanup_finish_step` |
| Closing and retiring frames preserve unit storage interfaces | `closing_finish_step`, `retiring_step` |
| Successful actual plan generation retains callback contracts in order, and disposal materializes them above surviving clause work | `PlanReturns`, `plan_append`, `make_plan_returns`, `close_control_returns`, `discard_step` |
| Earlier callable contexts, stacks and configurations embed in this layer | `callable_context_included`, `callable_stack_included`, `callable_configuration_included` |
| A nine-event raw disposal trace invokes cleanup, releases a resource, completes closing and returns a callable; a running cleanup has no plan | `DisposalExample.captured_results`, `DisposalExample.initial_results`, `DisposalExample.actual_plan`, `DisposalExample.disposal_execution`, `DisposalExample.running_cleanup_cannot_be_planned` |

These results use `Ash.OneShot.CompletionFrames`. `PlanReturns` checks result
behavior, not resource access, effect interpretation, disposal permission or
fresh ownership. The disposal example starts at a supplied captured state and
proves raw execution and result preservation. It does not claim initial
admission or joined safety for that trace.

[CompletionJoint.lean](CompletionJoint.lean) combines these extended result
checks with the shared type/effect/usage record and the actual issued-resource
world.

| Result | Checked theorem or judgment |
| --- | --- |
| Shared histories, lifetime freshness and declared input bounds connect both invariant components | `Valid`, `recorded_history`, `registry_fresh`, `result_registry_fresh`, `active_input_contract` |
| Four initial structural checks establish validity; previous callable validity embeds | `initial_configuration_valid`, `callable_valid_included` |
| Capture and resumption preserve the full joined invariant; current payload typing derives capture access | `resume_access_checks`, `resume_preserves`, `capture_preserves`, `current_payload_access`, `request_access_checks`, `capture_without_payload_premise` |
| Current closure and non-cell access, ordinary computation, entry and returns preserve the extended invariant | `current_closed_value`, `value_access_checks`, `handler_return_preserves`, `clause_return_preserves`, `beta_preserves`, `bind_preserves`, `plug_preserves`, `cell_return_preserves`, `entry_access_checks`, `entry_results`, `entry_preserves`, `focus_preserves` |
| Cleanup derives actual callback typing/metadata, retains saved result behavior and completes the same owner | `cleanup_entry_preserves`, `cleanup_start_preserves`, `cleanup_finish_preserves` |
| Disposal preserves all components under actual plan, typing, access, resolution and lifetime-freshness checks | `discard_preserves` |
| Close completion and retirement preserve contracts with the same accounting event | `closing_finish_preserves`, `retiring_preserves` |
| A checked initial program runs cleanup, invokes its returned function and reaches `17`, issuing and completing cleanup `7` once | `Examples.initial_valid`, `Examples.callable_cleanup_execution` |

These results use `Ash.OneShot.CompletionJoint`. They establish local joined
preservation and the seven-event normal-cleanup example. The earlier finite
checked-run theorem is not yet extended to disposal/cleanup. Deriving safe
closing admission at every new capture remains necessary; it cannot be replaced
by assuming intermediate validity. See the
[cleanup and disposal proof account](KERNEL.md#cleanup-and-disposal-with-full-result-contracts).

[ClosingRequirements.lean](ClosingRequirements.lean) computes the least outward
effect row of an ordered disposal plan. Structural induction proves that the
finite check `checkClosingEffects` is equivalent to `CloseReady` for a stack
whose retained contents are typed. The proof covers arbitrary capture nesting.
`mem_required_append` states ordered composition: a suffix's retained providers
can satisfy the front's requests. Providers released in the front cannot
satisfy later callbacks. Four checked examples cover both orders, a nested
capture and rejection of a nested running cleanup.

This eliminates a separate closing-effect derivation for a concrete typed
stack. It does not establish resource access, exact interpretation agreement,
disposal permission or source admission for future captures. See the
[induction and checking account](KERNEL.md#induction-and-closing-effect-checking).

[ClosingAdmission.lean](ClosingAdmission.lean) adds exact executable checks for
the existing structural closing judgments. `checked_plan_iff` proves soundness
and completeness against `Closes`, including callback resource access, exact
interpretation identity and nested capture order. `checked_disposal_iff` adds
the independent pending-ticket check and characterizes `Discardable`.
`check_captured_iff` combines this with the effect checker for a typed scoped
stack: acceptance is equivalent to an actual `makePlan` result with both
`PlanTyped` and `Discardable` for that same erased plan. Owner accounting and
exclusion of protected frames follow.

Eight checked examples cover equal effect instances with different handler
activations, resource release order, outside and internally owned ticket work,
nested protection, and combined scoped checking. These checks inspect a concrete
capture and its actual surviving control. They do not grant disposal permission
or establish that every future capture of an initially checked program passes.
Independent usage, ownership and activation-history invariants still apply.
See the [structural closing admission account](KERNEL.md#executable-structural-closing-admission).

[ProtectionContexts.lean](ProtectionContexts.lean) establishes the ordered
context component needed by source protection admission. Its two modes record
whether a captured prefix owns protected work. `source_cut_mode` and
`scoped_cut_mode` prove exact agreement with actual source-handler cuts;
`select_target` preserves the selected interpretation. Capture and full
resumption transport protection, including recursively dormant captures.

An actual nested cut shows why a resume-only callback effect is insufficient:
its handler clause can request a farther outer effect whose capture also owns
the running cleanup. Internal ticket accounting accepts that transfer, but
closing rejects it. An inner handler installed before the running frame instead
receives an unprotected capture. This is a context-realization theorem and
counterexample, not yet a complete source typing judgment. Mode propagation
through clause bodies and qualified callable contracts remain necessary. See
the [protection-context account](KERNEL.md#ordered-contexts-and-protection-modes).

[ProtectionContracts.lean](ProtectionContracts.lean) makes the clause/callable
protection interface finite. A footprint records exact instances, operations
and protection introduced before the receiving context. Each handler operation
offers optional outward rows for unprotected and protected capture. Selected
rows are checked recursively outside that handler, at the actual invocation
context. The checker is sound and complete for the structural `Admitted`
judgment; sequencing and protection qualification have checked composition laws.

`checked_capture_contract` connects an admitted request to an actual protected
scoped cut and proves that its selected summary denies disposal. The summary
must still be authenticated against the actual clause and fixed source policy.
Source derivation, resumption-phase preservation, builtin operation typing and
other ownership/access checks remain separate obligations. Eight examples
exercise forwarding, local disposal, completion phases, surviving barriers,
invocation context, missing operations and distinct mode requirements. See the
[finite protection-contract account](KERNEL.md#finite-protection-contracts-at-invocation).

[CallableProtection.lean](CallableProtection.lean) derives protection footprints
from the callable computation forms of the existing scoped `Code`. Function
contracts retain latent demands, including inside higher-order results. Closed
substitution preserves the exact contract and footprint; actual beta and bind
steps preserve the source check under a fixed supplied context. Cleanup checks
its callback's latent demands under a running barrier. Ten examples include
ordinary invocation, protected rejection and higher-order substitution.

This component alone does not relate that context to the runtime stack,
authenticate operation-supplied callable results, or supply source rules for
handlers, tickets and generative resources. Its cleanup theorem constructs a
callback check; the frame bridge below connects actual transitions. See the
[source callable account](KERNEL.md#source-callable-protection-and-substitution).

[CallableProtectionFrames.lean](CallableProtectionFrames.lean) derives the
protection context from the actual stack and proves exact source-summary
decomposition and reconstruction at retained evaluation frames. Local focus,
plug, beta, bind and cleanup entry/start/finish rules preserve their respective
certificates, including full callable results and the waiting frame's residual
demands. The callback and outside continuation keep separate phase checks.

Handler tables can now take their disposal bits directly from the fixed source
ticket policy. Induction on an actual cut then proves that a checked protected
request selects a policy that denies disposal. Outward clause rows remain
supplied, and whole-machine preservation across capture/resumption is still
open. Six examples check actual context realization, policy rejection and
cleanup stages with a callable result. See the
[runtime frame bridge](KERNEL.md#protection-at-runtime-frames-and-policy-selection).

[ProtectionResiduals.lean](ProtectionResiduals.lean) computes the requirements
exported through an ordered interpretation prefix. Its factorization theorem
holds for every outside context; composing prefixes computes the same residual
as processing them together. Unhandled requests remain available to the outside
context, while missing operations or unsupported modes at a matching handler
fail within the prefix.

An actual capture cut now derives an outside residual from a checked footprint.
The resumption theorem characterizes its check under restored captured frames,
waiting caller frames and the surviving tail. Eleven examples distinguish
handler order, phase-specific protection, missing operations, dormant handlers,
and a waiting handler that invalidates an earlier check. These concern supplied
footprints, not complete source admission or a reachable execution trace. See the
[residual composition account](KERNEL.md#residual-requirements-across-capture-and-resumption).

[ClauseProtection.lean](ClauseProtection.lean) derives source requirements while
threading the existing `available` and `consumed` ticket states. Requests use
the phase after their operands evaluate. Resume removes this ticket's owned
barrier; disposal inserts the closing barrier. Other owners' barriers remain.
The judgment projects to the existing structural usage rules, and closed
substitution preserves endpoint phases, full callable contracts and exact rows.

Ten examples include `F; resume; F`, double-resume rejection, the lambda ticket
barrier, normal cleanup after resume, and disposal protection. Requirements
inside the captured continuation and close plan remain supplied inputs; stack
equations characterize their use but do not authenticate them. Handler and
generative-resource source rules and whole-machine preservation remain open.
See the [source clause phases](KERNEL.md#source-clause-phases-and-protection-requirements).

[CertifiedClauseRows.lean](CertifiedClauseRows.lean) requires a source-body
derivation for every offered handler mode row. Each clause uses one operation
input/result lookup, its actual parameter and ticket binder, and the fixed
ticket policy. Certification preserves clause order and checks entry with no
fictional local handlers. A mode marked unavailable offers no row.

From a certified table, actual cut and checked request, the capture theorem
derives the selected body's requirements after closed payload substitution and
their acceptance at the surviving tail. With the independent source-closure
premise, it constructs the actual capture step and source usage certificate.
Twelve examples include rejection of a fabricated empty offered row, a concrete
capture, and substitution of a used clause parameter.
Captured-row provenance and whole-machine preservation remain open. See the
[offered-row certificates](KERNEL.md#source-certificates-for-offered-clause-rows).

[DisposalProtection.lean](DisposalProtection.lean) derives disposal requirements
from an executable close plan and the actual retained callback source contracts.
Each callback exports protected requests that its remaining plan suffix cannot
supply. The proof first transports callback contracts through nested plan
construction, then computes requirements against the assembled suffix. An
outer release can therefore satisfy an inner callback's request.

Stack induction preserves existing callback contracts through capture, resume
and disposal. The source discard rule, a row certified against the built plan,
and actual ticket resolution construct the raw discard transition and establish
callback readiness at its generated closing stack. A separate invocation
theorem constructs the callback's raw start step with a checked application at
the exact remaining suffix. Twelve example lemmas cover release order, exact
cell identity, nested capture, disposal, retirement and outward protection.

These results do not preserve readiness through callback execution, derive
contracts for future cleanup expressions, or replace ordinary typing, access,
ownership-ledger and independent disposal checks. Whole-source admission and
joint preservation/progress remain open. See the
[disposal requirement derivation](KERNEL.md#disposal-requirements-from-executable-plans).

[CleanupProtection.lean](CleanupProtection.lean) derives new callback contracts
from source checking and preserves stored contracts through every raw transition.
Its installation premise names only the actual source cleanup expression;
source summary and clause derivation theorems discharge that premise.

The source cleanup rule also produces a certificate for normal invocation in
the body's final ticket phase. Exact residual equivalence transports the body
derivation under its newly armed frame. At return, the certificate yields an
invocation check at the actual live or spent boundary and constructs the raw
callback start with its saved full result contract. Seven example lemmas include
a future-phase check that succeeds after consumption while premature invocation
at the protected live boundary fails.

The certificate does not prove that the body reaches the recorded phase or
that its intervening execution preserves the required context. The fixture uses
supplied handler rows and a supplied captured execution row; it is not a jointly
valid execution-prefix proof. Ordinary typing and the joint invariant remain
necessary for progress. See the
[cleanup installation and return phases](KERNEL.md#cleanup-installation-and-normal-return-phases).

[ClauseProtectionFrames.lean](ClauseProtectionFrames.lean) derives pending-frame
certificates from the source phase judgment. A context records the focused
child's return phase and full contract, the suffix's final phase/result, and
its exact exported requirements. Focus splits the source derivation and stores
this certificate; plug transports the closed returned value into the saved
analysis environment and reconstructs only the remaining expression.

Bind and beta preserve exact rows and phases. Branch selection derives an
accepted row for the chosen arm. Sixteen example lemmas check a post-resume
suffix, consumed resume rejection, residualized handler rows, a callable
initializer under a saved environment, cleanup's final phase, and actual local
reductions. These are local raw transitions and source certificates, not a
composed resume execution or a joint machine invariant. Runtime owner/scope
realization and ordinary frame-port agreement remain open. See the
[pending source phases](KERNEL.md#pending-contexts-and-source-continuation-phases).

[PhaseBoundaries.lean](PhaseBoundaries.lean) connects those local certificates
to actual live/spent owner boundaries and the existing joint machine invariant.
The interpretation contexts come from the actual waiting prefix and outside
tail. Ownership and name history establish available/consumed phase facts and
exclude resurrection of a completed owner. Focus derives actual frame
annotations from ordinary typing; plug restores the suffix at its return phase.
Capture shares one selected clause, fresh owner, registry extension and
successor between source checking and joint preservation.

Eight example lemmas include a composed callable-handler execution through
capture, one resumption and return into the clause's pending bind, plus
rejection of a wrong protection bit and an available completed owner.
Captured-row provenance, source/port contract agreement, general source
admission and whole-program progress remain open. See the
[runtime boundary account](KERNEL.md#runtime-phase-boundaries-and-joint-capture).

[SavedFrameRequirements.lean](SavedFrameRequirements.lean) derives resumed rows
from source evidence for saved ordinary frames and cleanup callbacks. Each
frame's requirements are interpreted through its own remaining suffix, so an
already exited provider cannot satisfy a later request. Induction proves
equivalence with positional checking and supports actual capture decomposition
and resumption into a checked waiting caller. Resumption joins these checks to
the existing ownership/type invariant on the same named successor.

Thirteen examples cover provider order, dormant captures, cleanup protection,
and an admitted callable-handler execution through resumption. Frames whose
pending code consumes a continuation still require phase-judgment integration;
general source-contract alignment and whole-program progress remain open.
See the [saved frame requirements](KERNEL.md#requirements-at-saved-frame-positions).

[PhaseFrameUsage.lean](PhaseFrameUsage.lean) derives the runtime owner and exact
scheduled demand of a continuation-consuming source frame from the existing
usage registry and saved scope. An unchanged source phase gives an empty
consumption demand. Active frames require a live owner below them; dormant
frames use their explicit outside-access interface. Ownership balance rejects
duplicate sequential consumptions while permitting alternative branches.

Fourteen examples cover distinct binder/owner names, nested resumption, dormant
outside access, duplicate rejection and idle scopes naming consumed owners.
Phase-sensitive effect-row composition and whole-source preservation remain
open. See the [scheduled owner account](KERNEL.md#source-phases-and-scheduled-runtime-owners).

[PhaseContextChains.lean](PhaseContextChains.lean) connects each pending plain
context's input phase and full callable contract to its predecessor's output.
Structural induction proves composition, decomposition and source reconstruction
for arbitrary finite chains. Focus and plug preserve the source invariant
alongside the existing joint invariant on the same named transition. Bind,
beta reduction and branch selection retain the appropriate remaining demands.

Nine examples check a consuming resume followed by application, phase-sensitive
latent effects, rejection of duplicate consumption and incompatible holes, and
a callable handler's return to its waiting clause. This covers contiguous plain
frames for one supplied source ticket and a shared analysis environment. General
handler/resource interleaving, agreement with saved runtime scopes and ordinary
ports, and preservation through every transition remain open. See the
[context-chain account](KERNEL.md#phase-and-contract-composition-of-pending-contexts).

[ChainOwnerAgreement.lean](ChainOwnerAgreement.lean) derives a plain source
segment's unique consuming owner from the existing runtime ownership balance.
Induction projects source phases onto actual consumption demands. The selected
live boundary's dormant capture cannot demand its own owner, so the current
expression or a pending plain frame must consume that owner. The proof derives
both its runtime identity and the source's available-to-consumed phase change.

Resumption uses this derived identity to preserve the existing joint invariant
and retain the waiting source chain at its consumed phase. Eleven examples cover
outside owners in dormant captures, rejection of the wrong owner and abandoned
ownership, idle historical scopes, and an admitted callable capture/resume
prefix. Other frame kinds, ordinary port/contract agreement, authenticated
capture rows and all-transition source preservation remain open. See the
[derived owner agreement](KERNEL.md#ownership-balance-determines-the-source-owner).

[NeutralFrameRows.lean](NeutralFrameRows.lean) proves that phase-neutral source
code and contexts are equivalent to ordinary callable summaries with exact
exported rows. Induction derives positional saved-frame rows for consumed
pending chains, including composition with a remaining interpretation suffix.
Adding plain frames to an exact handler cut derives the extended capture row
from their source contexts and the retained suffix's rows.

Resumption now derives the waiting prefix's positional check and owner identity
from its source chain. Eight examples cover retained protection, latent callable
effects, cleanup invocation, provider position and an admitted callable execution
whose capture row and waiting check both follow from source contexts. Captures
with phase-changing interleaved frames, authenticated handler tables, full
contract/port agreement and all-transition source preservation remain open. See
[neutral source rows](KERNEL.md#phase-neutral-source-and-derived-saved-rows).

[CaptureInterfaces.lean](CaptureInterfaces.lean) derives an occurrence-specific
continuation interface from actual saved-frame rows and executable close plans.
Unavailable disposal is distinct from an empty plan. A local specialization of
the existing structural clause rules replaces the key-based capture-row input
at this capture proof boundary. The same selected clause and named successor
preserve the interface alongside the existing joint invariant.

Twelve examples include two exact cuts at the same handler and clause with
different derived rows, a nested disposal plan, recursively protected dormant
control, and an admitted callable capture with the actual interface. The
same-clause row comparison is structural evidence, not two new fully admitted
executions. Uniform handler contracts across occurrences, phase-changing saved
code, contract/port alignment and full source preservation remain open. See
[occurrence-specific capture interfaces](KERNEL.md#interfaces-for-actual-capture-occurrences).

[ParametricClauseRows.lean](ParametricClauseRows.lean) makes clause derivations
reusable across capture rows. Its structural schemas summarize existing source
code using explicit resumption and disposal row parameters. Successful evaluation
instantiates the existing concrete judgment; every coherent concrete derivation
can be abstracted into a schema. Continuation usage is checked independently of
row arguments. Clause-list specialization retains source order and constructs
an occurrence-specific certificate.

Fifteen examples cover the same clause at different captures, independent
one-shot use checks, alternative branches, unavailable and protected disposal,
and an admitted capture using a specialized schema. These are analysis
expressions, not new computation forms. Interpreting parametric contracts
throughout the ordered stack, capture inference, contract/port agreement and
full source preservation remain open. See the
[parametric clause account](KERNEL.md#parametric-clause-row-schemas).

[EffectBounds.lean](EffectBounds.lean) connects exact clause and saved-frame
requirements to shared effect upper bounds. Repeated handling exposes an
obstruction in exact occurrence specialization: a clause that performs `Audit`
then resumes would require the finite-list equation `R = Audit :: R`. Coverage
admits the shared bound `[Audit]` while retaining exact source derivations,
protection bits, interpreter order and independent one-shot use checks.

Induction covers every finite number of pending requests under that shared
bound. Local capture and resumption preserve the existing joint runtime invariant
under the stated source premises. Full bounded source preservation and inference
remain open; this family is structural admission evidence, not a fully admitted
execution family. See [effect bounds and repetition](KERNEL.md#effect-bounds-and-repeated-handling)
for the proof boundary and current Core comparison.

[UniformClauseBounds.lean](UniformClauseBounds.lean) proves coverage transport
through any fixed finite ordered interpretation context and clause schema.
A table evaluated at shared upper bounds certifies every covered capture input,
without specializing the table again. Actual capture preserves the exact source
interface and existing joint runtime invariant under that certificate.

The same fixed table now covers both different-row captures and their protected
variants with unavailable disposal. Bound inference and the complete source
invariant remain open. See [uniform clause bounds](KERNEL.md#uniform-clause-bounds)
for the precise scope and availability condition.

[OwnedPhaseRows.lean](OwnedPhaseRows.lean) retains phase-changing pending code
when its live owner boundary is captured with it. Structural chains record full
contracts, one-shot phases and actual scope resolution. Runtime ownership derives
the scope equations at a request; the chain must consume its owner once and
return that owner's answer contract. Capture and resumption join these rows to
the existing runtime invariant, and shared clause checking accepts the new rows.

A nested request demonstrates why ordinary frame summaries were insufficient:
it captures a pending resume. Lean checks its source and ownership evidence;
current Core returns `17 : Int`. Open owner segments, intervening non-plain frames
and the complete source invariant remain unfinished. See
[owned phase rows](KERNEL.md#captured-segments-with-pending-owner-consumption).

[OpenOwnerUses.lean](OpenOwnerUses.lean) derives a capture's outside-owner use
interface from structural stack usage. Under existing ownership separation,
an empty interface is equivalent to the internal-use premise needed by disposal.
Restoration preserves the exact interface, and valid capture derives its linearity.
The preceding phase-row system is proved to have only empty outside interfaces,
so admitting open captures requires extending its source rules.

The example retains an outside resume obligation through a raw resumption step
and its ownership check, while rejecting disposal despite an executable empty
plan. Current Core returns `17` for the resumptive `let` fixture and rejects its
discard variant. The direct resume-operand variant instead exposes a reproducible
Core build failure. See [outside-owner use interfaces](KERNEL.md#outside-owner-use-interfaces)
for evidence and the remaining phase/effect integration.

[OwnerPhases.lean](OwnerPhases.lean) retains named live and spent owners in
ordered interpretation contexts. Projection recovers the existing stack context.
The structural consumption judgment is equivalent to its checker, has a unique
result, and rejects a second use. Runtime name history authenticates the selected
owner across arbitrary intervening frames.

Resumption restores the capture before the updated caller and preserves the
existing joint runtime invariant. Disposal installs its actual closing plan and
preserves usage under the outside-interface check. A running-cleanup example
shows why spending the owner alone does not remove restored protection. These
are general context-transition proofs; connecting them to the complete source
phase/effect judgment remains open. See [named owner phases](KERNEL.md#named-owner-phases-in-ordered-contexts).

[OpenPhaseSegments.lean](OpenPhaseSegments.lean) adds source segments that expose
one owner outside the capture. All seven evaluation-frame kinds and spent
boundaries compose through the existing direct expression judgment. Each frame
checks its code at its remaining interpretation suffix; composition matches full
callable contracts and threads the exposed owner's phase. Interior live-owner
groups still require integration.

Induction proves splitting, recomposition and the exact source demand for the
outside owner. Source rules cover focus, plug, bind, application reduction,
branch selection, handler return and synchronous cleanup. Focus, plug and
restoration join the same source certificates to the existing joint runtime
invariant. The earlier open capture now has source evidence and still rejects
disposal. A protected example checks different effect requirements before and
after owner consumption. Captured phase transitions must still enter general
continuation interfaces and clause checking; initial admission and whole-program
progress remain unproved. See [open phase segments](KERNEL.md#source-segments-with-an-exposed-outside-owner).

[CapturedPhaseContracts.lean](CapturedPhaseContracts.lean) puts a captured
segment's outside phase transition into its continuation contract. Clause source
checking tracks local one-shot use separately from the outside phase changed by
resumption. Effect rows remain upper bounds. An available disposal plan requires
an empty outside-use interface and therefore cannot change that outside phase.

The actual capture rule retains the interface across registry extension and
checks the selected clause after closed parameter substitution. Once the local
owner is spent, the remaining clause derivation converts back to the existing
outside-owner source judgment. Examples distinguish effects before and after
resumption, reject unsafe discard despite an empty physical plan, and retain
safe discard for a phase-preserving capture. The resumption handoff for a
contiguous plain caller is established below. General phase-aware handler tables
and whole-program progress remain unfinished.
See [captured phase contracts](KERNEL.md#captured-phase-contracts-and-clause-checking).

[PhaseResumption.lean](PhaseResumption.lean) connects that clause source judgment
to the actual restored source configuration. Evaluation contexts and arbitrary
chains of plain waiting frames compose both continuation states and full value
contracts. Induction proves chain splitting and composition; focus and plug join
the resulting source certificates to the same named runtime steps and joint
invariant.

At resumption, the retained capture starts at its input outside-owner state. It
supplies the output state and answer contract expected by the waiting clause.
The actual capture row is checked beneath the advertised effect bound. The
restored source certificate accompanies the same step that preserves ownership,
closure and runtime typing. A concrete open-capture example checks the actual
stack, ownership and a later effect accepted only after the outside owner is
consumed. This remains a source fragment with one exposed outside owner and a
contiguous plain caller. Interior live-owner groups, general handler tables and
whole-source preservation remain open. See [resumption into open source](KERNEL.md#resumption-into-open-source).

[OwnerPhaseTransitions.lean](OwnerPhaseTransitions.lean) supplies one shared map
of owner states and a structural transition relation for arbitrary finite demand
lists. Induction proves composition, splitting, uniqueness, no resurrection and
no repeated consumption. Restriction derives the captured outside interface;
each earlier single-owner protocol is a projection of the same map.

The phase map interprets the existing ordered context without reordering its
layers. It matches actual runtime ownership, including dormant owners, and
recovers the earlier two-state contract and residual effect interpretation.
Actual capture retains the phase interface across registry extension; actual
resumption consumes exactly its selected owner. Safe disposal preserves every
outside owner's state. A capture containing an interior live owner has checked
usage, phase and raw resumption evidence, while a theorem shows why the earlier
source segment cannot admit it. Lifting the complete source judgment to the
shared map remains necessary; this is not whole-source progress. See [shared
owner phases](KERNEL.md#shared-owner-phase-transitions).

[OwnerSource.lean](OwnerSource.lean) threads the shared owner map through direct
expressions, evaluation contexts and source segments. Resume checks lexical
resolution and permission separately from the captured transition. All seven
frame kinds compose with live and spent owner boundaries. A live boundary may
be reached only after preceding source code has consumed its owner; a value at
an actually live boundary is therefore excluded by the source invariant.

Induction proves capture splitting and recomposition with full contracts,
owner demands and effect rows. Closed substitution, focus, plug, bind,
application and branch selection preserve the supported source information;
focus and plug also join the same named steps and runtime invariant. Immediate
requests are checked at the actual ordered stack. The preceding interior-owner
example now has source evidence before and after its raw resume. Its captured
contract agrees with the example's saved source and runtime demand.

Continuation records remain annotations requiring general authentication against
saved source and disposal plans. Source preservation from authenticated records,
handler-installation and resource-acquisition source rules, and complete
admission/progress remain unfinished. See [source with shared owner
phases](KERNEL.md#source-with-shared-owner-phases).

[OwnerSourceResumption.lean](OwnerSourceResumption.lean) derives the restored
source judgment from the before-resume judgment and a saved-segment derivation
at the actual restored suffix. Structural induction transports pending source
through arbitrary waiting frames and live groups, using the fact that the
selected owner has already been consumed. All other interpretations stay in
order. The same named runtime step preserves the full joint invariant, and its
actual ownership map indexes the resulting source. The nested-owner example's
after-source now follows from its before-source through this theorem.

The saved-segment premise is a structural derivation with full contracts,
owner demand and an effect row covered by the resume contract. It still needs
to follow from a maintained registry invariant. The theorem does not infer it
from an annotated row or move a saved derivation across arbitrary handlers.
Capture and disposal need corresponding integration with source rules. See
[general one-shot source restoration](KERNEL.md#general-one-shot-source-restoration).

[OwnerCaptureContracts.lean](OwnerCaptureContracts.lean) derives the resume
contract's full input and answer contracts, owner transition, protection and
effect row from the actual source capture split. Structural induction retains
expression, context, frame and segment derivations when fresh contracts are
added. Historical registration connects source-name freshness to the same
runtime allocation. The capture theorem retains source and raw usage evidence
for the same saved stack under the new owner.

A selected clause's source derivation, closed payload substitution and the
surviving tail now construct its after-capture source. Captured source supplies
the resumption premise after checked interpretation transport; a spent marker
alone is transparent. The nested-owner example connects source capture and
resume starting with no contract for the fresh owner. Replacing an existing
contract fails extension, and a waiting handler can change the exported row.
Maintained registry authentication, declaration/port coherence, closing-plan
authentication and source admission remain open. See [captured source contract
provenance](KERNEL.md#captured-source-contract-provenance).

[OwnerClosingSource.lean](OwnerClosingSource.lean) derives a closing plan's
source segment from its callback rows and actual retirement sequence. Releases
and callbacks preserve the owner map; retirement consumes one available owner.
Each callback is interpreted against the remaining plan and receiving suffix.
The plan retires exactly the captured owners, and runtime name history supplies
their separation from the surviving owner markers.

`ClosingData` retains the executable plan, callback source and the structural
check for abandoned outside-owner obligations. Its checked exported row and
retirement list supply the closing contract fields. Disposal source preservation
joins the same named runtime step and full joint invariant, with the resulting
actual ownership map. Source rules also cover synchronous callback start/finish,
retirement, closing completion and resource release. The example checks a
callback, nested retirement and resource release; reversing callback/release
availability fails the effect check. Maintained registry authentication and
complete source admission/progress remain unfinished. See [closing source and
disposal](KERNEL.md#closing-source-and-disposal).

[CoherentSourceTypes.lean](CoherentSourceTypes.lean) gives the stable callable
source component shared value annotations. Each binding chooses one annotation
whose projections produce ordinary port typing and protection contracts on the
existing `Code` syntax. Substitution and actual beta/bind reduction preserve the
shared derivation. Pending contexts retain the same hole and result annotations;
focus/recomposition and checked plain-frame metadata connect both analyses.

Executable operation-shape checks reject missing declarations and incompatible
callable shapes. Paired registry projections preserve their checked input and
answer shapes under fresh insertion. The actual request and a checked operation
entry determine the captured input's shape. The shared saved-segment layer
below now derives the captured answer from the same pending derivation. Examples distinguish scalar protection
from ordinary types, show why independent lambda derivations do not imply
agreement, and check a higher-order beta step and a pending application frame.
Shape agreement alone checks neither latent effects nor stored support. Complete
record authentication and handler/resource admission remain open. See
[shared source types](KERNEL.md#shared-source-types-and-pending-contexts).

The same module's `Owners.Derives` extends shared expression annotations to
one-shot resume and discard. Its projections retain ordinary typing and the
owner-phase source judgment, including the exact consumption trace. Shared
continuation records agree with the complete runtime port contract, including
resume and close effect lists. Substitution, beta/bind reduction and fresh
registry insertion preserve these shared choices. Examples reject a wrong
resume operand, repeated resumption and protected disposal, while admitting a
conditional that chooses resume or discard with one consumption on either path.
This agreement does not yet authenticate every saved capture or maintain its
evidence at every receiving stack. See [shared owner source
contracts](KERNEL.md#shared-owner-source-contracts).

[SourceReinterpretation.lean](SourceReinterpretation.lean) retains request
obligations before interpreting a receiving suffix. Structural induction derives
finite requirements from source expressions, pending contexts, frames and saved
segments. Re-evaluation at another receiver constructs a source derivation with
the new row and the same owner transition. Shared value annotations are retained
as well. The restoration bridge accepts changed contexts when the recomputed row
still fits the advertised bound; equal context projections are no longer needed
for that reconstruction.

The examples prove that a cached residual row alone cannot determine requirements
at another handler stack: a handled request and no request both reduce to `[]`
at one receiver and differ at another. The retained requirements distinguish
them, preserve handler order and reject newly protected disposal. An old empty
bound fails when the new receiver exposes an effect. Resume sites therefore
still need to specialize retained requirements rather than use a fixed cached
row as a bound for every caller. Referenced continuation rows and the owner-phase
indices remain fixed in this reconstruction theorem; maintaining their full
runtime invariant is unfinished. See [source
reinterpretation](KERNEL.md#source-reinterpretation-at-receiving-stacks).

[ResumeSpecialization.lean](ResumeSpecialization.lean) checks a resume site with
its recomputed row, without requiring coverage by the original cached row. It
constructs the before-source under a temporary checking view and the restored
source under the original registry. Structural induction proves that changing a
consumed owner's source row preserves expressions, contexts, frames and segments.
Shared annotations retain exactly the same runtime port contracts. A conditional
join connects specialization to the same named resume step and actual ownership
maps. The changed-handler example admits the newly exposed effect at an explicit
outside interface and rejects its absence. Complete record authentication and
source admission remain open. See [resume-site
specialization](KERNEL.md#resume-site-specialization).

[CaptureAuthentication.lean](CaptureAuthentication.lean) recursively checks
historical resume-source certificates for every retained live capture, following
both dormant captures and active tails. Stack decomposition and recomposition
preserve this evidence. Every transition that allocates no ticket preserves it;
fresh capture constructs its certificate from the actual source cut and extends
all older certificates. Retrieval provides saved source and reinterpretable
requirements. A counterexample shows that the earlier active-segment rule and an
outer certificate can miss an unregistered nested owner; the recursive judgment
rejects it. Actual nested resume and disposal steps retain this component.
Closing annotations, shared port agreement, current phase agreement and complete
source admission are additional obligations. See [recursive capture
authentication](KERNEL.md#recursive-capture-source-authentication).

[SharedSourceSegments.lean](SharedSourceSegments.lean) carries one value
annotation through owner-aware pending contexts, frames and saved segments.
Its recursive live rule checks the saved code and the tail against the same
record. Projection derives ordinary stack typing, the owner-phase source
judgment and recursive capture authentication together. Focus decomposition and
recomposition retain the shared choices; configuration bind and beta reduction
preserve them. The actual handler cut determines the captured answer port, while
the operation entry determines the input annotation. Fresh capture constructs a
shared record and live boundary while retaining every older record. A concrete
integer-to-Boolean capture and resume distinguishes ordinary atom types that
protection shapes alone cannot distinguish. Incorrect frame and capture metadata
are rejected. Closing fields, ordinary effect-list authentication, current phase
agreement and handler/resource source admission still need integration. See
[shared saved-segment annotations](KERNEL.md#shared-saved-segment-annotations).

[SharedClosingSource.lean](SharedClosingSource.lean) extracts shared callback
annotations and retirement records from the actual executable close plan. The
same callbacks derive ordinary outward effects and a protected source footprint.
The planned source segment retains shared unit types. A consumed live boundary
can become spent while preserving the shared waiting stack. Disposal reconstructs
the after-source and joins it to the same named runtime step and actual owner
phases; independent plan typing is no longer supplied. Recorded closing bounds,
signature/registry agreement and access checks remain explicit premises. Cleanup
start and completion, close completion, retirement and cell release preserve the
shared source judgment. Examples check callback-before-release ordering, a
concrete disposal and cleanup start, and rejection of a Boolean-returning cleanup
that scalar protection alone admits. General phase/row transport and complete
source admission remain unfinished. See [shared closing-plan
source](KERNEL.md#shared-closing-plan-source).

[PhaseRechecking.lean](PhaseRechecking.lean) extracts finite requirements that
evaluate against the receiving stack and current owner availability. Sequential
checks advance the owner state; branch arms start at the same state and must
consume the same owner set. Successful evaluation reconstructs shared source
expressions, pending contexts, frames, segments and configurations with their
original value annotations. Nested captures retain their historical source
certificates. Examples distinguish alternative from sequential uses of one
owner, preserve an unrelated owner, and show why protection checking must follow
consumption order. Referenced continuation rows remain supplied annotations;
the result does not derive successful checks at every future call. See
[source rechecking at current owner phases](KERNEL.md#source-rechecking-at-current-owner-phases).

[SharedResumption.lean](SharedResumption.lean) extracts the selected capture's
historical shared derivation and rechecks it at the restored suffix and current
owner state. Successful checking composes that capture with the waiting caller
and derives the shared after-source. The invocation uses its newly computed row;
the waiting stack and historical records retain their original registry.
Ordinary configuration typing agrees across this local view. A conditional join
preserves the same named runtime step, runtime invariant and actual owner map.
An example accepts a newly exposed effect that the original empty row cannot
cover. A nested example has matching runtime owner maps and two actual steps,
but its later inner invocation exposes an effect rejected by the empty outside
interface. This identifies a remaining recursive admission obligation; it does
not establish reachability from a completely admitted initial program. See
[shared resumption at current callers](KERNEL.md#shared-resumption-at-current-callers).

[RecursiveRequirements.lean](RecursiveRequirements.lean) replaces cached rows at
continuation references with owner/mode keys and exact demands. The executable
checker recursively evaluates finite stored templates at the caller's ordered
context and owner state. Invocation also requires structural selection from
the active context; retained ownership alone is insufficient. Its structural
`Checked` judgment is equivalent to successful evaluation and derives one-shot
consumption. A referenced template
has a strictly smaller demand than its caller, proving absence of linked cycles
and sufficiency of the demand-length evaluation bound. Prefix composition retains
interpretation order through recursive calls. The earlier nested example now
exposes the inner request at the outer check, rejecting an empty outside
interface. The inner template reconstructs its actual shared saved source.
General template extraction, authentication and preservation remain open; this
is not yet complete source admission. See [recursive continuation
requirements](KERNEL.md#recursive-continuation-requirements).

[SourceTemplates.lean](SourceTemplates.lean) derives recursive requirements from
shared expressions, pending contexts, frames and captured stacks. The structural
judgments retain shared value annotations, ordinary effect bounds, scope
resolution and continuation permissions. Stack derivation collects resume
templates for all live captures, including dormant captures. Lookup certificates
locate each body in that same retained forest and match its input, answer and
demand to the shared record. Structural active selection and distinct owned
tickets identify that template with the exact capture execution restores.
Checked current configurations require owner uniqueness and derive ordinary
typing and one-shot consumption from the actual initial owner map. A checked
configuration with a closed resume operand constructs its raw step and runtime
ownership trace without a supplied stack cut or additional access premise. Contract extension preserves templates, locations and checks.
The nested example uses a source-derived store, rejects direct invocation of the
dormant inner owner, and derives the outer resume step. Closing templates,
ordinary effect bounds, handler/resource admission, and preservation of the
complete check through stack-changing steps remain open. See [source-derived continuation
templates](KERNEL.md#source-derived-continuation-templates).

[RecursiveTransport.lean](RecursiveTransport.lean) preserves recursive checking
when normalized caller contexts and available-owner lookups agree. Consumed
boundary updates and deletion of both modes of a spent owner meet these
conditions. The authenticated resumed body therefore remains checked at its
physical waiting caller and actual successor owner map. Distinct owner/mode keys
also make template-store permutation preserve lookup and checking; this does not
reorder interpretations. Source-derived resume stores obtain key uniqueness from
runtime ownership. The nested example constructs a complete checked successor
for the outer resume, including its new store and ordinary types. The following
recomposition result supplies the general pending-caller construction; the other
transition families still need integration. See [recursive checks across consumed
callers](KERNEL.md#recursive-checks-across-consumed-callers).

[RecursiveRecomposition.lean](RecursiveRecomposition.lean) constructs complete
source segments and checks when a captured segment is restored before an
arbitrary pending caller. It derives the physical boundary replacement, exact
collected-store relationship and ownership transition. `resume_step_preserves`
proves preservation for every raw step from a checked resume with a closed
operand; `resume_preserves` combines it with progress to construct a step. Both
retain the result annotation and checking footprint while removing exactly the
invoked owner from the demand. The proof covers every prefix frame and
live/spent boundary. Both the nested
case and a nonempty effectful bind-prefix case instantiate the general theorem.
Fresh capture, closing-store integration, ordinary context/source-entry steps
and whole-program safety remain open. See [general resumption
recomposition](KERNEL.md#general-resumption-recomposition).

[RecursiveExpressions.lean](RecursiveExpressions.lean) proves closed substitution
with the exact recursive requirements, then preservation for ready binds,
applications and branches. Binds and applications retain the demand and checking
footprint. Branch selection retains a permutation of the demand and a sublist of
the footprint; the pending caller remains checked at the same resulting owner
map. Every raw step of these ready expressions preserves the complete checked
configuration and runtime stack. Typing supplies lexical readiness, so progress
constructs a step without a supplied successor check. Examples connect a bound
operand to nested resumption and check branch alternatives that each consume the
same continuation. The following result supplies focus/plug integration; fresh
capture, closing integration, source entry and whole-program safety remain open.
See [ordinary recursive source
reductions](KERNEL.md#ordinary-recursive-source-reductions).

[RecursiveContexts.lean](RecursiveContexts.lean) proves decomposition and
recomposition for all nine current pending-context forms. Inserting a plain
frame's neutral layer preserves both interpretation and continuation selection,
including recursively checked templates. Focus constructs runtime annotations
and pending-ticket translation from the shared source and preserves the complete
configuration. Plugging a value restores the frame's saved scope and preserves
checking; typing supplies the value's lexical closure for progress. Both retain
the actual collected store, demand, footprint and runtime owner map. An example
focuses a bind inside a resume operand, reduces it, plugs the returned unit and
then resumes a nested capture. Fresh capture, disposal/cleanup, source entry and
whole-program safety remain open. See [recursive evaluation
contexts](KERNEL.md#recursive-evaluation-contexts).

[RecursiveCapture.lean](RecursiveCapture.lean) derives saved and surviving
segments from the actual handler cut, including their exact template-store and
checking decomposition. Every owned ticket has a source contract, so registry
freshness implies absence from current ownership. Fresh record construction
retains all old templates, adds one resume entry and derives the actual owner
map. For an immediate-resume clause with a shared reply summary having no
immediate effects, capture constructs the raw step and complete checked
successor without a supplied successor check. Operand substitution, shared
result annotations and outside acceptance remain connected. The example captures
an integer-to-Boolean continuation and feeds the new checked state into general
resumption preservation. Arbitrary clause admission, closing contracts, source
entry and whole-program safety remain open. See [recursive fresh
capture](KERNEL.md#recursive-fresh-capture).

[RecursiveClauses.lean](RecursiveClauses.lean) reconstructs recursive templates
and checking from structural clause derivations, given authenticated component
invocations. A clause that leaves its local owner available has an empty demand
and changes no owner's phase. For resume-only contracts, a completed clause's
exact demand follows from its structural derivation. The actual saved check
then authenticates invocation, and a general clause joins the fresh boundary
and surviving caller without a supplied whole-clause recursive check. An
example includes effects before and after alternative resumptions; sequential
double resumption is rejected. Handler-table admission and bounds, disposal
integration, source entry and whole-program safety remain open. See
[structural clauses and authenticated invocation](KERNEL.md#structural-clauses-and-authenticated-invocation).

[RecursiveDispatch.lean](RecursiveDispatch.lean) derives the selected handler's
exact offer and residual through the actual surviving tail. Capture separates
the original footprint into request, saved-computation and caller rows. Given a
structural derivation of the selected clause and its bound by the first two
rows, argument substitution and the saved continuation construct the raw capture
step and complete checked successor. Every demand in its footprint is covered by the original
footprint, and ownership gains exactly one ticket. Membership coverage permits
interleaved requests and repeated branch obligations without commuting execution. The actual effectful-clause
example discharges these premises and rejects an understated empty offer.
Handler admission must still establish them generally; disposal, source entry,
allocation history and whole-program safety remain open. See [structural clauses
at actual dispatch](KERNEL.md#structural-clauses-at-actual-dispatch).

[RecursiveClosing.lean](RecursiveClosing.lean) derives callback rows and recursive
templates from actual closing plans and retained source. The exact checking
equation combines retirement availability with callback effects at their actual
remaining suffix; it is independent of the continuation store. Materializing the
plan with its surviving caller constructs a checked configuration using only
the caller's collected records, and retirement leaves exactly its owner map.
A disposal invocation is authenticated by that plan template. Examples check
callback-before-release order and nested retirement, expose the missing-cell
obligation after reversal, and reject duplicate retirement. The closing-record
construction below collects these entries and derives abandoned-use checks;
recursive consumption preserves the actual disposal step. Handler admission,
source entry and whole-program safety remain open. See [recursive
closing templates](KERNEL.md#recursive-closing-templates).

[RecursiveCompletion.lean](RecursiveCompletion.lean) proves progress and
preservation of the recursive check for every raw step from a checked value.
It covers callback startup and completion, closing guards, scope exits, plugging
and retirement. The pending source derives readiness; returning through a live
unconsumed continuation is rejected. Ticket-completion events account for the
exact change in demand and actual owner map. A six-step closing example reaches
the empty caller with each successor checked. Preservation for the richer store below and the
combined resource/access and name-history invariants remain unfinished. See
[recursive cleanup and value completion](KERNEL.md#recursive-cleanup-and-value-completion).

[RecursiveRecords.lean](RecursiveRecords.lean) collects actual-plan disposal
records beside resume records in the same store. Structural plan rules determine
callback obligations and retirement demands; unique ownership gives unique keys
for both modes. Collection also checks that discarded pending uses belong to
the capture's own live tickets. Capture retains old closing records and adds the
new record when both checks pass. Resumption removes the consumed owner's record and recomposes the
surviving records. The richer checked-state judgment admits actual disposal and
derives its raw step, while preserving admission of previously checked states.
Examples exercise both modes for one owner, nested retirement and rejection of
an incorrect closing demand. A raw closing plan with an outside pending ticket
use receives no disposal record. Every checked disposal cut derives this
abandoned-use condition. Full checking preservation and the resource/access,
usage and history invariants still need integration. See [collected
closing records](KERNEL.md#collected-closing-records).

[RecursiveConsumption.lean](RecursiveConsumption.lean) proves progress and
preservation for every actual ready-resume or disposal step from the richer
checked state. Resumption removes both record modes of the consumed owner and
recomposes the saved and waiting stores. Disposal transfers the actual closing
template to the surviving caller's store; it keeps nested retirement ownership
until those later steps execute. Both preserve the exact remaining demand,
footprint and output type. The mixed example resumes a saved bind containing a
nested disposal, and a separate actual disposal yields a checked materialized
plan. The other transition families, source admission and combined safety still
need integration. See [recursive state preservation through
consumption](KERNEL.md#recursive-state-preservation-through-consumption).

[RecursiveExecution.lean](RecursiveExecution.lean) carries the combined record
store through bind, beta, branch selection, constructed focusing, plugging and
every raw value-completion step. It derives progress for these forms and tracks
the exact owner retirement events. The earlier mixed example now completes all
seven steps from outer resume through nested disposal to unit at an empty
stack; every state checks, and the actual allocation ledger proves no duplicate
completion. The capture construction below addresses a resume-only new clause;
builtin providers, source installation and the general combined safety theorem
remain open. See [recursive ordinary execution
and completion](KERNEL.md#recursive-ordinary-execution-and-completion).

[RecursiveAllocation.lean](RecursiveAllocation.lean) transfers fresh capture to
the combined record store. It preserves old records in both modes and constructs
new closing records from actual plans and internal-use evidence. A structurally
admitted resume-only new clause can restore a saved computation that disposes
nested continuations. The example checks all nine steps from an operation
request through fresh capture, resume, nested disposal and return, including
fresh allocation and no duplicate completion. Omitting the original disposal
record rejects the pending check. The construction below adds the new clause's
disposal case with derived ownership balance; handler-table admission
and the combined safety theorem remain open. See [fresh capture with
combined records](KERNEL.md#fresh-capture-with-combined-records).

[RecursiveDisposalCapture.lean](RecursiveDisposalCapture.lean) checks either
mode of the newly bound clause. Structural induction derives a single
invocation's demand, and a derived permutation law equates the caller's final
owner phases for resume and disposal. The actual closing template authenticates
disposal's row and retirement demand. The example checks both branches of a
handler clause and executes fresh capture followed by disposal and nested
retirement through final return, with no duplicate completion. Reusing the existing check
decomposition, source provenance and ownership traces now derives complete
ownership balance for every existing `CheckedState`, including arbitrary
finite dormant nesting. Induction over the complete checking derivation and
the actual capture tree connects consumed owners to their saved owners.
Source dependency and ticket-translation proofs extend the internal-use bound
to recursive demands in the enclosing caller. General capture now derives
mode balance and returns it as a conclusion; the example supplies no separate
balance certificate. Complete source admission, closing-effect admission, clause
bounds and combined safety remain open. See [capture with either
one-shot clause mode](KERNEL.md#capture-with-either-one-shot-clause-mode).

[RecursiveEntries.lean](RecursiveEntries.lean) derives cleanup installation
from the existing checked source, including the callback closure, latent
effects and stored answer annotation. It reuses value decomposition and
neutral-frame interpretation to preserve the same demand, footprint and both
record collections. The example installs a fresh cleanup around the existing
nested disposal, preserves its lifetime ledger, and then disposes owner 23
while retaining owner 19's retirement demand. Resource entry is covered below
for bodies with enclosing-continuation actions; handler installation remains open. See [cleanup installation with
combined records](KERNEL.md#cleanup-installation-with-combined-records).

[RecursiveCells.lean](RecursiveCells.lean) transfers cell read/write to the
combined record judgment. It reuses request decomposition and ownership
transport, preserves both stores, and requires the existing canonical builtin
port signature for the selected operation. A nine-step execution continues
the previous materialized disposal plan through its callback's cell read,
cleanup completion, cell release and nested-owner retirement, with no duplicate
completion. A write example changes the stored payload from 17 to 18. These
results assume actual builtin selection; the next construction derives it for
closed checked requests. See [builtin cells with
combined records](KERNEL.md#builtin-cells-with-combined-records).

[RecursiveRequestProgress.lean](RecursiveRequestProgress.lean) derives an
actual interpretation for a checked request with a value operand and an empty
external context. Residual checking, actual owner phases and physical stack
resolution supply the connection. Existing canonical-form and selection proofs
construct a preserved builtin step. Existing typed capture constructs a raw
handler step at a fresh historical slot. The existing registry-history and
fresh-owner proofs then derive allocation and preserve the named step's ledger.
Examples derive the write update and
the earlier handler cut without supplying either selection. An unmatched
request is rejected; existing protection proofs also deny disposal of a
protected capture under policy-derived tables. General handler-clause admission
and initial-source progress remain open. See [request progress from recursive
checks](KERNEL.md#request-progress-from-recursive-checks).

[RecursivePlanAdmission.lean](RecursivePlanAdmission.lean) derives closing
template evaluation from the existing structural effect-admission judgment and
actual ownership. Retirement availability and the surviving caller's phases
come from established trace and projection lemmas. The general capture theorem
now takes the plan's ordinary residual check and derives recursive evaluation;
its example no longer constructs that evaluation separately. A reused nested
plan checks a cell-reading cleanup, release and retirement. Handler admission
must still establish the closing effects in the actual surviving caller. See
[closing admission from structural effects](KERNEL.md#closing-admission-from-structural-effects).

The [resource-world transport](KERNEL.md#resource-world-extension-with-combined-records)
now carries the existing recursive source and both continuation stores into
any larger resource world. It reuses port-world weakening and retains the
same requirements, ownership demand, phase transitions and accepted footprint.
The proofs live alongside the existing source and record judgments. This
closes the transport prerequisite for acquisition.

The [resource-entry construction](KERNEL.md#resource-source-entry-with-combined-records)
now admits a general initializer and resource bodies that consume enclosing
continuations. `ResourceRequirements.Hides` structurally discharges exact local
cell requests while retaining invocation keys, owner demands and sequencing.
Existing evaluator and residual lemmas prove agreement under the actual builtin
interpreter. Induction on an existing recursive check derives a finite freshness
condition covering its saved bodies and nearer handler expansions.

Entry uses that condition and the existing world/support proofs to derive the
opened body with both continuation stores preserved. The same source extension
preserves the existing complete ownership-balance theorem. A six-step source
example initializes, reads and closes a fresh resource, returning 17. Another
enters a resource and disposes its enclosing owner 23, retaining dormant owner
19's retirement demand. The freshness regression demonstrates that reusing an
observed cell identity would change a saved invocation's residual.

The [recursive clause connection](KERNEL.md#recursive-clause-ownership-and-capture-entry)
now derives exact clause ownership from existing checked traces and source
invocation provenance, including resource bodies. The existing capture theorem
has been factored so both phase-indexed and recursive clauses reuse its actual
allocation, closing-plan and recomposition proofs. A checked example captures
into a clause whose resource body disposes the newly created continuation.

Complete selected-clause and closing-effect admission and the combined
initial-source theorem remain open. The declaration connection below derives
clause completion; the actual clause check and footprint bound remain inputs.

The [handler-registration and entry proofs](KERNEL.md#fresh-handler-registration-and-entry)
now preserve both continuation stores when registering an activation fresh for
the existing lifetime history. Agreement covers dormant handlers as well as the
active caller. A counterexample shows that changing a dormant table can change
its saved interpretation while leaving the active context equal.

The [shared computational handler rule](KERNEL.md#shared-handler-expressions-and-ordered-resource-discharge)
now supplies those entry premises from the current combined source check. It
reuses clause substitution, world transport, interpreter-prefix and ownership
proofs. The complete handler-expression example derives its installed state;
a second example enters a resource and installs that handler inside it.

Resource discharge interprets nearer handler layers before removing local cell
requests. Two regressions distinguish handlers that export a local request from
handlers that introduce a request handled by the builtin. Invocation discharge
retains its nearer context. Declaration/source admission remains open, including
handler-bearing cleanup callbacks and justification of table rows and clause
checks. The combined initial-source theorem also remains open.

The [declaration capability connection](KERNEL.md#declaration-capabilities-and-table-modes)
requires the existing structural `ClausesUse` judgment in the source handler
rule. [RecursiveClauseUsage.lean](RecursiveClauseUsage.lean) reuses selected-clause
usage, lexical ticket dependencies and checked ownership traces to derive
completion of the actual captured owner. Capture no longer takes completion as
a separate premise when the declaration's usage evidence is supplied.

`SourceTemplates.ClauseModes` walks clauses and table entries together. Each
entry must cover its clause's possible disposal, using the existing action
analysis. Substitution and resource instantiation preserve this check. Handler
entry returns usage and mode evidence for the installed declaration, and capture
connects it to the selected table entry. An accepted protected capture therefore
has a clause checked with resume-only rights for its own continuation; nested
clauses keep their independently checked rights. This does not establish the
table's outward effect rows or the combined invariant over execution.
The existing parametric clause compiler satisfies this mode check for every
row specialization when the declaration's independent usage check holds.

The [outward-summary proof](KERNEL.md#outward-summaries-before-caller-interpretation)
in [RecursiveOutward.lean](RecursiveOutward.lean) now factors checking of source
expressions without an enclosing continuation into their own interpretations
and the actual caller's interpretation. It covers the shared computational
handler and scoped resource rules. Source induction derives an empty demand on
pre-existing continuation owners, and the summary is independent of the
continuation store. Existing uniform coverage transports advertised outward
bounds to the actual check. Examples distinguish caller-dependent residuals and
failure inside a nearer exact handler. The shared callable connection below
uses this factorization; clause effect admission and combined initial-source
safety remain open.

The [shared callable source connection](KERNEL.md#shared-callable-source-bodies)
admits a function whose body contains a computational handler. Its body uses
`SourceTemplates.Expression`, and its latent row comes from a proved outward
summary. [CallableSources.lean](CallableSources.lean) retains this body evidence
in the ordinary summary component. This is checking evidence for the existing
`Code` syntax and sequencing operation.

[SourceCallableTransport.lean](SourceCallableTransport.lean) reuses dependency
agreement, port transport, fresh-resource bounds and usage judgments to transport
these values. [SourceCallableSubstitution.lean](SourceCallableSubstitution.lean)
proves closed substitution for the shared expression and callable judgments,
including resource bodies, with exactly the original requirement certificate.
Function application, context decomposition, capture, collected consumption and
disposal capture retain that evidence. [CallableContexts.lean](CallableContexts.lean)
provides ordinary context decomposition. Cleanup callbacks and saved values can
contain handlers; [SourceClosingRows.lean](SourceClosingRows.lean) retains their
source evidence in closing plans with the existing residual equations.

[SourceCleanupExamples.lean](SourceCleanupExamples.lean) checks a cleanup callback
containing a handler through actual installation, invocation and beta reduction,
reusing the existing preservation proofs. Its closing-plan row also checks. The
remaining entry and request interfaces pass the grouped checks. Table-row
justification, selected-clause effect bounds and the combined initial-source
safety theorem remain open. The full integration check passes.

The [recursive bound connection](KERNEL.md#recursive-effect-bounds) transports
ordinary row coverage through saved continuation records at arbitrary finite
nesting. [RecursiveBounds.lean](RecursiveBounds.lean) preserves owner demands,
invocation modes and interpretation positions. Capture now derives the actual
clause check and bound from a checked upper certificate; closing-plan admission
also derives an actual exported row from an admitted bound. General
declaration-derived upper certificates and combined initial-source safety
remain open.

The [chosen closing-template connection](KERNEL.md#chosen-closing-templates)
computes the actual closing row before allocation and carries the same template
into the new disposal record. Bounded handler capture derives both invocation
checks and the clause's actual check; its source and upper certificate remain
explicit inputs at that interface. The existing nested-disposal example and its
complete execution proof now use this allocation path.

The [retained declaration connection](KERNEL.md#retained-declarations-and-selected-allocation)
derives full clause source typing from the selected handler declaration and
retains it through capture and fresh allocation.
[SourceClauseCapture.lean](SourceClauseCapture.lean) combines that derivation
with structural upper bounds to construct a runtime capture step, checked
successor, ownership permutation and effect containment. It handles captures
with a closing plan and captures where no plan or internal abandoned-use proof
is available. The latter path authenticates resumption and proves that disposal
cannot pass the recursive checker.

The examples construct immediate-resume certificates using the existing
value-evaluation and saved-invocation proofs. One captures across a running
cleanup callback, proves disposal unavailable, and then takes a preserved
resumption step. Handler entry now retains supplied full declarations on the
installed frame; registration preserves declarations in dormant captures too.
Declaration families also survive closed substitution and changes to unused
environment entries, using existing source transport proofs. General upper
certificates, declaration retention throughout executable code, and the combined
initial-source safety theorem remain open.

The [hereditary source connection](KERNEL.md#hereditary-source-declarations)
now retains full declarations recursively in executable clause, callable and
resource bodies. Its erasure preserves the existing full type, owner demand
and recursive requirements. Source-derived handler entry installs the
declaration and retains the stronger current body, using the existing entry
and ownership proofs. The [hereditary transport and substitution proofs](KERNEL.md#hereditary-transport-and-substitution)
now preserve that evidence through environment changes, world and contract
growth, closed substitution and selected payload binding. Source beta reduction
retains the function body's declarations and outward certificate while using
the existing rule's continuation scope `none`. The [hereditary execution proofs](KERNEL.md#hereditary-frames-and-execution)
now retain this evidence in every active or saved frame, through ordinary
reduction, value completion, installation, cell operations and one-shot
resumption. Hereditary closing records, disposal and both capture paths are
now connected too. Source-derived closing conditions and the combined initial-source
theorem remain open.

The [request-capture join](KERNEL.md#request-capture-from-one-checked-source-state)
now derives payload typing, clause selection, capability evidence and the offered
row from one checked source state. Protected captures have preserved successors
without extra closing or mode certificates. Unprotected outside-owner and
closing-budget admission, then the combined initial-source theorem, remain open.

The [outside-owner check](KERNEL.md#capture-sensitive-outside-owner-checking)
now has a finite selected-capability test and an ordered-composition law. It
reuses the existing internal-use and capture proofs. Actual small and large cuts
show why the test must use the captured region. Initial source summaries still
need to establish the test at every possible capture.

The [combined execution invariant](KERNEL.md#execution-with-structural-effect-checking)
now retains structural source/effect checking with the existing ownership,
resource support, one-shot usage and result contracts. Non-disposing capture
chooses its fresh owner and derives payload access before preserving the entire
invariant. Resumption preserves it through saved-continuation and caller
recomposition. Returned-value transitions, bind, application, branch selection,
focus, resource entry, cleanup installation and handler installation now
preserve it too. Release checks follow from structural result contracts; fresh
owners and activation names follow from the current history. The generalized
payload proof reuses the existing argument without assuming the older
pending-stack effect annotation. Cell reads and writes now preserve the same
invariant, including through cleanup frames. Closed request checking derives
the builtin step or nearest source-handler cut. Discard now preserves the
invariant from an earlier structural closing certificate and a successful
current footprint check, after an arbitrary checked caller execution. Current
resource support is derived. Source admission must still establish that
certificate and later check success, alongside disposal-enabled capture
admission and initial-source execution induction.

The [hereditary dependency annotations](KERNEL.md#hereditary-source-dependency-annotations)
now preserve cleanup/body associations through function types and applications.
Their erasure reuses the existing source types, clause-row checks and owner
requirements. Their [closed substitution and bind/beta connection](KERNEL.md#substitution-with-dependency-annotations)
now preserves the annotations and reuses the old requirement checks. Structural
capture checking now has a [local recursive guard](KERNEL.md#local-capture-guards-for-dependency-scopes).
The [actual-cut connection](KERNEL.md#dependency-scopes-and-actual-captures) now
derives the matching plan and owner accounting. The [retained source connection](KERNEL.md#retained-source-dependencies-through-capture-and-recomposition)
now derives those scopes from pending code and recursively saved source. Capture,
append and live-boundary replacement retain enriched function types and reuse
existing owner-record and evaluation laws. The [invocation-scope checks](KERNEL.md#structural-invocation-checks-and-receiving-callers)
now construct the exact resume and disposal arrangements, with independent
permission and owner-phase checks. A scope-level example shows why saved code
must be rechecked at its receiving caller. The [structural source checks](KERNEL.md#structural-source-checks-and-retained-work)
now express that rechecking obligation, preserve it through bind and beta
reduction, and derive a request's capture guard. Uniform clause-family checking
and full control-transition preservation remain open, so initial-source safety
is not yet established.

The [projected contexts and uniform clause schemes](KERNEL.md#projected-source-contexts-and-uniform-clause-schemes)
reuse these structural checks, prove resume/disposal families over arbitrary
admitted captures, and connect selected schemes to the same typed declarations.
Permission-map, phase and resource-world transport are proved. The strengthened
request rule supplies callback-schedule checking for fresh capture preparation.
Disposal now recomposes the rich callback source with ticket ownership and the
one-shot phase transition, reusing existing plan and accounting proofs. Closing
effect admission remains explicit. The selected store template now fixes the
recomposed requirements and checked row. Store reduction preserves that check,
the structural layout and richer retained certificates. A shared captured-annotation map now
connects the selected template to its contextual disposal check. Exact prefix
extraction identifies the checked waiting scope with the rich reconstructed
scope; disposal now preserves both judgments at its actual new owner phases.
Capture allocation now derives the closing template and captured annotation
from the same saved source used by the actual transition. It extends the
annotation binding and preserves existing rich records. The checked pending
computation supplies the capture row; the established allocation proof derives
the balance between captured demand and actual plan retirements. The contract's
closing row now comes from its exact stored template. Fresh insertion preserves
the saved and waiting checks against the updated store and supplies both
invocation checks. The current request check determines the selected offer's
export through the actual stack. The existing executable closing check supplies
disposal availability and closing-row coverage, after which the selected clause
reuses its existing row certificate. The closed-source connection below now
derives a successful closing check from the corrected source judgment and the
empty-outward guard. Complete initial-source admission remains open.
A [source-typed regression](SourceDependencyBudgetGap.lean) shows that richer
capture and caller typing, an exact closing template, and the contextual checks
still permit an empty normal row and a nonempty closing row. It reuses the
existing nested-handler fixture and its row proofs. The fixture uses a nonempty
outward interface: the empty outward closing guard used by the current `Run`
rejects it. This rules out a general open-segment budget implication, but does
not refute admission or progress for closed initial programs.
Complete initial admission and preservation of the combined source/ownership
invariant remain open.

The enriched lambda rule now checks that its latent footprint names only effects
in its declared interface. An inconsistent empty-interface annotation is rejected;
the same body remains accepted with a consistent interface. Existing transport,
substitution and canonical-form proofs retain this check. For a closing plan
typed with no outward effects, it implies an empty closing footprint. The
`closed_capture_budget` theorem constructs that plan and a successful budget
check from an actual supported cut and its checked empty-outward guard. The
future handler admission and other transition families still need integration.
The disposing-capture successor and owner-use connection are described below. See the
[source-state account](KERNEL.md#shared-enriched-source-state).

The [shared enriched source state](KERNEL.md#shared-enriched-source-state) now
combines these components at the same requirement indices and actual stack.
Its initial runtime construction reuses the existing resource/name ledger and
source initialization proofs. Bind and beta reduction preserve the enriched
state. Disposal now has both progress and preservation for the joined runtime
invariant, with exact owner consumption and an unchanged checked row. Its typed
plan is derived from the retained certificate. Existing proofs preserve resource
accounting, name history, usage and completion contracts for the same actual
step. Disposing capture now also has runtime progress and preservation from the
enriched invariant and the actual selected operation. The local source request
rule bounds pending work by the captured owners; its connection to runtime
owner use is proved in [SourceDependencyOwners.lean](SourceDependencyOwners.lean).
Resource support follows from the existing support and unique-ownership
invariants. Capture derives the
closing budget and new certificate, preserves ownership accounting and bounds
the new row by the old row. Annotation history connects every stored annotation
to an issued owner; the existing fresh-owner proof supplies freshness for all
three registries. This candidate invariant still lacks complete source admission
and runtime preservation for the other transitions.

The handler-admission gap now has a checked counterexample in
[SourceDependencyHandlerGap.lean](SourceDependencyHandlerGap.lean). A handler
clause performs an operation through an outer interpretation before resuming.
Its rich declaration, including its row bound, is admitted, and its dependency
tree passes contextual checking with that outer handler present. The existing
uniform declaration certificate is nevertheless impossible: it also requires
checking the clause with an empty receiving stack. Enlarging the outward effect
list does not supply the missing interpretation. The certificate must retain
outer-context assumptions; attaching it unchanged would reject this composition.
This is a source-admission counterexample, not a reachable-run counterexample.

The contextual certificate in
[SourceContextualClauses.lean](SourceContextualClauses.lean) retains the exact
receiving stack and remains general over owner names and admitted captures.
Existing uniform certificates embed unchanged. An operation capability records
exact nearest lookup; its source-handler case currently supplies a resume-only
offer in both protection modes. It permits a request prefix before a certified
suffix and can be reused for repeated requests. The previously rejected
declaration now has this contextual certificate; missing and shadowed
interpretations remain rejected. Selection and capture preparation reuse the
existing source, mode and recomposition proofs. Spent-marker projection
preserves certification. Retained recipes and finite rechecking extend this to
changed caller contexts below; source admission and runtime integration remain open.

The stored component in
[SourceContextualForest.lean](SourceContextualForest.lean) attaches contextual
certificates to actual handler frames and their exact annotated suffixes.
Splitting an actual handler cut returns the selected certificate and the same
operation lookup; recomposition and capture preserve certificates throughout
nested dormant continuations. Old uniform forests embed unchanged. The earlier
composition now passes this stored-component judgment on an actual pair of
handler frames, while the old judgment rejects it. Spent-marker projection and
resumption at the captured owner's boundary are proved. General reconstruction
under a finite scope check is described below. Source handler admission and
replacement of the shared runtime invariant remain open.

The source join in
[SourceContextualCapture.lean](SourceContextualCapture.lean) now connects that
forest to the same rich source segment. Successful exact lookup identifies the
stored and typed capture scopes. Contextual allocation then reuses the common
allocation proof for the actual step, exact ownership increment, rich payload
substitution, closing records and independent invocation interfaces. The old
uniform allocation theorem is a wrapper around that same proof. Contextual
allocation retains the existing explicit plan, internal-owner, freshness and
row-checking premises; integration must derive them from the combined invariant.
This does not yet establish complete contextual runtime progress or preservation.

Finite requirement recipes are defined in
[SourceContextualRequirements.lean](SourceContextualRequirements.lean).
They retain how a clause or declaration certificate is constructed from explicit
resume/dispose permissions, silent prefixes, resource binding and local requests,
pure cleanup, external and internally handled request prefixes, and choices.
The contextual recipe no longer accepts arbitrary uniform future-body proofs.
Its compiler reuses the proved primitive recomposition lemmas, and the actual-plan
recipe erases directly to the same structural constructors. The separate older
semantic certificates remain proof tools, with no bridge admitting arbitrary
certificates as source recipes. The executable checker
is sound and complete for the existing `RequestCapability` judgment. Requirements
use membership rather than occurrence counts, independently of continuation use
and interpretation order. Rechecking accepts compatible caller contexts and
compatible nearer handlers, while rejecting missing operations and disposing
overrides for the current resume-only request-prefix rule.

[SourceContextualRechecking.lean](SourceContextualRechecking.lean) checks each
actual handler's requirements at its annotated receiving suffix. It reconstructs
the contextual forest for arbitrary nested captures. Full-prefix resumption
preserves the retained recipes by a handler-membership law; disposal retains a
subset of those handlers. Both operations now reconstruct certificates from a
finite check at the recomposed stack. An actual nonempty caller example passes.
These theorems still take successful rechecking explicitly. Initial source
admission must retain the recipes and establish the checks at invocations;
complete runtime progress and preservation remain open.

[SourceContextualHints.lean](SourceContextualHints.lean) places the requirement
data and executable tests below the source-checking judgments in the import
graph. `Hints` adds per-handler requirement lists to the existing source scopes,
retaining their declaration tables, dependency families and dormant captures.
Its checker uses no runtime stack or handler registry.
[SourceContextualHintChecking.lean](SourceContextualHintChecking.lean) proves
that this test decides the structural `Compatible` judgment. Authenticated
annotations produce exactly the runtime check and reuse the existing certificate
reconstruction proofs for resumption and disposal. A negative example passes
the current-scope check but fails resumption under a masking caller; a separate
proof rejects fabricated empty requirements for the saved handler. Admission
must still retain these annotations and recipes and require the invocation
checks. The shared source and runtime judgments have not yet been changed.

[SourceContextualInvocationHints.lean](SourceContextualInvocationHints.lean)
adds annotated owner lookup and executable invocation checks. Lookup erases
to the existing active-spine lookup, including its exclusion of dormant owners.
The existing access, permission, phase and closing checks are combined with
handler compatibility at the exact recomposed annotation.
[SourceContextualInvocations.lean](SourceContextualInvocations.lean) proves
that these tests decide structural `Resume` and `Dispose` judgments. An admitted
invocation constructs the actual runtime step, matching annotations, contextual
handler certificates and an exact owner-consumption trace. Disposal reuses the
existing closing-plan and captured-owner accounting proofs. A nested disposal
example includes a callback, a dormant owner and an outer resource. This closes
the invocation component connection; initial source admission, preservation of
all rich source components and the combined runtime induction remain open.

[SourceDeclarationPlans.lean](SourceDeclarationPlans.lean) retains declaration
annotations through sequencing, clause modes, cleanup callbacks and fresh
resource bodies. [SourcePlannedChecks.lean](SourcePlannedChecks.lean) adds
structural local and pending-code judgments over those plans. They erase to the
earlier checks, retain recipes for future handlers, and supply the contextual
handler-entry and actual invocation proofs. Examples check a forwarding handler,
its installation inside a callback, and rejection without its required outside
interpreter. These results do not yet carry plans through full expression/value
typing or prove that capture produces a clause satisfying the strengthened
checks. Those connections precede shared runtime preservation and execution
induction.

[SourcePlanSignatures.lean](SourcePlanSignatures.lean) separates stable checking
annotations from literal clause syntax. Value substitution changes a clause's
code while preserving its signature; changing required continuation actions
does not preserve that signature.
[SourcePlanSignatureChecking.lean](SourcePlanSignatureChecking.lean) proves that
equal signatures preserve declaration recipes, recursive certification and all
strengthened local checks. It also transfers a handler check to the actual
clause witness authenticated by source annotation.

[SourcePlannedTyping.lean](SourcePlannedTyping.lean) checks these signatures
through all source forms and retains them in function types. Its `Typed`
judgment pairs the annotation derivation with the existing hereditary derivation
at the same code, environment, result type and dependency indices.
[SourcePlannedTransport.lean](SourcePlannedTransport.lean) supplies environment,
world and contract transport.
[SourcePlannedSubstitution.lean](SourcePlannedSubstitution.lean) proves closed
substitution, bind reduction, beta reduction and fresh resource-body opening.
Bind and beta reduction reuse the earlier ownership-demand and requirement
evaluation proofs. A higher-order cleanup example checks both substitutions.
Synchronizing intermediate type choices for machine-frame storage, deriving the
stronger clause check at capture, and shared runtime preservation remain open.

[SourcePlannedSources.lean](SourcePlannedSources.lean) now makes intermediate
type agreement structural. One derivation chooses value types, signatures,
requirements and owner demands together; the earlier source and annotation
derivations are projections. Handler decomposition retains its full body and
declaration proofs.
[SourcePlannedContexts.lean](SourcePlannedContexts.lean) decomposes actual
evaluation positions with the same intermediate type on the child and retained
context. It constructs the actual focus step and ordinary frame metadata using
the existing frame-preparation proof, with an unchanged owner trace.

[SourcePlannedSourceTransport.lean](SourcePlannedSourceTransport.lean) and
[SourcePlannedSourceSubstitution.lean](SourcePlannedSourceSubstitution.lean)
preserve this stronger derivation under environment, world and registry
transport and closed substitution.
[SourcePlannedSourceReduction.lean](SourcePlannedSourceReduction.lean) retains
it through bind, beta reduction and context recomposition. Bind and beta also
preserve the strengthened local check at the same receiving scope and owner
phase. The higher-order cleanup example now checks the stronger result through
both substitutions. Deriving the stronger checks for the clause selected at
capture and retaining the stronger source evidence throughout `State` and `Run`
remain integration obligations.

[SourcePlannedRecomposition.lean](SourcePlannedRecomposition.lean) splits and
joins the stronger pending checks while retaining exact handler annotations,
callback plans and dormant branches. It constructs head resume and disposal
clause checks from the saved and waiting pieces at the consumed owner phase;
permission, availability, protection and closing routes remain independent.
Request prefixes reuse the earlier operation-capability proof. The existing
nested-disposal example now authenticates the complete callback, including its
bind, with a structural source derivation at the retained plan signature. It
retains the stronger pending check through the actual step and reuses ownership
and closing-plan accounting. Deriving the
required piece checks at every source capture remains open.

[SourceNeutralScopes.lean](SourceNeutralScopes.lean) addresses the
pure pending frame introduced when focus moves to the right side of a pair,
spent-history markers introduced by capture, and armed pure callbacks.
Its structural expansion keeps dormant programs and existing frame annotations
fixed. It preserves interpretation capabilities, handler compatibility,
protection, closing routes and owner bounds.
[SourcePlannedNeutralFrames.lean](SourcePlannedNeutralFrames.lean) reuses those
observations for handler compatibility and independent resume/disposal
judgments. [SourcePlannedCuts.lean](SourcePlannedCuts.lean) recovers the exact
annotated handler cut from existing lookup and preserves it through expansion.
[SourcePlannedNeutralChecks.lean](SourcePlannedNeutralChecks.lean) uses those
pieces to prove full `Local` and `Pending` transport, including disposing
requests, callbacks and nested continuations.

[SourceProviderInsertion.lean](SourceProviderInsertion.lean) establishes the
independent checks needed for resource-scope admission. Inserting one builtin
cell on the active spine preserves closing-route agreement, capture guards,
operation-capability requirements and independent continuation access. A
matching request may switch from a source handler to the builtin; lookup
results need not be equal. Existing saved continuations remain identical, and
the inserted cell remains in the recomposed caller or waiting suffix. The
proof reuses existing cuts and checks, and requires no resource-support premise
for these observations. Runtime freshness, resource support and owner-ledger
checks remain separate obligations.

[SourceDependencyProviders.lean](SourceDependencyProviders.lean) transports the
mutually recursive local and pending dependency checks, including source
restored by resume and callback schedules selected by disposal.
[SourcePlannedProviders.lean](SourcePlannedProviders.lean) reuses that result to
retain declaration plans and independently checked invocation compatibility.
[SourceScheduledProviders.lean](SourceScheduledProviders.lean) transports the
existing handler and owner cuts through the actual retained plans.
[SourceScheduledProviderChecks.lean](SourceScheduledProviderChecks.lean) then
preserves the full scheduled `Local` and `Pending` judgments, including handler
requirements at their receiving suffixes. Each layer also proves outside
transport for dormant saved code. No future-success premise is introduced.

The [provider examples](SourceScheduledScopeExamples.lean) check a resource body
that uses its new provider before resuming, a resumed request switching from a
source handler to a builtin, an armed callback captured by a disposing request,
and disposal with an effectful saved callback. These are local source checks,
not complete initial executions. The consuming declaration grammar now also
admits resource binding and its locally supplied operations. An explicit
provider-list index records the resources available to the current body;
`localRequest` checks membership without adding an outer requirement, and
`resource` adds the freshly bound identity for its body. Declaration boundaries
use an empty provider list. Compilation interprets the list as the ordered
actual caller prefix, reusing provider insertion and resource-world extension.

The resource declaration examples derive a resource-bearing disposing body at
capture with no outer operation requirements, retain its recipe through actual
payload substitution, and admit nested resources with repeated local requests
before one continuation consumption. A negative case rejects a local request
without an enclosing provider. These results include recipe erasure,
certification, signature transport and scheduled compilation; complete initial
admission remains separate.

[SourceHandlerInterference.lean](SourceHandlerInterference.lean) now gives an
[exact closing criterion for handler insertion](KERNEL.md#exact-handler-interference-during-closing).
Its structural `Shielded` judgment checks each callback at its original suffix,
including dormant captures. A callback requesting the inserted effect must
already reach a nearer builtin. The finite checker is sound and complete for
this criterion, and the existing closing checker factors exactly into its old
result and this extra check. A finite list of exposed effects represents the
same obligations; membership suffices, without counting repeated effects.
Existing closing-effect rows bound that list, so excluding the inserted effect
from the row supplies a sufficient check without adding a contract field.
Positive cases admit overlapping effects shielded by a builtin; negative cases
reject exposed active and dormant callbacks. Established realization and
ownership proofs supply the operational closing interface. This completes a
closing-interference prerequisite, not general handler-clause admission. Its
scope excludes operation selection, clause capabilities and retained pending
source; the finite requirement result below addresses part of that boundary.

[SourceHandlerRequirements.lean](SourceHandlerRequirements.lean) now derives
the [finite operation interface for installed-handler requirements](KERNEL.md#finite-operation-requirements-at-handler-insertion).
The interface retains only requests whose lookup reaches the scope's outside,
including requirements from dormant captures at their receiving suffixes.
For an already checked scope, satisfying this finite interface is necessary
and sufficient for replacement of that outside scope. Handler insertion needs
the new table's capability only for exposed requests that reach the insertion
point and match its effect. Missing operations do not fall through; nearer
builtins can shield their operations. The result reuses the existing
`RequestCapability` and structural `Compatible` judgments. The old provider
requirement transport now specializes this general theorem. These are exact
results for installed-handler requirements, not full pending-source transport,
selected-clause body typing or general handler-clause admission.

[SourceHandlerSelection.lean](SourceHandlerSelection.lean) proves the
[exact capture and waiting-scope transformations](KERNEL.md#exact-selection-and-capture-pieces-at-handler-insertion)
that the operation interface alone does not retain. An inserted handler can
take over an exposed matching operation, enter the capture of an outer
selection, or enter only the waiting scope of an inner selection. Each case
reuses the existing lookup-to-cut theorem on the actual annotated hints.
Missing nearest operations stay blocked. The local capture guard is preserved
when only its waiting scope changes; full pending-source checks remain separate.
The source capability-prefix theorem now reuses this general lookup law for
sequencing and live-owner frames. A reused protected-capture counterexample
confirms that selecting a disposing handler does not establish permission to
capture running cleanup.

[SourceHandlerClosingInsertion.lean](SourceHandlerClosingInsertion.lean)
connects closing interference to these exact captured scopes. Closing after
insertion is equivalent to the old closing judgment and the finite shielding
check on the prefix before insertion. The same equivalence holds for the
existing executable checker. An outer selected handler's capture guard is
preserved when that extra check holds for its disposing mode; its contract and
protection mode remain unchanged. Positive and negative cases distinguish
builtin-shielded callbacks from callbacks intercepted by a complete resumptive
handler. Full pending-source preservation still requires the mutual source
transport proof.

[SourceHandlerRequests.lean](SourceHandlerRequests.lean) and
[SourceScheduledHandlerRequests.lean](SourceScheduledHandlerRequests.lean)
now prove [full request transport when the inserted handler enters an existing capture](KERNEL.md#source-request-transport-with-an-unchanged-closing-schedule).
Closing removes that frame, leaving the old callback schedule and live-owner
inventory unchanged. The request's owner bound is transported structurally;
the stronger theorem retains the actual callback plans and authenticates their
cut with the existing uniqueness proofs. The finite interference check is
the only extra premise beyond the old request and exact insertion case. No
replacement schedule is supplied. An example reuses the existing disposing
cleanup derivation, while another uses established resumptive capabilities for
a new handler taking over a builtin operation. Full mutual source transport,
including changed waiting scopes and the pending source restored by invocation,
remains open.

[SourceInterpretationInsertion.lean](SourceInterpretationInsertion.lean)
generalizes the existing provider owner-selection proof to builtin and handler
frames. The selected saved program remains identical; exactly one caller or
waiting piece changes. Resume/dispose retain independent ticket permissions,
phases, protection and saved closing checks. The existing provider proofs now
reuse this shared result.
[SourceHandlerInvocations.lean](SourceHandlerInvocations.lean) supplies exact
[finite invocation compatibility checks](KERNEL.md#continuation-invocation-under-handler-insertion).
At a known insertion point, only the new declaration's requirements and the
preceding exposed operations it intercepts need checking. Its structural
`Interface` is necessary and sufficient given the original compatibility.
Caller and waiting examples reuse admitted continuations; a masking handler
preserves independent access but fails compatibility, and a spent owner remains
rejected.
[SourceScheduledInterpretationInsertion.lean](SourceScheduledInterpretationInsertion.lean)
retains the actual stored plans and existing authenticated owner cuts. The
saved plan is identical through resume and disposal recomposition. Existing
scheduled-provider owner proofs also reuse this generalization. These results
establish access, compatibility and exact plan placement. The retained-site
transport below handles the pending traversal; the full mutual proof and a
general handler recipe remain open.

[SourceScheduledPendingSites.lean](SourceScheduledPendingSites.lean) gives an
exact [decomposition of retained source checks](KERNEL.md#retained-code-sites-and-handler-transport).
A pending check consists of finite declaration compatibility and checks of the
actual stored plans at their receiving sites. Insertion leaves each site's
scope unchanged or inserts the same interpretation there, preserving callbacks,
running protection and dormant receiving suffixes. Its transport theorem
requires a proof transformer for affected local code sites; this is a theorem
argument, not a source-admission annotation. Both existing provider pending
transport proofs now reuse it.
[SourceScheduledHandlerRequests.lean](SourceScheduledHandlerRequests.lean)
uses this traversal for insertion in the waiting side of a selected request,
reusing its original captured schedule and owner bound.
[SourceScheduledHandlerInvocations.lean](SourceScheduledHandlerInvocations.lean)
uses it for scheduled resume and disposal at the spent-owner phase. Each helper
retains the local proof-transformer obligation of the full mutual theorem.
Examples discharge that obligation for captured pure callbacks. General
handler recipes and the final mutual proof remain open; these helpers do not
assume a replacement pending schedule. Fresh disposing interception now has
the structural prefix rule described next.

[SourceScheduledClosingCallbacks.lean](SourceScheduledClosingCallbacks.lean)
checks each retained callback at its actual closing suffix, walking the original
forest and recursively saved branches. It constructs the closing `Pending`
schedule and proves the converse.
[SourceScheduledFreshRequests.lean](SourceScheduledFreshRequests.lean) combines
these [structural fresh-capture checks](KERNEL.md#newly-selected-disposing-handlers)
with the existing owner-bound judgment and independent capture guard. The
result is exactly the existing disposing request judgment at its actual cut.
`installed_request_from_prefix` derives the new captured obligations from the
preceding prefix: the installed handler adds neither owners nor callbacks.
An example changes a builtin request into a disposing capture containing a
pending ticket use, its owner, an effectful callback and the callback's retained
resource. No old disposal schedule or replacement `Pending` proof is supplied.
The general declaration rules still need to establish these prefix judgments;
the source-to-execution milestone remains incomplete.

[SourceHandlerCoverage.lean](SourceHandlerCoverage.lean) checks finite coverage
of the nearest interpreter's operation interface. The
[source request connection](KERNEL.md#finite-coverage-of-an-intercepted-operation-interface)
derives builtin operation validity from structural typing, so a typed request
needs no separate assumption that a cell operation is 0 or 1. A checked negative
example rejects operation 2 despite successful abstract cell lookup. This
connection checks individual requests; saved-code transport and callable
contract admission remain separate obligations.

[SourceScheduledHandlerSelection.lean](SourceScheduledHandlerSelection.lean)
classifies every actual selected handler after insertion: interception by the
new frame, insertion inside an old capture, or insertion in its waiting suffix.
It retains exact contract, modes and stored plans.
[SourceScheduledHandlerTransport.lean](SourceScheduledHandlerTransport.lean)
uses that classification to assemble the
[general request transport case](KERNEL.md#exhaustive-request-transport-under-handler-insertion).
Captured insertions reuse the same closing code and owner checks. Waiting
insertions reuse the retained-site traversal; closing carries no installed
handler requirements, so only affected callback code needs transport. Fresh
captures use structural owner and callback judgments. The capture guard remains
an independent source check. Three examples use this single theorem, including
a fresh disposer with a nonempty capture and an effectful callback.
The recursive callback transformer is a proof-level parameter of this helper.
The structural judgment below discharges recursion without storing such a
function as a declaration annotation.

[SourceScheduledHandlerAdaptation.lean](SourceScheduledHandlerAdaptation.lean)
introduces mutually inductive `Adapt` and `Retained` judgments. Their rules walk
actual plan constructors, code frames, callbacks and dormant captures.
`Adapt.sound` and `Retained.sound` compile these derivations into the existing
local and pending checkers by mutual induction. Resume and disposal derive
finite invocation compatibility from the recursively compiled retained checks;
no separate invocation interface or target pending proof is a source premise.
Retained adaptation preserves the owner list, including order and multiplicity.
The context relation remains independently established by insertion, splits
and authenticated cuts.

The nested example resumes owner 19 into stored disposal of owner 23, then
checks owner 23's effectful callback against retained resource 7. A waiting
request and the earlier simple invocation examples also use the structural
compiler. The existing missing-operation counterexample rejects a structural
adaptation through an unsafe shadowing handler. General declaration admission
must still produce these derivations; this does not extend the consuming recipe
grammar or complete initial-source safety.

[SourcePlannedPhases.lean](SourcePlannedPhases.lean) transports the stronger
checks through phase, permission and resource-world extensions using the
existing laws. Nested declaration witnesses are retained in the larger world.
[SourcePlannedCapturePrep.lean](SourcePlannedCapturePrep.lean) derives the
saved-code, waiting-stack and disposal-callback checks from the request and
pending checks before capture. It reuses the law that spending the freshly
introduced owner restores the original phase map. These results prepare clause
admission; they do not yet check every actual clause body or preserve the shared
runtime invariant.

[SourcePlannedClauseRecipes.lean](SourcePlannedClauseRecipes.lean) supplies
structural rules for resume, disposal, resource binding and local requests,
silent prefixes, pure cleanup, external and internally handled request prefixes,
and choices at actual plans. Compilation reuses the independent invocation and
recomposition proofs; capture derives its premises from the pre-capture checks.
[SourcePlannedRecipeDeclarations.lean](SourcePlannedRecipeDeclarations.lean)
retains these recipes for both offered modes and selects the exact stored plan
using existing clause lookup. The annotation supplies the earlier declaration
and certification premises for handler entry. The existing example requiring
an outer interpretation passes these rules and still fails uniform admission.
[SourcePlannedSelectedSources.lean](SourcePlannedSelectedSources.lean) joins the
synchronized source body and local capture check at that same selected plan.
These results cover the stated recipe constructors. General handler-bearing
clause bodies need further structural rules; retaining the stronger recipes throughout
source judgments and runtime states and the final preservation induction remain
open.

[SourcePlannedCaptureSubstitution.lean](SourcePlannedCaptureSubstitution.lean)
substitutes the closed operation payload into the synchronized clause body,
retaining its signature and row judgment. Existing port typing supplies lexical
readiness; the actual capture step reuses the established owner and phase laws.
[SourcePlannedRuntimeCuts.lean](SourcePlannedRuntimeCuts.lean) authenticates the
saved and waiting hints against the physical handler cut, including dormant
branches, and extracts the selected handler's supplied requirements from the
original compatibility check.
[SourcePlannedCaptureEntry.lean](SourcePlannedCaptureEntry.lean) combines these
results with source selection and structural recipe checking. The actual
successor retains matching hints, local and pending checks, and exactly one new
owner without duplication. For a supplied fresh matching continuation contract,
it derives both the raw capture step and the substituted source body. This
component does not construct that contract's saved and closing records or
preserve the complete runtime invariant.

[SourcePlannedAllocationData.lean](SourcePlannedAllocationData.lean) retains the
selected clause's synchronized source, actual plan, local and pending checks,
and runtime-matching hints through allocation. Its construction follows from
the actual cut and structural source checks. Erasure supplies the older
allocator's interface; refining its returned contract changes only the selected
value annotations and preserves every demand, row and effect field.
[SourcePlannedAllocation.lean](SourcePlannedAllocation.lean) reuses the shared
allocation theorem to return the stronger substituted body under that exact
contract, alongside all existing saved and closing records, ownership, scope,
row and combined-budget results. The shared theorem now retains proof data at
the selected answer, family and effect interfaces as well as both scopes.
Saved and closing source structures still use the older annotations; their
strengthening and adoption by the complete runtime invariant remain open.

[SourcePlannedFrames.lean](SourcePlannedFrames.lean) retains actual source plans
in frames and stack segments, including synchronized handler declarations and
structural recipes for both offered modes. Erasure reuses the existing frame
proofs, and matching relates the annotations to the actual runtime stack.
[SourcePlannedFrameCuts.lean](SourcePlannedFrameCuts.lean) preserves this stronger
source evidence across the actual handler cut.
[SourcePlannedFrameInterfaces.lean](SourcePlannedFrameInterfaces.lean) derives
the allocation interface from that installed handler and reuses the allocator.
The selected stronger declaration certificate and saved/tail decomposition no
longer need separate premises. Allocation still returns the earlier saved and
closing source structures. Matching stack hints alone does not tie each retained
frame's source plan to its pending check.

[SourcePlannedCheckedFrames.lean](SourcePlannedCheckedFrames.lean) addresses that
identity with joint structural judgments. Plain contexts and cleanup callbacks
share one plan between source typing and local checking; dormant continuations
retain the same relationship recursively. The older source and pending judgments
are projections of this joint evidence.
[SourcePlannedCheckedRecomposition.lean](SourcePlannedCheckedRecomposition.lean)
recomposes joint segments with their actual receiving suffixes and the existing
requirement-evaluation equation.
[SourcePlannedCheckedCuts.lean](SourcePlannedCheckedCuts.lean) retains joint saved
and waiting segments at a physical cut, with one refined answer type and exact
annotation recomposition.
[SourcePlannedCheckedInterfaces.lean](SourcePlannedCheckedInterfaces.lean) derives
clause data indexed by that same refined answer; its pending premise follows
from the joint source. `TypedClauseData.allocated_body` preserves the fixed answer
through contract refinement and substitution. The earlier allocation interface
remains an existential projection.

[SourcePlannedCheckedTransport.lean](SourcePlannedCheckedTransport.lean) extends
joint frames and segments through fresh contract, permission and phase changes.
[SourcePlannedCheckedAllocationData.lean](SourcePlannedCheckedAllocationData.lean)
retains those segments at the allocator's exact demand and requirement indices.
It aligns clause checks with the actual saved/waiting hints and rebuilds the
joint live segment under the constructed contract's refinement.
[SourcePlannedCheckedAllocation.lean](SourcePlannedCheckedAllocation.lean) reuses
the shared allocation proof to return that joint successor alongside the actual
capture step, exact owner increment, owner uniqueness and existing record checks.
The clause and retained stack share the same refined answer and runtime hints.
Closing records still use the older source annotations. Their strengthening must
also connect scheduled cleanup checks to the actual retained callback plans;
the current scheduled `Pending` judgment can hide another plan at the same
dependency index. The remaining clause recipe rules, source-derived closing
budget and complete runtime preservation/progress remain open.

[SourcePlannedClosingPlans.lean](SourcePlannedClosingPlans.lean) records the
actual callback plans alongside the existing release, retire and invoke
sequence. Extraction from joint captured source includes dormant continuations.
`Contents` and `Template` retain synchronized callback source; `Checked` checks
the same annotation at the actual closing suffix. Materialization produces a
joint closing stack with the template's exact requirement body.
[SourcePlannedClosingRecomposition.lean](SourcePlannedClosingRecomposition.lean)
splits and joins those checks without changing callback plans, transports
templates through registry extension and caller-scope changes, and recomposes
the materialized stack with its waiting stack using the existing accounting
equation. The request/disposal rules must still derive this stronger scheduling
judgment. Allocation must retain the stronger template at the actual chosen
closing requirement body; an independently chosen template does not establish
that identity. The following allocation connection retains that exact witness.

[SourcePlannedClosingAllocationData.lean](SourcePlannedClosingAllocationData.lean)
constructs a stronger closing template from the joint saved source and supplies
its erasure to the shared allocator. The shared proof now has an entry point
that accepts this template construction and retains its evidence at the same
raw footprint and requirement body; the earlier interface remains a wrapper.
[SourcePlannedClosingRecords.lean](SourcePlannedClosingRecords.lean) retains that
evidence in disposal records and transports older records across the actual
capture using the established location equations.
[SourcePlannedClosingAllocation.lean](SourcePlannedClosingAllocation.lean)
returns the stronger closing template and disposal records under the same
refined contract as the joint clause and live stack. Ownership, row and record
checks reuse the shared allocation proof. The retained-plan judgments below
derive scheduling for actual callback plans; this allocation wrapper still
uses the earlier source judgments. Stronger record
retention also reuses the existing post-step layout and capture-origin proof
for steps that create no ticket, while exact lookup selects the corresponding
planned template. Integrating these components into all runtime transitions
remains open.

[SourceRetainedPlans.lean](SourceRetainedPlans.lean) adds explicit annotations
for the actual pending and callback plans. Existing nearest-handler cuts split
these annotations, and fixed annotated scopes determine the pieces uniquely.
[SourceScheduledChecks.lean](SourceScheduledChecks.lean) checks sequencing,
cleanup, requests and invocations against those retained plans. Invocation
capabilities and owner selection remain the existing independent checks.
Handler installation retains structural recipes for the actual clause plans,
matching the evidence required by installed handler frames.
Erasure recovers the earlier planned checks; closing checks now refer to the
actual callback plans instead of existential alternatives at the same indices.

[SourceScheduledFrames.lean](SourceScheduledFrames.lean) connects those
annotations to typed contexts and callbacks and projects to the established
joint source and pending judgments.
[SourceScheduledClosing.lean](SourceScheduledClosing.lean) extracts closing
annotations from that source, preserving the exact callback plans through
nested dormant captures. The request and disposal rules derive the extracted
template's scheduling check at the actual receiving suffix and owner phase.
These are component results. Capture allocation, retained records, all
transition families and initial-source progress still need to adopt the
stronger judgments; full clause recipes and the source-derived closing budget
also remain open.

[SourceScheduledRecomposition.lean](SourceScheduledRecomposition.lean)
splits and joins checks over the same retained plans. Typed segment composition
preserves requirement evaluation and record concatenation, including dormant
captures. Head resume and disposal checks follow from the retained pieces and
the existing independent access and compatibility checks.
[SourceScheduledCuts.lean](SourceScheduledCuts.lean) decomposes the actual
handler cut into typed captured and waiting segments, retaining the exact plan
annotations and accounting equations.
[SourceScheduledCaptureClosing.lean](SourceScheduledCaptureClosing.lean)
uses that decomposition to derive the closing template and callback checks
from the whole source stack. For a disposal-enabled handler, existing checked-cut
and owner-bound proofs also derive successful plan construction and internal
owner use. These are conclusions, together with the captured source and the
existing ownership-split equation; no independent successful-plan premise is
required.
[SourceScheduledTransport.lean](SourceScheduledTransport.lean) preserves these
plans through registry, permission and available-phase extensions, reusing
existing expression, context and continuation-access proofs. Complete source
admission, adoption by the runtime state and full runtime preservation remain open.

[SourceScheduledNeutral.lean](SourceScheduledNeutral.lean) retains actual
plans when pure pending frames, spent-history markers or armed pure callbacks
are inserted. Handler and owner cuts lift existing selection evidence, and
expansion preserves the selected dormant continuation. `Expansion.forClosing`
relates the resulting closing forests; it retains new callbacks rather than
asserting that the forests are equal.
[SourceScheduledNeutralChecks.lean](SourceScheduledNeutralChecks.lean)
transports the stronger source and pending checks through that relation, reusing
the earlier capability and compatibility proofs while retaining callback plans.
Its `pure_cleanup` rule wraps any locally admitted body with an effect-free pure
callback, including resume, disposal and a request that disposes its capture.
The examples also check repeated wrapping and prove that adding this callback
changes the closing schedule.
[SourceDependencyNeutral.lean](SourceDependencyNeutral.lean) reuses the same
scope relation and selection lemmas at the erased checker, allowing
`Recipe.cleanup` in both declaration recipe layers without an import cycle.
The declaration examples in
[SourceScheduledScopeExamples.lean](SourceScheduledScopeExamples.lean) now
derive a cleanup-bearing body at capture from its request and retained checks,
and preserve a cleanup/resume recipe through an actual clause substitution.
[SourceScheduledCapturePrep.lean](SourceScheduledCapturePrep.lean) derives the
fresh capture's live, restored and closing checks from the request and the
pre-capture forest.
[SourceScheduledClauses.lean](SourceScheduledClauses.lean) compiles the existing
structural recipes against those exact plans. Declaration selection returns
the stronger clause check and source-body family at the same selected plan.
This covers resume, disposal, resource binding and local requests, silent
prefixes, pure cleanup, external request prefixes and choice. Handler and
effectful-cleanup declaration recipes remain open; the supported recipe fragment is not the final calculus.
The later [runtime progress result](KERNEL.md#scheduled-capture-and-exhaustive-progress)
covers states admitted by that fragment.

[SourceScheduledClauseHandlers.lean](SourceScheduledClauseHandlers.lean)
adds a [capture construction for handler-bearing clauses](KERNEL.md#constructing-handler-bearing-clauses-at-capture).
It derives the original consumer check, structurally adapts its retained code,
and checks newly introduced requests only after installing their handler.
Actual clause selection and source typing refer to the same full plan. Checked
examples cover repeated newly supplied operations, reinterpretation of a saved
request, and disposal with an effectful saved callback under running protection.
The old recipe grammar still rejects the full wrapper; general declaration
admission must generate and retain the structural adaptation evidence. This
component does not establish complete initial admission or runtime preservation
for the new clause form.

[SourceScheduledAdaptationCompilation.lean](SourceScheduledAdaptationCompilation.lean)
generates the retained adaptation traversal by induction, including callbacks
and dormant saved branches. A structural `RequestFootprint` also generates code
adaptation from a finite operation-list check for stored code without explicit
continuation invocations. Sequencing, choice, nested handlers, effectful cleanup
and resource binders compose this footprint. The resume and disposal examples
now use these compilers; they no longer supply handwritten retained trees.
Continuation invocations keep their independent checks. The
[compilation boundary](KERNEL.md#compiling-adaptation-from-source-interfaces)
explains the remaining declaration and execution obligations.

[SourceRequestFootprints.lean](SourceRequestFootprints.lean) defines that
interface directly on stable source signatures. The plan-facing
`RequestFootprint` is an abbreviation for the same judgment, so callable types
and actual retained plans share one annotation. The
[source retention results](KERNEL.md#request-interfaces-through-source-substitution)
in [SourceRequestInterfaceRetention.lean](SourceRequestInterfaceRetention.lean)
reuse rich-source substitution, beta reduction and handler decomposition.
Changed literal clause witnesses retain their interfaces at the same signature;
changed handler requirements cannot be hidden by an equal dependency index.
These results do not authenticate every latent operation type or extend the
consuming-declaration grammar.

[SourceScheduledCallbackInterfaces.lean](SourceScheduledCallbackInterfaces.lean)
derives a newly installed disposer's callback checks from original retained
source and finite callback interfaces. Its exported operation list exactly
replaces the individual callback capability checks, including builtin filtering
in dormant branches. Capture routing and ownership remain separate. The
adaptation compiler also preserves an existing disposing request: insertion in
its captured prefix reuses the closing schedule, while insertion in its waiting
suffix compiles callback adaptation. Checked cases include same-effect
replacement of a resumer with a disposer and a rejected capture whose callback
capabilities pass but whose closing route changes. The
[disposal compilation boundary](KERNEL.md#compiling-disposal-from-callback-interfaces)
retains the distinction from general declaration admission.

[SourceScheduledScopedInvocations.lean](SourceScheduledScopedInvocations.lean)
characterizes resume and disposal under arbitrary caller prefixes, including
handlers, resources, cleanup frames and dormant captures. It proves necessary
and sufficient local obligations: independent access, saved-source rechecking
at the new receiving context, caller-prefix checking and waiting-tail checking.
All three pending checks use the consumed owner phase. The existing recipe
compiler now uses these rules for its head invocation cases.

[SourceScheduledScopeExamples.lean](SourceScheduledScopeExamples.lean) checks
local clause plans with a handler, a resource and cleanup surrounding the
invocation. Both resume and disposal pass; the disposal case retains an
effectful callback. Two negative cases show why broader recipes need more than
the old head check: a nearer handler can lack the requested operation, or a
nearer disposing handler can capture running cleanup protection. In both cases,
original pending checks and independent resume access pass while the stronger
resume check rejects the changed context. These are local checker results,
not complete source admission or execution proofs. General declaration
annotations still need to derive the exact receiving-context obligations.

[SourceScheduledRequirements.lean](SourceScheduledRequirements.lean) derives
requirements at positions in the complete plan grammar. Each position retains
its receiving forest and resource world: sequencing exposes its pending suffix,
handler and resource bodies enter their scopes, and cleanup callbacks enter
running protection. Request, continuation-use and handler-installation
requirements have explicit definitions in terms of existing checks.
`Satisfied` means every structurally generated position meets its requirement;
`compile` and `necessary` prove equivalence with the local judgment. The
resource case covers every fresh identity. This is a family of contextual
requirements, not an unqualified list of effect names or a decidable-checker
claim. Handler installation still includes the existing declaration checks.
`Site.owner_cut` derives the same captured segment and waiting tail at every
source position; only the caller prefix changes. The resume and disposal site
lemmas express the exact access and three scheduling obligations for those
original pieces at the site's resource world. Their derivation uses source
traversal alone, without assuming a successful local execution check. The
obligations themselves still need to be discharged by source admission.

The generalized `capture_body_from_requirements` rule in
[SourceScheduledClauses.lean](SourceScheduledClauses.lean) checks the actual
source-selected plan through those requirements. It does not require the
restricted recipe grammar. `capture_entry_from_requirements` in
[SourceScheduledCaptureEntry.lean](SourceScheduledCaptureEntry.lean) connects
that result to payload substitution, the raw capture step and existing exact
ownership accounting. The previous recipe rules are specializations. These
are relative results: source admission must still supply the contextual
requirements at every actual request. Shared source frames now parameterize
declaration evidence while preserving the same source types, actual plans and
local checks. The default remains the older restricted recipe annotation;
`planEvidence` retains typing without claiming execution admission. Structural
erasure, recomposition, capture cuts and transport support either evidence.
The scheduled allocation interfaces now preserve arbitrary declaration evidence
and consume the selected clause's explicit contextual requirements. The typing
projection alone does not discharge those requirements.

[SourceScheduledAllocationData.lean](SourceScheduledAllocationData.lean)
retains the selected body and stronger checks at explicit saved and waiting
forests. Contract refinement and closed payload substitution preserve the same
plan and forests; erasure supplies the earlier allocator certificate.
[SourceScheduledCaptureEntry.lean](SourceScheduledCaptureEntry.lean) connects
the stronger checks to the actual substituted capture step, reusing the exact
owner increment and uniqueness proofs.
[SourceScheduledInterfaces.lean](SourceScheduledInterfaces.lean) aligns clause
selection with typed stack decomposition using both hint and forest uniqueness.
Its requirement premise is tied to the actual declaration evidence, operation
lookup, authenticated cut and selected plan. `capture_requirements_from_recipe`
reuses the established restricted judgment to discharge that premise where
applicable; the earlier capture-entry theorem uses this common bridge.
[SourceScheduledSavedPlans.lean](SourceScheduledSavedPlans.lean) adds an
owner-indexed annotation containing each capture's actual saved forest.
Structural `Matches` checks that annotation at every live boundary, including
inside dormant captures. Capture, resume and disposal recomposition preserve
agreement. This annotation records plan identity; permissions and consumed
phases continue to govern whether the continuation can be used.

[SourceScheduledCaptureData.lean](SourceScheduledCaptureData.lean) retains
those aligned witnesses and their annotation agreement. It rebuilds the live
source under the allocated contract while retaining evidence indexed by the
same saved forest. Capture data and reconstruction preserve the input declaration
evidence; the projection to the earlier recipe-specific certificate remains
available for that default evidence only.
[SourceScheduledClosingData.lean](SourceScheduledClosingData.lean) uses that
index to carry the exact closing template and its equality with the saved
forest's cleanup plans. The shared allocator preserves this certificate at
all source-interface indices, not only its erased scope.

[SourceScheduledClosingRecords.lean](SourceScheduledClosingRecords.lean)
retains that exact template in the disposal store. Under structural annotation
agreement, lookup selects the same saved forest as active-owner selection and
derives the scheduling check for the stored requirement body. Record transport
reuses the existing capture-origin and ownership uniqueness proofs. Its general
non-allocating step lemma still requires the retained layout and store inclusion.
`Records.capture_existing` transports all prior certificates through capture
without requiring a new disposal certificate; the disposing path reuses it.

[SourceScheduledAllocation.lean](SourceScheduledAllocation.lean) calls the
shared allocator once and returns the stronger clause, live source, annotation
agreement and exact disposal records alongside the existing ownership and row
results. The earlier scope-only annotation bound now follows from structural
agreement. Allocation now accepts arbitrary declaration evidence with explicit
contextual checks; it does not derive those checks from general source admission.
Its clause-bound result requires the closing-budget check only when the selected
offer permits disposal. `ClauseRowAdmission.Interface.of_resume` supplies a
resume-only interface without using closing metadata, and the existing row
proofs then give the clause bound even for a closable capture. A checked
regression retains an actual closing row outside the advertised budget while
admitting the same resume interface with disposal forbidden.
Deriving the contextual checks, integrating these components into every runtime transition and
deriving closing readiness and budgets remain open. Complete preservation and
progress are not yet proved.

`allocate_without_closing` covers captures with no executable cleanup plan or
with pending uses outside their owned continuation set. The checked request
then rules out a disposal-enabled offer, and source clause-mode checking rules
out disposal by the selected clause. The theorem inserts only a resume record,
sets the unused closing row to `none`, and retains the typed live segment,
actual saved forest, prior disposal store and exact ownership increment. Existing
row-instantiation proofs derive the substituted clause's bound without a closing
budget. This includes protected captures. It still requires the general clause's
contextual site checks and is not complete initial-source progress.

[SourceScheduledState.lean](SourceScheduledState.lean) now joins these results
in one state indexed by the actual retained forest. Current expression typing,
its source plan, pending source, saved-plan map, closing records, owner uniqueness
and combined effect checking share the same runtime stack. Initial construction
and erasure to `DeclaredConnectedSources.State` are proved. Bind and beta
reduction reuse the existing substitution and evaluation lemmas while retaining
the exact body plan and saved forest.

`capture_preserves` covers both allocation branches in this same state with an
empty outward guard. It derives the selected row and payload closure from source,
classifies the actual closing plan and internal owner uses, and constructs the
successor. Existing clause-consumption and ownership lemmas prove that its demand
is a permutation of the fresh owner followed by the previous demand; its combined
effect row is contained in the previous row. The saved-plan map and exact closing
certificates refer to the actual captured forest. A closable resume-only capture
needs no closing budget. Disposal-enabled capture derives its budget from the
existing source-support proof.

This theorem still takes a physical cut, selected clause and table lookup,
a value operand, fresh contract/action/annotation names, captured resource
support, and the selected clause's contextual site requirements. It does not
assume a successor state. Deriving those remaining premises throughout execution,
integrating the other transitions and proving initial-source progress remain
open. The older runtime results do not automatically preserve this stronger
scheduled state.

[SourcePlannedFocus.lean](SourcePlannedFocus.lean) connects that transport to
every source `Focus` rule. Signature decomposition selects the child and
continuation plans from the original check. The actual focus step retains the
strong child source, typed context, local and pending checks, matching runtime
annotations and unchanged owner trace.

[SourceScheduledFocus.lean](SourceScheduledFocus.lean) now integrates every
focus rule into the shared scheduled state. It retains the actual context plan,
pushes that plan into the forest, transports the same disposal certificates,
and reuses source decomposition, frame preparation and effect-row reassociation.
No new child-source or local-check premise is needed.

[SourceScheduledValues.lean](SourceScheduledValues.lean) reconnects returned
values with their retained contexts and proves preservation for every actual
returned-value step that retires no continuation ticket. This includes leaving
handlers, resources and spent clause boundaries, starting cleanup, and finishing
cleanup or closing frames. Context recomposition retains the exact source plan;
cleanup starts the actual retained callback under its running-protection marker.
The same saved-plan map and closing templates remain attached to their captures.
The source demand, effect row and owned-ticket phase map are preserved.

[SourceScheduledPhaseRestriction.lean](SourceScheduledPhaseRestriction.lean)
proves that local and typed pending checks depend only on availability of live
owners in the actual retained forest and receiving suffix. This includes
recursively saved captures and the schedules restored by invocation. Ordinary
frames introduce no live owner, and closing and recomposition retain only
owners already present. This supplies phase restriction without requiring
availability of an owner that has been retired.

[SourceScheduledRetirement.lean](SourceScheduledRetirement.lean) uses that
result to finish ticket retirement. Existing ownership realization proves
that every retained live owner remains available. Existing demand, effect-row
and consumption-trace lemmas then construct the complete successor with the
same source plans and closing certificates. `value_step_preserves` covers all
eight returned-value transitions, including resource completion and ticket
retirement, and removes exactly the consumed tickets from demand. No successor
check is a premise. General source admission, the other transition connections,
and full runtime preservation and initial-source progress remain open.

[SourceScheduledRechecking.lean](SourceScheduledRechecking.lean) connects a
structural pending check under a new receiving suffix to the same typed source
plans. It retains every requirement and record, including dormant captures.
[SourceScheduledSplitting.lean](SourceScheduledSplitting.lean) splits an actual
runtime stack while retaining the exact forests and requirement evaluation on
both sides; it is the converse of the existing checked append construction.

[SourceScheduledResumption.lean](SourceScheduledResumption.lean) uses these
connections to preserve the full scheduled state for ready resumption under an
arbitrary caller prefix. The existing invocation rule supplies the saved,
caller and tail checks at the consumed phase. Ownership uniqueness selects the
same boundary in the runtime stack and plan forest. The proof derives resume
permission, retains exact saved-plan agreement and closing certificates, and
reuses record removal, effect evaluation and phase accounting. The effect row
is unchanged and demand loses exactly the selected owner. It assumes neither a
successor source check nor a separate resume permission. The remaining execution transitions and initial-source admission still require
integration. Disposal now has the conditional source-state connection below.

[SourceScheduledClosingRecomposition.lean](SourceScheduledClosingRecomposition.lean)
materializes the exact stored closing template as a scheduled typed segment.
Its callback plans and requirement body are retained; the disposal schedule
supplies the checks at the new receiving suffix. Recomposition uses the existing
segment append and its evaluation equation.

[SourceScheduledDisposal.lean](SourceScheduledDisposal.lean) connects that
materialization to ready disposal in the shared state. The selected record
supplies the exact template, while the current invocation supplies the closing
and caller schedules. The proof retains caller plans and remaining certificates,
checks the effect row against the reduced record store, and preserves ownership
while scheduling retirement of captured owners. Its explicit premise is that
the actual closing plan is typed against the selected contract's closing-effect
interface. The scheduled runtime now derives it from its retained disposal
certificate and registry coherence, as described below.
Neither a replacement template nor a successor scheduling check is assumed.

[SourceScheduledEntries.lean](SourceScheduledEntries.lean) preserves the full
scheduled state for branch selection and cleanup installation. Branching keeps
the selected plan and may shrink the effect row. Cleanup retains the actual
callback source and plan, with its protected execution check.

[SourceScheduledRegistries.lean](SourceScheduledRegistries.lean) transports
existing source frames and segments when clause tables, dependency families
and declaration requirements agree at retained activations. This includes
handlers inside dormant captures. Closing templates and their exact saved-plan
certificates survive table registration through the existing closing-context
independence theorem.

[SourceScheduledHandlers.lean](SourceScheduledHandlers.lean) proves handler
installation for the full scheduled source state with structural recipe
evidence. The local handler rule now retains
`SourcePlannedRecipeDeclarations.Declarations` for its actual clause plans;
[SourcePlannedRecipeCongruence.lean](SourcePlannedRecipeCongruence.lean)
transfers these recipes through their stable signatures to the clause witness
authenticated by source typing. This transport no longer depends on the
restricted grammar uniquely determining the entire plan. Regression proofs
exhibit different scoped plans with equal signatures, reject changed provider
requirements, and retain a recipe after clause substitution.
Fresh activation registration reuses the existing requirement-relocation proof.
The successor retains the body plan, ownership, effect row and disposal
certificates without a successor-check premise. Resource installation and cell
reads/writes, complete runtime integration and retained-state progress are
connected below. Complete source admission remains open: the consuming recipe
grammar still needs extension for general scope-bearing clause declarations.

[SourceScheduledWorld.lean](SourceScheduledWorld.lean) preserves exact source
plans and disposal certificates when the resource world grows. The existing
scheduling transport now includes world extension; earlier entry points are
specializations of that proof.
[SourceScheduledResources.lean](SourceScheduledResources.lean) uses these
transports and the established finite freshness proof to preserve the full
scheduled source state on resource installation, including the actual body
plan, hidden resource requirements and unchanged ownership demand.

[SourceScheduledCells.lean](SourceScheduledCells.lean) preserves the same
retained forest through cell reads and writes. The payload update reuses
interpretation and ownership equations. The reply retains disposal certificates
using the raw-step capture-origin theorem, and its checked effect row is a
sublist of the request's row. This completes the previously outstanding ordinary
transition families at the scheduled source layer.

[SourceScheduledExecution.lean](SourceScheduledExecution.lean) joins that source
with the existing runtime access, ledger, name history, completion and usage
invariants. Initial assembly takes explicit source, scheduling and completion
judgments plus declaration-signature agreement. Its `checkInitial` computes
requirement evaluation, closed-row acceptance and resource support together;
`checkInitial_iff_previous` proves equivalence to those former separate checks.
A checked example retains the resource-support test: source typing, scheduling
and completion can admit an unused handler whose effect identity contains an
unissued resource. The combined check rejects it. Runtime disposal preservation derives its actual
`PlanTyped` interface from the retained certificate and registry coherence;
disposal progress reuses the established access-checked step and keeps the
stronger scheduled successor. The remaining runtime cases and exhaustive
progress are connected below. Complete source admission is not established by
this disposal join.

[SourceScheduledRuntimeControl.lean](SourceScheduledRuntimeControl.lean) joins
focus, all returned-value transitions and resumption to the scheduled runtime.
Progress derives the live owner boundary from current usage. The proofs reuse
the actual source successors and existing runtime completion results, retaining
exact ownership accounting and the effect row.
[SourceScheduledRuntimeComputation.lean](SourceScheduledRuntimeComputation.lean)
connects bind, beta and branch reduction, retaining the same forest and a checked
row contained in the original row.

[SourceScheduledRuntimeEntries.lean](SourceScheduledRuntimeEntries.lean)
connects resource, handler and cleanup installation with existing name freshness
and completion proofs. Handler entry registers all three source metadata maps
at the same activation.
[SourceScheduledRuntimeCells.lean](SourceScheduledRuntimeCells.lean) connects
builtin replies and exact request selection: a ready request either makes a
builtin step preserving the strong runtime, or selects a physical handler cut.
It also derives builtin operation validity from retained source typing and uses
it to check a primitive request under a covering caller handler.
The capture connection is described below.

[SourceScheduledRecipeCapture.lean](SourceScheduledRecipeCapture.lean) derives
the existing capture-site clause obligations from structural recipes and the
actual retained source. `Pending.handler` and `Frame.handler` now retain the
finite provider-requirement check at the receiving suffix. `Pending.compatible`
projects the established structural compatibility judgment, including handlers
inside dormant captures. Installation, splitting, recomposition, rechecking and
phase/world transports preserve this evidence. The source capture theorem no
longer takes a separate `Compatible` or clause-obligation premise.
This applies to the existing consuming-recipe grammar; general handler and
effectful-cleanup clause rules remain open.
[SourceScheduledCompatibilityGap.lean](SourceScheduledCompatibilityGap.lean)
now rejects the former missing-provider example. It also accepts a dormant
handler whose waiting suffix supplies the required provider, and rejects
recomposition under a caller that masks that provider with an incomplete
handler. General handler and effectful-cleanup clause admission remain open.

[SourceScheduledRuntimeCapture.lean](SourceScheduledRuntimeCapture.lean)
connects every one-shot capture mode to the retained runtime invariant. The
existing ledger supplies name freshness and resource support. The actual
selected clause supplies disposal permission and its source request supplies
the closing certificate. The source capture result also exposes its operation
input type, so the existing coherent-record constructor allocates the same
contract. The successor retains its actual saved forest, satisfies the updated
registry, adds exactly one owner to the demand multiset, and has an effect row
contained in the previous row.

[SourceScheduledProgress.lean](SourceScheduledProgress.lean) proves exhaustive
`Run.progress`: a state carrying the retained structural source/runtime invariant
either is an ordinary terminal or takes an actual machine step to another state
carrying that invariant. It reuses typed-expression classification and every
transition connection, with no unresolved capture case.
[SourceScheduledFiniteRuns.lean](SourceScheduledFiniteRuns.lean) reuses the
existing counted-step relation and finite-prefix induction. For any requested
length it constructs an actual prefix ending in the same invariant, with either
that length or an earlier terminal. At a terminal, issued and discharged owners
are permutations and no owner is discharged twice. `initial_finite_prefix`
starts from five explicit inputs: source typing, local plan checking,
`checkInitial = true`, a completion derivation and signature agreement. The
initial theorem derives an empty demand and residual row. The executable check
does not authenticate the source annotation or replace the other judgments.

[Finite coverage of an intercepted operation interface](KERNEL.md#finite-coverage-of-an-intercepted-operation-interface)
checks a replacement handler against the nearest provider's declared operation
keys, including both typed cell operations. It derives the existing request
capability in ordinary and protected modes and feeds the scheduled request
checker under arbitrary passing caller prefixes. This supports same-effect
interception; it does not yet discharge whole-clause or callback obligations.

[Source-derived entry annotation guards](KERNEL.md#source-derived-entry-annotation-guards)
now separate annotation selection from supplied-choice preservation for focus,
resource, handler and cleanup entry. The source determines the ports, metadata
and any forbidden names; every supplied name/type satisfying the finite guards
preserves the joined runtime. The existing progress theorems reuse these
results. This does not yet connect annotation provenance across a whole trace
or extend the event relation below.

[SourceScheduledRetainedRuns.lean](SourceScheduledRetainedRuns.lean) reuses
`CallableRuns.StableEvent` for value transitions, bind/application/branch steps,
builtin reads/writes and resumption, and adds access-checked disposal.
`retained_step_preserves` derives the successor invariant for every supplied
event of these forms. `retained_run_preserves` uses the standard transitive
closure induction to cover every nonempty finite sequence of these events,
with no intermediate-validity premises. The effect row can only shrink.
Focusing, resource/handler/cleanup installation and capture remain outside this
event interface; their source annotations still need authentication.

These results establish progress and finite execution existence for the current
structural admission boundary. They do not prove preservation of every arbitrary
trace with unchecked machine annotations. General scope-bearing consuming
recipes, complete source admission and the final checked-execution interface
remain outstanding; Core correspondence remains a status assessment.

## Verification

The proof files use pinned Lean and its bundled standard library. There are no
third-party proof dependencies. Run from this directory:

```sh
bash check.sh
```

The current inventory verifies 387 modules and 6,293 exact theorem-dependency
reports with Lean 4.33.1. Twenty-two targeted capture-identity, callback and
non-disposing capture reports extended the
preceding 207-module batched integration. The capture-budget group adds eight
further reports, checks 17 affected modules, and reuses 194 unaffected module
results. Seventeen targeted resource-return and binding-support reports extend that group.
Eighteen structural completion-contract connections and four strengthened source
entry points extend it further. The input-interface group checked thirteen
modules and reused two hundred unchanged results. The subsequent disposal
connection checked two affected modules and reused 211 unchanged results. The
initial-state connection checked one module and reused 212 unchanged results.
The combined execution connection adds four reports and one generalized payload
proof; its grouped check covers 105 affected modules and reuses 109 unchanged
results. Ten further completion and entry reports check only the changed leaf
and reuse 213 unchanged results. Five builtin and request-selection reports
extend that leaf with the same reuse boundary. Four retained-disposal reports
extend it further without a new induction. Five disposal-interface reports
expose the actual checked source plan, derive its current footprint check and
physical request resolution, and reuse the existing pure-callback regression to
distinguish source footprint admission from structural closing compatibility.
These connections add no induction; their grouped verification checks three
affected modules and reuses 211 unchanged results.
The [current-state disposal admission gap](KERNEL.md#current-state-disposal-admission-gap)
adds twelve reports proving that the current combined invariant alone does not
guarantee access-checked progress. Three further execution reports connect the
existing scoped declared-request judgment to disposal with a retained
structural certificate. This group checks two modules and reuses 213 unchanged
results; it adds no induction. Establishing and preserving those additional
judgments from source admission remains open.
The [retained structural closing invariant](KERNEL.md#retained-structural-closing-invariant)
now has thirteen reports: it retains declared-request typing and concrete closing
certificates, constructs the initial state, and preserves the stronger state
through disposal, resumption and all returned-value transitions. Existing
capture provenance supplies certificate transport across all raw transitions.
Seven [action-usage reports](ScopedActionUsage.lean) and one generalized capture
report distinguish checked actions from granted runtime permissions. A selected
clause receives its least action bound; every raw transition with the existing
usage checks preserves the independent usage registry. Certificate obligations follow that bound. A
resume-only clause needs no new closing certificate even under a policy that
grants disposal, while nested clauses keep their independent policy checks.
These connections add no induction. Twenty-nine further
[action-interface reports](ScopedActionInterfaces.lean) replace unconditional
resume/closing interface requirements with structural obligations guarded by
those actions. A source declaration and local resumption regression demonstrate
why the old unconditional judgment was too restrictive. The main `Prepared`
invariant now uses the replacement, retaining its initial, disposal, resumption
and returned-value proofs and rejection of the disposal counterexample. The new
relation needs structural transport inductions; expression, frame, port, value
and plan lemmas are reused. This group checks the new module and its closing
integration, reusing 216 unchanged modules. Complete source capture admission
still needs closing certificates for disposing clauses and the declared
interfaces required by the selected actions.
The [deterministic interface-progress connection](KERNEL.md#deterministic-computation-and-entry-annotations)
adds eighteen reports. Ready bind, beta reduction, branches and builtin cell
read/write now construct actual steps preserving the full `Prepared` invariant.
Request selection retains this preservation in its builtin branch and exposes
the nearest handler cut in the other branch. Exact handler-cut
decomposition exposes the captured and surviving interfaces for capture work.
A cleanup-entry regression proves that raw metadata selection can invalidate
interface typing, while a compatible annotation preserves it for the same code.
The entry proofs must therefore choose annotations consistently; the example
does not refute existential progress. This group checks one new module and
reuses 218 unchanged modules.
The [current-form and capture-retention connection](KERNEL.md#current-form-classification-and-source-capture-retention)
adds eight reports across two modules. General resumption now derives its owner
and live boundary from current usage. Exhaustive classification returns a
terminal state, a step preserving `Prepared`, or one of the three remaining
entry/capture forms. This is not full progress. At a non-disposing source
capture, the selected declaration now supplies the fresh action guard, and the
actual capture preserves independent usage, history and all retained closing
certificates. The source/runtime theorem now produces the same access-checked
successor and coherent record as that retention proof. Exact selected-handler
uniqueness needs one four-case cut induction; the existing clause-mode,
ownership and provenance proofs are reused. Capture's effect-interface connection
and disposing source admission remain open.
Six [installation-progress reports](DeclaredInstallationProgress.lean) now
connect source-chosen resource and handler entries to full `Prepared`
preservation. Stack annotations determine the same result port in both proofs.
Existing resource opening and handler typing supply the connected interfaces;
no new induction or annotation restriction is needed. Classification allows
the actual handler-table update and leaves focus, cleanup entry and capture as
the three unresolved transition kinds.
Ten [shared source-interface reports](DeclaredSourceInterfaces.lean) now give
focus and cleanup entry a common annotation witness. The structural `State`
rule uses the actual current source derivation's allowed effect list as the
connected caller interface. It projects to existing source and effect judgments;
the original initial-source premises establish it without another admission
condition. Focus and cleanup construct a successor retaining this shared
witness, reusing existing decomposition and evaluation proofs without induction.
The cleanup decomposition now exposes its existing request-subset premise.
The `Run` invariant retains this witness alongside the runtime and independent
action evidence; it projects to `Prepared` and follows from the same initial
premises. Focus and cleanup now construct access-checked steps preserving `Run`,
including freshness, result contracts and closing certificates. Five
[shared computation reports](DeclaredSharedComputation.lean) retain it through
ready bind, beta reduction and branch selection. Existing substitution and
runtime proofs describe the same successor. Seven
[shared value reports](DeclaredSharedValues.lean) now recover the common source
witness whenever the current expression is a value. Existing progress proofs
therefore preserve `Run` through resumption, disposal, builtin reads and writes,
and returned-value steps whose successor is also a value. Disposal still uses
the retained certificate; capture must establish it. Two
[shared cleanup reports](DeclaredSharedCleanup.lean) now preserve `Run` at
callback start. The callback's own request annotation supplies the new current
source bound, and the existing value-transition proof supplies the same running
frame's interface. Context plugging remains the unresolved returned-value case.
These additions use no new induction.
Four [shared resource](DeclaredSharedResources.lean) and
[shared handler](DeclaredSharedHandlers.lean) reports now preserve `Run` through
both installation forms. Resource decomposition exposes its existing bound by
the fresh cell plus the current allowed row. Handler installation retains the
same residual bound in the body, declarations and frame. Each proof chooses
one fresh identity and uses it for the source and runtime successor. Existing
result, ownership, table-relocation and finite-check proofs are reused. The
shared witness still needs preservation through context plugging and capture;
disposing capture must also establish its closing certificate.
Preservation through the remaining transitions stays open; the general
`Prepared` classification is unchanged because its premises do not include the
shared witness.
The [structural stored-segment judgment](DeclaredConnectedSources.lean) now
strengthens that witness: each plain context shares its source allowed row with
its caller, and each handler shares one residual row across declarations and
effect typing. Its source and effect projections preserve the existing
judgments. Initial source establishes it, focus stores it, and plugging retains
it by reusing the existing context-plug and value-transport lemmas. Two structural
projection inductions account for arbitrary nesting; no new substitution or
execution induction is introduced. The [runtime connection](DeclaredConnectedExecution.lean)
establishes the stronger `Run` initially and preserves it through actual focus
and plug steps. Together these add twelve reports. Other transitions must still
retain this stronger segment evidence; the earlier `Run` preservation theorems
do not supply that converse automatically. Thirty further reports now retain the
stronger segment through [environment changes](DeclaredConnectedTransport.lean),
[ready computation](DeclaredConnectedComputation.lean),
[resource installation](DeclaredConnectedResources.lean),
[handler installation](DeclaredConnectedHandlers.lean),
[all returned-value transitions](DeclaredConnectedValues.lean) and
[cleanup installation](DeclaredConnectedCleanup.lean). One structural transport
induction covers resource-world, contract, action and table changes; the
transition proofs reuse the existing substitution, evaluation, completion,
ownership and runtime components. Fourteen further reports cover
[structural recomposition](DeclaredConnectedRecomposition.lean),
[resumption](DeclaredConnectedResumption.lean) and
[builtin cells](DeclaredConnectedCells.lean). Resumption retains the saved
derivation selected by the independent resume capability and consumes exactly
one owner. Cell updates retain the same stored annotations and yield a sublist
of the original requirement row. Both preserve the combined runtime invariant;
request selection either constructs such a builtin step or identifies the
actual handler cut. The experimental source offer rule now requires each used
continuation effect bound to equal the declaring handler's residual row. Its
unused bounds remain independent, with source examples for both resume-only and
dispose-only clauses. Existing declaration transport and substitution preserve
the equations. [Capture decomposition](DeclaredConnectedCaptureSplit.lean)
retains the actual shared residual on the captured segment and caller, then
derives the selected clause's compatible interfaces. The
[allocation connection](DeclaredConnectedAllocation.lean) constructs the live
boundary with those same source indices and chosen contract. It does not yet
join the complete source state, stores and runtime transition. Disposal
preservation and source admission of disposing captures also remain open.
Completing the one-shot proof system takes priority over Core correspondence;
the interface equations change the proposed source judgments, with no change
to normative Ash or current Core.
Five [closing-route separation reports](DeclaredClosingRouteGap.lean) strengthen
the existing source regression: the same current source annotation has a
connected normal interface, and the complete callback row types its closing
plan, but no outward row supplies an open closing certificate. The plan removes
the callback's selected local handler. This rules out repairing the fixed
capture merely by widening its closing row. The callback is pure with a
conservative annotation; the result neither establishes initial reachability
nor rules out choosing a different annotation at source entry. The selected
clause only resumes, so its capture remains valid.
Registry-extension preservation strengthens the existing
finite-run induction; verification rebuilt the 178 dependent modules and reused
the checks for 29 unaffected modules. All printed dependencies use only standard
Lean axioms. The preceding clean full integration
checked 205 modules and 4,697 reports.

The source-usage group includes local restart after actual resumption through
an arbitrary finite access-checked caller run. It reuses full resumption
preservation and value-scope transport. [Saved capture identity](KERNEL.md#saved-capture-identity-through-caller-execution)
now derives preservation of the prefix from its original ticket and allocation
history. Source admission of that run remains open.

[Hereditary callback admission](KERNEL.md#hereditary-callbacks-at-their-closing-positions)
connects the actual plan-footprint check to callback bodies and their checked
requirements at protected closing positions. Deriving these checks from
initial source and preserving them through the full execution remains open.

[Non-disposing capture](KERNEL.md#capture-without-disposal-admission) now
preserves a checked request state even when a raw closing plan exists but its
admission fails. It reuses allocation and clause certificates without a new
induction. Disposal-enabled capture admission and the combined initial-source
theorem remain open.

[Actual capture-budget checking](KERNEL.md#checking-the-actual-capture-budget)
now connects the source cut's resumption row to allocation. Successful finite
checking supplies a disposal-enabled capture successor without a separate
post-allocation budget premise. The two existing proof entry points were
refactored, and their affected dependents checked as one group. Initial-source
admission of successful checks remains open.

[Resource-return admission](KERNEL.md#hereditary-source-and-resource-return-admission)
now connects the existing finite template-support check to hereditary source
entry, and the preserved return invariant to actual release. An existing
retaining-outer closure completes acquisition and release with source evidence;
a retaining-own-resource template demonstrates why source typing alone cannot
supply the release check. A finite check on actual bound values now preserves
template support through hereditary source substitution and actual strict bind.
The alias example completes bind, acquisition and release using those results.
Source-wide entry and binding admission remain open.

[Structural completion contracts](KERNEL.md#hereditary-source-with-structural-completion-contracts)
now preserve full higher-order result evidence alongside hereditary source at
bind, beta, resource entry and release. A function returned through application
passes this structural check although finite template inference is unknown.
Resumption and disposal also retain both judgments and exact owner consumption.
Actual capture now preserves the structural result contract at the same source
successor and fresh owner, retaining the operation's input-bound evidence.
Both capture paths now insert source and result contracts into the existing
shared runtime registry with port agreement and actual clause permissions.
The disposing path retains the successful structural plan and combined-budget
checks. One shared construction reuses existing capture, cleanup/disposal,
recomposition and registry-extension proofs. Source-wide admission of these
checks and preservation of the full execution invariant remain open. The initial
empty machine now has both checked hereditary source and all existing runtime
invariant fields derived from structural source/result checks and a finite
free-resource check. This does not establish all-run progress.

The earlier batched integration covered 199 modules and 4,629 exact
theorem-dependency reports with Lean 4.33.1. It combines the successful prefix
of the integration run with a checked dependency group and the corrected final
regression module. The affected group covers 22 modules and 240 reports.
Its preceding clean single full run covered 196 modules and 4,581 reports.

Verification includes hereditary source transport and substitution, indexed
saved frames, ordinary execution and value completion, handler/resource/cleanup
installation, cell operations, resumption, disposal and both conditional capture
paths. Clause-row certificates remain attached to nested declarations and are
used by capture. The false empty advertisement is rejected for every source
derivation of its example clause.

The [closing-budget counterexample and correction](KERNEL.md#closing-and-resumption-budgets-can-differ)
show why disposal cannot generally be bounded by the resumption row alone.
The clause interface instead checks the combined exported advertisement and
resumption budget. Its regression reuses the existing disposal schema and
keeps capability permission independent. The full run reached the new regression;
a targeted repair corrected its proof tactics and checked the remaining module.
No second full run was needed for that local repair.

There are no `sorry`, `admit`, custom axioms or unchecked native decision
procedures. Printed dependencies are limited to Lean's standard `propext`,
`Quot.sound`, and `Classical.choice`, or none for some theorems. The exact report
inventory, local links, trust boundary, whitespace and artifact scans pass.

The [remaining admission obligations](KERNEL.md#remaining-proof-construction)
concern source-derived closing-cut compatibility and the combined closing budget,
then the combined initial-source progress and preservation theorem. The checked
counterexample and interface correction do not discharge these obligations.

A subsequent targeted check verifies the seven request-capture theorems in
`DeclaredSourceRequests.lean`. It reuses the established request, capture and
ownership proofs and brings the inventory to 200 modules and 4,636 reports.
The addition changes no existing proof module and has targeted verification only.

The subsequent outside-owner module passes 14 exact reports, bringing the
inventory to 201 modules and 4,650 reports. It has targeted verification only;
no existing proof module changed.

The [ordered owner-use summaries](KERNEL.md#ordered-owner-use-summaries) add
11 targeted reports, bringing the inventory to 202 modules and 4,661 reports.
They reuse the existing interpretation, capture and source-focus proofs.
The summary describes the exact captured owner region; source-derived guarantees
through calls and future captures remain open.

The [source grouping refinement](KERNEL.md#source-grouping-is-lost-by-flattening)
adds 17 targeted reports, bringing the inventory to 203 modules and 4,678 reports.
It retains source scopes at the existing requirement index and reuses the old
evaluator and phase proof. A checked counterexample shows that identical
flattened requirements can require different capture-owner decisions. Source
grouping, runtime cuts and their owner checks agree in that example; the general
initial-source safety theorem remains open.

A subsequent group checks retained clause tables and callable-body grouping:
`OwnerOfferContexts`, the updated `ScopedRequirementShapes`, and
`CallableSourceShapes`. Its 36 reports pass, bringing the inventory to
205 modules and 4,697 reports. Callable-body conversion and closed substitution
reuse the existing proofs. Source sites now select the capability from their
own ordered clause tables. The group does not establish preservation of all
future owner and closing checks or the initial-source safety theorem.

The [caller-owner composition result](KERNEL.md#locally-closed-prefixes-and-caller-owner-checks)
reuses the existing usage bounds, unique ownership and capture checker. At an
outward request, a prefix whose usage has no outside owners leaves the caller's
selected owner check unchanged. Its targeted addition follows the clean full
205-module run. Deriving and preserving that local usage interface throughout
function execution remains an initial-source obligation.

The [source-owner closure projection](KERNEL.md#source-entry-and-local-owner-closure)
now derives initial usage from the existing source judgment. Its five reports
also connect the existing checked finite-run invariant to the caller-owner
composition theorem. The run still supplies explicit access checks; their
source admission and transfers through an outside caller remain open.

Related edits are checked in groups, with the full suite run at integration
checkpoints. The script builds imported modules in a temporary directory removed
on exit. The foundational assumptions and proof checker are part of the trust
boundary. A compiling file proves only its stated lemmas; it does not establish
unfinished entries in the construction above.

The callable-support comparison also has executable Core fixtures. From the
repository root, the first command returns `() : Unit`; the second exits with
`type.resource-escape`:

```sh
cargo run --quiet -- docs/design/direct-effects/one-shot/fixtures/callable-payload-inside-owner.ash
cargo run --quiet -- docs/design/direct-effects/one-shot/fixtures/callable-payload-outside-owner.ash
```

The [copied-integer handler fixture](fixtures/copied-integer-handler-result.ash)
returns `42 : Int`. A generic integer-producing operation captures a resource
scope, resumes with a copy, and the resulting closure is called after the
resource closes. This checks a concrete Core result, not a formal translation
or event-by-event correspondence:

```sh
cargo run --quiet -- docs/design/direct-effects/one-shot/fixtures/copied-integer-handler-result.ash
```

The [builtin-read fixture](fixtures/copied-integer-cell-result.ash) returns
`41 : Int` after calling a closure that retains the copied integer outside
its resource scope:

```sh
cargo run --quiet -- docs/design/direct-effects/one-shot/fixtures/copied-integer-cell-result.ash
```

The [nested-resource closure fixture](fixtures/nested-resource-closure-result.ash)
returns `17 : Int`. Both scopes use the same resource binder name; the returned
closure retains neither acquisition. The Lean example checks both resource
entries and returns, then checks application of the returned closure separately.
This comparison does not establish a formal Core translation.

```sh
cargo run --quiet -- docs/design/direct-effects/one-shot/fixtures/nested-resource-closure-result.ash
```

The [ordinary-bind fixture](fixtures/nested-resource-bind-result.ash) also
returns `17 : Int`. An enclosing bind waits while an inner bind and both resource
scopes execute. The Lean example checks the eight steps through the returned
closure with saved analysis environments and result certificates; the Core run
is concrete comparison evidence.

```sh
cargo run --quiet -- docs/design/direct-effects/one-shot/fixtures/nested-resource-bind-result.ash
```

The [nested-clause fixture](fixtures/nested-handler-clause-result.ash) returns
`17 : Int`. An outer clause resumes with `42`, continues through a bind and
installs an inner handler whose clause resumes with `17`. Lean checks a
thirteen-step execution to the same result and its ticket ledger. This does
not establish a formal Core translation or full admitted execution.

```sh
cargo run --quiet -- docs/design/direct-effects/one-shot/fixtures/nested-handler-clause-result.ash
```

## Semantic comparison obligations

- [Exact capture and deep restoration](../../../../spec/dynamic-semantics.md#effect-handlers-and-completion).
- [Resource access and owned capture](../../../../spec/dynamic-semantics.md#scoped-cell-execution).
- [Cleanup and protected running completion](../../../../spec/dynamic-semantics.md#scoped-cleanup-actions).
- [Outside pending resume rejection](../../../../tests/resource_scope_typing.rs).
- [Function barriers for structural resume capabilities](../../../../spec/static-semantics.md#effects).
- [Removed nearest interpreter cannot fall back](../../../../tests/cleanup_interactions.rs).

An ownership multiset alone is insufficient: it can conserve a captured
resource while abandoning the only pending resume of its outside owner. The
pending-use and close judgments must rule out that counterexample explicitly.

The [joint-record handler fixture](fixtures/single-handler-joint-result.ash)
returns `17 : Int`, matching the endpoint of the five-step execution with a
combined invariant at each state:

```sh
cargo run --quiet -- docs/design/direct-effects/one-shot/fixtures/single-handler-joint-result.ash
```

This remains concrete comparison evidence, not a Core correspondence theorem.

The [outer-handle payload fixture](fixtures/outer-handle-capture-payload.ash)
returns `17 : Int`. An exact handler inside the outer cell passes that cell's
handle while capturing an inner cell scope:

```sh
cargo run --quiet -- docs/design/direct-effects/one-shot/fixtures/outer-handle-capture-payload.ash
```

The Lean boundary execution checks capture, resume and both normal releases;
its starting state already owns both cells. The fixture also executes acquisition,
which is not yet connected by a formal translation.
