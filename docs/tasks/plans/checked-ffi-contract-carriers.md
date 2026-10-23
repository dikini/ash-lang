# Checked FFI Contract Carriers Implementation Plan

Owned by [TASK-0051](../TASK-0051-checked-ffi-contract-carriers.md).
Authority is accepted [CP-0024](../../proposals/CP-0024-checked-foreign-host-profile.md).
This plan implements its obligations; it cannot invent source or Core authority.

Goal: preserve checked foreign contracts through source, summaries, linking,
Core and image reconstruction without a legacy execution bypass.

Architecture: extend the existing original foreign contracts and their checked
phase projections. Explicit H selects one original Type formal; assumption and
owner facts retain their original module route and complete Type/Row context.
The runtime and Linux executor remain separate delivery boundaries.

Tech stack: Rust compiler/evaluator, existing contextual parser, canonical typed
Core, Cargo integration tests and existing private-image validation.

## Slice 1: Retain checked declaration intent and refuse incomplete admission

Files: `src/parser/foreign_grammar.rs`, `src/parser/foreign_project.rs`,
`src/surface/foreign.rs`, `src/foreign/source_contract.rs`,
`tests/foreign_source_syntax.rs`, `tests/foreign_source_contracts.rs`,
`spec/syntax.md` and `spec/static-semantics.md`.

1. Add a syntax test for public/private `foreign checked library` alongside legacy
   declarations. Run the new test and observe the missing syntax failure.
2. Add a preparation rejection test showing the checked marker cannot enter the
   legacy ABI route, even for otherwise valid scalar declarations. Observe its
   failure before the implementation permits parsing.
3. Add the explicit marker to the surface library, contextual recognition,
   concrete-shape validation and projection. Preserve exact source spans and
   reject malformed contextual prefixes.
4. Refuse the unsupported checked route at source-contract preparation with an
   existing appropriate contract error and original declaration span. No native
   startup, bridge or independent-result permission can arise.
5. Run the new tests, all three affected suites, formatting and targeted lint/doc
   checks. Document only this implemented subset and explicit refusal.
6. Obtain exact-head independent review, repair findings, retain with an unsigned
   commit, and update TASK-0051 acceptance only for this subset.

## Slice 2: Carry checked declarations and original assumptions

Extend `src/surface/foreign.rs`, foreign grammar/projection, resolution and
`src/foreign/source_contract.rs` / `checked_source.rs` together. Tests cover
original assumption names, duplicates, unknown references, exact selected H,
non-Type or missing H, and same-kind donor substitution. Use existing original
module/ordinal identities rather than matching names. Keep automatic inherent
assumption floors and authored references distinct. Preserve complete ordered
Type/Row arguments and charge construction/checking. Unsupported paths refuse.

## Slice 3: Introduce host scopes and checked effects

Add the accepted host expression through surface, resolved, elaborated and
Effect Core forms using existing scope/identity infrastructure. Test a closed
checked scalar call, residual legacy/ordinary rows, nested distinct H, host escape,
ordinary-handler attempts to eliminate H and wrong-host owner use. Interpret only
admitted exact owner-free native instances at the host boundary; owner operations
remain under the actual resource lifecycle. Core reconstructs these rules.

### Next connected scalar-host checkpoint

Start from unsigned retained `f7f13071851a4abfdd344f0bb5a1d5b99a2fbb1f` on
`codex/checked-ffi-f3-hosts`. PR #84 supplied passive original metadata only.
The next checkpoint connects static authority for scalar calls; it does not
admit owners, checked lifecycle completion or a native launch.

1. Append the canonical checked report/call nominal inventory to the immutable
   builtin Foreign module, preserving every existing nominal, constructor and
   global ordinal. Authenticate `CheckedCall` and its entire referenced boundary
   codec by defining module/role, original declarations, ordered Type formals and
   constructor payloads; a same-shaped user codec cannot substitute. Introduce
   the canonical `NativeHost<H>` effect role with one Type formal and no ordinary
   request/implementation authority. Generate its reserved builtin identity in
   the existing module/registry preparation path, not a user-declarable effect
   flag. Ordinary source effects retain their current grammar and behavior.
2. Add explicit static `resolve_checked_foreign_module` admission followed by
   the existing `check_module` API. Default `resolve_module`, build and run remain
   legacy routes and refuse checked host work. This API produces no configured
   executable image. Add contextual `foreign host H { body }` syntax, shape validation and original
   spans. Resolve H as one fresh rigid Type identity using the existing lexical
   identity/scope machinery. Preserve nesting and scope checkpoints; charge new
   storage and identity work before publication. Keep host names and outer
   ordinary Type/Row variables distinct.
3. Extend original checked scalar binding with the canonical CheckedCall codec,
   exact selected H and automatic/authored premises from the retained library.
   Its operation computation carries both its complete original native instance
   and `NativeHost<H>`; the symbol's outer arrow remains pure. Use the existing
   registry/operation facts and phase projections, with no parallel binding
   inventory. Legacy binding keeps its present independent refusal guard.
4. Add a dedicated host boundary through resolved expressions, elaboration and
   Effect Core. It interprets only exact admitted checked owner-free scalar/void
   native instances for this H and removes those instances plus its exact H
   effect. It preserves the body result type and all unrelated outward effects.
   Owners remain ineligible at this checkpoint. Reuse iterative traversal,
   effect subtraction and fresh-identity escape checks from existing resource
   and copy-window scopes. H cannot escape in result types, latent rows,
   closures, captures, evidence or retained dependencies.
5. Independently reconstruct host and checked operation authority in Core from
   canonical registry originals and complete Type/Row vectors. Extend copy,
   instantiation/specialization, capture analysis and transformed-node validation
   for this scope. The dedicated `ForeignHostIdentity` mode on the existing
   NativeInterpret Core node binds H and shares its body/interpretation-vector
   traversal. Ordinary mode has no host binder and rejects checked contracts;
   checked mode rejects legacy, owner and other-H vector entries. Independent
   mutation checks remove or forge the mode and alter H, effect and vector.
   Ordinary handlers/native interpretations cannot remove the
   sealed host effect, including a return-only zero-clause handler for this
   zero-operation builtin. Check the entire required checked closure, including
   unreachable required branches and imported/opaque helper facts; unsupported
   summary paths refuse rather than erase dependencies.
6. Keep executable launch unavailable. Existing-profile source/build/image
   routes reject the complete required host/checked-operation closure before
   any native callback, including an unexecuted required checked branch.
   A successful static checker/validated Core result is not a configured checked
   program image. Private-image encoding/admission and runtime must explicitly
   refuse unsupported host nodes until their independent reconstruction and the
   F4/F6 connection exist. Do not add a test-only native execution bypass.

Reserved builtin provenance has two checks. Source admission verifies the actual
loaded/defining SourceFile bytes against the immutable compiler source. Core
admission repeats that comparison for every reserved module/source association,
including unused or replayed module identities, before reconstructing roles.
The existing image restore must continue comparing immutable bytes. A source
span or namespace coordinate alone grants nothing; test an equal-length rewritten
source with a replayed reserved ModuleId against the real Core admission API,
with a passing canonical-byte literal control.

Preserve existing-profile behavior when the inert builtin role is present.
Existing exact builtin inventory/image gates may extend only for independently
authenticated appended metadata; they cannot become open-ended nominal/global or
polymorphism allowances. The private metadata String function is absent from
public exports and native/preflight roles. Actual host nodes remain ineligible for
unconfigured images and execution.

Affected seams: `src/module.rs` builtin inventory and exports;
`src/foreign/checked_source.rs` canonical call/binding validation;
`src/parser`, `src/surface`, `src/resolve` and `src/resolved.rs` scoped originals;
`src/elaborate` and `src/core/{effect,transform,capture,validate}` static scope and
independent checking; `src/build/image.rs` and existing whole-program foreign
admission for incomplete-route refusal. Update only implemented specification
claims in syntax, static semantics and elaboration.

Write meaningful red tests before implementation: a closed checked scalar call
under its exact host statically succeeds; nested distinct hosts stay distinct;
a same-kind donor H, same-shaped codec, host escape through a returned closure,
hidden imported dependency and ordinary-handler host erasure each reject at its
own boundary. Preserve an unrelated ordinary outward effect and nearest ordinary
handler behavior. Mutated Core host identity/native vector/metadata rejects after
construction, and exact/one-short/fresh work cases share the real checker. The
legacy/source/build negative asserts that its native callback never enters.
Pure host-body static success is a control, not the positive scalar-host witness.

The developer remains the only build operator. Freeze source/configuration pins,
retain raw focused test/Clippy logs, obtain independent exact-head review and
use GitHub squash-and-merge (GitHub merge commit fallback) before author
acceptance, then fetch/synchronize local and origin retaining refs and verify the
actual retained tree. Locally authored commits remain unsigned. The later user
instruction supersedes local squash retention for future PRs. F3's
original checklist remains open for the unimplemented module/Core/image,
wrapper, owner/lifecycle and checked-primitive obligations; F-core and F2/F6
architecture/deployment gates remain separate.

## Slice 4: Preserve body-free contracts and checked primitives

Extend module summaries, wrapper/capture facts, copy/specialization and linked
validation. Add the distinct checked builtin identities/codecs from CP-0024;
legacy byte/copy functions cannot authorize checked access. Test imported wrappers
without source-body inference, opaque/re-exported origins, complete Type/Row
instantiation, hidden captured S/C/H, branch/recursive joins and forged assumption
or dependency removal. Nearest ordinary-handler precedence remains unchanged.

### Next body-free wrapper checkpoint

Start from retained PR #85 at `bdae57436e33158c931b740886f05ad335b98106`.
Publish this plan as an early draft PR before implementation. The previous
checkpoint supplies static scalar hosts and canonical symbol facts, with runtime
and image refusal. This checkpoint must connect those facts through ordinary
wrappers rather than infer authority from retained source bodies or effect names.

Use the existing export/import, global scheme, capture and contract carriers.
Preserve original operation/assumption identities and full Type/Row substitutions
through generic wrappers, aliases and re-exports. An internal host may remove
native/H effects from a wrapper's outward row; that cannot erase its required
native contracts or assumptions. A body-free consumer must retain that dependency
and the explicit checked-profile requirement. Empty authored assumption sets
continue to retain automatic native premises. No parallel registry, source-name
special case or serialized checked flag may supply authority.

An internal H remains lexically bound in portable host provenance. It must not
be exported as a free Type identity or reused as authority by independent calls.
The same closed wrapper called twice has separate host activations. Consumer
checking receives only `DependencyExports`/summaries; producer code is supplied
separately at linking. Resident bytes authenticate original declarations rather
than re-infer wrapper requirements. Erasing an outward-pure wrapper's checked
requirements must reject against independently reconstructed original facts.

The first erasure probe confirms that native-table authentication alone cannot
prove an outward-pure wrapper's capture requirements were retained. Complete
local `CheckedGlobalScheme` facts therefore publish once per original binder as
immutable shared originals. Export/import projections retain that same original
across aliases and re-exports, compare binder/scheme/origin/capture against it,
and reject a missing, donor or stale original. Mint only from completed local
checked facts, never from an imported projection. Clone and comparison work is
charged before allocation; failure publishes no partial summary. Source consumers
remain body-free, while linking/Core independently check producer code.

Write positive and negative cases before changing behavior:

- Direct and generic imported scalar wrappers, preserving unused Type/Row actuals
  and exact H selection, lower through independently validated Core.
- A wrapper with an internal checked host exposes its transitive contracts after
  its outward row closes; a body-free default-profile consumer refuses it.
- Namespace aliases and re-exports preserve original identities; opaque views
  retain required contract facts without exposing hidden constructors or bodies.
- Wrong H, reordered complete vectors, hidden/captured host dependencies and
  erased or substituted assumption/contract metadata reject independently.
- Branch-only dependencies, selected evidence and bounded recursive/higher-order
  summaries preserve the union. If a path cannot be reconstructed in this subset,
  refuse it explicitly and keep that original obligation pending.
- New summary/capture reconstruction work has exact, one-short, cumulative and
  fresh sufficient-budget controls. Existing legacy exports remain valid.

This wrapper checkpoint covers ordinary globals and callable control summaries.
Selected-evidence carrier/anti-erasure coverage remains pending under the original
F3 criterion. These controls establish effect references in callable and nested
Type/Row metadata; they do not establish complete nominal/resource type-closure
erasure coverage. Checked owner/copy/lifecycle and
executable-image obligations also remain separate.

Freeze and independently review each coherent subset. Preserve the scalar and
legacy image/owner regressions; select focused checks for changed boundaries and
retain exact raw results. Keep the active worktree committed and clean between
handoffs. Continue using one Cargo job and the existing shared target.

Checked owner lifecycle execution, checked byte/copy operations and launch/image
admission are excluded from this wrapper checkpoint. They remain original F3 or
connected F4/F6 obligations; this subset cannot close TASK-0051. Missing proposed
semantics return to CP-0024 rather than becoming local implementation choices.

### Selected ordinary implementation-method checkpoint

Start from retained `284e6046499a43dcf48b600ecb3e61fd55286483` on
`codex/checked-ffi-f3-selected-evidence`. PR #86 retained ordinary-global
publication and callable effect closure; PR #88 added evidence only. Publish this
plan as an early draft before implementation. Authority remains accepted CP-0024
and this task's original summary/evidence obligations; no new source semantics.

1. Build a passing connected control using a module-level public interface
   implementation method that calls a closed checked scalar wrapper. A generic
   consumer selects that implementation through an imported prerequisite DAG.
   Its checker receives only `DependencyExports`; producer code enters separately
   at linking and independent Core validation. The explicit static profile must
   pass, while default profile refuses the transitive checked requirement despite
   an empty outward row. Lexical `with` alone cannot establish this control.
2. Extend controls through aliases/re-exports and opaque views, generic heads and
   complete distinct Type/Row actuals. Inspect exact original implementation,
   interface method, method binder, prerequisite and operation/assumption union;
   use two distinct native contracts so a dropped branch is observable. Internal
   H remains bound in host provenance, never free authority or an adapter-created
   replacement. Preserve existing unsupported runtime/image refusal.
3. After the unmodified fixture authenticates, mutate method capture alone and
   capture/native/effect tables together. Test missing, same-shaped donor and
   stale original facts, wrong route/owner/head/actuals, prerequisite and adapter
   substitutions. Route authorization is not proof of a completed method body.
   Retain each meaningful failure before implementing a repair. If existing
   canonical facts already reject a case, preserve that evidence without adding
   duplicate metadata or changing authority.
4. Repair only demonstrated gaps using the existing completed implementation/
   method fact and original publication pattern. Mint a defining publication
   only from successful local checking, retain the same original through import
   and re-export projections, and compare owner/method/binder, full scheme,
   head-parameter boundary, prerequisites and capture. Never mint from an import
   or trust a serialized flag; linking/Core still checks producer correspondence.
   Charge traversal/cloning/comparison/reservation before publication; preserve
   iterative destruction and failure atomicity.
5. Exercise independent selected-evidence/Core reconstruction after a valid
   source control: mutate selected binder/complete actuals/prerequisite/adapter,
   and preserve valid identity/fold transforms. Test shared prerequisite/capture
   DAG memo work with exact, one-short, spent-prefix and fresh sufficient budgets,
   including refusal without partial published authority. Select affected ordinary
   implementation/import/summary/capture regressions and targeted Clippy after
   freezing source/configuration; one build operator owns the shared cache.

The intended locations are `tests/checked_foreign_wrappers.rs`, a dedicated
private selected-evidence test module beside `checked_wrapper_tests.rs`, and the
existing implementation/evidence/Core carrier seams in `src/resolved.rs`,
`src/core/capture.rs` and elaboration as the red controls require. Add or update
specification wording only for behavior actually delivered and independently
verified. Send the exact candidate to independent review, then use the current
GitHub integration/acceptance workflow; keep clean committed checkpoints.

Nominal/resource declaration-closure erasure remains a separate red-driven
checkpoint unless a concrete dependency prevents this selected-method control.
Checked owners, copy/lifecycle, full image admission, F4/F6 runtime, whole F3 and
F-core remain pending. Do not infer their delivery from a generic refusal or an
ordinary resource fixture. A missing semantic rule returns to CP-0024 rather
than becoming a local permission or method-name special case.

### Capture-only nominal declaration-closure checkpoint

Start from retained `036c366834c839e4f0a503cf63e9db46448bb486` after accepted
PR #93 and closed issue #91. This supersedes the read-only preparation's older
PR #89 source pin; its hypotheses are not observed defects. Publish this focused
plan in an early draft. At this reviewed documentation checkpoint, retire
completed TASK-0052 and repair inbound links to immutable history while keeping
all durable startup evidence. No separate TASK-0052 plan exists.

1. Establish an actual private `type Held = Held(Int)` captured intact by a
   closure returned from an exported wrapper. Destructure Held inside that
   closure and pass Held as an ABI-unused Type actual through the existing closed
   generic checked scalar wrapper. A data-only captured value need not produce a
   callable type edge; that rejected fixture is not a product defect. The public
   scheme must omit Held. Assert the real callable graph reaches Held, that only
   hidden identity/kind metadata supplies it, and that exact native/assumption
   identities remain. Require explicit-profile source, unchanged summary,
   body-free DependencyExports consumer, separate producer linkage/independent
   Core and valid identity/fold transforms to pass before mutation.
2. Erase Held's complete hidden nominal/order mirrors, and constructor/order
   mirrors only if the valid fixture retains them. Hidden constructor access
   remains unavailable. Perform the erasure while
   preserving completed global publication, callable graph, resident provenance,
   public scheme and native/effect facts. Test summary authentication, actual
   consumer and independent linked Core separately; name the first failing
   boundary. Keep an unrelated removable nominal control if a real unchanged
   fixture establishes it. A missing capture edge or malformed baseline is a
   fixture problem, not an erasure result.
3. Repeat through a selected-only module-level `Read<Int>` implementation, with no
   public term/type/constructor rescue. Retain the completed implementation/method
   publication, head, prerequisites and exact selected capture edge. Demonstrate
   alias/opaque/re-export routes only after their supported positives pass.
4. Repair only a demonstrated closure gap using the existing canonical retained
   declaration worklist and original facts. Charge every root, lookup, definition
   edge, memo hit and reservation before traversal/allocation. Preserve exact
   original identity and complete Type/Row contexts; imports cannot mint authority.
   Shared or recursive references need bounded operation-local visits, not
   unbounded monomorphization or a new FFI registry. Source text remains declaration
   provenance, never wrapper-body inference or constructor access.
5. Retain distinguishing positive/negative cases and exact/one-short/nonzero-prefix/
   spent/fresh Type and constraint budget controls. Freeze and run affected
   ordinary nominal/import/capture/global/selected and Core-transform regressions,
   both startup defaults/image suite and targeted Clippy as the changed boundary
   requires. Preserve raw outputs and source/configuration pins. Independent
   exact-head review precedes root-authorized GitHub integration/acceptance.

Constructor-payload transitive/donor, generic actual, deeper resource and broad
nominal/resource graphs remain subsequent red-driven controls unless essential
to this exact checkpoint. ResourceApply already has resolver and contract
traversal; do not patch its visitor based on appearance alone. Checked owners,
copy/lifecycle, executable image/runtime activation, whole F3 and F-core remain
pending. A genuine semantic gap returns to CP-0024.

### Constructor-payload declaration-closure checkpoint

Start from retained `2d04de76463febaaf36e082e7bccd8f6e85dc26b` after independently
reviewed PR #94 and PM-confirmed partial issue #59 acceptance. PR #94 closes
capture-root nominal-kind membership, including existing kind-only resource
families, and retires TASK-0052. Its result does not establish transitive
constructor-payload closure. Publish this plan in an early item draft.

1. Establish private `Leaf(Int)` and public transparent `Envelope(Leaf)`, with
   exported make/inspect functions and the supported closed checked scalar
   wrapper. Use no ABI-unused Leaf native actual. Require actual source,
   summary, body-free DependencyExports consumer, separate producer linkage,
   independent Core and identity/fold positives. Assert Leaf is required by
   Envelope's retained constructor payload and scheme, but absent from public
   global schemes and callable type roots. Hidden Leaf metadata grants no Leaf
   source name or constructor access. Refine the fixture if that edge is absent;
   no product gap is inferred from a malformed or rescued control.
2. Remove only required Leaf hidden lookup/order metadata while preserving
   Envelope's identity, constructor payload/scheme/origins, complete original
   global publications, captures, native facts and resident sources. Name the
   first rejection boundary; distinguish summary, real consumer and separately
   mutated already-valid Core. Retain an unrelated unused nominal contrast.
3. Establish a same-kind Donor through an independently valid declaration route
   (for example another public constructor payload), without giving Leaf an
   additional capture/global root. Coherently replace Leaf with Donor in both
   Envelope constructor payload and scheme, preserving arity, IDs, provenance,
   access and all original publications. Assert the unchanged donor control
   succeeds before testing summary, import/link and Core correspondence. A
   mismatched payload/scheme is not a coherent substitution control. Compare
   against actual defining facts and supported constructor uses; no imported
   projection may mint a replacement original.
4. Existing checks may already reject every case; a tests-only checkpoint is
   valid. Repair only a demonstrated missing boundary using existing canonical
   declaration facts and paid worklists. A missing semantic or architectural
   authority returns to CP-0024/design before product changes; do not create an
   FFI registry, constructor access or stronger inferred source semantics.
5. Exercise supported alias/re-export and identity/fold paths plus exact,
   one-short, nonzero-prefix, spent and fresh Type/constraint ledgers at the
   actual boundary. Freeze source/configuration inputs and retain raw outcomes;
   run affected import/nominal/Core/capture regressions and Clippy, including
   startup/image checks if production admission changes. Independent exact-head
   review precedes root-authorized GitHub integration and partial acceptance.

The current [delivery evidence](../evidence/checked-constructor-closure/README.md#final-delivery-verification)
records the demonstrated coherent-donor summary/consumer red and independent
Core refusals. The bounded repair reuses the defining checked registry reference
inside existing constructor carriers; it does not copy a new publication fact.
It preserves newtype effective payloads, original continuity and selected access.
A real nonempty latent-row mirror red also required the fused kind walk to
reject mixed pure/effectful presentations unless their row is empty. Final
focused verification passes 331 distinct tests and Clippy, including image 16/16
and unchanged startup limits. PR #95 retained this reviewed subset at
`2532f528795e5cdc3974685d10313e6cb4b778a9`; author acceptance, reviewer
retained-result audit and PM confirmation are complete.

Generic actual/row, recursive/shared payload and deeper resource closure remain
later red-driven controls unless essential to this fixture. ResourceApply already
has resolver/contract traversal. Whole F3, F-core, checked owners, copy/lifecycle,
image/runtime activation, deployment and Main integration remain pending.

### Static checked-owner binding prerequisite

Start from PR #95 retained `2532f528795e5cdc3974685d10313e6cb4b778a9`
after its independent retained-result audit and PM-confirmed partial #59 record.
Accepted CP-0024 selects explicit exact H for owners and symbols, and requires
ordinary lifecycle handling to retain H until the lexical host closes it. At this checkpoint’s baseline,
static checked resolution only bound scalar symbols; the legacy owner binder
refused checked contracts. Resource host/checked_scope admission is a later,
separate boundary. No binding fact supplies executable or lifecycle permission.

The first individual PR is the dependency-ordered binding prerequisite:

1. Establish an actual checked prepared opaque State<H,R> owner with distinct
   explicit Type H and owned R, nullable acquisition and void disposition
   teardown. Test canonical original owner/symbol binding and full ordered
   vectors under the explicit static profile. Keep default/legacy binding
   refusal and checked dependency/access/unsupported call refusal explicit.
2. Extend the existing owner and symbol binders, not a parallel registry. Exact
   original nominal/parameter/origin/host correspondence must survive binding;
   acquisition, teardown and owner operands select the same H. Use canonical
   CheckedCall with unchanged inner Output/Nullable/Disposition relations.
3. Observe the red before production changes. Mutate H/R positions, original
   State, host selections, owner applications, source/origins and codec roles at
   the actual binding boundary. Preserve complete Type/Row actuals and authored
   assumptions. Pay lookup, clone and publication work before committing facts;
   test exact, nonzero prefix, one-short, spent and fresh allowances.
4. Require real source static resolution/checking of passive owner declarations
   once binding is connected. Body-free summary/import/re-export and independent
   Core may retain passive facts only if each existing authority check supports
   them; name an unsupported boundary rather than claiming lifecycle completion.
   Run affected scalar/owner/foreign, import, default-image and Clippy controls.
5. Freeze inputs and raw receipts for independent review. Root assigns GitHub
   integration, followed by partial acceptance; no whole TASK-0051 criterion is
   accepted by this prerequisite alone.

The next dependency checkpoint connects resource host selection and canonical
checked_scope/CheckedFinish/CheckedScope to existing Acquired/Refused and finish
phase rules. It requires actual source/summary/body-free consumer/link/Core and
identity/fold positives, then independent wrong-H acquire/free/State/resource,
nested-host, donor-R, erased completion Host and fake-codec negatives. The host
boundary must never interpret owner operations. A mismatch with CP-0024's O/K
transition rules returns to proposal/design; no new disposition rule is selected
locally. Declared C-to-S owner dependencies remain separate.

Checked byte/copy/lifecycle execution, K/quarantine, runtime/image activation,
protected storage/deployment, SQLite, F4/F6, whole F3 and F-core remain pending.
AD-0015 remains owner-free; this static work grants no deployment permission.

## Slice 5: Independently validate retained Core and private images

Extend existing Core and private-image reconstruction with canonical checked
contracts, exact host/owner/window lineage and complete projection comparison.
Mutate origins, host effects, assumptions, independence, full argument vectors
and native-window order after construction. Each mutation must reject separately;
constructor APIs and serialized checked flags grant no permission. Run exact,
one-short and fresh sufficient work/capacity cases without effect replay.

## Handoff and final checks

Every slice reports Delivered, Remaining, Awaiting and Owner against TASK-0051.
No partial slice closes F3 or removes CP-0024. Full F3 acceptance requires the
complete source/summary/Core/image behavior and independent review. F-core waits
for connected F4/F6 and accepted F2 prerequisites; one build operator owns that
frozen full gate. Current Main remains the original specification until separate
verified integration.

PR #96 prerequisite result: passive exact original owner/acquire/teardown facts
now bind under the explicit static profile, and actual body-free selected imports
preserve them. Legacy binding and both legacy resource codecs remain refusals.
The [uniform evidence](../evidence/checked-owner-binding/README.md#final-delivery-verification)
passes 223 distinct tests and Clippy, including source-resource 30/30 and default
images 16/16. Independent review and root-assigned integration remain next;
connected checked_scope/lifecycle and all whole-criterion gates remain pending.

### Connected static checked-owner lifecycle checkpoint

Start from PR #96 retained `91e6dee036c9728d89f016aee61ff337b8a978e1`,
with independent retained/partial acceptance audited and PM-confirmed in #59.
The passive binding prerequisite is complete; it did not admit checked resources.
Accepted CP-0024 governs this checkpoint, not the current legacy codec behavior.

The connected positive uses one dependency-free opaque State<H,R> and source
Probe<H,R>, distinct explicit host H and owned R, nullable acquisition and void
consumed/retained teardown. A lexical foreign host encloses canonical
`codec checked_scope`, `Foreign.CheckedFinish<State,E>` and
`Foreign.CheckedScope<Answer,I,E>`. Acquisition keeps existing Acquired/Refused
rules. Resource handling removes only its exact listed native/resource instances;
H remains through acquisition, calls and required completion. Host lowering never
interprets an owner operation. Same-shaped user codecs supply no authority.

1. Establish the real source fixture and its first failing boundary before
   production changes. Add source header host and checked codec projection using
   existing surface/resolved/header/codec records. Authenticate original owner,
   complete actuals, canonical builtin roles and exact H independently.
2. Extend the existing paid symbolic flow arena with private exact finish-request
   outcome lineage. Every returning finish branch accounts for one conforming
   native or synthetic outcome. FinishedBoundary requires that owner's exact
   attempted-request boundary payload, forwarded directly; public constructors,
   attempted=true, borrowed/earlier failure, donor owner/H or reconstructed data
   cannot mint the witness. No separate registry or runtime proof flag.
3. Preserve required source continuation after the request independently of native
   disposition and K. Support direct payload forwarding first. Broader helper or
   decomposition/reconstruction transport remains unsupported until separately
   proven; concrete CP-0024 O/K ambiguity returns to design, not a local rule.
4. Require source, summary, body-free consumer, linked independent Core and
   identity/fold positives before separate mutations: wrong H in acquisition,
   free, State/resource and nested hosts; donor R/State; fake codec; erased
   completion Host; missing/duplicate attempt; substituted/borrowed boundary
   failure; one returning branch without a witness; boundary outcome relabeled
   consumed/retained; erased required source continuation. Keep each boundary's
   canonical control and semantic/non-Resource failure independent.
5. Charge all traversal, clones, comparison and publication. Test exact,
   nonzero-prefix, one-short, spent and fresh allowances and refusal atomicity.
   Run affected legacy source-resource/owner/import/capture/Core/transform and
   default-image controls plus Clippy with one shared cache/job. Preserve
   unchanged standalone startup limits and separate source input-derived work.
6. Publish frozen inputs/raw evidence and request independent exact-head review.
   Root assigns GitHub integration; author partial #59 readback follows actual
   retained-tree verification. All four whole-F3 boxes remain unchecked.

This is static correspondence, not actual native completion or K discharge.
Checked runtime/native/image execution, K/quarantine implementation, bytes/copy,
SQLite, deployment, F4/F6 and F-core remain excluded. AD-0015 remains owner-free.
Declared enclosing C-to-S dependencies and remaining declaration-closure cases
remain visible. No Main integration or whole F3 acceptance follows.

### Bounded static lifecycle delivery record

The delivered carrier uses the existing immutable source header/templates and
source-code publication. Finish admission records exact request/outcome/payload
lineage; independent Core authenticates the flow-checked template and every
specialized copy rather than replaying symbolic flow at each scope. Native
consumed, retained and boundary alternatives preserve the actual post-request
source continuation. Pattern inspection preserves the original whole witness;
reconstructing diagnostic data does not remint it.

The connected closure required three existing-fact repairs: coexistence of
canonical legacy preflight Call and checked native CheckedCall in one builtin
module; hidden same-module provider-interface retention/import; and referenced
private foreign State metadata without constructor or source-name access. The
sealed Host control event now has its own paid independent value port. Pending
provider rows use existing exact subtraction equations and deferred result/row
H-escape checks; no unknown-row absence assumption or owner interpretation is
added to the host.

The [delivery evidence](../evidence/checked-owner-lifecycle/README.md) separates
historical red/setup receipts from the final uniform source/configuration
verification. It includes source/body-free consumer/Core/identity/fold controls,
exact copied completion-H and required-continuation mutations, both latest-D E
contract variants, refusal/budget controls, and the retained-base deep-fixture
comparison. Standalone default limits remain unchanged; source checking keeps
its separate established input-derived allowance.

This remains a bounded static subset. The acquisition codec in the connected
fixture is public; private local acquisition-codec constructor closure remains
unsupported. The earlier combined producer/Cell original-template context and
multi-checked-library lifecycle fixtures remain unaccepted broader cases, not
proofs of new support. General failure-witness helper/reconstruction transport,
checked Borrow/byte/window roles, declared C-to-S owner dependencies and broader
declaration closure remain outside the delivery. Runtime/native/image execution,
K realization, F4/F6, deployment, Main and whole-F3 acceptance remain pending.
The F-core trigger remains the connected generated-host F3/F4/F6 path.

### Static scalar Current Borrow checkpoint

Start from retained PR #97 at `73a982f012f370cb9f2fb808b6b5d6f01490c9e4`.
Its connected dependency-free lifecycle and private finish lineage are accepted
as a partial delivery. This checkpoint implements the next bounded part of
CP-0024 and TASK-0051 Work 2–4 / Slices 4–5: one opaque Current scalar Borrow
inside its owning resource's direct handler. It does not expand owner transport.

At the test-first snapshot, the shared owner binder already validated scalar
Current Borrow signatures, while the checked symbol entry excluded that role. First establish a real
prepared contract and observe its actual explicit-profile binding refusal. A
code exclusion alone is not red evidence. Use the PR #97 State<H,R> library with
an additional `Read<H,R>: State<H,R> -> Foreign.CheckedCall<Int>`, a scalar C ABI
result and one Current operand. Keep exact H, owned R, complete formal vectors,
original native/owner/assumption identities and canonical CheckedCall. The
resource lists Read<H,R>; its direct read handler performs that request on its
Current and resumes the complete checked result, without source State forwarding.

1. Publish this focused plan in an early individual draft PR under #59/#52/#51.
   Record genuine preparation facts, then the binding red on frozen inputs
   before product changes. Legacy/default profile remains refusal.
2. Repair only the demonstrated checked-role gap using existing canonical owner
   binding and phase rules. Checked acquisition, finish and no-resource-context
   Borrow remain refusals; preserve legacy phase behavior. Admit no Access
   result, byte representation, view,
   window, initialized extent, dependent owner or general helper transport.
   Pay exact role/signature/identity checks and publish no partial permission.
3. Require actual checked source, summary, body-free import and re-export, linked
   independent Core, identity and fold positives. Preserve hidden State and
   provider facts without publishing names; retain native and Host rows through
   exact resource interpretation and host completion. Check original Read,
   State, H/R and role-linked assumptions at each existing carrier boundary.
4. After canonical positives, test wrong H/R/State, wrong or erased Read original,
   missing interpreted membership, fake codec and erased native/assumption/Host
   facts. Ordinary handlers cannot simulate native authority, and direct calls
   outside the owning phase remain refused. Existing post-finish Current
   retirement, finish outcome and source-continuation controls must stay green.
   A checked Borrow BoundaryFailed alternative remains independent diagnostic
   data: visit its actual branch, reject Current transport, and never mint the
   private finish request/outcome witness from that result.
   Independently mutate retained Core operation/vector/row/original facts.
5. Preserve default work limits and bounded traversal. Cover exact, nonzero
   prefix, one-short, spent, fresh and refusal-atomicity behavior for newly
   admitted binding/phase paths, then affected foreign/owner/import/resource/
   capture regressions, both original startup defaults, images and Clippy.
   Freeze complete inputs and raw receipts; obtain independent exact-head
   review before root assigns GitHub integration and partial acceptance.

The direct-handler scalar result is the only new supported owner operation in
this checkpoint. Checked byte/copy operations, Access/view/window results,
C-to-S dependencies, general callbacks/helpers/State forwarding, lifecycle
outcome expansion, checked evaluator/native/image execution, K realization,
deployment, SQLite and F4/F6 are excluded. AD-0015 remains owner-free. Broader
declaration closure and whole F3 stay pending. The existing generated-host
connected F3/F4/F6 trigger for F-core and separate Main integration are unchanged.
A concrete semantic gap returns to CP/design rather than selecting local rules.

The candidate now admits the exact direct State-to-Int role only in Handler,
retaining the legacy behavior and checked Acquire/Finish refusals. Direct demand
and substituted row realization reconstruct exact Host from the native original
and complete request vector. Fresh focused positives include genuine four-formal
Before-row/H/R/After-row metadata with distinct nonempty rows, body-free import
and re-export, independent Core/copy mutations and identity/fold. The actual
request component distinguishes independent Borrow BoundaryFailed from private
finish authority. A caller-handled independent observer gates its State-hostile
source refusal; that refusal is not attributed solely to symbolic payload flow.

The appended-observer declaration exposed a separate OriginalTemplate source-order
census limitation before flow. Its pinned failure remains evidence; equivalent
declaration ordering isolates the assigned direct-handler case without changing
the census. Final uniform affected regressions, startup defaults, images, Clippy
and exact-head review remain the delivery gate. No F-core or whole-F3 pass follows.

### Checked byte and copy window checkpoint

Start from retained PR #98 at `c8a1fee506a00f68065cb08c6e2e9911d44a58aa`.
This implements the remaining checked primitive part of CP-0024 and Slices 4–5
as one coherent delivery: all four authenticated `@builtin.foreign` functions
`checked_byte_read`, `checked_byte_write`, `checked_copy_bytes` and
`checked_copy_nul`. It must not substitute another opaque scalar admission case.
The earlier OriginalTemplate ordinary-formal/unused-host ordering limitation
remains recorded; no source census exemption follows.

Current Ash has legacy sealed byte/copy functions returning `Call` with empty
ordinary rows. Existing initialized State, original access families, exact view/
extent keys, direct provider windows and non-suspension rules supply the native
lineage. The four checked functions are absent, and the checked binding subset
still rejects the needed initialized-byte owner and access-producing shapes.
The [test-first evidence](../evidence/checked-byte-windows/test-first/README.md)
now records genuine preparation success. Initial resolution stops at the absent
`checked_byte_read` export. A resolver-only spelling isolation then reaches the
unchanged checked library and fails `ForeignContract / InvalidLibrary`: the
checked owner gate requires Opaque and refuses this Bytes State. That control
never source-checks legacy calls or grants checked permission. No product change
preceded these receipts. Legacy canonical controls must remain valid.

Use existing builtin declaration/fact, source-owner/access, primitive-call/window,
summary/original publication, specialization and independent Core/image carriers.
Preserve existing builtin identities and append distinct checked roles; source
names, module membership or a serialized checked flag cannot create authority.
Each checked signature has explicit first Type H, the exact State S or view V,
canonical `CheckedCall`, and `NativeHost<H>`. Reconstruct H from the admitted
owner and complete actual vector; never select a convenient same-kind formal.
Pure scalar/NUL preflights, data/private-state functions and extent inspection
keep their existing identities/codecs and authority restrictions.

Retain the existing distinct Acquire/Handler/Finish live-State/window rules; the
PR #98 Handler-only scalar Borrow subset is not a blanket byte-phase rule. Checked
primitive function values retain their latent exact Host effect, and each applied
occurrence must reconstruct it independently. Byte/copy failure alternatives are
independent diagnostics, never private finish-request/outcome witnesses. Exact
view/Extent value lineage, producing member and scalar keys remain required in
addition to compatible types; NUL copying also requires its original Nul family
and an independent bound.

1. Establish one real checked byte State with authenticated initialized extent,
   nullable acquisition, actual checked finish and independent source continuation.
   Exercise both checked byte operations in its owning direct phase. Separately
   establish a genuine original access query and preserving extent query inside
   a direct fresh window, then exercise both checked copy operations on that
   exact V/Extent/owner/window/key relation. No source pointer or view escapes.
   If the real view requires a declared parent/child dependency, carry the exact
   declared C-to-S originals, full vectors and revocation/liveness facts rather
   than removing the dependency to manufacture a positive.
2. Preserve exact original library/member/assumption, ABI representation,
   initialized-output selection and complete ordered Type/Row facts through
   genuine source and summaries. Require body-free import plus re-export, linked
   independently validated Core, identity/fold and static private-image
   reconstruction/validation. Static record validation does not authorize checked
   runtime, bridge/native activation or generated checked execution.
3. Require canonical positives before hostile controls: arbitrary/wrong H,
   same-kind State/view/Extent donors, erased initialized extent, wrong native
   ordering or preserving member, removed assumptions/dependencies, incomplete
   Type/Row substitution, split/reordered/suspending windows and stale copied
   contracts. Reject legacy byte/copy calls on checked owners/views independently;
   also reject calls outside the owning phase/window and State/view forwarding
   through ordinary helpers. Mutate retained real Core/image facts separately,
   keeping ordinary registry shape and immutable originals intact where possible.
4. Reuse paid work/storage and iterative teardown; compare originals before
   publication. Measure exact, prefix, one-short, spent and fresh budgets plus
   refusal atomicity at meaningful new boundaries. Preserve PR #97/#98 finish,
   Current retirement, Host and source-continuation regressions, legacy byte/copy
   behavior, both startup defaults and image checks. Freeze inputs/tools before
   the final focused batch and independent exact-head review.

The first required red gate is real checked contract preparation followed by
expected-positive initialized owner/primitive resolution or source admission;
record whichever precise boundary actually refuses. A separate builtin inventory
probe may establish missing declarations but cannot replace connected lineage
positives. The first two commands above establish preparation and the separate
inventory/binding refusals only; connected source and later gates remain pending.

Runtime/native/checked image execution, K/quarantine implementation, arbitrary
raw pointers, general callbacks/helpers, privileged lifecycle transport,
deployment and SQLite activation are excluded. Existing checked runtime/image
refusal remains until its separately assigned prerequisites connect. F4/F6,
SQLite, F7/F8 and the full milestone remain required overall. AD-0015 remains
owner-free; all four whole-F3 criteria stay unchecked. Root assigns F-core only
when the real generated-host F3/F4/F6 path and accepted F2 are ready. A concrete
semantic omission or O/K conflict returns to CP/design, never a local rule.

[Product candidate evidence](../evidence/checked-byte-windows/candidates/README.md)
retains reconstructible compile failures and preflow failures. Exact diagnostics
identified separate codec-family identity and missing defining-H scheme-kind
correspondence, without relaxing source ordering, flow or lexical scope checks.
The current frozen five-test candidate passes actual initialized-State/view
preparation, default refusal, binding/inventory and all-four source/summary.
Two additional controls pass family remint refusal and paid complete-formal kind
lookup. Both commands share 591 equal inputs, aggregate `c74e45c0`.
Body-free consumer/re-export, independent Core/transforms, passive image
validation, hostile controls and affected bounds/regressions remain pending.
No runtime or image activation permission follows.

The next frozen candidate passes both actual body-free consumer routes and
linked independent default Core/identity/fold (7/7 with the prior source gates).
Foreign-free Pure, inert legacy import, checked-host image refusal and scalar/NUL
atomicity controls pass. Passive-image tamper completion and stale formal-count
fixtures need test-premise corrections. More materially, both buffer and the
dependent-discard startup probes now exhaust the unchanged 327680 allowance;
these are delivery blockers, with measured repeated codec proof work retained.
No budget, startup fixture or activation guard may be relaxed to close them.

The first measured operation-local family codec proof sharing preserves connected
7/7, family controls 3/3 and image-subset 2/2, but default startup still exhausts
the unchanged allowance. A second exact duplicate full-inventory replay through
per-row Host checks is measured and a projection-preserving repair is authored,
not executed. Its future results must not inherit the first candidate's passes.

The second Host-proof sharing candidate passes four family controls, connected
7/7, image subset 2/2 and complete passive-image tamper validation, at 591 equal
inputs `837b5c5b`. Startup still fails at unchanged 327680. Complete caller/cost
evidence separates repeated proofs inside immutable table operations from
independent admission boundaries; no cap or validation waiver is permitted.

The grouped immutable-table/owned-pointwise repair passes five focused controls
(`704cc8e8`) but still fails all three unchanged startup probes. Selective size
and legacy byte imports/re-exports reach the next case; direct checked-copy NUL
then fails codec admission both before and after this repair, confirmed against
exact `a99a9c4c` plus the same test overlay (`cd784d8a`). Preserve that distinction
and diagnose its actual closure fact; no codec or budget waiver follows.

The selective dependency repair now retains the exact canonical nominal,
constructor-family and Host checking closure through direct imports and facades,
without adding public names or other globals. A real coherent Call-constructor
truncation initially authenticated; expected membership now comes from the
existing immutable canonical inventory after original authentication. The fresh
candidate passes 9 connected/source/privacy tests and 7 family/summary controls
(including 2 summary tests), all at 591 equal inputs `57500e29`. All three startup
probes still exhaust the unchanged allowance. Next measure exclusive capture
charges with a reversible bounded diagnostic overlay; do not infer a cost repair
from successful closure or relax any guard or budget.

The reversible exclusive-charge observer and pinned pre-byte comparison are now
retained as diagnostics. Both complete reports reconcile without overflow; small
final-total variability also occurs with the observer off. Pre-byte startup
passes near 311414 while the current candidate remains Resource. Most lost
allowance (about 26872 cells) occurs before capture; graph work adds only 570.
A baseline earlier-phase ledger is retained, with the current-side counterpart
still required before a paid-work simplification is selected. Temporary source
hooks were restored and removed; no product profiler, cap or guard change is
part of this checkpoint.

#### Coordinate and window-control checkpoint

The paid canonical-coordinate factory and operation-local scalar/owner/Host
chain have five passing focused controls. The connected checked-window matrix
now passes 15 tests, including genuine donor/key positives, legacy-call and
post-attempt refusals, and copied Core Host/vector/order mutations. See
[the candidate receipts](../evidence/checked-byte-windows/candidates/coordinate-host-and-window-controls/README.md).
The original startup limit remains 327680: nested cleanup passes at 327334,
while two-owner and dependent startup remain Resource. Separate alternate-cap
cost diagnostics measure deficits 6748 and 10443; they confer no default pass.
Next work addresses repeated exact source/inventory proof within one immutable
admission, then actual checked-owner static-image and remaining hostile/bounds
and affected regression gates. PR101 and whole F3 remain incomplete.

The first genuine checked-window static-image candidate compiles and encodes,
but canonical restoration refuses at normalized prepared-library reconstruction,
before owner/symbol rebinding or hostile image cases. See the
[exact red record](../evidence/checked-byte-windows/candidates/checked-static-image-first/README.md).
The next image repair must retain the full checked profile, assumptions and
Host/member relations through fresh original-source reconstruction; the legacy
wire/profile guards remain intact. This is not private-image completion.

The operation-local builtin proof candidate has passing component controls and
an actual selective-legacy source→linked independent Core positive; see
[the qualified candidate record](../evidence/checked-byte-windows/candidates/operation-local-builtin-proof/README.md).
Default startup remains 1/3: two-owner exhausts work, and dependent exhausts
work in its post-restore static library comparison (masked as InvalidRecord by
the fixture). The selective partial checker view additionally retains Host
without its complete checking inventory; old and new source authentication
agree on refusal, while the ordinary linked program passes. Restore this
internal original-view positive through exact retained-Host metadata closure;
do not accept a silent unsupported reclassification. The checked prepared-image
carrier repair remains separate. No budget, public build or runtime gate moved.

The restore-root byte witness candidate now passes eighteen focused non-startup
controls, including full checked static-image reconstruction and its hostile/work
bounds. Default startup is 2/3: nested cleanup uses 320798 and dependent discard,
including original-library correspondence and cumulative bounds, uses 325013;
two-owner discard still exhausts the unchanged 327680 allowance. See
[the tested candidate and measurement limits](../evidence/checked-byte-windows/candidates/restore-root-byte-witness/README.md).
The proposed resource-expression/context traversal was rejected without a product
patch because accepted slot contexts need not belong to the interned path set;
a complete paid fallback would erase its measured gross saving. Keep fresh
semantic admission, remaining startup and affected regression gates open. This
unmerged candidate does not complete PR101, whole F3 or runtime activation.

The bounded prepaid control-inventory candidate passes three new payment/gate
controls, the complete ordered owner-row control and the actual full static
roundtrip. It preserves no-control skipped work and fresh semantic inventory;
only unused structural payment is carried across the same lexical root call.
See [the candidate evidence](../evidence/checked-byte-windows/candidates/prepaid-control-inventory/README.md).
Startup remains 2/3: nested cleanup uses 320640 and dependent discard uses
324967; two-owner still reports Resource at 327680. Measure its current actual
prefix and failure phase before choosing another repair. No full regression,
PR101 completion or runtime activation is claimed.

Issue [#114](https://github.com/dikini/ash-lang/issues/114) interrupts the next
performance change with a current-specification row-equality repair. Preserve
PR110 and its unmerged candidates; do not bundle comparator semantics into that
ownership change. The genuine test-only baseline already demonstrates failed
idempotence with raw function representations. Compare normalized function
components consistently through the existing paid iterative queue, then verify
set/permutation/duplicate laws, pure/empty equality and hash correspondence,
complete Type/Row vectors, deep bounded work and storage failures. Refresh
affected type/Core/private-image tests and the three unchanged default startup
controls, with Clippy and independent current-head review. No full-workspace
baseline or per-PR full gate replaces the connected F-core checkpoint.

The #114 final fixed-04 batch is complete: 341 distinct selected units, 351 outer
test occurrences, all three unchanged startup-budget controls and Clippy with
warnings denied pass on one frozen source map. Fresh per-phase accounting
corrects the earlier scan-only attribution without changing product validation or
global limits. [Original and final evidence](../evidence/effect-row-comparator/README.md)
retains the genuine baseline red and both failed fixed attempts. Proceed to the
separate unsigned delivery checkpoint and independent review; preserve PR110
until this comparator correction is retained. Whole F3/F-core remains pending.
