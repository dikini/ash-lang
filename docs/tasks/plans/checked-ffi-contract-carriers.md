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
and unchanged startup limits. Review/integration/acceptance remain pending.

Generic actual/row, recursive/shared payload and deeper resource closure remain
later red-driven controls unless essential to this fixture. ResourceApply already
has resolver/contract traversal. Whole F3, F-core, checked owners, copy/lifecycle,
image/runtime activation, deployment and Main integration remain pending.

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
