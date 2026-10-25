# CP-0025: Lexical region construction and paired allocators

- ID: `CP-0025`
- Status: accepted
- Related: [TASK-0055](../tasks/TASK-0055-lexical-regions.md),
  [DN-0054](../design/DN-0054-base-lexical-region-memory-contracts.md),
  [DN-0055](../design/DN-0055-algebra-of-regions-lifetimes-and-ownership.md),
  [AD-0012](../decisions/AD-0012-proof-development-feedback-and-build-reuse.md),
  [M2 #53](https://github.com/dikini/ash-lang/issues/53),
  [R1 #65](https://github.com/dikini/ash-lang/issues/65),
  [R2 #66](https://github.com/dikini/ash-lang/issues/66),
  [R3 #67](https://github.com/dikini/ash-lang/issues/67),
  [R4 #68](https://github.com/dikini/ash-lang/issues/68),
  [R5 #70](https://github.com/dikini/ash-lang/issues/70)

> This accepted transition is not current Ash. The matched finite model, frozen gate and delivery passed independent review. [PR #146](https://github.com/dikini/ash-lang/pull/146) at `aee02227b69fb6cbbd00c23904ffe2a0c7df6924` retains the contract and proof; retained verification and R1/R2 acceptance are complete. R3 implementation is active and partial.

## Current behavior

Main `0d8df03d4db2e70294487fc2e61f3629ff33b246` has ordinary immutable construction, mathematical integers, lexical closures and guarded recursive data, but no selectable region storage. The evaluator uses a `Vec<HeapCell>` for tuples/constructors/recursive slots, separate boxed tuple fields, inline closure values with host-managed environments, and separately owned Bytes/String/BigInt backing. Existing scoped owners, actual-dependency analysis, exact effects, one-shot capture/resume/discard, ordered cleanup, independent Core validation and body-free summaries supply the foundations.

Address is an inert pointer with no inferred ownership or typed initialization authority. Slim FFI binding modules perform ordinary checks and state foreign assumptions. Neither an Address nor an effect signature proves native memory validity.

## Proposed behavior

### Complete interface and fixed association

The approved conceptual interface is:

```text
RegionAllocator<R> {
    allocate : Request -> Storage<R>
    release : Unit -> Unit
}
```

Both members bind to the same implementation/state for R. A successfully initialized region's type and allocation/reclamation discipline cannot change during its lifetime. The owner controls release invocation; a change of allocation default does not redirect release. One implementation may serve several regions, but releasing one preserves the others and does not implicitly destroy shared allocator state.

M2 uses lexical ownership and bulk reclamation. The default is host-backed. A fixed-capacity instance follows the same contract; its capacity is a bound on the managed storage specified by that implementation, not a claim that evaluator/control overhead vanishes. Physical allocation and reclamation strategy remain handler/module responsibilities. No automatic alternate-region fallback is introduced.

### Exact candidate source forms

Add these two forms. `primary_expression` and `block` retain their existing meanings:

```ebnf
region_expression ::=
    "region" "<" upper_identifier ">" identifier
    [ "=" primary_expression ] block ;

region_selection_expression ::=
    "using" primary_expression block ;
```

`region<R> r = provider { body }` establishes one fresh region. The provider expression has the ordinary pair shape `(allocate, release)` representing the two members of `RegionAllocator<R>`; it is not a new first-class handler object. Each component is an ordinary monomorphic function after instantiation. Its complete type is `(Request -> Storage<R> ! ea, Unit -> Unit ! er)`, with actual rows `ea` and `er` inferred/checked by existing rules. Parentheses in this type denote an ordinary tuple, not a source effect-row existential.

Before provider evaluation, reserve a fresh prospective activation a and bind fresh kind-Type R to that same a in lexical instantiation for the provider's expected type and body. The prospective record is not live access or a published completion owner. The term r is available only in the body. The provider is evaluated once under the preceding live allocation context; its function records, pair and captured state are therefore constructed there. R cannot occur in the provider evaluation's outward effects/result other than the retained member contracts, and the initializer has no live r access. A source request to a not-yet-established R cannot be admitted as setup. Setup failure publishes no region access or completion owner.

After complete preparation, publish that same prospective activation a; never replace it with another identity after the provider closures captured R. Then r denotes allocation/selection access to R. Copies of r do not acquire release authority. The owning region frame retains the paired release member; ordinary callers cannot invoke release through r. Binding-module contracts still govern any other aliases a provider exposes to its underlying foreign state; no general foreign-memory-safety claim follows.

When `= provider` is omitted, elaborate the selected host-backed default provider with default parameters. Explicit provider construction can capture a configuration or fixed-capacity state prepared in the enclosing scope. This is source convenience over the same pair and lifecycle, not a second mechanism.

`using r { computation }` selects an existing live region for new construction in that computation and its called helpers. It acquires no owner, relocates no value and restores the preceding selection on return. It lowers to ordinary action-local handlers associated with that r, as defined below. Existing lexical scope/name-resolution rules apply; r may be a lexical capture or a parameter with known actual dependencies.

Ordinary blocks and function calls acquire no regions. The closest enclosing live selection supplies the default. A closure's own record resides where it was created; calling it does not move/recreate that record. Its fresh constructions use the caller's selection unless its body explicitly selects another region. Actual captured dependencies remain unchanged.

### Root configuration and completion

The generated entry wrapper establishes one host-backed root before ordinary program construction. Its configuration is host entry parameters/static configuration metadata, with defined default parameters when omitted. This proposal does not admit arbitrary source computation before any region exists. Custom source regions/providers are constructed under an already live enclosing region.

The root retains backing through entry-result observation and all required completion. The selected host implementation performs its setup and supplies the initial provider interpretation using established host startup/control storage under existing limits. These administrative records are not ordinary Ash objects secretly placed in a fallback source heap.

An ordinary allocation refusal at entry is handled by the generated entry boundary using checked continuation disposal and the existing host observation/reporting foundation. Its host result distinguishes declared allocation refusal from internal exhaustion; it need not allocate an Ash error constructor in the failed root. If required close cannot complete, report that actual failure rather than fabricate a clean refusal. This adds no general source exception/unwind form.

### Effect rows and explicit Core

Allocation is an ordinary tracked effect. Surface `! {}` includes the purity-compatible defaults adopted for this milestone, namely the default-allocation requirement; `! {Console}` includes that default plus Console. The absence of an explicit row has the same existing annotation behavior with this default expansion, not general body-row inference. No other implicit purity effect is selected here. Additional observable effects of an allocator/handler remain in the actual computation's visible contract.

Use one ordinary monomorphic private/generated `DefaultAlloc` effect for implicit construction. If retained in elaboration, `Alloc<R>` is only a private/generated allocation-facing alias of the same owner service, not a separately interceptable public route:

```ash
effect DefaultAlloc {
    allocate : Request -> StorageView
    context : Unit -> RegionView
}

effect Alloc<R> {
    allocate : Request -> Storage<R>
}
```

These declarations select operation shapes. DefaultAlloc is the private generated default-service API; its context query adds no user-facing region feature. Generated handlers cover both operations. Alloc<R> has no independent provider-dispatch semantics; release remains an explicit member of the complete RegionAllocator<R> contract. `StorageView` is the same supplied storage without a source-visible R index, not storage without a region dependency. The full interface still includes release, retained by owned completion.

For each source value-function computation annotation, expand the default requirement before checking. A written default member is not duplicated. Existing row-tail/lacks obligations apply exactly as if the default member had been written; expansion does not guess exclusions or change row unification. The required pure outer `P -> Q` shape of an effect operation declaration is not itself a value-function computation annotation; nested value-function types inside P or Q receive the ordinary expansion. Compiler-supplied host/control leaf contracts state their actual full rows directly.

Checked summaries and Core retain complete explicit rows. Extra implementation effects propagate through ordinary handler typing. For example, an allocation clause that performs Console makes the handled computation require Console; surface elision of allocation cannot remove it. Purity classification and the request-capable Core dialect name are not equated.

Core contains no implicits: region/provider operands, full rows, request targets, handler clauses, views and construction steps are explicit. Stored closures remain rank-1: their ordinary latent `DefaultAlloc` effect is interpreted by the caller's explicit handler; they do not contain a hidden universal region binder.

### Explicit lowering and typed storage

A region's body is evaluated with a generated ordinary `DefaultAlloc` handler whose allocate clause delegates to `RegionAllocate(r, request)`. `using r` installs that handler with the explicit selected operand. A retained `Alloc<R>` projection delegates to the same primitive and is private/generated; it cannot provide another callback execution route. These handler nodes are explicit Core, not copied captured handlers. Public effects performed by provider code retain ordinary exact dispatch; this proposal introduces no public allocator-handler override or equivalence mechanism.

The `DefaultAlloc.context ()` query returns the actual selected region as a small private `RegionView` carrying its access dependency. Its operand is Unit; it does not transport the action or captured younger fields. At a cleanup registration site, Core explicitly evaluates the original action once, performs this query, and retains both results in the existing owned cleanup frame. The queried view is not a function, existential callback row or captured-handler package.

**Narrow new region primitive:** `RegionAllocate(context_operand, request_operand)` returns `StorageView`. Both operands are explicit Core children. Its row is the union of their rows with the allocation requirement `{DefaultAlloc}`. Runtime interpretation is directed by the supplied live region activation to the same region owner's saved allocate implementation; it does not ask for an ambient default or dynamically unpack an exact-R callable type at the helper. The region record already retains that typed implementation, its lexical R instantiation and complete allocate/release rows.

**One canonical provider execution position.** Normal construction and cleanup use this same owner-targeted service. `RegionAllocate(a, q)` separates the serviced continuation segment from the supplied owner's interpretation position and retains it as a one-shot return continuation, with the outside control retained separately. The saved allocate member runs at that owner position under its stored lexical environment/instantiation. The owner service explicitly supplies the preceding allocation context saved at region setup as the ordinary callback call-site context; this is not a definition-time-default exception. That saved selected view can differ from the owner-parent edge when setup occurs under explicit selection, and the two facts are retained separately. Body-local handlers above the owner position stay in the serviced segment; they do not interpret the provider's backend effects. The provider's own action-local handlers and handlers available outside that owner position dispatch normally. Thus provider bookkeeping construction uses the preceding allocation context, not a recursive implicit request to the region it supplies.

On a successful callback result, the explicit driver validates/registers storage for a, then returns through the one-shot service continuation and restores that segment's selection, pending initializer and ordinary control. It neither duplicates owner frames nor overwrites outside clause state. Callback effects may capture this computation through existing one-shot rules; refusal/abandonment must satisfy those rules and all required completion. No additional unwind or implicit resumption is introduced.

During owned close, the same owner service remains available at its structural interpretation position through the required cleanup and release completion, with an explicit live/closing access operand. The target owner remains live through the request/return or closing service, as required by its completion obligation. Its presence is part of the region primitive, not restoration of a removed source handler. The same preceding allocation context and callback lexical environment apply. A public backend handler required there must survive or be supplied action-locally; if discard removed that required interpreter, ordinary cleanup-context checking rejects the close. An outer same-instance handler cannot replace it. Both owner-targeted service admission and this close availability are new narrow region-Core validation rules, not claims that existing ordinary handler syntax alone already implements them.

The region Core boundary includes provider evaluation, allocate and release rows in its outward row unconditionally, as ordinary handler clause accounting does. Its allocation-service discharge additionally requires the existing owner/dependency analysis to establish that every owner-targeted invocation has a live protecting region boundary in the admitted control/close chain. A request to an enclosing selected region is interpreted by that supplied owner; its provider row remains included by the enclosing region boundary. An unknown/missing protecting owner cannot be hidden by discharging the default effect. These are new explicit region-specific validation obligations, not a new source effect-row inference rule or a proof of interpreter equivalence from row inclusion alone. Thus a helper can retain the monomorphic DefaultAlloc contract while a custom provider's Console or other effects remain visible in the containing checked region computation.

The region owns the saved release member separately from those body handlers. Its normal or abandoned close invokes that member through the existing owned-completion rules. Required backend interpretations must survive or be installed ordinarily inside the release action. A closure containing an effect request does not capture its handler.

Existing tuple/constructor/function/recursive Core shapes supply layout and evaluation order. Their allocation sites lower to: evaluate the required children; form a private Request; perform the explicit allocation request; validate the returned storage facts for the saved layout; initialize locally; expose the completed value. No allocator receives the source fields or captured values. Newtype conversions still erase.

A request has logical fields `(usable_bytes, alignment)` in a private immediate runtime descriptor, using checked implementation-size quantities, with no Ash tuple/BigInt allocation needed to form or copy it. Binding the request to an invocation attaches the explicit selected owner/driver reference as private call metadata; it does not add source payload fields or arbitrary user authority. That metadata carries its actual owner dependency and is validated against the saved requested activation. Independent requirements may reach that owner's admitted interpreter; younger construction fields still stay local. Alignment must be nonzero and supported by the selected implementation; overflow and unsupported layouts are not successful storage requests. No source fixed-width integer family is introduced. Any source-facing inspection/conversion follows ordinary value/effect rules, not an exemption making arbitrary Int/error construction free.

**Backing-to-storage adaptation is explicit.** A module's low-level host/FFI leaf can return a backing locator, extent and alignment under its contract. That leaf is not the approved complete allocator interface. The bound allocate implementation's private driver takes explicit `(selected_owner, saved_request, returned_backing)` operands, checks the live/closing owner and reply requirements, registers a fresh pending allocation record under that owner, and returns `Storage<R>`/`StorageView`. This adaptation realizes `RegionAllocator<R>.allocate : Request -> Storage<R>`; it does not replace it with a public Backing API. The provider's R type index or raw Address never creates an ownership/initialization fact by itself. Host functions that implement the interface receive the bound invocation metadata explicitly; no live source r needs to be captured before publication.

Freshness/disjointness and physical validity still rely on the module's storage contract; record registration does not prove arbitrary foreign pointers safe. Invalid association, replay of an initialized record or insufficient stated extent fails typed construction. Publication and release use the registered record/owner, not a later current default.

Storage and StorageView use the same opaque runtime representation: the actual region activation, the region-owned allocation-record reference, usable extent/alignment and backing locator. The record has pending/initialized disposition. The view conversion changes no backing, association, lifetime or initialization state. This is private construction state, not a general ownership token/registry or public raw-memory API. A reused initialized record cannot be initialized again. The provider contract supplies freshness/disjointness and physical validity; an arbitrary Address cannot establish them merely by being wrapped.

Pending request, field values and the expected typed layout are retained in explicit evaluator control, so capture does not require reconstructing them from source. Layout metadata comes from the validated code/value representation, not a source-supplied assertion. Provider storage must actually back object records, owned persistent buffers and closure storage. Continuing to allocate these independently in the old heap while charging a quota does not implement this proposal. Existing locations may become private region-backed locators; their source semantics remain unchanged.

Tuple/constructor shapes, recursive slots/aliases and function templates are reused. Large-integer digits, Bytes/String backing and newly retained closure storage use supplied storage; temporary arithmetic/control work may use the documented host foundation under existing ledgers. Mathematical integer results are unchanged. No source heap/object relocation is introduced.

For zero requested bytes, success promises no readable byte. Record identity/accounting remains valid, and the typed layout must actually require zero readable storage before such a reply can initialize it. Concrete layouts include all owned persistent representation required by the object; a zero payload does not excuse unaccounted ordinary object storage.

### Small-step operational contract

Write `CONFIG(H, E, c, K)` as in the current specification. H additionally contains region-owned allocation records; K retains explicit region/selection/initialization and existing cleanup/capture state. The following named transitions refine current evaluation; they are not a second machine.

| Transition | Preconditions and state change |
| --- | --- |
| `EnterPrepare` | Reserve fresh prospective a and bind R to a in initializer lexical instantiation; evaluate the provider once in preceding allocation context. Prepare administration without publishing live r/completion authority. Failure publishes no owner; reserved identities need not be reused. |
| `EnterLive` | Complete preparation and publish the same a captured by provider closures, with its fixed pair/discipline and one completion frame. Bind r to live access; enter explicit handlers. |
| `SelectEnter/Return` | Require live actual access a; install explicit default forwarding to the canonical owner service for a. Return removes that handler and restores enclosing control; no new region or relocation. |
| `ContextQuery` | An explicit Unit request returns the selected dependency-bearing RegionView; cleanup retains it beside the already evaluated action. No action/payload crosses this query. |
| `RegionAllocate` | Evaluate explicit context/request operands; retain the serviced segment and outside control separately; invoke the supplied live/closing owner's allocate member at its canonical interpretation position with saved lexical instantiation and preceding allocation context. Its return/driver path restores the serviced segment once. Body-local handlers do not move into provider control; no ambient lookup or callback-row package. |
| `Request` | After required children evaluate in order, create the immediate independent descriptor, retain children/layout in pending control and perform the exact explicit effect request. Existing request selection moves the captured segment into one clause owner. |
| `Supply/Register` | Under the module contract, obtain fresh disjoint backing. The explicit driver `(a, saved_request, backing)` checks the actual requested live owner and extent/alignment, then registers one pending record and returns Storage for a. No readable object exists yet. Refusal creates no successful record. |
| `ResumeStorage` | Consume the ordinary continuation capability once and restore its saved regions, selections and pending construction. Check actual selected region/record/layout compatibility. Do not replay operands or acquire another region. |
| `Initialize` | Write through the pending record using locally retained fields/captures and their actual dependencies. No outer request transports those fields. A mismatched/reused record is an internal invalid-construction failure, not another source authority. |
| `Publish` | After complete initialization and reply preparation, mark the record initialized once and return a value carrying its actual residency plus required field/capture dependencies. Strict children must have completed. |
| `Project/Use` | Require initialized storage and valid actual dependencies. An independent referenced outer value may shed a container dependency; an inline view retains it. No view or alias changes placement. |
| `Call` | Use ordinary lexical function environment/application. Its explicit default-allocation requests meet the caller's handlers. The existing closure record and captures do not move or reinitialize. |
| `Capture/Resume` | Split a captured segment from outside caller/clause control; retain both separately. Move/restore the segment and its same activations/pending state once, splicing it above the saved clause continuation. Never overwrite outside frames or reset shared published state. Owner enclosure is not recomputed from a new visible stack. |
| `Discard` | Existing checking proves owned close skips no outside/running completion and has compatible interpreters. Consume the capture once; revoke unpublished access and account/dispose pending records under their allocator contract; close inner obligations in structural order. Do not replay abandoned body code. |
| `CloseBegin` | A normal saved result must not depend on the closing region; required inner cleanup/dependent uses complete while backing is live. Entry observation is completed before root close. Begin the saved release action once; keep its unfinished completion required. |
| `CloseFinish` | On the release contract's normal successful completion, revoke live access and bulk-retire all remaining records for that region; its storage is released/reusable as promised. Other regions and shared allocator state remain valid. Restore enclosing control. No copied access/reference owns another close. |

Refusal follows ordinary handler control: the clause can resume only with valid successful storage, or, if admitted, discard and return its handler's ordinary refusal result. Already performed effects are not rolled back. Refusal reporting needs pre-existing/surrounding storage or the documented host entry reporting foundation. Internal work/control/storage exhaustion retains its distinct terminal boundary and existing limits on source-cleanup guarantees.

A normally returning release action establishes the physical reclamation promised by its module contract only under that contract's host assumptions. Reporting, divergence or failed native behavior is not proof of physical release; this proposal adds no quarantine/disposition protocol to repair violated assumptions.

### Recursion and cleanup

Recursive groups keep current guardedness. Preallocated data slots are private/uninitialized; direct-function templates and slot locations enter the recursive environment; guarded initializers run in source order; each completed member stores its alias. The group body begins after initialization. Recursive fields may refer to slots through the already admitted constructors/tuples/delayed function bodies, but cannot force or transport unfinished access through forbidden forms. There is no new whole-group transaction or same-region-only restriction. Abandonment exposes no unfinished graph; earlier published values remain valid.

Data cycles do not form resource-owner cycles. Bulk release does not recursively chase cyclic references to decide which same-region object to free. The strict older-owner rule for retained Cell contents is unchanged.

Cleanup uses its explicit saved RegionView after inner selection/region restorations. For helper-created cleanup, the registration-time Unit context query supplies that view without requiring a hidden R binder in the helper's function type. The generated action-local DefaultAlloc handler has two explicit clauses: `context ()` resumes the saved view; `allocate q` resumes the result of `RegionAllocate(saved_view, q)`. Its handler nodes, saved operand and primitive call are present in Core. The typed region owner supplies the exact implementation/rows, so RegionView does not conceal a polymorphic callback package.

This adapter is admitted only with the explicit saved region association and the canonical owner service available in the admitted close chain. It does not prove equivalence between arbitrary source handlers or reconstruct a removed public backend interpreter. If a required public backend handler was removed, an outer same-instance handler or the region service cannot substitute: existing `effect.cleanup-context` rejection applies. Ordinary normal completion can use its surviving required handlers. A running action and unfinished close remain non-abandonable.

For example, let outer Console handler H surround `region<R> r = provider`, where provider.allocate performs Console, and let inner Console handler J surround a construction in the region body. Normal DefaultAlloc forwarding reaches the owner service; provider Console selects H, not J. A cleanup registered inside J may itself perform Console and remains subject to ordinary availability checking for J. If that cleanup instead allocates, its generated action-local forwarding reaches the same owner service, and provider Console again selects H. Discard that removes J can admit this allocation-only cleanup when H and the owner service remain available; discard that removes required H cannot replace it with another outer Console handler. An action-local Console handler inside the provider would take precedence in both routes. The provider's Console requirement remains visible in the region's outward contract regardless of which route called it.

The release member retains the original R-associated implementation/state and actual transitive effect requirements; it is never redirected through the current default. This completes the proposed private context/owner-invocation bridge. Source/Core correspondence must verify its explicit operands, owner discharge, handler-compatibility conditions and row propagation; it is not assumed already implemented or proved.

## Semantic delta and resulting specification truth

After complete implementation/integration, ordinary construction has explicit checked allocation effects and actual selected-region backing; implicit surface defaults expand before Core; lexical declarations and explicit selection control new placement; region type/discipline stays fixed; closures retain actual dependencies and allocate under callers; recursive immutable graphs use checked pending initialization; matched allocation/release and ordered bulk close preserve owners and other regions. Region and object access never outlive permitted lifetime merely because bytes remain allocated.

This changes current source annotations, construction lowering, runtime value/backing representation and entry wrapping. It does not change integer mathematics, newtype erasure, exact handler selection, rank-1 source values, guardedness, existing Cell ordering or the slim FFI assumption boundary.

### Integer residency admission

`Int` remains mathematical and unbounded. Its type alone does not establish
region independence. Known immediate literals and intrinsically bounded leaves
are independent when their complete persistent representation is immediate.
Large literals retain the selected region that backs their digits. Aliases,
projections and calls preserve actual dependency summaries; unknown Int results
have no blanket scalar exemption. Cell storage/read and request results must
preserve these facts rather than copy host BigInt ownership or erase residency.

Potentially large addition and multiplication retain selected-region residency,
even if a particular execution produces an immediate result. Without existing
facts proving independence, admission rejects that result escaping its region.
For example, the body `42` may leave a host-backed `region<R> r`, while the body
`20 + 22` is conservatively rejected at that same boundary. Projecting a known
immediate field preserves its independence; applying addition to projected
operands does not establish a bounded result. These are required admission
examples for the next implementation, not claims of current executable support.

This deliberately changes lifetime admission, not mathematical results. Runtime
small-result representation does not retroactively authorize a rejected escape.
No constant/range propagation or implicit copying/relocation is introduced, and
existing arithmetic escape fixtures must not be silently rewritten. The private
immediate encoding must cover byte values and checked implementation-size request
metadata without recursive allocation to formulate requests; its exact range is
an implementation choice, not a public numeric type or a bound on `Int`.

## Affected specification areas

- [lexical-structure](../../spec/lexical-structure.md), [syntax](../../spec/syntax.md): `region`/`using`, provider-pair checking, default-expanded computation annotations.
- [name-resolution](../../spec/name-resolution.md): fresh R/r scope, provider initializer restrictions and ordinary imports.
- [static-semantics](../../spec/static-semantics.md): expanded rows, allocation/residency facts, region/selection checks, constructor/call effects, summaries and cleanup correspondence.
- [elaboration](../../spec/elaboration.md): explicit provider arguments, handler projections, typed request/init/publish, owned close and full Core validation.
- [dynamic-semantics](../../spec/dynamic-semantics.md): actual backing, root lifetime, immediate descriptors, transitions above, refusal/control and observations.

## Interactions and non-goals

Use existing computations, effects, parametricity, module opacity, typed Core, owner/capture graphs and ledgers. Ordinary source contracts/FFI binding assumptions govern host allocation and release; no proof of malloc or foreign memory safety is claimed. New private representations are only those needed for the agreed construction boundary. No public raw-memory API, general token/registry, row-inference expansion, higher-rank callable scheme, source per-object free, relocation, general copying, alternate-region recovery, GC/RC implementation, concurrency, NUMA policy, backend matrix or broader DN-0055 theory is included.

## Required evidence

R1 proves the bounded transition preservation below and records assumptions/correspondence limits. R2 and R1 must describe the same operations before acceptance. Product evidence under R3/R4/R5 must include:

- Default/root, nested selection and imported helper construction; a stored closure created in A called under B and A without moving its record/captures.
- Actual provider-backed tuple/constructor/closure/owned-buffer storage, including large Int/Bytes/String; fixed-capacity refusal preserves previous objects. A quota-only wrapper around unrelated allocations fails this criterion.
- Nonrecursive first-root/request/reply/failure bootstrap, exact/short existing-ledger checks and no hidden source heap.
- Positive local initialization of outer storage with younger locally valid captures; rejection of outward younger payloads, escapes, stale views, invalid Cell retention and owner cycles.
- Guarded cyclic data, sharing, pending initialization capture/resume and abandonment; no unfinished reads, repeated publication or accidental relocation.
- Normal close, allocation refusal and outer discard; same release implementation/state despite another default; required cleanup before release; no duplicate release; shared allocator isolation; removed-handler rejection and action-local positive cases. Provider backend effects must select the same owner-position interpreter for normal and cleanup allocation, including the H/J Console case above.
- Expanded full rows in summaries/Core; additional observable custom-allocator effects visible; no unresolved Core defaults or broad inference changes.
- Independent Core/transform/image reconstruction, source diagnostics, existing regression boundaries, focused PR verification and the scheduled R-core/R-final full gates. No new benchmark framework.

## R1 finite model and handoff

The proof assignment is a finite sequential transition model, not a whole-compiler or foreign-allocator theorem. Use a bounded universe of region IDs, allocation IDs, value/field ports and control-owner IDs. Sizes/capacities can be naturals; finite support, rather than a physical address-space model, bounds the relevant maps. A fixed-capacity handler is one admitted contract instance; host supply/refusal is abstract nondeterminism satisfying the same local guarantees.

State components:

- Region records: phase `preparing/live/closing/closed`, enclosing owner, fixed implementation/discipline tag, owned close status and allocation set.
- Allocation records: owning region, extent/alignment, private/initialized/retired status, abstract layout, field/reference dependencies and pending initializer progress.
- Values/roots: actual residency and required access dependencies, distinguishing existing references from inline views.
- Control: ordered outside caller/clause frames and separately owned captured/service segments, explicit selected association/RegionViews, owner interpretation positions with saved preceding allocation contexts, pending construction, saved results, cleanup status and capture ownership `live/consumed`.
- Provider state: available capacity or abstract host supply, successful allocation identities and release accounting sufficient to state disjointness and isolation.

Transitions are exactly `EnterPrepare`, `EnterLive`, `SelectEnter/Return`, `ContextQuery`, `RegionAllocate`, `Request`, `Supply/Register/refuse`, `ResumeStorage`, `Initialize`, `Publish`, `Project/Use`, `Call`, `Capture/Resume`, `Discard`, `CloseBegin/Finish`. Recursive initialization is repeated pending-slot/alias progress within these construction transitions; it is not an extra collector or rollback protocol.

Local assumptions, each stated separately:

1. Successful provider replies are fresh/disjoint where required, have sufficient extent/alignment, preserve earlier live storage and bind to the requested region's paired release discipline. Refusal changes no published allocation.
2. Release fulfills its declared region-specific backing contract when it completes successfully; it preserves other regions. No theorem assumes that every release terminates or native code cannot violate its contract.
3. Validated source/Core admits only guarded reads, actual-dependency-safe uses/escapes and existing ordered owner enclosure/Cell contents. State those as local access/transition premises; do not assume the entire next state is well formed.
4. Capture/discard obligations and interpreter compatibility come from the existing one-shot/cleanup contract. Represent the moved/closed owners explicitly and prove the region extension preserves them. Do not import the entire experimental ownership algebra.
5. Host control preparation is bounded/available for a successful transition; internal exhaustion has no source-cleanup guarantee and is modeled as terminal disposal, not ordinary allocator refusal.

Required invariants/preservation:

- Readable roots refer only to initialized, nonretired storage whose actual region/access dependencies are valid.
- Every allocation has one owning region; its implementation/discipline association is unchanged after live publication; aliases/views do not relocate.
- Pending construction is privately owned; resume preserves its identity/progress; abandonment publishes no unfinished access; initialized records are not initialized/published twice.
- One-shot control and region completion owners are neither duplicated nor lost by admitted transitions. Closing requires dependent completion and cannot skip outside/running obligations.
- Resource-owner edges stay strictly enclosing/acyclic; immutable data edges may cycle.
- Bulk close retires exactly that region's remaining allocations only after required uses/cleanup and preserves other regions.
- Refusal preserves previous published objects and operand-effect history; internal exhaustion is not mislabeled as recoverable refusal.

Prove preservation by the concrete update for each transition and its local premises. Supply counterexamples for omitted initialized-state, dependency, one-shot, close-order and allocator-isolation premises. Do not encode `well_formed(next)` as a provider or transition assumption.

The correspondence report maps each transition to the source forms and explicit Core operands above, including context query, canonical owner-position invocation/return and row discharge, public backend-interpreter availability, prospective identity capture, backing registration and preserved outside continuation. It must check those mappings rather than treat them as a model-only safety claim. A frozen Lean integration receipt under AD-0012, independent review and reconciled R2 contract remain acceptance gates. Use a small standalone module/minimal imports and the existing integration runner/cache; no proof run was performed to draft this file.

## Acceptance and evidence

The acceptance owner accepted the semantic content on 2026-10-25 after matched
model/correspondence review and independent audit of the actual frozen gate.
The reviewed pre-adoption proposal SHA-256 is
`4455ca6657439037b02e8164c61e73e99e91da2aa05419741dd1421b53a9c796`;
this adoption changes status and evidence metadata, not that semantic content.
The [model guide](../design/lexical-regions/README.md),
[correspondence and assumptions](../design/lexical-regions/correspondence.md) and
[gate/transfer record](../design/lexical-regions/evidence.md) identify the matched
eight modules, 195 reports, independent review and frozen gate receipt.
The gate validated eight cached artifacts and performed no fresh module compilations.

The accepted proof scope is finite sequential `Coherent` preservation under
local admissions and stated source/Core/module assumptions. Context query is
observational; typed RegionView results, per-action saved-view payloads and
generated adapters remain source/Core obligations. Effect-row discharge,
lexical handler compatibility and physical provider validity/isolation are not
proved by finite preservation. Acceptance does not claim a native allocator
or compiler-correctness theorem.

Exact proof-source/registration transfer and exact-head delivery review passed.
[PR #146](https://github.com/dikini/ash-lang/pull/146) at `aee02227b69fb6cbbd00c23904ffe2a0c7df6924` retains the reviewed tree; independent retained verification and
author/PM readback completed R1/R2 acceptance. R3 implementation has begun with
source/Core/runtime control plumbing and actual supplied host tuple backing.
Native/custom backing, other required representations, root observation-before-release
ordering and full construction/completion acceptance remain pending; normative specification
changes have not begun.
