# Scalar arena safety and correspondence

This record gives a reviewed argument for the selected Unit, Bool and checked signed-64 storage fragment governed by [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md) and [candidate A-0](semantics.md#selected-arena-contract-a-0). It is experimental evidence, not current Ash semantics or accepted architecture. The argument is not a mechanized preservation theorem or a complete compiler-correctness proof.

## Evidence and authority

[Results](arena-results.md#verification-boundary) retain the exact source and receipt boundaries. The frozen functional source manifest `833bcb70` passed 1,674 library tests, all seven public arena cases and both unchanged 64 KiB stack regressions. The later mechanical and scanner source manifest `3d351316` belongs to unsigned source commit `ffa1d8ef4178cb1e5651411162ff09c117b725f7`. Its two affected architecture checks, strict workspace/all-target/all-feature lint, 41 adapter unit plus ten backing tests, native41 and formatting all pass. The complete Original gate passes at `7a518e83230fec568978b269b1d69776ab6051c5`; [combined-delivery-2026-10-08 receipt](combined-delivery-2026-10-08/README.md) retains its exact scope. Main delivery and its focused checks remain pending. Earlier preparation receipts do not establish a fresh result on either later source.

Current [resource typing](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies), [interface evidence](../../../spec/static-semantics.md#interfaces-and-constrained-schemes), [elaboration](../../../spec/elaboration.md#validation-boundary) and [execution](../../../spec/dynamic-semantics.md) provide the baseline obligations. Resource access is duplicable; the acquired scope owns completion. Dependencies follow actual fields, captures, selected evidence and request operands. Results cannot retain the closing owner. Exact source handlers retain precedence. Ordinary values use the evaluator heap. Those facts do not themselves define general Layout dictionaries, arena storage families or object references; these are selected experimental additions.

The [cell evidence](../effect-ash/resource-scope-evidence.md#cross-stage-evidence) transfers dependency, exact-dispatch, fresh-activation and independent-Core mutation cases. The [native-buffer evidence](../effect-ash/narrow-foreign-provider-evidence.md#evidence-coverage) transfers guarded acquisition, release, terminal failure and separate host teardown experience. Neither establishes arena serialization or family safety.

The [one-shot proof register](../direct-effects/one-shot/README.md#current-proof-status), including [initial admission](../direct-effects/one-shot/SourceScheduledInitialAdmission.lean) and [finite-prefix execution](../direct-effects/one-shot/SourceScheduledM4.lean), records results for an annotated control calculus under its structural certificates and builtin cell-signature law. Its [translation boundary](../DN-0034-one-shot-kernel-soundness-and-practicality.md#context-and-evidence-boundary) remains relevant: these are not theorems for every accepted Ash program, and do not prove A-0's dictionaries, Ref relations or native publication protocol.

## Selected invariant

The connected [layout contract](semantics.md#layout-and-publication) admits only:

| Payload | Native representation | Natural alignment |
| --- | --- | ---: |
| Unit | Zero bytes; each allocation has its own object record | 1 |
| Bool | One byte, encoded as 0 or 1 | 1 |
| Int | Eight-byte little-endian signed two's-complement integer | 8 |

Ordinary Ash Int retains its usual precision; values outside the encoding range refuse allocation. Requested alignment zero means natural alignment. Other admitted alignments are powers of two at least as large as natural alignment and at most 64. Checked arithmetic includes padding in payload usage. The [backing allocator](../../../foreign-adapter/src/arena.rs) owns a stable 64-byte-aligned block and a fixed object table. Published objects are fully initialized, immutable, within the block and identified by exact owner, object and layout. Coincident addresses for zero-sized objects do not identify their distinct records.

`Layout<T>` is sealed. Its immutable dictionary binds the original foreign interface, method and witness declaration to the exact payload and producer type. Source implementations, lexical substitutes, names, scalar tags and reconstructed numeric keys cannot supply that authority. Generic helpers retain explicit abstract requirements. An authenticated pure Unit-to-LayoutWitness invocation produces independent immutable metadata; it grants no owner, state, Ref or native publication permission.

`Ref<R,T>` is opaque, duplicable and non-owning. It identifies an object under a live activation and exact layout; it carries neither an exposed address nor an owner keepalive or release action. Store retains `ObjectRef(owner, allocation site, actual payload)` provenance. Load authenticates that reference and copies the actual bytes into the scalar result. The current payloads contain no embedded owner dependencies. The broader [relational storage obligation](semantics.md#payload-relations-storage-and-copying) still requires containment checks for later payloads.

These obligations follow the selected interpretation. A source override that refuses performs no native Store. A load override may return independent data without a native Load. Reusing an earlier authentic Ref preserves its earlier object relation. An unused native fallback cannot impose a native-store precondition on the override's unused operand.

## Source and Core correspondence

The bridge in [foreign facts](../../../src/foreign.rs), [evidence validation](../../../src/evidence_validation.rs) and [provider authentication](../../../src/core/provider/external.rs) retains original declaration identity through checking. A family checks under its rigid payload parameter and original ordered requirements. Finite specialization authenticates complete Type/Row goals, original family certificates and exact prerequisite nodes in the same immutable selection plan. A lexical ID or member ordinal is only a locator.

[Specialization](../../../src/core/provider/specialization.rs) checks original forests, substitutions, freshening, occurrence slots and copied projections. Each original dictionary formal corresponds to its exact copied binder, canonical initializer and selected requirement, in order. Binder uniqueness and lexical domination remain mandatory. Authority prerequisites do not automatically become executable adapter arguments: family dictionaries have their own authenticated initializers, while ordinary helper and implementation applications retain their executable evidence production.

Source analysis has distinct borrowed Prepared and Admitted group views. They authenticate current dictionary and native-flow projections once per group. Ordinary concrete Layout occurrences additionally use the sealed original catalogue and anchor, selected producer and exact current intrinsic header. Origins describe current nodes; they do not replace original selection authority.

Direct abstract `Layout.witness` invocation differs from dictionary installation. Its original requirement, family formal, method and pure Unit-to-canonical-Witness header are authenticated. Aliases retain that lineage. After projection construction completes, an immutable loan binds the exact node and route slices; indexed original-route membership and the full current header are checked before capture receives an independent callable fact. Copying a descriptor or cloning a node slice cannot reproduce this loan. Only the exact authenticated payload's metadata slots and canonical Witness roles receive the corresponding analysis facts. Ordinary helpers may capture the callable or Witness, return that Witness, or use it internally while returning Unit or Int. Arbitrary opaque data, raw dictionaries and state/reference capabilities remain restricted.

These source views mint no independent final Layout token. Prepared scopes remain non-executable. [Independent Core validation](../../../src/core/validate.rs) must still authenticate the original certificates, whole copied flow, exact dictionary binders and domination, ordinary producer occurrences, native request operands and Store/Load relations. A different genuine same-typed dictionary with the same producer cannot replace the selected binder. Identity and fold transformations preserve these checks.

[Authority regressions](arena-results.md#authority-and-regression-evidence) cover these boundaries using genuine source and linked programs: exact and one-short budgets at prefixes 0 and 17, fresh retry, cloned slices, stolen routes, changed headers/binders, source-versus-executable denial, and dictionary substitution under both transforms. They provide finite evidence for the correspondence obligations, not a general simulation theorem.

## Publication protocol

The following rules summarize the implemented [borrowed invocation boundary](semantics.md#deferred-publication-of-borrowed-native-results). They explain its case argument; they do not add normative operational rules. `H` is evaluator state, `S` is published native storage, `q` is authenticated operation/layout/activation authority, `p` is non-owning scratch plus a prepared candidate, and `r` is an admitted result that source execution cannot yet observe. Each premise includes the production work and storage checks.

```sequent
family scalar-arena-publication:
  Prepare :=
    q authenticates the selected native Store and scalar encoding
    prepare(q, value, S) = p without changing S
    ===>
    <H, S, Store(q, value)> -> <H, S, Admit(p)>

  Admit :=
    validate_and_decode(p.output, H) = (H', r)
    ===>
    <H, S, Admit(p)> -> <H', S, Commit(p, r)>

  Reject :=
    result admission fails with evaluator state H' and p is abandoned
    ===>
    <H, S, Admit(p)> -> <H', S, TerminalFailure>

  Publish :=
    q and the candidate still match the live owner, cursor, count and full range
    initialization succeeds and one complete object record is published as S'
    ===>
    <H', S, Commit(p, r)> -> <H', S', Return(r)>
```

The rejection rule states native-storage preservation; failed admission may have consumed evaluator work or allocated unreachable heap data. It promises no evaluator rollback. Ordinary `AllocationRefused` is a separately admitted source result, rather than the terminal failure in that rule.

[Evaluator invocation](../../../src/eval/foreign.rs) validates and decodes the result before committing. Its borrowed work capability preserves the first precise failure even if an adapter swallows a charge error. A pending commit retains neither that capability nor an owner keepalive. Failure abandons it.

The [typed adapter](../../../foreign-adapter/src/arena_bindings.rs) rechecks original manifest identity, operation, dictionary, activation and live owner. It reserves observation capacity before native publication. The backing allocator rejects stale or foreign candidates before exposing the reservation to initialization. Initializer failure or unwinding panic clears unpublished reservation bytes and preserves prior objects and counters. Scalar encoding is already prepared; successful initialization publishes one plain record and updates counters without allocation or further caller code. The adapter's remaining Store observation and the evaluator's Return assignment are infallible after successful publication.

Load authenticates the live owner/object/layout, reads actual bounded bytes and prepares a copied scalar result. Its observation is committed only after result admission and a final live-activation/read-extent check. Rejected replies publish no Store or Load observation. Load does not create an object or mutate payload bytes.

## Reviewed preservation and progress argument

Preparation preserves every published object because it changes no record or usage counter and retains no owner. Admission failure preserves the same native state and exposes no candidate Ref. Commit checks freshness and the entire reservation before writing; successful publication extends the initialized immutable object set by exactly one record. Failed initialization cannot expose partial bytes through a published object. Load preserves storage and returns the scalar represented by the authenticated bytes. Exact dictionary and reference checks connect each case to the source payload type.

The source ownership relation and independently checked Core prevent an access value from escaping its owner. Resume retains the original activation. Grouped cleanup preserves exact handler/resume interpretation and restores both row caches on bounded replay failure. Normal completion and admitted owned discard perform source cleanup before one normal release. A clause's outward request is not discharged merely because the body demanded another family member. [Public storage and control cases](arena-results.md#actual-storage-and-control) observe actual reads, exact ordering and owner release, including mixed scalars and zero-sized objects.

Progress here is conditional and local: an admitted synchronous protocol step either advances, returns its declared refusal or reports a structured runtime failure, under the native assumptions below. It does not prove termination of arbitrary source programs. Divergence provides no eventual-release guarantee. Terminal host failure stops source execution, abandons pending publication or observation and quarantines the owner until runtime destruction. That host-teardown release is distinct from normal completion and does not run source cleanup as recovery.

## Assumptions, limits and remaining work

The trusted native boundary must implement checked arithmetic, Rust allocation/alignment rules, valid pointer ranges, initialization, scalar encoding, non-colliding owner/object identity and exact layout checks. The registered adapter and original manifest binding are trusted; a foreign signature does not prove arbitrary host code safe. Preparation and commit are synchronous and admit no source callbacks or concurrent mutation. [Backing tests](../../../foreign-adapter/tests/arena.rs) exercise stale candidates, partial initialization, panic rollback and non-owning aliases; [public tests](../../../tests/provider_arena_allocation.rs) connect the declared contracts to actual source execution.

Work exhaustion and detected reservation failures remain explicit. Process-aborting allocation failure is not converted into `AllocationRefused`, and deterministic host OOM has not been tested. Payload/object capacities exclude native table allocation, compiler metadata, codec scratch and evaluator heap. These repairs raised no previously calibrated phase budget, depth or stack limit. The separate [calibrated-admission policy](calibrated-admission-2026-10-08/README.md) records the earlier user-authorized larger public-driver allowances and finite margins; it is empirical admission policy, not a universal complexity or optimization result.

The private [aggregate codec](../../../foreign-adapter/src/arena_codec.rs) remains preparation evidence for packed and nominal encodings. It does not admit aggregate or Ref-containing stored payloads. Reference-containing graph sharing, deep or recipient-arena copying, borrowed views, owner transport and wider memory policy need additional relational and correspondence evidence.

Later demands whose payload mentions a fresh inner owner still have an open lexical placement obligation: an outer family's native fallback cannot be specialized outside that owner's scope. The [inner-owner refusal sketch](../../../tests/fixtures/provider-experiments/arena-typed/inner-owner-source-refusal.ash) records the pressure; no placement alternative is selected here, and primitive scalar delivery does not settle it. Production adoption requires the proposal, decision and specification workflow. The [authoring blueprint](arena-blueprint.md) and [results](arena-results.md) describe the bounded executable experiment within these limits.
