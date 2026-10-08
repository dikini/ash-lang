# Scalar arena authoring blueprint

Authoring guidance for the selected Unit/Bool/checked signed-64 experiment under [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md) and [A-0](semantics.md#selected-arena-contract-a-0). This is experimental authoring guidance, not current language truth. [Results](arena-results.md) distinguish observed behavior, foreign assumptions, excluded work and the exact verification boundaries.

## Start with an independent result

Use the ordinary API in [arena.ash](../../../tests/fixtures/provider-experiments/arena-typed/arena.ash):

```ash
import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, Int>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (8, 1)) {
match (Memory.allocate (arena, 41)) {
Memory.Allocated(reference) => Memory.load (arena, reference)
Memory.AllocationRefused(error) => 0
}
}
```

The fresh native receipt returns `Completed(41, Closed)` after an actual Store, Load and normal release. Configuration bounds payload bytes and object slots. Ref grants duplicable access while its lexical owner lives, owns no release action and supplies no lifetime keepalive.

Helpers require `StorageProvider<R,T>` and `Native.Layout<T>`. Imported ordinary implementations also meet existing instance-head and prerequisite-decrease rules; [scalar_implementation.ash](../../../tests/fixtures/provider-experiments/arena-typed/scalar_implementation.ash) uses concrete `Input<Int>` and explicit prerequisites. Syntax alone does not establish universal storage coverage.

## Define finite storage through ordinary providers

The library defines primary ArenaProvider/ArenaOps acquisition/completion and `family<Payload> where Native.Layout<Payload>` for StorageProvider/StorageOps. The template checks under a rigid payload parameter; complete finite demands select exact ordinary handlers. This adds no operation-local polymorphism or universal row subtraction.

The registered Layout table admits only Unit, Bool and signed-64 Int. LayoutWitness and Ref remain opaque; source impl/lexical evidence cannot forge Layout. Ash Int retains ordinary precision; out-of-encoding values refuse allocation. Wrong owners and numeric tuples grant no reference/layout authority. Preserve actual selected-handler behavior: an override may refuse without Store, return independent 99 without Load, or reuse an authentic earlier Ref without another Store.

## Preserve exact authority through checking and capture

Collect every original acquire/finish/primary/family namespace before allocating copied identities. Avoid original, substitution and previously allocated identities. Refresh post-zonk rows from original recipes and publish the complete group atomically. Keep original plans, complete Type/Row goals, prerequisite edges, method order and binder claims; final Bind/Function/Request/Variable nodes retain exact operand edges, uniqueness and domination.

A family prerequisite justifies selection. Its dictionary has an original formal, final binder and authenticated initializer. An ordinary helper/implementation application additionally needs reachable executable dictionary production and its original evidence anchor; do not eagerly lower unused family evidence into orphan executable nodes.

Direct `Layout.witness` is invocation rather than installation. Authenticate its actual original requirement, formal, method and pure Unit-to-canonical-Witness header. Preserve that provenance through aliases. Its result is independent immutable metadata; it grants no State/Ref/storage/native/final-admission permission. Ordinary helpers can capture the witness or its callable and use the corresponding rigid payload metadata, including helpers whose final result is Int or Unit. General opaque data and raw dictionary values remain conservative.

Source capture consumes an immutable loan of the completed authenticated projection's exact nodes and routes. A copied descriptor is insufficient. Check the indexed original route, variable binder, canonical Witness/payload and full pure header before producing a source-analysis callable fact. Seed only the exact authenticated payload's metadata slot. Already-proven independent captured Witness values still require the canonical original Witness role.

Prepared and Admitted scope views remain distinct and reauthenticate current dictionaries/native-flow projections once per group. Concrete ordinary Layout occurrences separately authenticate the original catalogue/anchor, selected producer and current intrinsic header. Current origins are metadata, not replacement original-span authority. None of these source routes mints a final Layout token. Independent whole-program validation still checks copied mappings, original occurrences, dictionary ownership and Store/Load relations. Equivalent names, reconstructed manifests, cloned slices and a different genuine same-typed dictionary cannot replace that proof.

## Interpret control at the owning phase

A group shares body, answer and output row. Subtract provided instances from the shared body only, then union clause demands interpreted through each exact native instance. Another demanded member does not discharge a clause's outward request. Acquire/finish use the primary native instance.

A surviving owning handler retains its genuine source members for cleanup without exposing native interpreters outside selected clauses. Replay exact handler/resume keys to the shared output and recompute member rows. Bounded refusal restores both node effects and handler output before retry. Public grouped resume performs four real loads and returns `Completed((82, true), Closed)`; owned discard loads Int then Bool during cleanup and returns `(42, 41)` before one normal release. Exact event checks exclude abandoned reads and reacquisition. Capture-sensitive family templates remain outside this fragment.

## Register and observe the executable binding

[arena_typed.rs](../../../foreign-adapter/examples/arena_typed.rs) pairs the provider and arena manifests with `arena_binding`, retaining the original registered memory-manifest Arc. Module roots supply static registration; ForeignRuntime supplies the executable binding.

```bash
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo run --locked -p ash-foreign-adapter --example arena_typed -- tests/fixtures/provider-experiments/arena-typed/allocation-entry.ash
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo test --locked -p ash --test provider_arena_allocation
```

Observe matching activation/owner/object/layout, actual bytes read, stable earlier objects after refusal, exact Store/Load order and one release. Zero-size Unit values still consume distinct records; padding consumes capacity. Local aggregates/closures may use live references but cannot carry them out. This does not admit Ref-containing stored payloads.

Normal source release and terminal host destruction have separate receipts. Actual reply rejection abandons pending publication/observation, keeps the owner quarantined until runtime drop and performs one host-teardown release. It does not execute source cleanup as recovery. Arithmetic, bounds, initialization, encoding and native identity remain explicit foreign assumptions.

## Keep the receipt precise

The historical functional closure records 1,674 library tests, all seven public arena tests, both unchanged 64 KiB regressions and genuine copied-authority mutations. Fresh native41 completes source checking at 88,793, final elaboration at 27,096 and independent Core at 82,277 work units. Preserve the exact source manifest and complete logs. Work, payload bytes, object slots, native metadata/scratch and evaluator heap are separate quantities; no memory or speed improvement is established. These Arena repairs preserve the previously calibrated phase budgets and existing depth and stack limits; the separate [calibrated-admission policy](calibrated-admission-2026-10-08/README.md) records earlier public-driver allowances.

The unsigned source delivery is `ffa1d8ef4178cb1e5651411162ff09c117b725f7`. Its separately frozen final source passes both affected architecture checks, strict workspace/all-target/all-feature lint, 41 adapter unit plus ten backing tests, native41 and formatting. [Results](arena-results.md#verification-boundary) retain the historical functional versus final mechanical-source attribution and the [selected receipts](arena-selected-2026-10-08/README.md). Complete Original verification is recorded in [combined-delivery-2026-10-08 receipt](combined-delivery-2026-10-08/README.md); Main delivery and focused/native checks are recorded in [main-delivery-2026-10-08 receipt](main-delivery-2026-10-08/README.md). Wider stored payloads, graph sharing, deep or recipient-arena copying, borrowing and memory policy need later work. Production adoption requires the governing proposal/decision and specification changes.
