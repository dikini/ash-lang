# S2 ordinary row-work correction

Working evidence for [TASK-0050](../TASK-0050-checked-ffi-regions-control-program.md); this is not language authority or final acceptance. Baseline is `2766e8260e2590d9ebdca7abd699115b3cd02a8a`.

The baseline `canonical_instances_with_budget` already returns an append-only input allocation before the canonical insertion reserve and its per-member charge. Its current body is unchanged. Sorted fixtures therefore bypass `CanonicalMembers`; the old fault test expected a reservation it never reached. The corrected fixture places the replacement before the source member in canonical order, retaining all six fault-site checks, exact hit counts (including the third canonical reservation), and storage-failure classification. No production row charge or reservation was added.

The same append-only path explains six work units per additional nullary member and 20 units for pure scheme projection, rather than the stale seven and 21. Exact, one-short and fresh-retry checks remain. The focused run passes all five cases: reservation faults, zonk work, pure projection, settled-cache invalidation, and wrapper emission. The existing `invalidate_settled_zonk_range` handles real test metadata mutation; no production mutation API was added.

Verification used Rust 1.97.1, the shared target, one Cargo job, and the compiled library test executable after `/tmp/slim-image-metadata-trace1.log` compilation. `/tmp/slim-row-repair2.log` records five successful isolated test processes (0 failures); its SHA256 is `e784ae36869da1e1c4c80b92d4d9539b52b76d5eb7aee271063483a26f2e81d7`. These are focused results, not a workspace gate.

Baseline function excerpts run from the `fn` declaration through its matching closing brace:

| Function | SHA256 |
| --- | --- |
| `canonical_instances_with_budget` | `2f66e6ac2f9a67ea29421f59e44f7cd387e1d21933b63e4d173492c6d358e095` |
| `complete_row_aware_zonk_owner_is_exact_and_retries_after_deep_failure` | `b21a7e2050c10cae0e972d1e582391ff6430fb106fcba8101b3bb9a4ffc25d7f` |
| `family_core_scheme_projection_preserves_pure_erasure_and_effect_rows` | `66bf213ca0baec5faa91bf0912cff7ed686614d8f7715d78b641caf4d0299145` |
| `runtime_row_canonicalization_and_tail_reservation_failures_are_not_work_charges` | `48b34ceab8bb7fd01b818cb3fb02bebf6d2c5b94fe8de85e4e0c143a6c1d523a` |

The later ordinary-regression checkpoint runs the Rust 1.97.1 library test binary
with `RUSTC_WRAPPER=` and `--test-threads=1`: 1,549 passed, zero failed, in
71.28 seconds. The rebuilt architecture binary passes all 47 checks in 44.83
seconds. The receipt hashes are respectively
`a627a8c1a31147b96da1a91889b92f63db76154fa97c70f8e4b0b6b40b092318`
and `9944454bdbdaf63b8181f90bd528831ebb71df6225c6ca6e0e6a6ea8043c3684`.
These precede the separately identified Cell export-shape call restoration and
are not a full workspace or native-host gate.

Summary fixtures now retain genuine defining constructor originals. A Newtype
constructor's defining payload is absent while the exported representation is
`Int`; both projections share the same canonical representation provenance.
Completed-publication retention adds eight fixed Type-work units, with zero
charge for cloning a Source origin. Exact deep and nominal freeze totals are
491,540 and 30. Alias checks retain independent Constraint-work formulas at
depths zero and 32,768, exact/one-short/retry checks, atomic index publication,
and the 256 KiB stack. Constructor late-origin refusal costs `2D + 18`: the
duplicate scheme comparison costs eight units, including its root and child
scheduling. The focused eight-test receipt hash is
`c76b1b78a37f45484d9799fc8ffb1cd70d8fd8c516e459d356d81c05fec92ab2`.
No production limit or comparison charge changes to match these receipts.
