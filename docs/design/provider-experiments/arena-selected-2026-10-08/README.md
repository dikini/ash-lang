# Selected arena delivery evidence

Informative DN-0036 evidence for the selected scalar fragment. These receipts
retain finite execution results and reviewed source identities; they do not
establish current language semantics, a formal theorem or production adoption.

The unsigned source delivery is `ffa1d8ef4178cb1e5651411162ff09c117b725f7`.
Its preserving Common source merge is `c49d4bdc6004168a161c8d51d90b43cf3afddbd6`. That merge has independent
static review. Complete Original verification passes at `7a518e83230fec568978b269b1d69776ab6051c5`; the [combined receipt](../combined-delivery-2026-10-08/README.md) records the full gate. Main delivery remains pending. Consult the
[consolidation record](../execution.md#current-consolidation-checkpoint) for
subsequent integrated results and exact checked commits.

## Frozen functional source

The [functional source manifest](round-compile-repair-pins.json) has SHA-256
`833bcb70c551b5e746579d08ffee53931c6ac4f5a20f862e02e4a29718ccf976`.
The [receipt](round-compile-repair-receipt.json),
[complete successful log](round-compile-repair-lib-allocation.log), and
[attribution](functional-attribution.json) record 1,674 library and seven public
allocation passes, with no failures or ignored cases. The unsigned recovery
`1824bb70b28c72da2dbc6308887c4577b5adb681` preserves these inputs. This result
predates the mechanical lint and scanner corrections below.

```sh
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo test --locked -p ash --lib --test provider_arena_allocation --no-fail-fast -- --test-threads=1
```

## Final connected source

The [delivered source manifest](round-retention-lint-pins.json) has SHA-256
`3d351316ad975160a55343e3f0f6cc37de4c23655e2bbd6e431219d360feabc3`.
Every one of its 352 source blobs matches the source-delivery commit above.
The [collected receipt](round-retention-lint-checks.json) and
[attribution](final-connected-attribution.json) record all five commands exiting
successfully against unchanged inputs. The retained logs are:

- [Two affected architecture checks](round-retention-lint-carrier-inventory.log).
- [Strict workspace, all-target, all-feature lint](round-retention-lint-strict-clippy.log).
- [Fresh adapter tests: 41 unit and ten backing cases](round-retention-lint-adapter.log).
- [Native scalar execution](round-retention-lint-native41.log).
- [Formatting](round-retention-lint-format.log).

Run these commands serially from a checkout containing the delivery; use one
Cargo job and the recorded per-command wrapper override. The collected receipt
retains each exact argument vector. A successful command list is not itself a
new pass receipt.

## Native result and measured work

The actual host acquires an arena, stores and loads eight bytes under one
activation/object, and releases it normally. Its result is
`Completed(41, Closed)`. The public integration test separately checks that no
owner remains retained. The complete observed compilation phases use:

| Phase | Charged units |
| --- | ---: |
| Source checking | 88,793 |
| Final elaboration | 27,096 |
| Independent Core | 82,277 |

These counts belong to the frozen Arena host run. They measure charged work,
not CPU time or memory. Fresh combined SQLite/arena costs and any accepted
within-10% deficit must be recorded separately after integration. The
[calibration policy](../calibrated-admission-2026-10-08/README.md) defines that
allowance and requires explicit optimization targets for accepted deficits.

Native arithmetic, representation, bounds and destruction remain foreign
assumptions supported by finite tests. See [results](../arena-results.md) and
the [safety argument](../arena-safety.md) for scope and remaining limitations.
