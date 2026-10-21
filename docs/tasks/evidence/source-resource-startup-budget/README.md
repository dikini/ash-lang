# Source Resource Startup Budget Measurements

These are red diagnostic controls for [TASK-0052](../../TASK-0052-source-resource-default-startup-budget.md)
and [issue #91](https://github.com/dikini/ash-lang/issues/91). The existing test
reconstructs a two-owner native-buffer image without entering native code.
Every retained command uses the unchanged cumulative standalone/private-image
default of 327680. These failures do not establish generated-host input-derived
gas exhaustion and do not satisfy startup or F-core acceptance.

Each raw log has an adjacent receipt and source/configuration hash map. The
runner found identical maps before and after each command. The retained map is
that common input. The aggregate hashes sorted compact JSON of the path-to-SHA256
map, without a trailing newline. Commands use one Cargo job, the existing shared
Rust target and an empty RUSTC_WRAPPER. Instrumentation is test-only and supplies
no admission authority. Nested event deltas overlap; do not add different labels.
Image marks are absolute caller work; Core marks may use a private loan ledger.
For `.total` records, the first number is call count and the second is summed
local work; `.count` records report inventory sizes. Isolated records start a
separate aggregation group.

| Run | Result | Measured boundary |
| --- | --- | --- |
| `startup91-measurement` | exit101, original Resource | Templates finish at185522; main reconstruction finishes at207355; final Core exhausts at327680. Template session has one fresh admission and two hits. |
| `startup91-final-core-phases` | exit101, original Resource | Final registry succeeds at18531 local units. Graph, type, owner, byte/window and scope checks reach72955. Capture dependency validation exhausts at120325 local units. |
| `startup91-capture-phases` | exit101, original Resource | Capture graph construction completes16175 units; cleanup discovery/query pruning reaches16885. Strict control-root analysis exhausts its remaining30485 units. |
| `startup91-control-analysis` | exit101, original Resource; isolated diagnostic succeeds | Original initial discovery refuses after172 processed states. The separately metered same-graph solver completes74308 units, including68262 discovery units and459 retained states; it supplies no startup result. |
| `startup91-discovery-costs` | exit101, original Resource; isolated diagnostic succeeds | Isolated call dispatch costs32485 units across74 dispatches; inner value-close rounds cost333. Nested State totals overlap dispatch and must not be added to it. |
| `startup91-call-costs` | exit101, original Resource; isolated diagnostic succeeds | Ordinary call value-close work26229 dominates; fixed borrowed-result closes cost642, so deferring those is not a useful repair. Two identical builtin-role reconstructions within one original proof cost15535 and15545. |

The first three measurements rule out missing template-session hits and localize
the refusal to strict capture control analysis. They do not yet identify a safe
repair. The fourth probe shows initial discovery dominates: isolated setup uses4517,
discovery68262, payload checks68 and later candidate enumeration1461 units;
focused checks add no work in this case. Dispatch and State probes identify ordinary call value propagation as the main
control cost. The separately measured repeated builtin-role reconstruction is a
concrete redundancy within one immutable original proof; consolidating it cannot
by itself satisfy the default startup test.
A separately labelled isolated solver diagnostic, if needed, may measure the same
immutable graph with a fresh standalone default. Its result cannot replace the
original cumulative startup result or give its caller credit.

Raw output bytes and hashes are preserved. No passing reconstruction, changed
limit, new execution permission or full-gate result is claimed here.
