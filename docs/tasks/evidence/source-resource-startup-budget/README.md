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

| Run | Result | Measured boundary |
| --- | --- | --- |
| `startup91-measurement` | exit101, original Resource | Templates finish at185522; main reconstruction finishes at207355; final Core exhausts at327680. Template session has one fresh admission and two hits. |
| `startup91-final-core-phases` | exit101, original Resource | Final registry succeeds at18531 local units. Graph, type, owner, byte/window and scope checks reach72955. Capture dependency validation exhausts at120325 local units. |
| `startup91-capture-phases` | exit101, original Resource | Capture graph construction completes16175 units; cleanup discovery/query pruning reaches16885. Strict control-root analysis exhausts its remaining30485 units. |

The first three measurements rule out missing template-session hits and localize
the refusal to strict capture control analysis. They do not yet identify a safe
repair. A further probe separates control setup, discovery and focused checks.
A separately labelled isolated solver diagnostic, if needed, may measure the same
immutable graph with a fresh standalone default. Its result cannot replace the
original cumulative startup result or give its caller credit.

Raw output bytes and hashes are preserved. No passing reconstruction, changed
limit, new execution permission or full-gate result is claimed here.
