# Source Resource Startup Budget Measurements

These are measurements and focused controls for [TASK-0052](../../TASK-0052-source-resource-default-startup-budget.md)
and [issue #91](https://github.com/dikini/ash-lang/issues/91). The existing test
reconstructs a two-owner native-buffer image without entering native code.
Each startup reconstruction command uses the unchanged cumulative standalone/
private-image default of 327680. Helper tests use their named metering controls.
Failures do not establish generated-host input-derived gas exhaustion. No F-core
acceptance follows from this focused evidence.

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
| `startup91-single-builtin-proof` | exit101, original Resource | Same-call proof consolidation saves15536 units; templates finish169986 and final Core enters191819. Isolated control demand is unchanged. |
| `startup91-single-proof-controls` | exit0, two tests pass | Exact builtin bytes/role and selective no-host/omission controls, including malformed/stale/missing identities and paid census bounds, remain enforced. |
| `startup91-scheduling-ab` | exit101, original Resource; isolated modes complete | Eager74308 versus deferred76592 units. The slower scheduling hypothesis is rejected; neither diagnostic supplies startup permission. |
| `startup91-const-coordinates` | exit0, original test passes | Instrumented candidate completes at318794/327680. Each of three full builtin checks saves12572 units; actual byte, shape, origin and registry checks remain. |

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

Raw output bytes and hashes are preserved. No changed limit, new execution permission or full-gate result is claimed here.
The first
production repair shares only the completed same-call builtin check with the
existing omitted-formal provenance field; it creates no cache or cross-phase
authority. Const expected coordinates provide the second measured reduction.

The rejected scheduling experiment is retained as `scheduling-experiment.patch`
against commit77544b1 and its exact source map. Both executed isolated modes used
separate fresh default allowances. New injected unit bodies in that patch were
compiled but filtered out; they were not run and supply no verification. Their
unbounded local test budgets were noticed before execution. The scoped scheduling
flag and all unrun scaffolding were removed after the slower cost result. The
production eager path stayed unchanged throughout. An `Ok` diagnostic alone is
not a claim of semantic equivalence.

The instrumented const candidate is retained as `const-coordinate-candidate.patch`
against commit77544b1, including the new descriptor module and exact source map.
Broad counters, isolated fallback, and their module were then removed. Final
focused checks are running on the delivered source, with new before/after maps;
no artifact fingerprint or result transfers across that cleanup. The candidate's
318794 result remains labelled instrumented until the clean-source run completes.
