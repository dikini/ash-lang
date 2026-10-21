# Source Resource Startup Budget Measurements

These are measurements and focused controls for [historical TASK-0052](https://github.com/dikini/ash-lang/blob/036c366834c839e4f0a503cf63e9db46448bb486/docs/tasks/TASK-0052-source-resource-default-startup-budget.md)
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
| `startup91-measurement` | exit101, original Resource | Templates finish at 185522; main reconstruction finishes at 207355; final Core exhausts at 327680. Template session has one fresh admission and two hits. |
| `startup91-final-core-phases` | exit101, original Resource | Final registry succeeds at 18531 local units. Graph, type, owner, byte/window and scope checks reach72955. Capture dependency validation exhausts at 120325 local units. |
| `startup91-capture-phases` | exit101, original Resource | Capture graph construction completes16175 units; cleanup discovery/query pruning reaches 16885. Strict control-root analysis exhausts its remaining30485 units. |
| `startup91-control-analysis` | exit101, original Resource; isolated diagnostic succeeds | Original initial discovery refuses after 172 processed states. The separately metered same-graph solver completes74308 units, including68262 discovery units and459 retained states; it supplies no startup result. |
| `startup91-discovery-costs` | exit101, original Resource; isolated diagnostic succeeds | Isolated call dispatch costs 32485 units across 74 dispatches; inner value-close rounds cost 333. Nested State totals overlap dispatch and must not be added to it. |
| `startup91-call-costs` | exit101, original Resource; isolated diagnostic succeeds | Ordinary call value-close work26229 dominates; fixed borrowed-result closes cost 642, so deferring those is not a useful repair. Two identical builtin-role reconstructions within one original proof cost 15535 and15545. |
| `startup91-single-builtin-proof` | exit101, original Resource | Same-call proof consolidation saves 15536 units; templates finish 169986 and final Core enters 191819. Isolated control demand is unchanged. |
| `startup91-single-proof-controls` | exit0, two tests pass | Exact builtin bytes/role and selective no-host/omission controls, including malformed/stale/missing identities and paid census bounds, remain enforced. |
| `startup91-scheduling-ab` | exit101, original Resource; isolated modes complete | Eager 74308 versus deferred 76592 units. The slower scheduling hypothesis is rejected; neither diagnostic supplies startup permission. |
| `startup91-const-coordinates` | exit0, original test passes | Instrumented candidate completes at 318794/327680. Each of three full builtin checks saves 12572 units; actual byte, shape, origin and registry checks remain. |

The first three measurements rule out missing template-session hits and localize
the refusal to strict capture control analysis. Those first measurements alone did not identify a safe
repair. The fourth probe shows initial discovery dominates: isolated setup uses 4517,
discovery 68262, payload checks 68 and later candidate enumeration 1461 units;
focused checks add no work in this case. Dispatch and State probes identify ordinary call value propagation as the main
control cost. The separately measured repeated builtin-role reconstruction is a
concrete redundancy within one immutable original proof; consolidating it cannot
by itself satisfy the default startup test.
The separately labelled isolated solver diagnostic measured the same immutable
graph with a fresh standalone default. Its result did not replace the original
cumulative startup result or give its caller credit.

Raw output bytes and hashes are preserved. No changed limit, new execution permission or full-gate result is claimed here.
The first
production repair shares only the completed same-call builtin check with the
existing omitted-formal provenance field; it creates no cache or cross-phase
authority. Const expected coordinates provide the second measured reduction.

The rejected scheduling experiment is retained as `scheduling-experiment.patch`
against commit 77544b1 and its exact source map. Both executed isolated modes used
separate fresh default allowances. New injected unit bodies in that patch were
compiled but filtered out; they were not run and supply no verification. Their
unbounded local test budgets were noticed before execution. The scoped scheduling
flag and all unrun scaffolding were removed after the slower cost result. The
production eager path stayed unchanged throughout. An `Ok` diagnostic alone is
not a claim of semantic equivalence.

The instrumented const candidate is retained as `const-coordinate-candidate.patch`
against commit 77544b1, including the new descriptor module and exact source map.
Broad counters, isolated fallback, and their module were then removed. Final
focused checks below ran on the delivered source with new before/after maps;
no artifact fingerprint or result transfers across that cleanup.

## Delivered-source verification

[Final verification](final-verification.json) records ten commands on the clean
production/test inputs at `95e9314134cc28aac0ef6c7b14a1f7b856fde74e`. All ten common
before/after maps contain 524 files and hash to
`b05551254ccf843933f127d1bb96743df5b8bb31f5cb2b46b790f687d7e0f203`.
Documentation changes after those commands do not change these source/configuration
inputs. The original startup test passes at 318794 of the unchanged 327680 units.

| Filter | Result |
| --- | --- |
| Exact original startup test | 1 passed |
| Builtin coordinate/parser parity and admission | 6 passed |
| Full checked builtin identity and work limits | 3 passed |
| Original declaration provenance and census | 12 passed |
| Source-resource images | 15 passed, 1 failed |
| Owner post-record regressions | 10 passed |
| Imported boundaries | 34 passed |
| Capture graph controls | 36 passed |
| Core host controls | 5 passed |
| Clippy, library and tests with warnings denied | exit 0 |

The image failure is
`dependent_discard_image_checks_original_facts_under_normal_cumulative_work`.
It refuses with `Resource` in `restore_effect`, before the later executable-library
checks. It is not a green image-suite result. The adjacent final logs retain the
failure as well as all passes; the final index records 119 distinct passing tests after deduplicating overlapping
filters.

[An exact retained-base comparison](startup91-dependent-base.receipt.json) runs
that same test from `a301a654bff2b7caed4befc32ce038abcf85dd7e` and reproduces
a default-budget failure at `source_resource_image.rs:3634`. The baseline reports
bare `ImageFailure::Resource`; the candidate reports
`ImageFailure::Validation(ValidationError::Resource)`. This proves the named
test already failed, not equal internal failure phases or complete demands. Its 523 source/configuration
files match the retained Git blobs and are unchanged before/after. The archive,
command, resulting unit-binary digest and log digest are retained. The temporary
archive changes `CARGO_MANIFEST_DIR` and source paths; it is not claimed to be an
identical path environment. An older overwritten binary was not reused.

This PR delivers the two bounded static-work reductions and the original startup
repair. The dependent-discard failure remains under issue #91 and TASK-0052 for a
separate measured repair. Whole task acceptance, the complete image suite and
F-core remain pending. No resource limit or independent admission check changes.
