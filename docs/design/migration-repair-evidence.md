# Migration-discovered compiler repair evidence

This informative report records TASK-0024's repair work from main baseline
`274bdbe`, after the `effect-ash` closeout `a64f10b`. Full verification and main
integration remain pending. The [specification](../../spec/README.md) defines
correct language behavior; this report records implementation evidence.

## Baseline and causes

The retained ash-doc evidence is at commit
`492a3abec1324c3c0c0e8f0376d380092e883561`, under
`lab/lib-ash-migration/body-free-summary-authentication`. Its historical
comparison used Modular Ash `dca16039923475c48025c5f17beadeb6bcb6a4bf` and
Lib Ash `d1e323d23390cdad03202ee3df76cd9100556e1d`.

Fresh baseline verification passed 1,214 library and 14 CLI tests. The eight
original entries did not all retain their historical failure: both search
programs already succeeded with their original hashes. The other six entries
and their dictionary dependencies exhausted type work before summary admission.

Three implementation defects were isolated:

- **Private access metadata versus semantic closure.** The historical
  constructor-family mismatch still reproduced with a wholly unused private
  type. Such a family has access metadata but no public semantic root. Summary
  validation now admits only unmatched local, non-lexical private families.
  Retained opaque and hidden families still require exact counts; foreign,
  lexical and unmatched opaque owners reject. Hidden closure is not enlarged.
- **Repeated shared capture scans.** Export-summary construction and import
  retention rescanned one immutable capture graph for every exported value or
  implementation method. Operation-local graph visits use allocation identity
  and keep graph owners borrowed. Freeze uses separate nominal/effect passes;
  imports use a fresh index per edge. Actual callable values, schemes, origins
  and authorization still receive their individual checks.
- **Repeated unrelated method searches.** Capture analysis searched all method
  records at each node and within function-body traversals. Red-black had 778
  nodes and 22 method records. Its cumulative type work rose from 67,845 at
  capture entry to 88,097 after value propagation and 326,358 after value-graph
  construction, leaving too little for control compilation. A bounded node
  index preserves each node's ordered records, including multiple requirements,
  while avoiding unrelated searches.

The type-work limit remains 327,680. No resource limits were raised and no
actual scan or retained type clone was left uncharged. Temporary profiling
instrumentation was removed.

[AD-0010](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md)
also requires producer-side authentication. Staged export summaries now run
the complete authentication pass against the existing cumulative ledgers before
publication. Synthetic freeze fixtures must satisfy the same admission
invariants as real summaries; this is not a diagnostic-presentation feature.

## Original-source outcomes

Each entry below was run unchanged with the repair worktree's freshly built
`target/debug/ash`. Source and evidence files in ash-doc were not edited.
All rejected entries have empty stdout. Successful entries have empty stderr.

| Directory | Entry | Status | Result |
| --- | --- | --- | --- |
| `search-frontier` | `main.ash` | 0 | Original found-path output hash retained. |
| `search-frontier` | `02-unreachable-cycle.ash` | 0 | Original exhaustion output hash retained. |
| `red-black-dictionary` | `main.ash` | 1 | `constraint.unsatisfied`; original client does not select the required implementation. |
| `red-black-dictionary` | `02-build-and-persistence.ash` | 1 | `constraint.unsatisfied`, with requirement, import and interface declaration labels. |
| `tree-iterator` | `main.ash` | 1 | `constraint.unsatisfied`; original client does not select the required implementation. |
| `tree-iterator` | `02-retained-state.ash` | 1 | `constraint.unsatisfied`, with requirement, import and interface declaration labels. |
| `tree-iterator` | `03-opaque-pattern.ash` | 1 | `resolve.opaque-constructor`; primary bytes 230–238, declaration bytes 523–549. |
| `tree-iterator` | `04-opaque-construction.ash` | 1 | `resolve.opaque-constructor`; primary bytes 103–111, declaration bytes 523–549. |

The search outputs have SHA-256 hashes
`254dc0d711ed8246b920f1be8b642af6d57a0aaa312a2d944de06fb570aea329`
and `bf32aeed3acf3194789234d517395cfd9b8b991d86d4122dc8d5ca8b620793a3`.
The red-black dependency's own main succeeds with hash
`6c159135693e2dff8d81dc97fb60fafcebfeb9b0c09cb4deebec4757e4a716fc`.
The search and iterator dependencies reach `entry.missing-main`, as expected.

These outcomes distinguish compiler repair from teaching-source migration.
Missing implementation selection is an ordinary source rejection under current
Ash, not a remaining internal compiler failure.

## Regression and verification coverage

- [Library import tests](../../tests/library_imports.rs) retain the unused
  private type, 192-export shared graph and 128-function method-rich regressions.
  Each reproduced a failure before its corresponding repair.
- [Resolver tests](../../src/resolve/module_tests.rs) cover shared global/method
  graphs in both selector orders, exact/one-short budgets, fresh retries and
  missing metadata on a fresh retention attempt. Existing duplicate-route and
  mutation checks remain in place.
- [Capture tests](../../src/core/capture.rs) cover distinct versus aliased graph
  allocations, fresh visits, ordered same-node method records, construction
  precharge, lookup work and resource exhaustion. Raw metadata scans retain
  their original charged-scan tests.
- [Summary tests](../../src/resolved.rs) cover private-family ownership,
  malformed producer publication and exact cumulative freeze/authentication
  work. Full fixture and workspace verification is still pending.

Focused import verification passed 128 resolver tests, 16 library-import tests
and 9 module-resolution tests before the later method-index and producer changes.
The method-index budget test and method-rich source regression passed afterward.
Final whole-worktree verification, independent final review and merged-main
verification remain required before completion.

Checkpoint verification passed formatting. The full library test run passed
1,215 tests and failed five; this checkpoint is not ready for integration.
The outstanding tests are:

- `driver::tests::relational_interface_graph_has_an_exact_cross_stage_boundary`
- `driver::tests::wide_interface_graph_records_the_exact_validation_prefix`
- `elaborate::tests::impl_method_substitution_uses_the_exact_constraint_budget`
- `elaborate::tests::one_constraint_budget_spans_all_checked_modules`
- `evidence_validation::tests::deep_constructor_scheme_crosses_check_and_link_then_is_disposed_before_core`

Investigate these failures before claiming full verification.

## Handoff boundary

No backports, tag movement, push, ash-doc target change or teaching-source edit
belongs to this repair. After verified fixes land on main, ash-doc owns its own
documentation migration. TASK-0021's presentation and JSON work remains separate.
