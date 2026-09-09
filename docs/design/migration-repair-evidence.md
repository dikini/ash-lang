# Migration-discovered compiler repair evidence

This informative report records TASK-0024's repair work from main baseline
`274bdbe`, after the `effect-ash` closeout `a64f10b`. The repairs are integrated
on verified main by signed merge `a271ac3`. The
[specification](../../spec/README.md) defines correct language behavior; this
report records implementation evidence.

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
Those baseline rejections returned status 2, empty stdout, and
`internal.resource.type-work` followed by `type work resource limit exceeded`;
they supplied no causal source labels. The search dependency returned status 1
with `entry.missing-main` at bytes 0–6521. A fresh baseline build reproduced
these distinctions during final verification preparation.

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

The full gate caught a capacity regression introduced by that additional
authentication: the existing 2,800-interface acceptance fixture exceeded the
cumulative constraint budget. Interface fact construction and selector
admission each counted method types in a separate walk before cloning them.
The clone's existing preflight now charges both ledgers, eliminating those
redundant worklists without removing semantic checks. The two-module fixture
uses `114W + 83` constraint cells, or 319,283 at width 2,800. Both that accepted
fixture and the 4,500-interface validation-exhaustion fixture are unchanged
and pass. No capacity test was weakened to accommodate publication checks.

## Original-source outcomes

Each entry below was run unchanged with freshly built repair-worktree and
merged-main `target/debug/ash` binaries. Source and evidence files in ash-doc
were not edited.
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

For the four constraint rejections, source 0 is the entry and source 1 is its
dictionary dependency. Byte ranges are half-open:

| Entry | Primary range | Required declaration | Interface declaration |
| --- | --- | --- | --- |
| `red-black-dictionary/main.ash` | 1088–1107 | 3417–3423 | 391–450 |
| `red-black-dictionary/02-build-and-persistence.ash` | 801–820 | 3417–3423 | 391–450 |
| `tree-iterator/main.ash` | 927–945 | 4155–4160 | 551–610 |
| `tree-iterator/02-retained-state.ash` | 1157–1175 | 4155–4160 | 551–610 |

Each also retains the causal import at source 0, bytes 0–35. The opaque
rejections in the first table identify the entry's primary range and the
dependency's declaration range. Missing-main dependency controls identify the
whole entry: bytes 0–6521 for search and 0–7764 for iterator.

To repeat an outcome, build `ash` with `cargo build --bin ash --locked`, then
invoke `target/debug/ash` with the absolute original entry path under the
retained ash-doc evidence directory. Check status, stdout hash or emptiness,
stderr reason and the ranges above. The historical two-pin verifier remains
unchanged; it tests historical failures, not the repaired compiler.

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
  work. All 121 focused summary tests pass.
- [Selector tests](../../src/evidence.rs) cover both ledgers' exact and
  one-short clone boundaries, polymorphic and wide method schemes, and two
  deep methods whose failed staging publishes no selector entries. Retrying
  that same selector with fresh exact ledgers succeeds on a 256 KiB stack.

Focused import verification passed 128 resolver tests, 16 library-import tests
and 9 module-resolution tests before the later method-index and producer changes.
The method-index budget test and method-rich source regression passed afterward.
Full worktree verification, independent final reviews and merged-main
verification passed.

Checkpoint `a7138e1` passed formatting. Its full library run passed 1,215 tests
and failed five accounting fixtures. The followup passed all 1,220 library
tests after correcting these boundaries:

- `driver::tests::relational_interface_graph_has_an_exact_cross_stage_boundary`
- `driver::tests::wide_interface_graph_records_the_exact_validation_prefix`
- `elaborate::tests::impl_method_substitution_uses_the_exact_constraint_budget`
- `elaborate::tests::one_constraint_budget_spans_all_checked_modules`
- `evidence_validation::tests::deep_constructor_scheme_crosses_check_and_link_then_is_disposed_before_core`

Producer authentication adds nine constraint cells to each small elaboration
fixture; combined clone preflights save six. The relational graph now uses
7,797 cells, including authentication and savings from shared capture visits
and clone preflights. The wide fixture derives width 5,040 from the unchanged
limit: linking uses 327,628 cells and validation reaches 574,643, preserving
validation as the first over-budget phase. The deep
fixture retains 16,384 levels on a 256 KiB stack and asserts its exact 213,021
type-work charge under the default budget. Exact, one-short, retry and stage
checks remain.

After the combined clone preflights, fresh verification passed all 1,221
library tests, six interface-resource tests and 61 resource-scope typing tests.
The unfiltered `cargo xtask verify` passed afterward: formatting, locked
metadata and build, Clippy with warnings denied, all workspace tests and
rustdoc with warnings denied. This includes 17 library-import tests, nine
module-resolution tests, 32 architecture tests and four method-resource tests.

The first workspace gate also detected the new borrowed graph-visit index
missing from the source-derived type-carrier inventory. Its manifest entry now
records transient borrowed retention, the caller's type-work ledger and summary
ownership. The inventory check itself is unchanged.
The method-resource source manifest also needed its two selector formula
expectations updated to match the verified probes: `10 + 5` and `5W + 7`.
All four method-resource tests passed with those corrected expectations.
The complete remaining-test check passed afterward, excluding only the long
architecture ownership check already passed by the preceding full run. This
is diagnostic evidence, not a substitute for the unfiltered workspace gate.

Independent semantic and code-quality reviews of `274bdbe..a7138e1` found no
blocking product issues. They checked closure and access boundaries, ordered
method records, per-edge graph visits, cumulative producer authentication and
synthetic fixture validity. A stale scan comment was corrected. One test
coverage limitation remains: the missing-metadata retention test supplies
fresh visitors directly; it does not itself detect moving the visitor outside
the import-edge loop. The actual loop placement was checked in both reviews.
Both reviews also approved the accounting-fixture corrections and the borrowed
carrier inventory entry. The corrected inventory test passed independently.
The combined clone-preflight implementation and deep dual-budget retry test
also passed both reviews. All eight original entries and three dependency
controls retained their recorded outcomes after that change.

## Integration and closeout

- Baseline main: `274bdbe4ff8b3898d0fb6bd9b344ed689b2b7104`.
- Retained repair tip: `964279cd885d1d4c0b8c75039d0542915a45c393`, including
  checkpoint `a7138e1` and its verified followup.
- Signed main merge: `a271ac317a632e363c650daa6ad3e5d5e063e264`.
  `git verify-commit` reports a good signature. Its tree exactly matches the
  retained repair tip.
- Unfiltered `cargo xtask verify` passed both in the repair worktree and on
  merged main, including all workspace tests and warnings-denied Clippy and
  rustdoc checks.
- The merged-main corpus replay checked all eight original entries and three
  dependency controls: status, stdout hashes or emptiness, stderr reasons and
  the causal byte ranges recorded above.
- TASK-0024 is complete. This report retains its evidence; Git retains the
  removed task and all repair commits.

## Handoff boundary

No backports, tag movement, push, ash-doc target change or teaching-source edit
belongs to this repair. The fixes are now on verified main; ash-doc owns its
own documentation migration. TASK-0021's presentation and JSON work remains
separate.
