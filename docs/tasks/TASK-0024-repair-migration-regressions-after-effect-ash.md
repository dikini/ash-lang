# TASK-0024: Repair Migration Regressions After Effect Ash

- ID: `TASK-0024`
- Status: active
- Related:
  [AD-0010](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md),
  [TASK-0021](TASK-0021-implement-human-diagnostics.md),
  [effect-ash closure](../design/effect-ash/milestone-closure-evidence.md)

> This task fixes compiler bugs discovered during ash-doc migration. It does
> not define Ash semantics or own the subsequent documentation migration.

## Dependencies and scope

Effect Ash is integrated into `main` by signed merge `5d126b2`; milestone tag
`effect-ash` identifies closeout `a64f10b`. The integration prerequisite is met.
Implement repairs from current `main` in an isolated worktree, then verify and
integrate them into `main`. Do not backport fixes or move historical tags.

Assume the discovered bugs may still be present, but reproduce them on the
selected current-main baseline before choosing a fix. Current
[import rules](../../spec/name-resolution.md#imports-and-namespaces) and
[module checking](../../spec/static-semantics.md#globals-and-modules) govern
correct behavior, not historical compiler output.

TASK-0021 owns human diagnostics, localization, JSON and structured failure
causes. It is not a prerequisite for this repair. Reuse any integrated work,
but do not add a diagnostic system or wait for its presentation changes.

## Retained evidence

The failures were recorded during ash-doc's migration from `modular-ash`
`dca16039923475c48025c5f17beadeb6bcb6a4bf` to `lib-ash`
`d1e323d23390cdad03202ee3df76cd9100556e1d`. The sibling repository's evidence
commit is `492a3abec1324c3c0c0e8f0376d380092e883561`. Its
[retained report](https://github.com/dikini/ash-doc/blob/492a3abec1324c3c0c0e8f0376d380092e883561/lab/lib-ash-migration/body-free-summary-authentication/README.md)
and adjacent `checks/verify.sh` preserve eight entries from Cases 9, 10 and 12.
All eight reported status `2`, empty stdout and `resolve.internal-state` at
imported-summary admission on the Lib Ash pin. Direct dependency controls
reached ordinary checking or execution.

| Evidence directory | Entries | Required distinction |
| --- | --- | --- |
| `search-frontier` | `main.ash`, `02-unreachable-cycle.ash` | Public qualified calls must reach the specified result. |
| `red-black-dictionary` | `main.ash`, `02-build-and-persistence.ash` | Original clients omit explicit `impl Order` selection; restored checking may correctly reject them. |
| `tree-iterator` | `main.ash`, `02-retained-state.ash` | Distinguish compiler failure from source rejection under current implementation-selection rules. |
| `tree-iterator` | `03-opaque-pattern.ash`, `04-opaque-construction.ash` | Restore specified opacity rejection and causal declaration information. |

The earlier investigation isolated a mismatch for the search dependency:
private constructor-access metadata includes unreferenced helper families,
while the hidden semantic closure omits their nominal facts. This is a lead,
not proof that all eight entries share one cause or still fail on current main.

## Work

1. Record the exact current-main baseline. Run the eight unchanged sources and
   dependency controls against it, recording status, output, diagnostic reasons
   and causal locations. Classify each result, including already-fixed cases.
   Preserve the historical evidence and its exact-pin verifier; rerun that
   comparison only when needed to resolve an evidence question.
2. Minimize each remaining compiler defect. Keep the complete downstream
   triggers as acceptance evidence and add focused failing regressions and
   corruption controls in Ash before changing product code.
3. Repair the current producer/authentication/admission relationship. For the
   recorded mismatch, test local private access-only families without enlarging
   the hidden semantic closure. Preserve privacy, opacity, identities, kinds,
   exact retained-family matching and implementation selection. Do not bypass
   validation. Return any missing semantic rule to proposal or design work.
4. Verify producer/admission agreement and authenticate summaries before atomic
   publication, as required by AD-0010. Retain bounded work accounting, failure
   atomicity and mutation rejection, including effects-era summary facts.
5. Run every original trigger against the repairs and record its specified
   outcome. Absence of an internal failure alone is insufficient. Use focused
   Ash fixtures with current syntax or explicit implementation selection where
   needed to demonstrate valid behavior; do not edit ash-doc teaching sources.
6. Review, verify and integrate the repairs into `main`. Record the exact
   integrated commit, causes, regression tests and eight-entry outcome matrix
   for the subsequent ash-doc migration.

## Verification and completion

- Show failing-then-passing regressions for each repaired defect and retain
  corruption rejection, resource-limit and atomic-publication tests. Record
  already-fixed cases without inventing a new repair.
- Run focused import, module-resolution and summary tests, then
  `cargo xtask verify`; verify the integrated main result.
- Check changed documentation, relative links, authority boundaries and
  `git diff --check`. Cargo verification does not replace prose checks.
- Close this task when fixes and evidence are retained on verified `main`.
  Preserve the outcome record and remove completed task artifacts according
  to the project artifact policy.

After the bugs are fixed on `main`, ash-doc will plan and perform its own
documentation migration in that project. Its edition pins, teaching sources,
automation and publication are outside this task and do not gate completion.

## Progress

- [Repair evidence](../design/migration-repair-evidence.md) records the causes,
  regression coverage and original-source outcome matrix.
- Scope clarified: current-main compiler repair only; no backports.
- Baseline `274bdbe` is isolated in `.worktree/migration-repair`. Fresh tests:
  1,214 library and 14 CLI tests pass.
- Current-main reproduction: both search-frontier entries succeed with their
  historical output hashes. The other six entries and both dictionary
  dependency controls fail with `internal.resource.type-work`, before the
  historical imported-summary failure. The search dependency control reaches
  `entry.missing-main` as expected. No ash-doc files were changed.
- A minimal unused-private-type regression reproduced the historical summary
  mismatch. The local fix admits only access-only private module identities;
  source acceptance and foreign/lexical/opaque-owner rejection tests pass.
- Repeated full scans of shared capture graphs exhausted the dictionary's
  export-summary budget. Collector-local graph visits now avoid repeated
  nominal/effect scans without changing limits. Exact/one-short/fresh-retry
  tests pass. Tree iterator's dependency now reaches `entry.missing-main` and
  its opaque-pattern entry reports the specified source rejection.
- Import retention now shares capture scans per import edge. The 192-export
  regression passes, with no increase to resource limits.
- Red-black's earlier capture-analysis exhaustion came from repeated all-method
  searches. A charged node index preserves same-node record order and avoids
  unrelated searches. The method-rich regression and exact-work tests pass.
  Temporary profiling instrumentation was removed.
- Producer publication now runs full summary authentication on the existing
  cumulative ledgers. All 121 focused summary tests pass, including malformed
  publication and exact-budget controls.
- All eight unchanged original entries now reach their expected success or
  ordinary source rejection; the evidence report records the outcomes.
- Full workspace verification, final review and main integration remain
  outstanding. This is an implementation checkpoint, not task completion.
- Checkpoint formatting passes. The full library run passes 1,215 tests and
  fails five; the evidence report lists the outstanding failures.

## Discoveries

Eight failing entries are not eight established root causes. A source rejection
for missing implementation selection is not itself a compiler bug.

## Deviations

The earlier combined repair/documentation-migration scope is replaced by this
compiler-only task. The downstream migration is separate ash-doc work.
