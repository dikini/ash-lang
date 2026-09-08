# TASK-0024: Repair Migration Regressions After Effect Ash

- ID: `TASK-0024`
- Status: deferred until `effect-ash` integrates into `main`
- Related: [AD-0010: Human Diagnostic Presentation and Localization](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md), [TASK-0021: Implement Human Diagnostics](TASK-0021-implement-human-diagnostics.md), [DN-0024: Executable Learning and Evidence Stream](../design/DN-0024-executable-learning-and-evidence-stream.md), [DN-0026: Effect Ash Resource-First Milestones](../design/DN-0026-effect-ash-resource-first-milestones.md)

> This task organizes repairs of specified behavior and downstream migration.
> It does not define Ash semantics or authorize effect features.

## Dependencies

- Start implementation only after `effect-ash` lands on `main`. Record the
  integrated commit and milestone evidence before creating a repair worktree
  from that `main`. Do not start a parallel repair on the Lib Ash compiler or
  cherry-pick a speculative fix into effects worktrees.
- The scheduling request calls this milestone `effects-ash`; current Ash
  artifacts name it `effect-ash`. A partial effect increment or an unmerged
  worktree does not satisfy this integration gate.
- AD-0010 retains the repair evidence obligation. TASK-0021 owns human
  diagnostics, localization, JSON, and structured failure causes. Reuse its
  integrated work if available; do not duplicate it. Coordinate JSON adoption
  before closing the downstream migration if the CLI contract changes.
- Reconstruct the then-current specification and accepted architecture after
  integration. Current [import rules](../../spec/name-resolution.md#imports-and-namespaces)
  require immutable checked dependency summaries and preserve privacy, opacity,
  identities, and kinds. [Module checking](../../spec/static-semantics.md#globals-and-modules)
  supplies the producer and admission boundaries. These rules, rather than
  predecessor output, govern the repair.

## Evidence and affected behavior

The sibling repository is `../ash-doc`. At planning time its evidence commit is
`492a3abec1324c3c0c0e8f0376d380092e883561`. Its
[retained report](https://github.com/dikini/ash-doc/blob/492a3abec1324c3c0c0e8f0376d380092e883561/lab/lib-ash-migration/body-free-summary-authentication/README.md)
and adjacent `checks/verify.sh` preserve eight entries from Cases 9, 10, and
12. The migration was from Modular Ash
`dca16039923475c48025c5f17beadeb6bcb6a4bf` to Lib Ash
`d1e323d23390cdad03202ee3df76cd9100556e1d`. All eight produce status `2`, empty
stdout, and `resolve.internal-state` at imported-summary admission on that
Lib Ash pin. Direct dependency controls reach ordinary checking or execution.

| Evidence directory | Entries | Required distinction after repair |
| --- | --- | --- |
| `search-frontier` | `main.ash`, `02-unreachable-cycle.ash` | Public qualified calls must reach the specified result; no interface selector explains this failure. |
| `red-black-dictionary` | `main.ash`, `02-build-and-persistence.ash` | Original clients omit explicit `impl Order` selection. Restoring checking may expose a source rejection before migrated clients succeed. |
| `tree-iterator` | `main.ash`, `02-retained-state.ash` | Original accepted clients also need the target's implementation-selection rules applied. |
| `tree-iterator` | `03-opaque-pattern.ash`, `04-opaque-construction.ash` | Restore the specified opacity rejection and causal declaration relationship. |

TASK-0021 isolated a set mismatch for the search dependency: private
constructor-access metadata includes unreferenced helper families, while the
hidden semantic closure correctly omits their nominal facts. This is a
concrete investigation lead, not proof that all eight entries share one cause
or that effects integration preserves the same implementation.

## Work

1. Reproduce the retained baseline using clean exact predecessor and Lib Ash
   checkouts. From ash-doc, run:

   ```bash
   bash lab/lib-ash-migration/body-free-summary-authentication/checks/verify.sh \
       /path/to/modular-ash /path/to/lib-ash
   ```

   Keep this historical verifier's exact-pin contract. Run the eight unchanged
   sources and dependency controls separately against the integrated effects
   commit. Record status, channels, stable reasons, and causal locations per
   entry. Classify any already-fixed or newly exposed failures individually.
2. Minimize each remaining compiler defect without replacing the complete
   downstream triggers. Start with `tests/library_imports.rs`,
   `tests/module_resolution.rs`, and the summary tests in `src/resolved.rs` if
   those boundaries remain after integration. Write a failing honest-summary
   regression and corruption controls before changing product code.
3. Inspect the then-current producer, authentication, and admission paths
   (currently `src/elaborate.rs`, `src/resolved.rs`, and `src/resolve.rs`). For
   the recorded mismatch, test whether local private access-only families can
   be admitted without a hidden semantic carrier. Preserve exact matching for
   opaque and retained-hidden families; reject foreign private ownership and
   malformed counts. Do not enlarge the hidden closure, expose private types,
   bypass authentication, or change implementation selection to make examples
   pass. Return a missing semantic rule to proposal or design work.
4. Authenticate honest summaries before atomic publication, retaining bounded
   work accounting and failure atomicity under the integrated compiler. Add
   producer/admission agreement and mutation evidence, including identities,
   kinds, ownership, opaque families, and retained-hidden closure. Reuse
   TASK-0021 structured causes; do not implement another diagnostic system.
5. Verify every original trigger against the repair and classify its next
   specified outcome. Absence of status `2` alone is insufficient. Record
   distinct root causes and repairs if more than one defect remains. Keep
   focused upstream regressions, not copies of entire teaching Cases.
6. Prepare and execute the forward migration below after the Ash repair is
   retained. Record exact commits and verification in both repositories before
   closing this task.

## Forward migration of ash-doc

The maintainer question is how all active teaching and the three blocked Cases
can run against one repaired effects checkpoint. Read ash-doc's `AGENTS.md`,
required writing skill, README, roadmap, active plans, and content indexes at
execution time. The current unpublished Lib Ash migration cannot close by
silently retargeting only the blocked Cases.

1. Write a bounded ash-doc migration plan that explicitly supersedes the
   unfinished Lib Ash edition outcome. Select one exact, retained Ash commit
   containing the integrated effects milestone and fixes. Record the actual
   milestone/tag name and peeled commit; do not invent a future hash or move
   the existing `lib-ash` tag. A canary is evidence, not an edition change.
2. Move ash-doc's single forward line together: target declarations in
   `AGENTS.md`, `README.md`, and `docs/project/roadmap.md`; active plan and
   publication intent; specification/tool links; canonical programs; displayed
   code; expected values, types, outputs, diagnostics; and verifier pin guards.
   Discover all target references rather than replacing hashes blindly.
   Preserve exact historical references in research and regression evidence.
3. Restore Cases 9, 10, and 12 from their retained sources into the active
   content family only when each complete unit verifies. Add the explicit
   implementation imports required by the new target to teaching sources,
   while retaining the lab originals unchanged. Update explanations for actual
   semantic changes; do not retrofit effect features into pure lessons without
   a teaching need.
4. Retain the historical two-pin lab comparison and add a separate repaired
   checkpoint comparison. Assert original-source outcomes independently from
   migrated teaching-source outcomes. Document why a missing implementation
   selection rejection can establish restored checking but cannot complete a
   lesson that promises successful execution.
5. Coordinate TASK-0021's JSON automation contract when present at the chosen
   checkpoint. Update shared and specialized rejection checks to parse stable
   facts and causal spans, not human wording. Verify the entire active Learn,
   Cases, and Libraries stream at the same pin, including displayed-source
   agreement and all intentional rejections. Keep unverified gaps visible.
6. Close the edition migration only after all required units verify. Preserve
   published ash-doc tags and use no old-edition maintenance branch or compiler
   compatibility mode. Any later publication uses the actual matching Ash
   milestone name; do not publish repaired effects content as `lib-ash`.

## Progress

- Planning only. No compiler changes or ash-doc target changes have started.
- TASK-0021's repair and edition-migration scope moved here to avoid concurrent
  changes to compiler boundaries during effects development.
- Implementation detail must be refreshed after the integration gate. If a
  temporary execution plan is needed then, link it here and remove it at task
  completion under the artifact policy.

## Verification

- Capture the historical eight-entry comparison and dependency controls, the
  integrated effects baseline, and the repaired outcome matrix with exact
  Ash and ash-doc commits and commands.
- Demonstrate failing-then-passing minimized regressions for every remaining
  defect, retained corruption rejection, producer/admission agreement, resource
  limits, and atomic publication. Exercise the effects-era summary facts too.
- Run focused import, module-resolution, and summary tests, then
  `cargo xtask verify` from the repair checkout. If files or test targets moved,
  record their replacements rather than applying stale instructions.
- Run every active ash-doc verifier against its one declared exact checkpoint.
  Check restored Cases' success observations and opacity failures separately
  from original-source missing-selection rejections.
- Review Markdown structure, lint, relative links, target references, and
  authority boundaries in both repositories; run `git diff --check` in each
  changed repository. Cargo verification does not cover manual prose checks.
- Record retained commits, root causes, outcomes, remaining exclusions, and
  downstream completion before removing this task and its index entry.

## Discoveries

Eight failures are documented as one observation family, not eight established
root causes. The ordinary implementation-selection migration is not another
compiler bug. Human diagnostics are the separate feature owned by AD-0010 and
TASK-0021.

## Deviations

None. Effect semantics, new learning topics, backports, publication tooling,
and changing historical evidence remain outside this repair task.
