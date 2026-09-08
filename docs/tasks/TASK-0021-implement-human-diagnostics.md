# TASK-0021: Implement Human Diagnostics

- ID: `TASK-0021`
- Status: active
- Related: [TASK-0024: Repair Migration Regressions After Effect Ash](TASK-0024-repair-migration-regressions-after-effect-ash.md), [AD-0010: Human Diagnostic Presentation and Localization](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md), [DN-0029: Human Diagnostic Presentation](../design/DN-0029-human-diagnostic-presentation.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- AD-0010 authorizes the human-first CLI, machine format, localization, and
  structured internal-failure boundaries.
- The bounded catalogue comparison in DN-0029 selected Fluent through
  `fluent-bundle`, `fluent-syntax`, and `unic-langid`.
- The exact `lib-ash` migration sources in the sibling `ash-doc` repository
  remain external regression evidence. TASK-0024 owns their compiler repair
  on current `main`. This task must not change summary
  acceptance or rewrite the retained sources to avoid the failure.
- Downstream `ash-doc` automation must migrate to the JSON contract in the same
  coordinated checkpoint that changes default Ash output. A newer canary does
  not silently change ash-doc's edition pin. That project owns its forward
  migration after TASK-0024's compiler fixes land on `main`.

## Work

1. Retain the isolated checked-export-summary failure as presentation evidence.
   Report its compiler responsibility and cause without changing the
   authentication relation; TASK-0024 owns that repair.
2. Replace `ResolvedBuildFailure::InvalidState` at the import-authentication
   boundary with a small structured invariant family and safe developer facts.
   Retain targeted corruption tests. Producer-side authentication before
   publication and its resource accounting belong to TASK-0024.
3. Compare existing catalogue formats using the English and Bulgarian cases in
   DN-0029. Record the evidence and retain the least mechanism that meets the
   accepted requirements.
4. Expose the existing phase-specific diagnostic facts through a small
   driver-owned presentation view. Retain enough source context to resolve
   every causal span without copying the compiler's semantic policy into the
   renderer.
5. Add explicit human, short, and versioned JSON-lines renderers. Make human the
   default and preserve stdout and exit-status behavior.
6. Add embedded, complete English and Bulgarian catalogues with typed named
   arguments, deterministic locale selection, and validated fallback.
7. Move every reachable CLI failure to the common presentation path. Do not
   retain mixed legacy output.
8. Update tool documentation, compiler terminology, tests, and downstream
   migration verification. Change specification wording only where it exposes
   avoidable implementation terminology; do not change semantics.

The implementation should reuse existing diagnostic types, source text, line
starts, reasons, and labels. It must not add runtime catalogue loading,
third-party catalogue overrides, an editor protocol, telemetry, automatic bug
submission, a translation service, interactive correction, or a custom
localization language. Color is not required for completion.

## Progress

- Design exploration and architectural decision are recorded.
- The task-owned [execution plan](human-diagnostics-execution-plan.md) records
  the test-first implementation and verification sequence.
- The migration failure has been reproduced and isolated. Implementation has
  not started.

## Verification

- Run focused structural, renderer, catalogue, locale, JSON, CLI, module, and
  checked-export-summary tests named by the execution plan.
- Check structured diagnostics against the eight retained entries at an exact
  canary checkpoint. Unrepaired entries may still report compiler failures;
  restored language outcomes are TASK-0024 acceptance evidence.
- Verify English and Bulgarian catalogue completeness, named-argument
  agreement, fallback, escaping, and explicit locale selection.
- Verify paths, one-based lines and columns, excerpts, tabs, Cyrillic,
  combining characters, wide characters, multiline spans, and cross-file
  labels.
- Verify one JSON object per diagnostic, schema versioning, locale independence,
  stable facts and byte spans, and multiple parser diagnostics.
- Run `cargo xtask verify`.
- Check changed Markdown, relative links, artifact authority, tool examples,
  and agreement between documented and tested CLI behavior.

## Discoveries

- Checked-summary validation counts withheld constructor families by owner and
  access kind. It then requires every such family to match either an exported
  opaque nominal or a retained local hidden nominal.
- The search-frontier dependency has six unreferenced private helper types.
  Their constructor names are correctly retained as private access metadata,
  but their nominal facts are correctly absent from the minimal hidden closure.
  The final equality therefore compares different sets and reports invalid
  compiler state. The repair must admit local private access-only families
  without weakening exact matching for opaque and retained-hidden families.
- Fluent is the smallest compared existing format that supplies named values,
  selectors, plural rules, embedded Rust resources, and syntax inspection for
  catalogue-contract tests.

## Deviations

- TASK-0024 owns the compiler repair on current `main`; ash-doc owns its later
  documentation migration. Diagnostic presentation and structured cause
  preservation remain here under AD-0010.
