# TASK-0021: Implement Human Diagnostics

- ID: `TASK-0021`
- Status: active
- Related:
  [Migration repair evidence](../design/migration-repair-evidence.md),
  [AD-0010](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md),
  [DN-0029](../design/DN-0029-human-diagnostic-presentation.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- AD-0010 authorizes the human-first CLI, machine format, localization, and
  structured internal-failure boundaries.
- The bounded catalogue comparison in DN-0029 selected Fluent through
  `fluent-bundle`, `fluent-syntax`, and `unic-langid`.
- The exact `lib-ash` migration sources in the sibling `ash-doc` repository
  remain external regression evidence. Their compiler repair is verified on
  `main`, as recorded in the linked repair report. This task must preserve
  repaired acceptance and must not rewrite the retained sources.
- Downstream `ash-doc` automation must migrate to the JSON contract in the same
  coordinated checkpoint that changes default Ash output. A newer canary does
  not silently change ash-doc's edition pin. That project owns its forward
  migration from the verified compiler repair on `main`.

## Work

1. Implement one compile-time type-mismatch diagnostic end to end: checked
   message construction, English and Bulgarian human/short output, source
   context and JSON. Use the selected Fluent integration. Verify that adding
   a message or changing wording does not require renderer edits before
   migrating all phases. This internal slice does not switch the CLI default.
2. Extend that compile-time path by phase, retaining semantic reasons and
   causal order. Keep one message declaration with checked named arguments,
   catalogue-owned wording and a small borrowed presentation view. Retain
   source text needed for excerpts without rereading files or copying every
   source on success. JSON preserves semantic label relationships and facts.
3. Preserve specific internal causes through summary production and import
   boundaries. Use corruption fixtures, a small private cause representation
   and safe facts; do not change authentication acceptance or its accounting.
4. Implement runtime reporting as a separate slice and interface. Preserve
   allocation-independent resource reporting, primary/teardown distinctions,
   cleanup outcomes and stop-on-write-failure behavior. Share output contracts,
   not an allocating compile-time presentation pipeline.
5. Wire explicit human, short and JSON formats and the defaults in AD-0010.
   Complete both catalogues and all reachable failure paths before switching
   the CLI default. Preserve stdout and exit classifications.
6. Update tool documentation, tests and coordinated downstream automation.
   Change specification wording only where it obscures the representation;
   do not change semantics. Ash-doc owns its separate edition migration.

The implementation should reuse existing diagnostic types, source text, line
starts, reasons, and labels. It must not add runtime catalogue loading,
third-party catalogue overrides, an editor protocol, telemetry, automatic bug
submission, a translation service, interactive correction, or a custom
localization language. Color is not required for completion.

## Progress

- Design exploration and architectural decision are recorded.
- The task-owned [execution plan](human-diagnostics-execution-plan.md) records
  the test-first implementation and verification sequence.
- Compiler repair is complete and recorded separately. Diagnostic presentation
  implementation has not started.
- The reviewed plan separates compile-time and runtime reporting and begins
  with one end-to-end compile-time example before broad migration.

## Verification

- Run focused structural, renderer, catalogue, locale, JSON, CLI, module, and
  checked-export-summary tests named by the execution plan.
- Check structured diagnostics against the eight retained entries at an exact
  canary checkpoint. Preserve the repaired source and execution outcomes in
  the repair report; use corruption fixtures for compiler-failure presentation.
- Verify English and Bulgarian catalogue completeness, named-argument
  agreement, fallback, escaping, and explicit locale selection.
- Verify paths, one-based lines and columns, excerpts, tabs, Cyrillic,
  combining characters, wide characters, multiline spans, and cross-file
  labels.
- Verify one JSON object per diagnostic, schema versioning, locale independence,
  stable facts, semantic label relationships, byte spans and parser ordering.
- Verify checked message construction, catalogue completeness and that wording
  changes need no compiler or renderer edits. Exercise all AD-0010 defaults.
- Verify runtime resource reporting independently: no required allocation or
  source effects, no recovery, preserved primary/teardown/cleanup facts and no
  retry after writer failure.
- Run `cargo xtask verify`.
- Check changed Markdown, relative links, artifact authority, tool examples,
  and agreement between documented and tested CLI behavior.

## Discoveries

- The historical summary failure confused private access-only families with
  the retained semantic closure. A minimal unused private type reproduced the
  mismatch on the repair baseline, although the original search examples
  already succeeded there. The implemented repair admits only local,
  non-lexical private access-only families and preserves exact matching for
  opaque and retained-hidden families.
- Fluent is the smallest compared existing format that supplies named values,
  selectors, plural rules, embedded Rust resources, and syntax inspection for
  catalogue-contract tests.

## Deviations

- Compiler repair is complete on `main`; ash-doc owns its documentation
  migration. Diagnostic presentation and structured cause preservation remain
  here under AD-0010.
