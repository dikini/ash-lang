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

1. Use retained checked-export-summary corruption fixtures as presentation
   evidence. Report compiler responsibility and cause without changing the
   repaired authentication relation.
2. Replace `ResolvedBuildFailure::InvalidState` at the import-authentication
   boundary with a small structured invariant family and safe developer facts.
   Retain targeted corruption tests and preserve the implemented producer-side
   authentication before publication and its resource accounting.
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
- Compiler repair is complete and recorded separately. Diagnostic presentation
  implementation has not started.

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
  stable facts and byte spans, and multiple parser diagnostics.
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
