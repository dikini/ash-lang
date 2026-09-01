# TASK-0021: Implement Human Diagnostics

- ID: `TASK-0021`
- Status: active
- Related: [AD-0010: Human Diagnostic Presentation and Localization](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md), [DN-0029: Human Diagnostic Presentation](../design/DN-0029-human-diagnostic-presentation.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- AD-0010 authorizes the human-first CLI, machine format, localization, and
  structured internal-failure boundaries.
- A bounded comparison must select an existing catalogue format and Rust
  integration before product catalogue code is retained.
- The exact `lib-ash` migration sources in the sibling `ash-doc` repository
  remain external regression evidence. The task must not rewrite those sources
  to avoid the compiler failure.
- Downstream `ash-doc` automation must migrate to the JSON contract in the same
  coordinated checkpoint that changes default Ash output.

## Work

1. Minimize or otherwise isolate the honest checked-export-summary failure
   exercised by the eight migration entries. Retain the failed invariant and
   fix the producer or validator relationship rather than only changing prose.
2. Replace `ResolvedBuildFailure::InvalidState` at the import-authentication
   boundary with a small structured invariant family and safe developer facts.
   Authenticate every honest summary before publication and retain targeted
   corruption tests.
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
- Implementation has not started.

## Verification

- Run focused structural, renderer, catalogue, locale, JSON, CLI, module, and
  checked-export-summary tests named by the execution plan.
- Run the exact eight-entry `ash-doc` migration verifier against the resulting
  Ash checkpoint and verify the specified current-language outcomes.
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

None yet.

## Deviations

None.
