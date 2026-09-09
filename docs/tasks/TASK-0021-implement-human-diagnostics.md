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
  implementation has started in `.worktree/human-diagnostics` from `0b376b8`.
- The reviewed plan separates compile-time and runtime reporting and begins
  with one end-to-end compile-time example before broad migration.
- The initial binding-initializer path borrows existing expected/found facts
  and causal spans. It has English/Bulgarian messages, human/short rendering
  and JSON with distinct initializer and annotation relationships. The CLI
  default and runtime reporter remain unchanged.
- Foundation review caught presentation-derived JSON facts and a separate
  message-test inventory. A failing JSON-independence regression drove semantic
  fact separation; a private declaration macro now derives the typed messages,
  formatting arguments and exhaustive catalogue examples together.
- Driver-owned source retention is implemented: after a compile-time pipeline
  failure, the graph moves admitted sources into its private failure context.
  Source text is not cloned or reread. Runtime failures retain an empty source
  slice and still use the bounded reporter directly. Tests cover entry and
  dependency sources, rendering after input removal, and runtime exclusion.
- The ownership check exposed the macro-generated enum's declaration scope.
  Messages now use a concrete private-field carrier with declaration-generated
  constructors and test cases. No scanner exemption or macro-expansion engine
  was added. The new pipeline context is recorded in the ownership manifest.
- Source-retention review found no important defects. Slice 1 passed the full
  `cargo xtask verify` gate: formatting, build, warnings-denied Clippy, workspace
  tests and warnings-denied documentation. This includes 1,227 library tests,
  14 executable tests and all 32 architecture checks. Markdown lint and
  `git diff --check` also passed. Slice 1 is complete as an internal checkpoint;
  no diagnostic implementation is merged into main.
- Slice 2 starts with lexical and parser messages. Retain existing expected-form
  and found-token facts before localization; do not interpret legacy English
  strings. Graph-loading failures also need the admitted importer sources
  retained at their owner. Broad phase migration, internal causes, runtime
  formats and CLI integration remain outstanding.
- Slice 2 now has checked lexical explanations and English/Bulgarian
  translations. The lexical view borrows offending text and spans; JSON ignores
  legacy English descriptions. Parser diagnostics retain their expected form,
  found-token category or fixed spelling, and immediate recovery position.
  Legacy token descriptions derive from the same exhaustive classification.
  No lexer acceptance, parser recovery, CLI default or runtime path changed.
- This slice-2 checkpoint passed the focused presentation, catalogue, JSON,
  rendering and existing diagnostic suites, all 1,227 library tests, the
  bidirectional type-field ownership check and warnings-denied Clippy.
  Review found no actionable defects in that checkpoint.
  Graph-loading source retention and the remainder of slice 2 are still open;
  the full workspace gate has not yet been rerun for this checkpoint.
- Parser presentation now uses typed grammar arguments and Fluent selectors.
  Tests check exact English/Bulgarian wording for all expected forms and found
  categories, punctuation, EOF, ordered parser diagnostics, and distinct
  immediate-recovery and synchronization relationships. JSON retains grammar
  categories independently of wording. Checked-construction examples reject
  English strings and the wrong enum type as grammar arguments.
- Parser review caught found-token facts incorrectly attached to the primary
  opening-group span, and an unjustified assumption that a missing recursive
  member always follows `and`. Failing regressions drove both fixes; followup
  review confirmed them. No recovery or acceptance policy changed.
- Parser checkpoint verification passed the five focused diagnostic suites,
  all 1,227 library tests, eight rustdoc tests and warnings-denied Clippy.
  Markdown lint, relative links and `git diff --check` passed. The broad
  compile-time migration and full slice-2 gate remain outstanding.
- Graph-loading failures now retain staged sources through a separate
  `GraphDiagnostic` owner. Original failures and source-rejection classifications
  remain unchanged. Syntax and projection failures retain the selecting import
  span; rejected source text is moved, not cloned. Tests remove the input files
  before inspecting nested-import and syntax diagnostics, and verify the actual
  earlier descendant source for a later owner-propagation failure.
- Graph-context review found no ownership or error-order defects. The five
  focused graph/module/corpus/diagnostic suites passed. Clippy exposed a large
  error carrier; boxing the graph failure keeps caller error values small,
  without adding allocation to runtime failure reporting. The graph-context
  checkpoint passed the full `cargo xtask verify` gate: formatting, build,
  warnings-denied Clippy, workspace tests and warnings-denied documentation.
  Markdown lint and relative links were checked separately. Graph/input
  presentation is next; the remaining compile-time families and later slices
  are not complete.
- Input read and invalid-UTF-8 presentation is implemented. Entry failures
  have no invented source labels; imported input failures retain input
  responsibility and label the selecting import. The view now permits an
  absent primary label and carries responsibility explicitly. Path arguments
  borrow UTF-8 text and own display text only when native paths require it.
- Target-path facts preserve non-UTF-8 Unix bytes or Windows code units in JSON,
  alongside an explicitly separate display string. Existing source-label paths
  still use display strings; equivalent native-path preservation there remains
  outstanding. I/O categories use stable compiler-owned names and complete
  English/Bulgarian selector cases, verified against the repository toolchain.
- Input checkpoint verification passed the focused input/presentation/JSON/
  catalogue/module-loading suites, all 1,227 library tests, rustdoc tests and
  warnings-denied Clippy. Review confirmed target/importer distinction and
  responsibility; an actual imported non-UTF-8 test exercises the import label.
  The full slice-2 gate and remaining graph/module adapters are still open.
- Graph syntax failures now render as an ordered collection, retaining the
  established lexical/parser stream merge and attaching the selecting import
  as related context. Syntax resource failures precede independent source
  diagnostics and retain compiler responsibility and exact integer limits.
  Tests cover rendering after input removal and limits through `usize::MAX`.
- Graph syntax review found no actionable defects. The six focused suites,
  all 1,227 library tests, nine rustdoc tests and warnings-denied Clippy passed.
  Remaining graph/module adapters, broad phase coverage and the full slice-2
  gate are still outstanding; runtime reporting and CLI defaults are unchanged.
- Module presentation now covers reserved, duplicate and invalid root names,
  unknown roots and compiler-owned modules, missing imported files and import
  cycles. The module owner selects checked messages; presentation borrows its
  retained root/path facts and import span. Real loader tests render after the
  fixture files are removed. Both catalogues cover these seven families.
- Review caught an import label claiming successful target selection for an
  unknown root or builtin. A failing human-output regression drove neutral
  processing-context wording in both catalogues; followup review confirmed the
  fix. Six focused suites, all 1,227 library tests and warnings-denied Clippy
  passed. Markdown lint and diff whitespace checks passed separately.
- Path-escape presentation retains the canonical target and selecting import,
  including when several roots own a module. Module resource messages identify
  each of the six retained resource categories without inventing a numeric limit
  or allocation cause. Presentation now obtains responsibility explicitly from
  the module owner rather than treating every non-source failure as invocation.
  Legacy source-rejection classification and CLI exits are unchanged.
- Review found no actionable defects
  in the path-escape and module-resource presentation changes.
- This checkpoint passed all 1,228 library tests, the focused module-loading,
  input, catalogue and existing diagnostic suites, and warnings-denied Clippy.
  Markdown lint and diff whitespace checks passed. The full slice-2 gate remains
  outstanding.
- Unavailable-root diagnostics retain invocation responsibility, configured root
  and native path, and the I/O category when available. Without a retained cause,
  wording states only that the path could not be used as a directory. Input-read
  and root messages share the existing I/O wording through a Fluent reference.
  Catalogue contract tests check transitive arguments and reject missing
  references and cycles. Review found no actionable defects.
- Unavailable-root verification passed all 1,230 library tests, five focused
  suites and warnings-denied Clippy. Markdown lint and diff whitespace checks
  passed; the full slice-2 gate remains outstanding.
- Graph source-model failures now have explicit messages for all ten retained
  causes. The source owner distinguishes input representation limits from
  compiler identity exhaustion and invalid internal spans or indexes. JSON
  retains native paths and exact range, offset, length and identity quantities;
  invalid source positions are never used to manufacture labels. The graph's
  existing `input.source-model` reason and CLI exit behaviour are unchanged.
- Review found that `TextTooLarge` also reports an invariant failure during
  span construction on admitted text. The graph boundary now retains a typed
  source operation, used for responsibility and wording and preserved in JSON.
  A failing regression demonstrated incorrect input blame before the fix;
  followup review confirmed the corrected compiler classification and wording.
- Source-model verification passed all 1,230 library tests, five focused
  diagnostic/source/module suites, warnings-denied Clippy and the bidirectional
  type-field ownership check. Markdown lint and diff whitespace checks passed;
  broad compile-time migration and the full slice-2 gate remain outstanding.
- Projection presentation preserves recovery-boundary failure, all ten internal
  syntax causes and both syntax resource limits. The parser owner selects reasons
  and typed messages; JSON retains the cause or exact limit independently of
  wording. Producer inspection showed that `InvalidSpan` also covers missing or
  invalid end-of-input markers; wording and the Rust documentation now cover
  those cases, with a regression in both locales. No projection acceptance or
  CLI behavior changed.
- Projection review caught `InvalidRootCount` also covering content outside a
  root. Both translations and its Rust documentation now describe failure to
  form one complete rooted tree; exact wording assertions failed before the
  correction.
- Projection verification passed all 1,230 library tests, four focused suites,
  warnings-denied Clippy, Markdown lint and diff whitespace checks. Followup
  review confirmed the wording correction. The full slice-2 gate remains open.
- Internal module-path failures now retain missing-parent or missing-segments
  causes and use compiler responsibility. Corruption fixtures call the actual
  resolver for all three producer paths. Their former source-rejection
  classification is corrected to compiler failure (status 2), without changing
  ordinary import behavior or the stable `module.invalid-path` reason. Review
  found no actionable defects in this correction.
- Internal-path verification passed all 1,231 library tests, four focused
  suites, the bidirectional type-field ownership check and warnings-denied
  Clippy. Markdown lint and diff whitespace checks passed. Broader compile-time
  presentation and the full slice-2 gate remain outstanding.
- Resolver presentation has started with both `UnknownName` producers. They
  retain the missing spelling and distinguish ordinary term scope from an
  operation belonging to the selected effect. Typed messages and JSON borrow
  those facts; the renderer does not inspect legacy English labels. Real
  resolver fixtures exercise both contexts. Other resolver families remain
  explicitly unsupported by the staged presentation adapter.
- Lookup inspection identified separate type/nominal, effect-row parameter,
  owning-interface determination parameter, constructor, interface, unqualified
  effect and selected-module effect contexts for the next migration. Qualified
  unavailable exports retain their existing separate reason family.
- Initial resolver verification passed all 1,231 library tests, five focused
  suites, the bidirectional type-field ownership check and warnings-denied
  Clippy. The existing unknown-term test now requires the retained spelling,
  while still rejecting unjustified help or unrelated labels. Review found no
  actionable defects; Markdown lint and diff whitespace checks passed.
- Foundation verification passed 1,225 library tests, five new integration
  tests, 45 existing diagnostic tests, ten source tests, warnings-denied Clippy
  and six rustdoc tests. The renderer fixture checks English and Bulgarian
  human/short output. Followup review confirmed both foundation findings were
  resolved. The subsequent full workspace gate covers source retention and the
  concrete message carrier as well.

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

- `ModuleReason::InvalidPath` used the source-rejection constructor despite
  detecting corrupt projected paths or an impossible canonical parent. This
  inconsistency is now corrected at its three producers, with retained causes
  and corruption tests; human wording does not invent a source correction.
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
