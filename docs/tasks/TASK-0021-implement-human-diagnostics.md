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
- Lookup migration now covers separate type/nominal, effect-row parameter,
  owning-interface determination parameter, constructor, interface, unqualified
  effect and selected-module effect contexts. Qualified
  unavailable exports retain their existing separate reason family.
- Initial resolver verification passed all 1,231 library tests, five focused
  suites, the bidirectional type-field ownership check and warnings-denied
  Clippy. The existing unknown-term test now requires the retained spelling,
  while still rejecting unjustified help or unrelated labels. Review found no
  actionable defects; Markdown lint and diff whitespace checks passed.
- The remaining lookup contexts were implemented and verified as one batch,
  reusing the existing adapter. Fixtures cover both effect-row producers,
  determination parameters and driver-retained constructor/interface/effect
  failures, including a qualified builtin-module import. The batch passed 1,231
  library tests, 49 diagnostic tests, catalogue and module-resolution suites,
  warnings-denied Clippy, Markdown lint and diff whitespace checks. No subagent
  runs or repeated full-workspace gates were needed for this mechanical batch.
- Duplicate declaration presentation now covers globals and operations, the
  shared type namespace, constructors, module aliases, type parameters, pattern
  binders and recursive members. Producers retain missing conflict names; the
  adapter preserves the original label order and distinguishes the first name
  declaration from the complete earlier definition. English and Bulgarian
  messages share those facts with JSON without interpreting legacy prose.
- The duplicate batch passed 1,231 library tests, 50 diagnostic tests, 60
  resolution tests, nine module-resolution tests, three catalogue tests and
  warnings-denied Clippy. Fixtures include mixed namespace conflicts in both
  declaration orders and method parameters conflicting with owner parameters.
  The broader run also found and corrected a stale unknown-name assertion from
  the earlier lookup batch. No subagents or full-workspace gate were needed.
- Equation/newtype name requirements, unused explicit parameters, import
  conflicts, unavailable exports and opaque constructors now have English and
  Bulgarian messages. The resolver retains private, missing-export and
  missing-alias causes independently of wording. JSON retains required names
  and cross-file declaration relationships without attributing a local import
  alias to the defining declaration. The existing name-context field carries
  the additional causes; no new reporting framework was introduced.
- Broader checks for this batch passed 1,231 library tests, 143 integration
  tests, the type-field ownership check and warnings-denied Clippy. Review
  identified the renamed-import label case; its regression fixture checks that
  only the occurrence carries the local alias spelling. After that correction,
  all 64 focused tests and warnings-denied Clippy passed again.
- All three source kind reasons now render from the existing expected/found
  facts. JSON distinguishes an exact kind from an applicable-kind pattern,
  and labels distinguish required-kind declarations from found-kind
  declarations. Existing causal fixtures cover type applications, interface
  arguments, tuple/function components and binding annotations; additional
  cases cover effect arguments and absent declaration origins. The batch
  passed the 1,231 existing library tests, a new absent-origin unit test,
  82 focused integration tests and warnings-denied Clippy. Kind-stage internal
  and resource failures remain outstanding. The catalogues now contain 94
  message templates per locale.
- All six entry-contract reasons now have explicit English/Bulgarian messages.
  The adapter preserves the module location for missing local `main` and the
  declaration location for other entry failures. Existing entry tests check
  presentation alongside source rejection and failure precedence; a retained
  failure fixture covers the open-result reason that earlier source checks may
  preempt. The batch passed 69 focused integration tests, warnings-denied
  Clippy, formatting and Markdown lint. There are now 102 message templates per
  locale. CLI defaults remain unchanged.
- Common type presentation now covers definition results, primitive operands,
  arguments, non-callable expressions and non-function equation signatures in
  addition to binding initializers: six of 35 source type reasons. The owning
  reason selects messages and causal relationships; the adapter preserves
  expected/found facts and optional application context. Missing required
  causes still fail explicitly. Sixty focused diagnostic, rendering, JSON and
  catalogue tests passed, along with warnings-denied Clippy. Both catalogues
  now contain 113 templates.
- Resolver type/interface/effect name-role failures now have explicit messages
  and machine facts, bringing resolution coverage to 21 of 30 reasons. The
  overloaded type-kind reason distinguishes an interface used as a value type
  from an implicit parameter used as both a type and a row tail. Effect-kind
  producers retain the offending spelling on local and qualified routes.
  The batch passed 128 focused diagnostic, resolution, module-resolution and
  catalogue tests and warnings-denied Clippy. Both catalogues contain 118
  templates; source acceptance and CLI defaults are unchanged.
- Effect operation shape, sealed resource providers, missing direct builtin
  imports and continuation use outside operation clauses now have explicit
  resolver presentation: 25 of 30 reasons. Phase facts distinguish `resume`
  from `discard` and cell from native-buffer imports. Shape wording explicitly
  excludes even an empty written outer effect row. Existing name facts remain
  unchanged; reasons without a named subject do not invent one. The batch
  passed 1,232 library tests, 125 focused integration tests and warnings-denied
  Clippy. Both catalogues contain 122 templates. Runtime reporting is unchanged.
- Duplicate exact effects now retain the first occurrence as a related label.
  Human messages and JSON distinguish it from the repeated occurrence; a
  positive fixture confirms that different type arguments remain allowed.
  All 26 source-rejection resolver reasons now have presentation, with four
  compiler resource/invariant categories still outstanding. The latter need
  their specific causes retained, including the different identifier spaces
  currently reported as binder exhaustion. Ninety focused tests and
  warnings-denied Clippy passed. Both catalogues contain 124 templates.
- Resolver identifier exhaustion now retains its exact identity space at all
  eight allocation sites: value binders, type binders, local nominal types,
  continuations and lexical evidence. English and Bulgarian messages and JSON
  identify compiler responsibility without changing allocation order or
  exhaustion behavior. Resolution presentation covers 27 of 30 reasons; the
  three remaining resource/invariant categories still need their specific
  causes retained. Both catalogues contain 125 templates. The batch passed
  41 identity-related library tests, the type-field ownership inventory and
  69 focused diagnostic/catalogue integration tests, warnings-denied Clippy,
  formatting and Markdown lint. Runtime reporting and CLI defaults remain
  unchanged.
- Pattern and coverage presentation now covers constructor payload/owner
  mismatches, pattern type mismatches, refutable binding/function/handler
  patterns, uncovered inputs and redundant cases. It borrows the phase's
  existing expected type or uncovered-value witness without inventing a
  found type. Match and equation cases share wording; an empty match has a
  separate explanation. Type presentation covers 14 of 35 source reasons,
  with 134 templates in each catalogue. The new tests cover all eight reasons
  and eleven source programs. The batch passed 125 diagnostic, catalogue,
  data/pattern and effect tests, including the 10,000-member recursive-data
  stress test. After replacing the presentation tuple with a named record,
  all 71 diagnostic/catalogue tests and warnings-denied Clippy passed again.
  Source acceptance, CLI defaults and runtime reporting remain unchanged.
- Single-location presentation also covers infinite and undetermined inferred
  types, unguarded recursive uses, and missing, repeated or captured
  continuation consumption. These six reasons retain source locations without
  inventing type facts. Nine source cases cover inference, recursion, branch
  completion, repeated resume/discard, and function/recursive capture. Type
  presentation covers 20 of 35 source reasons, with 140 templates per locale.
  All 94 focused diagnostic, catalogue and effect tests and warnings-denied
  Clippy passed. This changes compile-time reporting only, not runtime behavior
  or CLI defaults.
- Recursive initializer/root failures, newtype representation cycles and
  cleanup-context failures now render their complete related locations. The
  phase owns the recursive-group/member, cycle-participant and
  cleanup-action/abandoned-handler relationships. Missing required labels
  fail presentation rather than silently losing causal context. Four source
  fixtures verify both locales, JSON label order and exact spans, including
  a two-declaration representation cycle and an abandoned cleanup handler.
  Type presentation covers 24 of 35 source reasons; each catalogue contains
  149 templates. All 119 focused diagnostic, catalogue, recursion, newtype
  and cleanup tests and warnings-denied Clippy passed. Source acceptance and
  runtime behavior remain unchanged.
- Local nominal and resource escapes now relate the escaping dependency to
  its nominal scope or resource acquisition. Resource wording covers both
  exposed identities and stored dependencies hidden by a closure's ordinary
  type. Four driver-level fixtures exercise local values, returned handles,
  latent resource rows and identity-free closures with retained dependencies.
  Type presentation covers 26 of 35 source reasons, with 153 templates per
  locale. All 135 focused diagnostic, catalogue and resource-scope tests and
  warnings-denied Clippy passed; no source or runtime behavior changed.
- General `type.mismatch` presentation now borrows the failure's retained
  source type spellings. Human output and JSON expose required/found types
  and the original expression span without inventing a declaration location.
  Cleanup callback domain/result failures and a named nominal parameter
  exercise the adapter. This completes the separate one-reason general
  mismatch family; source-reason coverage remains 26 of 35. Both catalogues
  contain 154 templates. All 89 focused diagnostic, catalogue and cleanup
  tests and warnings-denied Clippy passed; the nominal-spelling case passed
  separately after being added. CLI defaults and runtime reporting are unchanged.
- Source type failures now retain a small phase-owned `TypeDiagnostic`
  wrapper, following the resolver's existing pattern. Common fields and
  legacy rendering remain available; localized presentation retains the
  wrapper rather than discarding its context. Anonymous-function failures
  preserve their typed binding, result, application or operator synthesis
  cause, including the case with no additional cause. Annotation advice is
  emitted only for binding contexts. Six producer-level cause cases and five
  source fixtures verify the semantic JSON context and causal labels. Type
  presentation covers 27 of 35 source reasons, with 159 templates per locale.
  All 1,234 library tests, 89 focused integration tests, the type-field
  ownership inventory and warnings-denied Clippy passed. A medium-effort
  review found no issues. Source acceptance, failure ordering and runtime
  reporting are unchanged.
- Equation arity retains a typed distinction between inconsistent/nonpositive
  pattern counts and patterns exceeding the declared function arrows. JSON
  exposes that requirement independently of wording; existing checks, spans
  and legacy messages are unchanged. Hook API presentation explains that the
  sole `publish` operation must have equal domain/result types before type
  argument substitution, for both hooks and registrations. Eight source cases
  cover these requirements. Type presentation covers 29 of 35 source reasons,
  with 162 templates per locale. All 103 focused diagnostic, catalogue and
  hook tests and warnings-denied Clippy passed.
- Handler coverage retains five distinct causes: argument count, operation
  owner, clause count, operation index and duplicate operation. Type-phase
  continuation errors retain whether the operation was `resume` or `discard`.
  Both locales and JSON use those facts without interpreting legacy prose.
  Existing checks, failure order, spans, legacy text and work charges remain
  unchanged. Type presentation covers 31 of 35 source reasons, with 167
  templates per locale. All 12 handler-related library tests, 116 focused
  integration tests and warnings-denied Clippy passed.
- Effect-row presentation retains nine causes across the main elaborator and
  deferred cleanup rows. Messages distinguish row union, infinite function
  rows, function-row mismatch, undeclared function effects, cleanup inference,
  unexpected cleanup effects, discard cleanup effects, deferred requirements
  and ambiguous effect removal. Existing checks, work charges and legacy text
  are unchanged. One producer-helper test covers all nine causes in both
  locales; two source cases distinguish union from undeclared effects. Type
  presentation covers 32 of 35 source reasons, with 176 templates per locale.
  All 107 focused tests and warnings-denied Clippy passed.
  Missing handled effects remain outstanding;
  their two producers are in the cleanup-row submodule.
- Unsafe-discard presentation retains the existing optional completion owner:
  clause, cleanup action or unknown. Human labels explain the capturing request
  and identified owner; JSON retains those relationships and the owner kind.
  Exact and insufficient work-budget cases preserve the existing charges.
  Missing-handled-effect presentation states the explicitly present exact
  instance requirement, including type arguments. Type presentation covers
  34 of 35 source reasons, with 183 templates per locale. All 108 focused
  tests and warnings-denied Clippy passed. Language acceptance, failure order
  and runtime reporting remain unchanged.
- Polymorphic-recursion presentation borrows the retained expected and found
  types. Both producers retain typed function/application label roles without
  changing their spans or order. A source fixture covers rigid method recursion;
  an adapter test covers no related label, either role alone and both roles,
  including rejection of missing required labels. Type presentation now covers
  all 35 source reasons, with 186 templates per locale. All 83 focused tests
  and warnings-denied Clippy passed. Internal failures,
  interface/constraint presentation and runtime reporting remain outstanding.
- Interface presentation now covers the six lexical-evidence admission reasons:
  missing local key, duplicate source, determination conflict, missing method,
  duplicate method and extra method. Phase-owned messages distinguish evidence
  keys, declarations and methods; related labels identify the earlier source,
  required method, earlier method or interface declaration. The adapter does
  not interpret legacy prose or discard unexpected facts or labels. No
  producer or admission behavior changed. Interface/constraint coverage is
  6 of 28 reasons, with 196 templates per locale. All 59 focused tests and
  warnings-denied Clippy passed.
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
