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
- Interface method signatures and implementation method membership now have
  precise messages: non-function signature, missing method, duplicate method
  and extra method. The phase supplies primary and related relationships;
  required causal labels cannot be silently omitted. Four source fixtures
  verify English, Bulgarian and JSON output, plus missing-label rejection.
  Interface/constraint coverage is 10 of 28 reasons, with 202 templates per
  locale. All 162 focused tests and warnings-denied Clippy passed. No producer,
  language check or runtime behavior changed.
- Implementation header messages distinguish an all-variable selection key,
  a prerequisite-only type variable and a non-decreasing prerequisite. Related
  labels identify the selected interface or governing implementation head.
  Three source fixtures exercise both locales; existing implementation and
  interface diagnostic tests retain semantic and precedence coverage. All
  163 focused tests and warnings-denied Clippy passed. Interface/constraint
  coverage is 13 of 28 reasons, with 208 templates per locale. No producer or
  language check changed.
- Public-definition privacy, public-implementation privacy and duplicate
  requirement messages reuse the retained private-interface or earlier-requirement
  spans. Five source cases cover global requirements, implementation heads and
  prerequisites in both locales. No new metadata or producer changes were
  needed. Interface/constraint coverage is 16 of 28 reasons, with 213 templates
  per locale. All 208 focused tests and warnings-denied Clippy passed.
- Implementation ownership presentation explains that neither dependent
  arguments nor nested nominals establish ownership. A linked-module source
  test retains the selected foreign-interface label in JSON and formats both
  locales. Interface/constraint coverage is 17 of 28 reasons, with 215
  templates per locale. All 156 focused tests and warnings-denied Clippy
  passed. No ownership check or producer changed.
- `InterfaceDiagnostic` retains the selection engine's existing `SelectionError`
  alongside the common diagnostic. Ordinary producers use the common fields
  unchanged; selection failures preserve declaration, import and four typed
  causal roles without parsing prose or allocating a second role list.
  Unsatisfied, ambiguous and cyclic requirements now render in both locales.
  Source fixtures cover all three; linked-module tests cover retained import
  and selected-implementation chains. Missing required labels are rejected.
  Interface/constraint coverage is 20 of 28 reasons, with 224 templates per
  locale. The public `TypeError::Interface` payload now requires retaining the
  wrapper for localized presentation, as with source type diagnostics.
  All 1,240 library tests, 207 focused integration tests and warnings-denied
  Clippy passed. A medium-effort review found no bugs; its test suggestion
  added exact JSON relationship-sequence checks to the cross-file fixtures.
- Interface arity retains typed expected/supplied counts at both producers.
  The existing wrapper now distinguishes plain, selection and argument-count
  context. Human messages and JSON integers use the same counts; neither
  presentation path parses legacy text. Four count pairs and six source cases
  cover global requirements, implementation heads and prerequisites. Legacy
  messages, spans and checks are unchanged. Interface/constraint coverage is
  21 of 28 reasons, with 226 templates per locale. All 169 focused tests and
  warnings-denied Clippy passed.
- Undetermined requirement parameters, implementation overlap and incompatible
  implementation dependents now have precise messages. Pair diagnostics retain
  the two import-route lengths already available at the producer; these preserve
  earlier/later definition and import roles without parsing labels. Three source
  cases and nine route combinations cover both locales, ordered JSON roles and
  rejection of missing/extra labels. Interface/constraint coverage is 24 of 28
  reasons, with 234 templates per locale. Checks, work charges and legacy labels
  are unchanged. All 229 focused tests and warnings-denied Clippy passed.
- Method-parameter diagnostics retain whether the signature has implicit
  binders, omits an interface parameter or omits a determinant. JSON retains
  that cause. Implementation determination-coverage diagnostics retain the
  optional variable label separately from determinant-argument labels. Four
  source cases and four label-layout cases exercise the messages and missing
  label rejection. All 206 focused tests and warnings-denied Clippy passed.
  Interface/constraint coverage is 26 of 28 reasons, with 242 templates per
  locale. Existing checks, precedence, work charges and legacy labels remain
  unchanged.
- Determination declarations retain six typed causes and their optional causal
  labels. Conflicting global requirements, implementation prerequisites and
  inferred dependent tuples retain distinct roles. Improvement diagnostics
  retain the already formatted determinant key with expected/found tuples;
  human messages and JSON use these facts without parsing legacy help text.
  Six source cases and focused unit cases cover both locales, structured facts,
  optional labels and missing-fact rejection. Interface/constraint coverage is
  28 of 28 reasons, with 258 templates per locale. All 1,245 library tests,
  216 focused integration tests and warnings-denied Clippy passed. Existing
  semantic checks, failure precedence and work charges remain unchanged.
- Core construction presentation preserves all 14 existing `BuildError` causes,
  including identity exhaustion, structural limits and inconsistent binder or
  payload state. Messages identify compiler responsibility; JSON retains stable
  cause names without inventing source spans. The compile-time elaboration
  adapter rejects other, not-yet-covered failures. Both locales cover every
  constructor. All 84 focused tests and warnings-denied Clippy passed. This
  covers one of the six elaboration internal/resource reasons and brings the
  catalogue to 272 templates per locale. No checks or budgets changed.
- Elaboration presentation now also covers coverage resources, type resources,
  constraint resources and effect syntax reaching the pure Core path. Coverage
  retains `UsefulnessError` in its public failure payload rather than discarding
  the state/work distinction. Existing reason codes, legacy text, checks and
  charges are unchanged. Resource wording names the affected work without
  guessing whether an allocation refusal or deterministic budget caused it.
  Both locales and JSON cover the five new cases. The 32 data/ADT tests,
  two shared-budget tests and 86 diagnostic/catalogue tests passed, along with
  warnings-denied Clippy.
  Elaboration internal/resource coverage is five of six reasons, with 277
  templates per locale. Generic internal state still needs retained causes.
- Evidence validation now presents unavailable selected implementations and
  type/constraint resource failures with compiler responsibility, the retained
  validation span and a structured stage fact. Resource messages reuse the
  existing catalogue entries. Both locales and JSON cover the three reasons;
  the linked unavailable-implementation fixture also renders its actual failure.
  Unknown-identity and invalid-root failures remain unsupported pending more
  specific retained causes. Evidence-validation coverage is three of five
  reasons, with 278 templates per locale. All 137 evidence-validation tests,
  three catalogue tests and warnings-denied Clippy passed. No validation check,
  resource charge or diagnostic precedence changed.
- Core validation presents wrong-dialect, invalid-root, cyclic-graph and
  unreachable-node failures. Human output and JSON retain an optional exact
  arena-local node number; no source provenance is invented from invalid Core.
  Node-bearing locale entries reference the base explanation to avoid duplicate
  wording. Eight layouts cover both locales and the maximum node handle.
  Core-validation coverage is four of 23 reasons, with 286 templates per
  locale. All 1,247 library tests, three catalogue tests and warnings-denied
  Clippy passed. Validation behavior is unchanged; broader invariant categories
  remain unsupported pending precise cause retention.
- Resolver type/constraint resource failures and kind-checker resource failures
  now retain stage-specific human explanations, structured stage/resource facts
  and their existing source spans. The kind-failure adapter delegates source
  rejections to the established source-kind adapter and keeps internal-state
  failures unsupported. Both locales and JSON cover the three resource reasons.
  Resolver coverage is 29 of 30 reasons; kind internal/resource coverage is one
  of two. The catalogues contain 289 templates each. All 1,249 library tests
  and 86 diagnostic/catalogue tests passed, along with warnings-denied Clippy.
  No checks or resource limits changed.
- Kind internal-state presentation is partially migrated: six typed causes cover
  15 effect-registry and binder-owner failure sites. The stage failure retains
  an optional private cause alongside its unchanged legacy explanation; the
  renderer never parses that text. Both locales and JSON preserve the cause
  even when a test replaces the legacy wording. Checks, work charges and spans
  remain unchanged. Other kind internal-state causes are still unsupported,
  so the reason-family coverage count does not advance. The catalogues contain
  295 templates each. All 28 kind-checker tests, three catalogue tests and
  warnings-denied Clippy passed.
- A second kind internal-state batch adds 18 causes across 29 sites: linked
  binder-count/identity mismatches, retained type/row disagreements, unused
  binders and missing or conflicting canonical kinds. Together, the two batches
  cover 24 causes at 44 sites. The remaining internal-state paths still need
  migration, so reason-family coverage remains unchanged. All 28 kind-checker
  tests, three catalogue tests and warnings-denied Clippy passed. Catalogues
  now contain 313 templates per locale; checks, work charges and legacy wording
  remain unchanged.
- Kind provenance diagnostics add 20 causes across 21 sites for resolved types,
  effect-bearing types, computation/effect rows and hook arguments. Wording
  distinguishes missing, surplus and mismatched records without narrowing a
  check beyond what it establishes. The cumulative kind internal-state migration
  covers 44 causes at 65 sites; the family is still incomplete. All 28
  kind-checker tests, three catalogue tests and warnings-denied Clippy passed.
  There are 333 templates per locale. Existing checks, work charges, spans and
  legacy explanations are unchanged.
- Nominal, newtype and declaration-order kind failures add 23 causes at 24
  sites, including payload ownership/provenance and invalid preflight indices.
  The cumulative internal-state migration covers 67 causes at 89 sites. Shared
  lookup helpers and other remaining paths still require cause retention, so
  the family is not complete. All 28 kind-checker tests, three catalogue tests
  and warnings-denied Clippy passed. Catalogues contain 356 templates each;
  validation checks, resource charges and legacy text remain unchanged.
- Interface, effect-row and determination kind failures add 24 causes at 28
  sites. These retain canonical-kind, argument-count, row-tail ownership and
  invalid-determination distinctions without changing their checks or work
  charges. The cumulative migration covers 91 causes at 117 sites; body-free
  checking and shared lookup helpers remain. All 28 kind-checker tests, three
  catalogue tests and warnings-denied Clippy passed. Catalogues contain 380
  templates per locale. Kind internal-state family coverage remains partial.
- Kind internal-state presentation is complete locally. The final 32 causes
  cover body-free checks and shared lookup failures, bringing the cause enum to
  123 variants. The lookup helper now requires a typed cause; the plain-text-only
  internal constructor is removed. A conditional owner-kind check also retains
  its selected cause. Every production internal failure now carries a cause;
  malformed test-only payloads without one remain rejected by presentation.
  Both kind internal/resource reasons are covered, with 412 catalogue templates
  per locale. All 1,250 library tests, 86 diagnostic/catalogue tests and
  warnings-denied Clippy passed. Legacy text and checks remain unchanged.
  Preserving kind causes through callers that collapse them into broader
  failures remains part of the compiler-cause boundary work.
- Internal kind causes now survive all four kind-to-evidence adapters. The
  evidence failure retains the copyable cause and its original span alongside
  the unchanged evidence reason and primary span. Human output and JSON preserve
  cross-file origins without duplicating a same-span label. Resource failures
  still map to their owning type/constraint category. Eight real duplicate-binder
  cases exercise the adapters, source retention and resource mapping. All 138
  evidence-validation tests, three catalogue tests and warnings-denied Clippy
  passed. Catalogues contain
  413 templates each. Other unknown-identity/invalid-root causes remain unmapped,
  so reason-family coverage is unchanged.
- The retained kind cause/span now uses an opaque, copyable `KindFailureContext`.
  Evidence adapters use this carrier and the cause enum is private again. This
  provides a carrier for the public failure boundaries on the matching,
  selection and summary routes without exposing the 123 internal variants.
  Propagation through those routes remains outstanding; no coverage count or
  message wording changes in this refactor. The eight-case evidence-adapter
  regression test and warnings-denied Clippy passed.
- Direct kind failures entering evidence selection now retain their typed cause
  through elaboration and presentation. The elaboration adapter accepts admitted
  sources and shows the original kind location, plus the use location when
  distinct. The stable `type.internal` reason and legacy display stay unchanged;
  constraint-resource failures retain their classification. Tests cover absent,
  same-file and cross-file use context. Catalogues contain 414 templates per
  locale. Matching, canonical-environment and summary routes remain outstanding;
  reason-family coverage is unchanged. All 1,253 library tests, 86 diagnostic
  and catalogue tests, and warnings-denied Clippy passed. The existing missing
  canonical-binder corruption fixture now asserts its precise cause and span
  while retaining its atomic-publication and exact-budget checks.
- Kind context now crosses canonical-environment retention, head matching,
  overlap, selection, checked-summary results and their elaboration/resolution
  adapters. Imported nominal comparison adapters also forward retained context.
  Resolution preserves the import/use span and original kind span in human
  output and JSON. Existing resource categories and legacy displays remain
  unchanged. Two regression tests first demonstrated cause loss; adapter tests
  cover the connected routes and English/Bulgarian rendering. Catalogues contain
  415 templates per locale. Other summary invariants and unification still need
  cause retention; reason-family coverage is unchanged. All 1,257 library tests,
  97 diagnostic/catalogue/module-resolution tests and warnings-denied Clippy
  passed. Five existing corruption fixtures now assert the precise kind cause
  and span while retaining their small-stack, exact-budget and publication
  checks. Markdown lint and `git diff --check` passed.
- Unification now carries retained kind causes through inference, row checking,
  pattern refinement and selection adapters. Its copyable payload also retains
  an attached use span when a failure passes back from elaboration through
  unification and selection. A real invalid type application checks that pattern
  refinement reports a compiler-owned kind cause without publishing a solution.
  Existing generic registry/invariant failures remain unmapped. No catalogue or
  reason-family count changed. All 1,258 library tests and 86 diagnostic/catalogue
  tests passed. Warnings-denied Clippy passed after removing three unnecessary
  returns from the new match arms.
- Core node-bound failures now retain four causes: missing child edge, foreign
  arena, missing stored node and unrepresentable node identity. Graph traversal
  retains the child lookup's cause while preserving its existing parent-node
  context. Eight catalogue messages cover each cause with and without a node
  handle; JSON records the same cause and optional node. Real corruption cases
  cover missing and foreign-arena children, and an oversized index checks the
  identity conversion. Core coverage is now 5/23 reasons and overall coverage
  is 161/197. Catalogues contain 423 templates per locale. All 1,259 library
  tests, 86 diagnostic/catalogue tests and warnings-denied Clippy passed.
- Core match-coverage presentation distinguishes no arms, a redundant arm and
  uncovered inputs. Redundant arms retain their one-based ordinal for both
  localized messages and JSON. The private cause constructor now derives its
  reason, preventing mismatched reason/cause pairs. Tests exercise all three
  validation branches and six optional-node layouts; the existing deep-pattern
  teardown regression also checks presentation. Core coverage is 6/23 reasons,
  overall coverage is 162/197, and catalogues contain 429 templates per locale.
  All 1,260 library tests, 86 diagnostic/catalogue tests and warnings-denied
  Clippy passed. Markdown lint and `git diff --check` passed.
- Core provenance diagnostics distinguish missing origins, excessive origin
  depth, cross-source related origins and unadmitted sources. Span validation
  retains the original source-model failure, including range/UTF-8 offsets and
  source length; unrepresentable source lengths and indices remain distinct.
  Invalid spans are not rendered as source excerpts. Tests exercise four real
  origin mutations and 16 optional-node message layouts, with real range and
  UTF-8 source failures. Core coverage is 7/23 reasons, overall coverage is
  163/197, and catalogues contain 445 templates per locale. All 1,262 library
  tests, 86 diagnostic/catalogue tests and warnings-denied Clippy passed.
- Core recursive-binding diagnostics retain 13 causes across empty groups,
  initializer/function shape, polymorphic parameter/body checks, constructor
  identity/owner/payload checks and guarded recursive payload forms. The guarded
  data helpers return a retained failure cause instead of discarding it into a
  boolean; traversal, short-circuit order and resource charges stay unchanged.
  Tests cover group-shape failures, accepted/rejected constructor relationships
  and 26 optional-node localized/JSON layouts. Core coverage is 8/23 reasons,
  overall coverage is 164/197, and catalogues contain 471 templates per locale.
  All 1,265 library tests, 86 diagnostic/catalogue tests and warnings-denied
  Clippy passed.
- Core scope diagnostics retain 17 causes for binder ownership/declaration,
  local nominal scope ownership/type/effects, unresolved root requirements,
  scope-owner correspondence and missing analysis data. Continuation root
  requirements keep their existing separate reason. Shared unreadable-child
  wording is reused. Tests cover foreign/duplicate/unbound binders, unavailable
  scope-analysis data and 34 optional-node localized/JSON layouts. Core coverage
  is 9/23 reasons, overall coverage is 165/197, and catalogues contain 503
  templates per locale. All 1,267 library tests, 86 diagnostic/catalogue tests
  and warnings-denied Clippy passed.
- Core type-scope diagnostics retain 12 causes for missing generated binders,
  unresolved type and row inference, unbound root requirements, row-tail kinds
  and unavailable requirement-analysis data. Shared unreadable-child wording
  is reused. Tests cover type/row causes, requirement consumption and last-use
  retention, and 24 optional-node localized/JSON layouts. Core coverage is
  10/23 reasons, overall coverage is 166/197, and catalogues contain 525
  templates per locale. All 1,270 library tests, 86 diagnostic/catalogue tests
  and warnings-denied Clippy passed.
- Core newtype-conversion diagnostics retain ten causes for registry relations,
  nominal ownership, argument counts and kinds, and representation agreement.
  Check order and resource charges are unchanged. Existing corruption tests
  assert precise causes; 20 optional-node layouts cover localized text and
  JSON facts. Core coverage is 11/23 reasons and overall coverage is 167/197.
  All 1,271 library tests, 86 diagnostic/catalogue tests and warnings-denied
  Clippy passed.
- Core effect-identity diagnostics retain nine causes for effect/operation
  lookup, operation ownership and signature, argument counts and kinds, and
  resource-provider API module/method-count agreement. Check order and charges
  are unchanged. Tests cover argument/operation failures, forged effect metadata
  and 18 optional-node localized/JSON layouts. Core coverage is 12/23 reasons
  and overall coverage is 168/197. All 1,273 library tests, 86 diagnostic/catalogue
  tests and warnings-denied Clippy passed.
- Core discard and resource-escape diagnostics retain capture-checker causes
  and causal spans. Unproved discard, unfinished clause completion, required
  cleanup, abandoned cleanup handlers and escaping resource dependencies have
  distinct explanations. Core presentation now takes retained sources, reuses
  existing label wording and preserves compiler responsibility. Tests exercise
  cross-file labels, exact byte spans, missing sources and corrupted programs
  before and after transformations. These two reasons bring Core coverage to
  14/23 and overall coverage to 170/197.
- Eight Core type-operation causes now distinguish missing kind-analysis
  results, duplicate generated type binders and non-inert effect abstraction
  bodies. This reason remains partially presented and is not counted complete.
  The combined batch passed 1,275 library tests, 86 diagnostic/catalogue tests
  and warnings-denied Clippy.
- Core type-operation presentation now covers its remaining 29 causes: recorded
  abstraction/application forms, parameter ownership, method instantiation,
  quantified types, argument partitioning/kinds and row-substitution failures.
  Compound checks retain their existing precedence and resource charges.
  The shared table covers all 37 causes in 74 optional-node localized/JSON
  layouts. Existing type-application mutation tests also require presentation.
  Core coverage is 15/23 reasons and overall coverage is 171/197. All 1,275
  library tests, 86 diagnostic/catalogue tests and warnings-denied Clippy passed.
- Core pattern diagnostics retain 22 causes for depth, recorded/expected types,
  binders, tuple shape, constructor ownership/visibility, nominal arguments and
  payload presence. Shared binder collection retains its Pattern classification;
  other binder classifications are unchanged. Tests cover concrete type/arity/
  binder failures, the exact depth boundary and 44 optional-node localized/JSON
  layouts. Core coverage is 16/23 reasons and overall coverage is 172/197.
  All 1,277 library tests, 86 diagnostic/catalogue tests and warnings-denied
  Clippy passed.
- Core continuation diagnostics retain 17 causes for unbound/captured uses,
  branch agreement, clause consumption, use-state markers, clause contracts,
  resume argument/result types and effect relationships. Check order and charges
  are unchanged. Tests exercise capture rejection, missing/forged contracts and
  34 optional-node localized/JSON layouts. Core coverage is 17/23 reasons and
  overall coverage is 173/197. All 1,280 library tests, 86 diagnostic/catalogue
  tests and warnings-denied Clippy passed.
- Core effect-row diagnostics retain 25 causes for union/removal, dialect and
  linked-root constraints, request/resource/handler relationships, row-owner
  exclusion checks and missing inferred rows. Cleanup-row failures retain their
  source span. Existing permissive removal of absent scoped effects is unchanged.
  Tests cover row operations, row-owner failures, cleanup source retention and
  50 optional-node localized/JSON layouts. Core coverage is 18/23 reasons and
  overall coverage is 174/197. All 1,283 library tests, 86 diagnostic/catalogue
  tests and warnings-denied Clippy passed.
- Thirty handler causes now distinguish cleanup/registration scope ownership,
  callback forms/types, scope origins/effects, duplicate handler/continuation/
  operation identities and clause coverage/types/effects. Tests exercise wrong
  cleanup/registration body forms and 60 optional-node localized/JSON layouts.
  Hook contracts, registration edges and capture-analysis internal failures remain
  unmigrated, so Handler is not counted complete. All 1,285 library tests,
  86 diagnostic/catalogue tests and warnings-denied Clippy passed.
- Thirty further handler causes cover callback-scope ownership edges and
  hook-root operation/input/continuation/provenance contracts. Shared checks use
  the same messages. The handler table now covers 60 causes in 120 optional-node
  localized/JSON layouts. Corruption tests cover shared cleanup owners across
  transformations and hook-root operation/input identities. Registration
  forwarding contracts and capture-analysis internal causes remain; Handler is
  still not counted complete. All 1,286 library tests, 86 diagnostic/catalogue
  tests and warnings-denied Clippy passed.
- Registration forwarding contracts now reuse the common hook messages and
  retain 15 further causes for declaration lookup, generated binding/request/
  application/resume forms and the forwarding value chain. The handler table
  covers 75 causes in 150 optional-node localized/JSON layouts. Existing
  nine-mutation fixtures across three transformation states require presentation
  and assert specific causes for target, duplicate-binder, input and continuation
  corruption. Only capture-analysis internal failures remain in Handler's generic
  path; it is not yet counted complete. All 1,286 library tests, 86
  diagnostic/catalogue tests and warnings-denied Clippy passed.
- Runtime JSON reporting now reuses the 14 existing base reasons and bounded
  resource-report facts without adding failure categories. The separate writer
  retains primary and first teardown details, cleanup status, zero and maximum
  integer amounts, and the undetermined cause of storage reservation failure.
  It uses borrowed data, static fragments and stack numeric buffers, without an
  owned JSON tree or catalogue formatting. Five new tests cover base reasons,
  resource causes and phases, cleanup states, and failure at every output byte
  without retry or flush after a write error. These tests, 14 executable tests,
  13 CLI tests, four compile-time rendering/JSON tests and warnings-denied Clippy
  passed. Human/short runtime output and CLI format selection remain outstanding;
  this does not count runtime reasons as fully presented. The unapplied capture
  catalogue expansion was set aside; remaining internal presentation must reuse
  existing classifications and retain only missing explanatory facts.
- Runtime human and short reporting now borrow messages prepared before
  execution from the English or Bulgarian catalogue. The 56 new templates
  explain existing reasons, resource units, phases and cleanup states; no
  failure categories were added. Reporting uses fixed-size failure data and
  prepared strings without allocating or invoking the catalogue. Tests exercise
  both formats after dropping the catalogue, all base reasons, resource causes,
  phases, units and cleanup states, first-teardown retention, and failure at
  every output byte in all formats and both locales. All 1,286 library tests,
  14 executable tests, 13 CLI tests, three catalogue tests, four compile-time
  rendering/JSON tests, eight runtime-reporting tests and warnings-denied Clippy
  passed. Runtime presentation covers 14/14 base reasons, bringing presentation
  coverage to 188/197; this is not an effort estimate. CLI format selection,
  preparation fallback and the remaining compiler-internal paths are still open.
- Diagnostic option selection is implemented separately from program/root
  validation and execution settings. It scans all arguments, preserves root
  operands and non-UTF-8 paths, and selects exactly one valid format before the
  entry path even when ordinary invocation validation will fail. Locale tests
  cover explicit selection, LC_ALL/LC_MESSAGES/LANG precedence, empty values,
  unsupported names and non-UTF-8 fallback. Missing, repeated and misplaced
  options are rejected; duplicate locale options use environment fallback for
  reporting the invocation error. The proposed CLI spelling is
  `--message-format human|short|json` and `--locale NAME`. Six selection tests,
  14 executable tests, 13 CLI tests, three catalogue tests, one compile-time JSON
  test and warnings-denied Clippy passed. Selection is not yet wired into the
  executable; its current default remains unchanged.
- Compile-time and runtime reporting now have separate format-dispatch entry
  points. Missing or defective localization falls back to the original JSON
  record, retaining reasons, facts and labels; runtime fallback does not
  allocate. Compile-time human output prepares its message and labels before
  writing, so a later catalogue defect cannot publish a partial diagnostic.
  A regression test exposed interrupted-write retries in compile-time formatting;
  a small writer adapter now applies the existing no-retry policy to text and
  serialization. Tests cover absent, missing and malformed catalogue messages,
  label failure after a valid headline, byte-by-byte writer failure in both
  locales and all formats, and flush failure without retry. All 1,287 library
  tests, 14 executable tests, 13 CLI tests, 93 compile-time diagnostic/catalogue/
  reporting tests, nine runtime-reporting tests and warnings-denied Clippy
  passed. These APIs are ready for executable dispatch; the CLI itself is not
  wired yet and the remaining compiler-internal presentation gaps stay open.
- Explicit `--message-format` and `--locale` options now reach the executable's
  compile-time and runtime reporting interfaces. File dispatch reuses existing
  graph and phase adapters and their retained sources. Runtime and stdout-error
  text is prepared before execution. Tests cover source rejection, invocation
  option ordering, input failure, runtime failure, unchanged success output and
  exit statuses, and no retry on a failed diagnostic channel. Known adapter gaps
  emit explicitly marked JSON with the original reason and retained legacy
  details; they are not counted as completed human presentation. Bare source
  failures without an owning path also remain marked context gaps. Tool docs
  describe the staged options: invocation without either option still uses the
  existing default until complete coverage and downstream verification.
  Verification passed 1,287 library tests, 18 executable tests, 16 CLI tests,
  the diagnostic/input/catalogue/selection/reporting batch, four file-dispatch
  tests and warnings-denied Clippy. Default switching, remaining internal
  presentation, full milestone verification and downstream closeout remain open.
- Required excerpt tests exposed incorrect tab/Unicode caret alignment and
  omitted continuation lines for multiline spans. Human excerpts now use
  four-column tab stops and Unicode display widths, show the spanned lines,
  retain empty EOF lines, and align multi-digit line gutters. Source coordinates
  and JSON byte ranges are unchanged. The pinned `unicode-width` dependency
  supplies width calculation rather than a local Unicode table. Two table-driven
  regressions and the combined rendering, reporting, JSON, diagnostic, CLI and
  runtime-reporting batch passed (117 tests), as did warnings-denied Clippy.
- Core resource failures now render from the existing reason and optional node,
  without new causes or producer changes. The message covers work and storage
  limits without inventing an allocation-failure cause. The existing reason-only
  fixture covers English, Bulgarian and JSON with and without a node. Coverage
  is 189/197 reasons, not an effort estimate. The library, catalogue, reporting
  and diagnostic batch passed, as did warnings-denied Clippy.
- Added presentation for the existing Core node-type, application-type and
  registry reasons, and evidence unknown-identity and invalid-root reasons.
  Messages describe the retained failed relationship; they do not invent a
  more specific cause. Existing structured causes still take precedence. No
  producer or validation behavior changed. Extended table tests cover both
  locales, optional Core nodes, evidence spans and unchanged JSON facts.
  The library, catalogue, reporting, diagnostic and file-dispatch batch passed,
  as did warnings-denied Clippy. Reason coverage is 194/197; internal-state
  presentation, default switching and final verification remain open.
- Added explicit messages for the retained Core handler/capture-state category
  and elaboration invalid-state category. More-specific causes still take
  precedence; neither message invents missing details or source corrections.
  No producer behavior changed. Both locales and JSON are covered by the
  extended tables, and the executable test now checks the elaboration category
  as a structured fact rather than an unsupported-adapter fallback. The library,
  executable, catalogue, reporting, diagnostic and file-dispatch batch passed,
  along with warnings-denied Clippy. Reason coverage is 196/197; resolver
  internal-state labels, source-context gaps, defaults and closeout remain open.
- Bare source-model failures now render without an owning path. Admission and
  span-construction failures preserve their distinct reasons, responsibility,
  cause and numeric facts; unavailable paths and labels are omitted. Graph
  source errors share the fact mapping and retain their paths and import labels.
  Eleven pathless templates cover the existing source-error variants and the
  span-construction length case in both locales. Table tests cover all ten
  variants in both operations. File-dispatch, input, catalogue and reporting
  tests passed, followed by the five catalogue-contract tests and warnings-denied
  Clippy. Bare syntax/projection context and resolver labels remain open.
- Bare projection errors now render their existing recovery/structure cause or
  resource limit without requiring a source path. Graph projection errors use
  the same fact mapping and keep their source path and import label. Four
  pathless templates cover the retained variants in both locales. Catalogue
  contract tests, file-dispatch, input and catalogue integration tests passed,
  as did warnings-denied Clippy. Missing-source fallback remains tested with
  an unretained lexical source rather than an already-supported projection error.
- Bare and graph-owned syntax failures now share the existing stream merge and
  diagnostic adapters. Resource-only failures need no source path and retain
  their limit; empty failures report missing facts. Lexical/parser labels still
  require their actual source, with the original-error fallback used when an
  API caller discarded that context. The missing-source test now uses real
  lexer output. File-dispatch, input, source and reporting tests passed, along
  with warnings-denied Clippy. No syntax behavior or diagnostic ordering changed.
- Dependency-summary mismatch and failed validation now retain presentation
  context on the existing resolver error, preserving its reason and source span.
  Both explanations are catalogue-owned and JSON retains the boundary cause;
  kind-specific failures continue to retain their original context. The existing
  reordered-dependency regression now checks presentation. A two-case table
  confirms localization and JSON do not depend on the legacy prose. Library,
  diagnostic and module-resolution tests and warnings-denied Clippy passed;
  the additional prose-independence table passed separately. Other resolver
  internal labels remain open; this does not complete that reason family.
- Converted all six existing missing-scope checks to four shared resolver
  presentation contexts: file, lexical, local nominal and local constructor.
  The reason, checks and spans are unchanged. The prose-independence table
  covers each message in both locales and preserves its cause in JSON. All
  132 resolver tests, five catalogue-contract tests and warnings-denied Clippy
  passed. Other unconverted internal explanations remain open.
- Converted 26 declaration-order checks using one template per locale, retaining
  declaration kind and ordering problem as separate JSON facts. The checks,
  original reasons and spans are unchanged. A table covers all five kinds and
  five retained problems. All 133 resolver tests, five catalogue-contract tests
  and warnings-denied Clippy passed.
- Eight declaration-capacity checks now reuse identifier-exhaustion presentation
  with their actual identity space. Their existing internal-state reason and
  source span remain unchanged. The eight-case locale/JSON table, all 134
  resolver tests, five catalogue-contract tests and warnings-denied Clippy passed.
- Thirty resolver work-state checks now share one template per locale while
  retaining the affected part and missing/extra/wrong/incomplete distinction in
  JSON. All existing distinctions are covered by the locale/JSON table. The
  checks, reasons and spans are unchanged. All 135 resolver tests, five
  catalogue-contract tests and warnings-denied Clippy passed.
- Eleven effect, cleanup, registration and lexical-evidence missing-value checks
  now reuse work-state presentation. Only value names were added to the existing
  template and table; no new error category or template was needed. All 135
  resolver tests, five catalogue-contract tests and warnings-denied Clippy passed.
- Thirty-five metadata and missing-value checks now reuse work-state messages,
  including imported effect/nominal facts, constructor ownership, route ranks,
  newtype representations and method parameters. The locale/JSON table retains
  those distinctions. All 135 resolver tests, five catalogue-contract tests and
  warnings-denied Clippy passed; no checks or original reasons changed.
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
