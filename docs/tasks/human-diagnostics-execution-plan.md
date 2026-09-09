# Human Diagnostic Implementation Plan

**Goal:** Precise human diagnostics and a stable JSON contract with little
message-maintenance work.

**Architecture:** Existing phase errors own semantics and facts. Compile-time
presentation renders one diagnostic at a time from those facts and embedded
catalogues. Runtime reporting has a separate interface and resource contract.

**Tools:** Rust, the selected Fluent integration, Serde JSON and Unicode display
width support where required. Use existing tests and inline expected output.

This temporary plan belongs to
[TASK-0021](TASK-0021-implement-human-diagnostics.md).
[AD-0010](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md)
governs its architecture and defaults. The
[design note](../design/DN-0029-human-diagnostic-presentation.md) records the
completed catalogue comparison. The
[compiler repair](../design/migration-repair-evidence.md) is complete on main.

## Execution boundaries

- Start implementation in a local `.worktree/` from verified current main.
- For each slice: add focused tests, demonstrate the expected failure,
  implement the smallest change, rerun tests, review and commit unsigned.
- Preserve language acceptance, causal order, resource limits, stdout and exit
  classifications. Runtime reporting invokes no source effects or recovery.
- Keep the current CLI default during internal slices. Switch only after all
  failure paths and downstream compatibility checks are ready.
- Do not repeat catalogue selection, build a universal error enum, parse prose,
  add global source registries, or make compiler phases print diagnostics.
- No messaging framework, code generator, color, wrapping, editor protocol,
  runtime catalogue loading, telemetry or translation service is required.

## Slice 1: One compile-time diagnostic end to end

Affected files: `src/diagnostic.rs`, `src/elaborate.rs`, `src/source.rs`,
`src/driver.rs`, `src/render.rs`, `src/lib.rs`, `Cargo.toml`, `Cargo.lock`.
Add `src/message.rs`, a small `src/presentation.rs`, `locales/en-US.ftl`,
`locales/bg.ftl`, and the focused tests below as needed.

1. Add a type-mismatch fixture. Inspect reason, expected/found facts and span
   independently of rendering. Add English and Bulgarian human/short output
   and locale-independent JSON expectations. Run
   `cargo test --test diagnostic_rendering` and
   `cargo test --test diagnostic_json`; confirm the new path is absent.
2. Declare each message identity and its typed named arguments once. Missing,
   extra or wrong-typed construction arguments must be caught by the Rust
   interface or explicit contract tests. Centralize any key/argument
   enumeration; do not add parallel registries or a general schema language.
3. Add the selected Fluent dependencies and both translations. Verify compatible
   versions against the repository toolchain and retain Cargo.lock; do not copy
   unverified pins from an old plan. Catalogue tests cover completeness,
   argument agreement, formatting, locale fallback and verbatim Ash values.
   Run `cargo test --test diagnostic_catalogues` and `cargo check --locked`.
4. Retain admitted sources through the failure owner without rereading files.
   Use existing ownership first; add a shared private SourceFile payload only
   if needed to avoid copying text. Render a borrowed view to a supplied writer,
   without requiring a complete intermediate output string.
5. Define JSON v1 with Serde DTOs, not serialized compiler internals: schema
   version, reason, responsibility, named typed facts, ordered labels with
   primary/related role, semantic relationship, path and byte range, and
   optional structured developer details. Name relationships from actual
   causal data. Derive message arguments and JSON from the same facts.
   Translation keys and prose are not machine semantics.
6. Rerun the three diagnostic tests. Add a second message using the same API
   and show that no renderer mapping changes. Change wording in a test
   catalogue and verify structural diagnostics and JSON stay identical.
   Review this maintenance workflow before broad migration. Do not compensate
   for duplicate mappings with more registries or generators.

This internal slice does not switch the CLI default. Do not substitute generic
messages to make incomplete migration appear complete.

## Slice 2: Complete compile-time presentation

Affected files: producers in `src/lexer/`, `src/parser/`, `src/module.rs`,
`src/resolve.rs`, `src/kind.rs`, `src/elaborate.rs`,
`src/evidence_validation.rs`, `src/core/validate.rs`, plus source ownership,
adapters, messages, catalogues and renderers from slice 1.

1. Add structural cases for input, syntax, resolution, kind, type, interface,
   constraint, pattern, coverage, entry and internal failures. Include several
   parser diagnostics and cross-file labels. Run
   `cargo test --test diagnostic_presentation` to expose missing coverage.
2. Migrate one phase at a time from prose strings to checked messages. Preserve
   typed reasons and facts. Detection sites select precise messages; adapters
   expose retained data, never reconstruct semantic policy. Add help only when
   facts justify it. Complete translations with each phase.
3. Retain source context at pipeline and graph-loading failures. Add entry and
   import cases in `tests/source_diagnostics.rs` and `tests/module_loading.rs`.
   A missing source is a compiler invariant; preserve the original diagnostic
   rather than replacing it with a layout failure.
4. Test one-based scalar locations, four-column tabs, Cyrillic, combining and
   wide characters, zero-width and multiline spans, and several files. Use
   display width only for marker alignment. Preserve label and diagnostic order.
5. Run `cargo test --test diagnostics`,
   `cargo test --test source_diagnostics`,
   `cargo test --test module_loading`,
   `cargo test --test diagnostic_catalogues`,
   `cargo test --test diagnostic_presentation` and
   `cargo test --test diagnostic_rendering`. All must pass.

## Slice 3: Preserve internal compiler causes

Affected files: `src/resolved.rs`, `src/resolve.rs`, `src/elaborate.rs`,
`tests/module_resolution.rs`, diagnostic adapters and catalogues.

1. Add corruption tests showing that a specific failed relationship survives
   producer publication and importer context. Resource exhaustion remains
   distinct from an invariant violation. Run
   `cargo test --lib withheld_constructor` and
   `cargo test --test module_resolution`; demonstrate lost cause information.
2. Carry a small private structured cause and safe facts through existing
   boundaries. Use only distinctions justified by the checks. Do not add a
   public variant per conditional or change authentication, hidden closure,
   resource accounting or publication order.
3. Add human/JSON assertions identifying compiler responsibility without
   unsupported source advice. Rerun focused tests and the original migration
   corpus according to the repair evidence. Require its recorded successes
   and source rejections, not merely absence of internal failures.

## Slice 4: Runtime reporting, separately

Affected files: `src/render.rs`, `src/main.rs`, report types in `src/eval/`
only if needed, `tests/cli.rs` and focused rendering/JSON tests.

1. Inspect `write_runtime_report` and its executable tests. Add expectations
   for primary failure, first teardown failure, cleanup status, resource kind,
   phase, requested/available amounts and writer failure in all three formats.
2. Expose a distinct runtime reporting entry point. Do not route runtime
   failures through allocating compile-time presentation or select safety with
   a flag. Share only helpers that satisfy the runtime contract.
3. Prepare any locale state before execution. Resource reporting uses bounded
   writes and static localized fragments or prepared data; it cannot require
   allocation or Fluent formatting after failure. JSON preserves runtime facts
   and schema conventions without constructing an owned DTO tree. Use
   writer-based serialization only where it meets these guarantees.
4. Retain existing failure-injection tests and cover each new format: no source
   effects, recovery or allocation-dependent resource reporting; preserved
   primary/teardown/cleanup facts; stop at the first failed write without retry
   or recursive reporting. Run `cargo test --bin ash`,
   `cargo test --test cli`, `cargo test --test diagnostic_rendering` and
   `cargo test --test diagnostic_json`. All must pass before CLI integration.

## Slice 5: Defaults and CLI integration

Affected files: `src/main.rs`, `tests/cli.rs`, rendering, messages and locale
handling. Presentation configuration stays outside RunConfiguration.

1. Add table-driven tests for AD-0010 defaults before implementation: human
   default; explicit format; explicit locale over nonempty LC_ALL, LC_MESSAGES
   and LANG; POSIX spelling; parent fallback; unsupported, malformed, C/POSIX
   and absent locales selecting English.
2. Test missing/repeated options, invalid formats and argument-order
   permutations. Invocation failures honor exactly one valid format before the
   entry path, otherwise human; locale fallback is independent. Keep options
   before the entry path and the existing root syntax.
3. Dispatch to the distinct reporting interfaces. Collections use an ordered
   loop. Source rejection stays status 1; invocation/input/compiler/runtime
   failure stays 2; success stays 0. Diagnostics remain stderr-only and success
   stdout remains unchanged.
4. Test catalogue-failure fallback: retain original reason and available facts,
   preserve JSON framing and avoid recursive diagnostics. Missing required
   translations still fail tests. Stop on stderr failure; a stdout failure may
   receive at most one bounded report on stderr.
5. Run `cargo test --bin ash`, `cargo test --test cli`,
   `cargo test --test diagnostic_catalogues` and
   `cargo test --test diagnostic_json`. Remove legacy compile-time rendering
   after every reachable failure has an intentional format path. Runtime
   bounded reporting remains intentional behavior, not a legacy exception.

## Slice 6: Documentation, downstream handoff and closeout

Affected files: `docs/tools/ash.md`, diagnostic tests, TASK-0021 and this plan.
Touch `spec/name-resolution.md` or `spec/static-semantics.md` only for justified
terminology corrections, never to define semantics through this task.

1. Document formats, JSON fields and compatibility, defaults, runtime reporting
   guarantees, stderr failures and unchanged exit/stdout behavior. Include a
   short contributor example for adding a message and updating a translation.
2. Coordinate ash-doc checks at adoption of the new CLI: request JSON and test
   facts and causal labels, not prose. Inspect that project's instructions and
   exact pin before authorized edits; preserve historical pins and evidence.
   A canary is not an edition migration. Record outstanding coordination rather
   than silently expanding this repository's implementation scope.
3. Run all focused tests above, then `cargo xtask verify`. Check Markdown,
   links, authority and `git diff --check` separately. Review message precision,
   translation quality and the addition/update workflow, not just coverage.
4. Obtain implementation review, resolve findings and rerun affected tests and
   the full gate. Record exact verified commits and downstream adoption checks
   before declaring the CLI transition complete.
5. Integrate under the user's merge/signing instructions and verify main.
   Retain evidence and remove completed task/plan artifacts. Clean the worktree
   only after its commits are retained on main. Do not push or tag implicitly.
