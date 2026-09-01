# Human-First Localized Diagnostics Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Replace Ash's reason-first CLI failures with source-aware English and Bulgarian human diagnostics, compact localized log output, and a versioned locale-independent JSON-lines contract, while fixing and identifying the checked-export-summary regression that motivated the work.

**Architecture:** Phase-specific failures remain the semantic authority. They expose structured messages, facts, and spans to one borrowed presentation view; a retained source catalogue resolves spans; Fluent supplies words only; three renderers consume the same view. Checked-export-summary validation gains a small structured invariant cause that survives producer and importer boundaries.

**Tech Stack:** Rust 1.97.1, `fluent-bundle`, `fluent-syntax`, `unic-langid`, `serde`, `serde_json`, `unicode-width`, Cargo integration tests, Bash downstream verification.

---

This plan belongs to TASK-0021. It does not define Ash semantics. Implement it
in a dedicated worktree from the commit containing this plan; do not reuse any
registered Effect Ash worktree. The plan's parent, `5430432`, allocated
DN-0029, AD-0010, and TASK-0021 after checking every registered worktree.

Keep the checkpoint narrow:

- do not add color, editor protocols, runtime catalogue discovery, generated
  Rust, telemetry, or automatic reports;
- do not create a universal compiler error enum or move semantic decisions
  into rendering;
- do not retain all private types merely to satisfy summary validation;
- do not translate Ash spellings, types, operators, paths, or reason codes;
- use inline expected strings rather than adding a snapshot-test framework;
- add dependencies only when the task below first needs them.

## Task 1: Reproduce and repair the checked-export-summary regression

**Files:**

- Modify: `tests/library_imports.rs`
- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify: `src/elaborate.rs`
- Modify: `tests/module_resolution.rs`

**Step 1: Add the smallest honest regression.**

Add an integration fixture with one imported module that contains a public
type and an unreferenced private helper type with constructors. Its entry
module must import and use only the public API. Name the test
`unreferenced_private_constructor_families_do_not_invalidate_exports`.

Run:

```bash
cargo test --test library_imports unreferenced_private_constructor_families_do_not_invalidate_exports -- --exact
```

Expected before the fix: failure with `resolve.internal-state` while admitting
the dependency summary.

**Step 2: Add relation-specific authentication tests.**

In `src/resolved.rs`, extend the withheld-family fixture to establish all three
cases:

1. an unmatched local `Private` constructor family is valid access-only
   metadata;
2. a retained local hidden family still requires the exact constructor count;
3. an unmatched opaque family or a private family owned by another module is
   invalid.

Run the focused library tests and observe the new honest case fail before
changing the relation:

```bash
cargo test --lib withheld_constructor -- --nocapture
```

**Step 3: Correct the relation, not the retained closure.**

In `ExportSummary::authenticate`, continue matching opaque public types and
retained local hidden types exactly. Permit only unmatched
`WithheldExportKind::Private` families whose owner belongs to the summary's
module. These entries exist to diagnose source access and need not have a
hidden semantic carrier when no public fact refers to the private type. Reject
every other unmatched family.

Do not retain unreferenced private nominal facts in `hidden_nominals`; that
would enlarge every summary and contradict the specified minimal hidden
closure.

**Step 4: Name the failed invariant.**

Replace the authentication path's undifferentiated invalid result with:

- a small `SummaryInvariant` family (`Index`, `WithheldAccess`,
  `NominalClosure`, `InterfaceClosure`, `ImplementationClosure`,
  `BinderClosure`, and `KindClosure`);
- a `SummaryInvariantFailure` containing the family, a stable check identity,
  and only safe integer or enum facts needed to compare expected and observed
  state; and
- a `SummaryAuthenticationFailure` that distinguishes that invariant from the
  existing type-work and constraint-work exhaustion cases.

Group related checks; do not add one public enum variant per `if` statement.
Map private helper failures to the owning family at the `authenticate`
boundary.

Carry this cause through dependency admission. `ResolveError` may still expose
`ResolveReason::InternalState` as its stage reason, but it must retain and
expose the `SummaryInvariantFailure`; the import span is context, not a
replacement cause. Producer-side failure in `ExportSummary::freeze` must carry
the same cause through `ElaborationFailure`.

**Step 5: Authenticate before publication.**

At the end of `ExportSummary::freeze`, authenticate the constructed summary
before returning it. Use the existing work ledgers and preserve atomic
publication. Update exact resource tests for the additional bounded pass; do
not bypass the check under release builds.

Add one assertion that an honest checked module's published summary
authenticates, and retain existing corruption tests with assertions for the
new invariant family/check rather than generic invalid state.

**Step 6: Verify the repair.**

Run:

```bash
cargo test --test library_imports unreferenced_private_constructor_families_do_not_invalidate_exports -- --exact
cargo test --lib withheld_constructor
cargo test --test module_resolution
```

Expected: the honest private helper passes; corrupt opaque, foreign-private,
and retained-hidden families fail with named causes.

**Step 7: Commit.**

```bash
git add src/resolved.rs src/resolve.rs src/elaborate.rs tests/library_imports.rs tests/module_resolution.rs
git commit -m "fix: authenticate private export metadata"
```

## Task 2: Add the bounded catalogue foundation

**Files:**

- Modify: `Cargo.toml`
- Modify: `Cargo.lock`
- Create: `src/message.rs`
- Create: `locales/en-US.ftl`
- Create: `locales/bg.ftl`
- Create: `tests/diagnostic_catalogues.rs`
- Modify: `src/lib.rs`

**Step 1: Add failing catalogue-contract tests.**

Define tests for:

- complete key coverage for both catalogues;
- exact named-variable agreement for every key;
- parse and formatting errors;
- English, `en-GB` to English, `bg-BG` to Bulgarian, unsupported locale to
  English, and `C`/`POSIX` to English fallback;
- Bulgarian plural selection for counts 1 and 2; and
- verbatim preservation of an Ash identifier, type, operator, and path.

Run:

```bash
cargo test --test diagnostic_catalogues
```

Expected: compilation fails because the catalogue API does not exist.

**Step 2: Add only the selected dependencies.**

Pin `fluent-bundle` 0.16.0, `fluent-syntax` 0.12.0, and `unic-langid` 0.9.6.
Do not add Fluent's higher-level loader. Pin `serde` 1.0.229 with derive and
`serde_json` 1.0.151 now because the same typed message values become JSON
facts in Task 6.

Run:

```bash
cargo check --locked
```

Expected: the pinned dependency graph builds with Rust 1.97.1.

**Step 3: Implement a small compiler-owned message contract.**

In `src/message.rs`, define:

- `MessageId`, with `ALL` and its Fluent key;
- `ArgumentName`, limited to names actually used by diagnostics;
- `MessageValue::{Number, Code, Path}`, where `Code` covers Ash spellings,
  types, operators, and other verbatim source-facing forms;
- `Message`, containing an ID and a small ordered set of named values;
- `Locale`, supporting embedded English and Bulgarian; and
- catalogue parsing, validation, fallback, and formatting.

The compiler owns the required argument names for each `MessageId`.
`fluent-syntax` tests read variable references from each FTL message and require
an exact set match. Fluent owns word order and grammar only.

Start with the messages used by the catalogue tests, including type mismatch,
coverage count, import context, and compiler-owned checked-summary failure.

**Step 4: Prove the two catalogues.**

Write natural complete English and Bulgarian versions of the initial message
set. Put a short Bulgarian terminology comment at the top of `bg.ftl` for the
recurring words used there. Do not build a separate terminology system.

Run:

```bash
cargo test --test diagnostic_catalogues
```

Expected: all catalogue, fallback, plural, and verbatim-value tests pass.

**Step 5: Commit.**

```bash
git add Cargo.toml Cargo.lock src/lib.rs src/message.rs locales tests/diagnostic_catalogues.rs
git commit -m "feat: add embedded diagnostic catalogues"
```

## Task 3: Make diagnostic text structured and translatable

**Files:**

- Modify: `src/diagnostic.rs`
- Modify: `src/lexer/mod.rs`
- Modify: `src/parser/mod.rs`
- Modify: `src/parser/cst.rs`
- Modify: `src/module.rs`
- Modify: `src/resolve.rs`
- Modify: `src/kind.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/evidence_validation.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/eval/mod.rs`
- Modify: `src/driver.rs`
- Modify: `tests/diagnostics.rs`
- Modify: `tests/source_diagnostics.rs`

**Step 1: Specify the structured boundary in tests.**

Add tests that inspect a syntax, resolution, kind, type, interface, entry, and
internal failure without rendering. Each must expose:

- typed phase reason;
- responsibility (`Source`, `Compiler`, or `Environment`);
- structured primary and related label messages;
- typed expected/found facts where relevant;
- structured justified help; and
- safe developer details for an internal invariant.

Run:

```bash
cargo test --test source_diagnostics
cargo test --test diagnostics diagnostic_structure
```

Expected: compilation fails against the current string fields.

**Step 2: Replace presentation strings with messages and values.**

Change `SourceLabel.message` and `Diagnostic.help` from `String` to `Message`.
Change expected/found fields to typed `MessageValue`s. Add explicit accessors;
remove `Diagnostic::render_plain` so semantic types cannot silently select a
legacy renderer.

Do not replace phase reason enums. Do not introduce a universal semantic error
enum.

**Step 3: Migrate producer messages mechanically by phase.**

Replace every user-visible `SourceLabel::new(..., "...")`, expected/found
category string, and help string with a `MessageId` plus named values. Reuse
one ID for identical meanings. Keep identifiers and rendered Ash types as
`MessageValue::Code`.

After each phase, run its existing focused tests. Finally run:

```bash
rg -n 'SourceLabel::new\([^\n]*"|diagnostic\.(expected|found|help) = Some\([^M]' src
cargo test --test diagnostics
cargo test --test source_diagnostics
```

Expected: the search finds no retained raw user-facing diagnostic fragment and
the structural tests pass.

**Step 4: Complete both catalogues.**

Add every new `MessageId` to `en-US.ftl` and `bg.ftl`. Prefer complete
sentences. Do not concatenate translated fragments. Re-run the catalogue test
after each phase so missing keys or arguments fail immediately.

**Step 5: Commit.**

```bash
git add src locales tests/diagnostics.rs tests/source_diagnostics.rs tests/diagnostic_catalogues.rs
git commit -m "refactor: structure diagnostic messages"
```

## Task 4: Retain source context through failure boundaries

**Files:**

- Modify: `src/source.rs`
- Modify: `src/module.rs`
- Modify: `src/driver.rs`
- Modify: `tests/module_loading.rs`
- Modify: `tests/source_diagnostics.rs`
- Modify: `tests/architecture.rs`

**Step 1: Add failing source-resolution cases.**

Cover:

- a pipeline failure in the entry file;
- a related label in an imported file;
- an import-time read or module failure whose primary span is in the importer;
  and
- a span whose source is absent, which must become a named compiler invariant
  rather than display a raw numeric source ID.

Assert path, source text, and one-based scalar line/column resolution.

**Step 2: Make `SourceFile` clones cheap.**

Keep `SourceId` on `SourceFile`, but place display path, text, and line starts in
one private `Arc`-owned payload. Preserve the existing public methods and
equality behavior. This allows failures to retain admitted sources only on the
error path without copying source strings or changing every compiler node.

**Step 3: Retain only needed sources.**

Change the pipeline form of `FileFailure` to retain the graph's cheap
`SourceFile` clones beside `PipelineFailure`. Add constructors/accessors so
callers do not assemble the pair inconsistently. Refactor the graph pass into
an inner function returning `PipelineFailure`; the outer owner attaches the
loaded sources once on error.

For graph-loading errors with an import span, retain the importing
`SourceFile`. Syntax and projection failures already own their source. Entry
path failures with no admitted source need no source catalogue.

Update pattern-matching tests to use accessors. Do not add a global source
registry or reread files during rendering.

**Step 4: Verify ownership and architecture.**

Run:

```bash
cargo test --test source_diagnostics source_context
cargo test --test module_loading
cargo test --test architecture
```

Expected: every retained span resolves through a failure-owned source and all
existing ownership checks pass.

**Step 5: Commit.**

```bash
git add src/source.rs src/module.rs src/driver.rs tests/module_loading.rs tests/source_diagnostics.rs tests/architecture.rs
git commit -m "refactor: retain diagnostic source context"
```

## Task 5: Add the common presentation view

**Files:**

- Create: `src/presentation.rs`
- Modify: `src/lib.rs`
- Modify: `src/driver.rs`
- Create: `tests/diagnostic_presentation.rs`

**Step 1: Write exhaustive adapter tests.**

Create representative failures for input, syntax, resolution, kind, type,
interface, constraint, pattern/coverage, entry, evidence validation, Core
validation, runtime, and checked-export-summary families. Assert reason,
responsibility, message IDs, facts, label order, resolved sources, help, and
developer details independently of prose.

**Step 2: Implement a borrowed presentation view.**

Define a small view containing:

- stable reason code;
- responsibility;
- title/explanation messages;
- typed facts;
- ordered primary and related labels with resolved `SourceFile` references;
- optional help; and
- optional safe developer details.

The view borrows existing failures and sources. It does not clone diagnostics,
parse prose, or define new language classifications. One `FileFailure` may
produce several views for independently retained parser diagnostics.

Use exhaustive matches on the existing failure enums so a new reachable CLI
failure cannot compile without choosing presentation data. Keep phase-specific
adapter functions near the phase or in `presentation.rs`; keep source layout
and Fluent formatting out of them.

**Step 3: Verify all families.**

Run:

```bash
cargo test --test diagnostic_presentation
```

Expected: all listed families have one common structural view, and the syntax
fixture produces multiple ordered views.

**Step 4: Commit.**

```bash
git add src/lib.rs src/presentation.rs src/driver.rs tests/diagnostic_presentation.rs
git commit -m "feat: expose diagnostic presentation views"
```

## Task 6: Implement human, short, and JSON renderers

**Files:**

- Modify: `Cargo.toml`
- Modify: `Cargo.lock`
- Modify: `src/source.rs`
- Replace: `src/render.rs`
- Create: `tests/diagnostic_rendering.rs`
- Create: `tests/diagnostic_json.rs`

**Step 1: Add failing human layout tests.**

Use inline expected output for:

- a one-line source rejection;
- expected/found and help;
- two labels in different files;
- a compiler-owned checked-summary failure at an import;
- tabs at four-column stops;
- Cyrillic, combining marks, and wide characters;
- zero-width and multiline spans; and
- two parser diagnostics in source order.

The human heading must be the localized explanation, followed by path,
one-based line/column, excerpts and labels, then help/developer detail when
present, and finally `reason: <code>`. Internal output must state that Ash
failed and must not suggest changing valid source.

**Step 2: Add display-width support only.**

Pin `unicode-width` 0.2.2. Keep `SourceFile::location`'s one-based scalar
columns for reported locations. Add private excerpt helpers that expand tabs to
four-column stops and use Unicode display width only to align underline
markers. Do not add wrapping, color, or terminal detection.

**Step 3: Implement human and short rendering.**

Replace the legacy plain renderer with renderers over presentation views.
Human output uses Fluent and source layout. Short output is one localized line
per view containing path/location when available and the stable reason. It is
for logs, not parsing.

**Step 4: Specify JSON v1 before implementing it.**

Add exact JSON-lines tests for this minimum schema:

- `schema_version: 1`;
- `reason`;
- `responsibility`;
- ordered typed `facts`;
- ordered `labels`, each with role, path, byte start, and byte end; and
- optional structured `developer` details.

Do not include localized prose. Use paths and byte spans as the machine source
contract; line/column remains a human display view. Each diagnostic is one
JSON object followed by one newline, including multiple parser diagnostics.

**Step 5: Implement JSON with Serde.**

Serialize dedicated version-1 DTOs. Do not serialize internal compiler structs
directly and do not hand-escape JSON.

**Step 6: Verify renderers.**

Run:

```bash
cargo test --test diagnostic_rendering
cargo test --test diagnostic_json
```

Expected: English and Bulgarian human/short fixtures pass; Unicode markers
align; JSON is byte-identical under `en-US` and `bg` and parses one object per
line.

**Step 7: Commit.**

```bash
git add Cargo.toml Cargo.lock src/source.rs src/render.rs tests/diagnostic_rendering.rs tests/diagnostic_json.rs
git commit -m "feat: render human and machine diagnostics"
```

## Task 7: Expose explicit CLI format and locale selection

**Files:**

- Modify: `src/main.rs`
- Modify: `tests/cli.rs`

**Step 1: Add CLI parsing tests.**

Specify:

```text
ash [--root name=path]... [--message-format human|short|json] [--locale locale] <entry-file>
```

Options must precede the entry path. `human` is the default. Repeated format or
locale options and unknown values are usage failures. `--locale` overrides
`LC_ALL`, then `LC_MESSAGES`, then `LANG`; strip POSIX encoding/modifier
suffixes and normalize `_` to `-`. `C`, `POSIX`, absent, and unsupported values
select English.

Test exit statuses and channels: source rejection remains 1, invocation/input/
compiler/runtime failure remains 2, success remains 0, and failure output
remains stderr-only.

**Step 2: Parse presentation options outside `RunConfiguration`.**

Introduce a private CLI configuration that contains the unchanged driver
`RunConfiguration`, message format, and selected locale. Do not make compiler
execution depend on output format or locale.

Render configuration and root errors through the same presentation path. If
writing output fails, retain the minimal fixed English emergency message
because catalogue rendering cannot repair a failed output channel.

**Step 3: Verify the executable boundary.**

Run:

```bash
cargo test --bin ash
cargo test --test cli
```

Expected: all formats and locale precedence behave exactly as specified, with
unchanged success output and exit classifications.

**Step 4: Commit.**

```bash
git add src/main.rs tests/cli.rs
git commit -m "feat: select diagnostic format and locale"
```

## Task 8: Remove the mixed legacy path and update terminology

**Files:**

- Modify: all tests still asserting legacy rendering
- Modify: `docs/tools/ash.md`
- Modify: `spec/name-resolution.md`
- Modify: `spec/static-semantics.md`
- Modify: compiler comments or docs found by the searches below

**Step 1: Prove the legacy path is gone.**

Run:

```bash
rg -n 'render_plain|primary: source|related: source|body-free authentication' src tests docs/tools spec
```

Expected before cleanup: remaining legacy tests or terminology are listed.

Update every reachable CLI assertion to human output or, when it asserts a
stable contract, JSON fields. Keep direct typed-reason assertions where the
test is about compiler semantics.

**Step 2: Document the formats and contract.**

Update `docs/tools/ash.md` with exact usage, locale precedence, human and short
examples, JSON v1 fields, stdout/stderr behavior, exit statuses, and the rule
that human wording/layout are not automation contracts.

In the specification's import sections, use “checked export summary” and state
once that it omits definition bodies. Do not change static judgments or Ash
validity. Internal Rust type names need not be renamed merely to remove every
historical word; remove the term from reader-facing diagnostics and docs where
it obscures the relationship.

**Step 3: Run the affected suite.**

```bash
cargo test --tests
```

Expected: no test depends on the first line of human prose or raw process
source IDs; structural and JSON tests retain stable contracts.

**Step 4: Commit.**

```bash
git add src tests docs/tools/ash.md spec/name-resolution.md spec/static-semantics.md
git commit -m "docs: define the diagnostic contracts"
```

## Task 9: Migrate ash-doc automation and verify the eight retained entries

**Repositories and files:**

- Modify in `../ash-doc`: `content/checks/lib.sh`
- Modify in `../ash-doc`: specialized rejection verifiers found by
  `rg -l 'primary: source|sed -n .1p.*stderr' content -g 'verify.sh'`
- Modify in `../ash-doc`:
  `lab/lib-ash-migration/body-free-summary-authentication/checks/verify.sh`
- Modify in `../ash-doc`:
  `lab/lib-ash-migration/body-free-summary-authentication/README.md`
- Modify in `../ash-doc`: migration roadmap/index links that describe the
  resolved evidence

**Step 1: Change automation to request JSON.**

Invoke Ash with `--message-format json --locale en-US` for every intentional
rejection. Parse each JSON line with the repository's existing available JSON
tool, or a short standard-library script if none exists. Assert reason,
responsibility, path, and byte ranges as data. Do not grep serialized JSON or
human messages.

Accepted-program checks continue to use ordinary success output and need no
format flag.

**Step 2: Turn the eight-entry lab into fixed-regression evidence.**

Preserve source hashes. Run the new Ash worktree against all eight entries and
record their actual current-language outcomes:

- search entries should reach their ordinary later checking or execution
  result;
- red-black and accepted iterator clients may reach the specified missing
  implementation-selection rejection rather than predecessor success;
- opaque iterator cases should reach `resolve.opaque-constructor` with their
  causal cross-file labels.

Do not assume predecessor outcomes where current `lib-ash` semantics differ.
Assert each observed reason/status/output and byte span in JSON. Rewrite the
README as resolved migration evidence: explain the set mismatch and the
restored later outcomes, and distinguish exact historical output from the new
contract.

**Step 3: Verify ash-doc.**

Run the focused eight-entry verifier against its required exact predecessor
checkout and the implementation worktree, then run:

```bash
bash -n ../ash-doc/content/checks/lib.sh
find ../ash-doc/content ../ash-doc/lab -path '*/checks/verify.sh' -print0 | xargs -0 -n1 bash -n
```

Run the ash-doc repository verifier required by its active migration task with
the new Ash worktree. Expected: all rejection checks consume JSON and the eight
entries no longer stop at a checked-summary compiler failure.

**Step 4: Commit ash-doc separately.**

Use an ash-doc commit that names the automation migration and resolved
evidence. Do not combine changes from the two repositories in one commit.

## Task 10: Full verification, review, and artifact closure

**Files:**

- Modify: `docs/tasks/TASK-0021-implement-human-diagnostics.md`
- Modify if evidence changed: `docs/design/DN-0029-human-diagnostic-presentation.md`
- Remove when the task completes: `docs/tasks/human-diagnostics-execution-plan.md`

**Step 1: Run focused contract checks.**

```bash
cargo test --test diagnostic_catalogues
cargo test --test diagnostic_presentation
cargo test --test diagnostic_rendering
cargo test --test diagnostic_json
cargo test --test library_imports unreferenced_private_constructor_families_do_not_invalidate_exports -- --exact
cargo test --bin ash
```

**Step 2: Run complete Ash verification.**

```bash
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
cargo xtask verify
```

Expected: all commands exit 0. Inspect the output; do not infer success from a
quiet or truncated command.

**Step 3: Check documentation and boundaries.**

Run the repository's Markdown/link checks through `cargo xtask verify`, then
manually confirm:

- spec changes only rename/explain the compiler representation;
- AD-0010 remains the architectural authority;
- both catalogues are complete;
- no human prose is asserted as an automation contract;
- JSON examples agree with tests; and
- excluded mechanisms were not added.

**Step 4: Request code review.**

Use `superpowers:requesting-code-review`. Resolve findings by severity and
rerun the affected focused checks plus `cargo xtask verify`.

**Step 5: Close TASK-0021 only after both repositories verify.**

Record the exact Ash and ash-doc commits, commands, outcomes, catalogue
selection, summary root cause, and any deviations in TASK-0021. Remove the
temporary execution plan and active-task/index entries according to the
project artifact policy only when the implementation is retained and no work
remains.
