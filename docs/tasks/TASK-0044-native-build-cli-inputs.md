# TASK-0044: Native build CLI inputs

- ID: `TASK-0044`
- Status: active
- Related: [issue #45](https://github.com/dikini/ash-lang/issues/45),
  [AD-0014](../decisions/AD-0014-rust-verification-stage-reuse.md),
  [executable contract](../tools/ash.md#native-link-inputs)

> This task organizes authorized tool work. It does not define Ash semantics.

## Dependencies

The user prioritized issue #45 before the remaining semantics repairs. Start
this separate PR at published Main `354c76b`; preserve the reviewed row PR and
the local ABI checkpoint. Reuse the sole product checkout and compatible cache,
Rust 1.97.1 and one Cargo job. The user authorizes unsigned commits and merges;
PM initiates integration after current independent review and required gates.

## Work

1. Add repeatable build-only `--native-static PATH` and `--native-shared PATH`
   before the entry file. Pass OS paths to the existing ordered native-input
   vector, preserving mixed occurrence order and duplicates.
2. Preserve diagnostic operand ownership and existing build validation,
   linking, loader, refusal, cleanup and publication behavior. Add focused
   parser, negative and real CLI-generated native regressions first.
3. Update all usage sites and the tool contract, publish a small Main-based PR
   and obtain independent review. Resume the saved semantics work afterward.

## Progress

The existing Rust build API already admits ordered static/shared files. Four
new regressions fail on Main `354c76b`: two parser cases, diagnostic operand
ownership and the public CLI's native-file diagnostic.

[PR #47](https://github.com/dikini/ash-lang/pull/47) publishes this standalone
CLI repair on `codex/issue-45-native-library-inputs` against Main `354c76b`.

The original candidate passed all 20 binary tests and 41 diagnostic/ordinary/module
CLI tests, five build-CLI tests and four existing builder controls. The real CLI
fixture requires distinct static-first, shared-middle and static-last symbols;
it returns `42` after source removal. Omitting the last archive refuses linkage
and preserves the existing destination. No Rust build driver supplies this
observation. Formatting and strict focused all-feature Clippy pass. Markdown,
links and authority checks add no finding; two pre-existing tool-documentation
line-length findings remain.

[Independent review](https://github.com/dikini/ash-lang/pull/47#discussion_r4304184287)
requested a fallback for the fixture's optional `CARGO_TARGET_DIR`. The original
test binary reproduces the unset-variable panic before child Cargo. The fixture
now follows neighboring tests: use the override, or the repository's `target`,
then `ffi-native-hosts`. Direct default/override checks avoid global environment
mutation. That new test and the native fixture pass in the assigned shared cache,
with formatting and strict affected Clippy. No additional native cache was built.
The repair's pins, red/green logs and timings are retained with the other receipts.

[Re-review](https://github.com/dikini/ash-lang/pull/47#pullrequestreview-5559719504)
cleared that candidate. Its fresh workspace gate passed format, metadata, check,
build and strict Clippy, then failed one of 1,879 library tests. Two native-image
tests shared a callback counter: both passed alone, while their first parallel
pair reproduced the same false callback observation. The synchronous callback
observer is now local to each test thread; all refusal and callback-count
assertions remain. The failed gate and isolated/parallel reproduction receipts
remain under `full-gate` in the evidence directory below. The changed candidate
passes all three native-image tests concurrently, 20 further parallel pairs,
the refreshed native CLI fixture, formatting and strict affected Clippy. It
requires independent re-review and a fresh full gate.

Focused commands, timings, hashes and equal source/configuration pins remain in
`.worktrees/semantics-alignment-context-20261017/issue-45-native-inputs`.
Re-review of the gate repair, the fresh pre-Main workspace gate, verified
retention and issue acceptance remain pending:

- [ ] CLI/parser and OS-path evidence, including mixed order and duplicates.
- [ ] Real static/shared CLI execution and preserved failure behavior.
- [ ] Current help/documentation, focused checks and independent review.
- [ ] Verified retention and issue acceptance.

## Verification

Run binary parser and diagnostic-option tests, CLI/build callers, formatting,
strict affected Clippy and manual documentation checks. Build and run a genuine
static/shared dependency fixture using the CLI, with loader configuration only
on the generated child. Keep source and build diagnostics and existing output
files on failure. Record exact inputs, commands, logs and timings. This focused
delivery requires a fresh full workspace gate before its Main integration;
the pending final combined semantics workspace gate remains separate.

## Discoveries

The diagnostic selector must preserve operands of build options even when a
native path resembles `--locale` or `--message-format`. Native paths remain
`OsString`/`PathBuf`; their validation belongs to the existing build API.

## Deviations

None. No language, native-input discovery, linker passthrough, rpath or work-limit
change is authorized by this task.
