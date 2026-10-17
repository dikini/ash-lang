# TASK-0044: Native build CLI inputs

- ID: `TASK-0044`
- Status: complete
- Related: [issue #45](https://github.com/dikini/ash-lang/issues/45),
  [PR #47](https://github.com/dikini/ash-lang/pull/47),
  [AD-0014](../decisions/AD-0014-rust-verification-stage-reuse.md),
  [executable contract](../tools/ash.md#native-link-inputs)

> This task organizes authorized tool work. It does not define Ash semantics.

## Scope

The user prioritized issue #45 before the remaining semantics repairs. This
standalone delivery started at published Main `354c76b`; the reviewed row PR and
local ABI checkpoint remain separate. The user authorized unsigned commits and
merges. PM assigned integration after independent review and the required gate.

Add repeatable build-only `--native-static PATH` and `--native-shared PATH`
before the entry file. Preserve OS paths and the existing native-input vector's
mixed occurrence order and duplicates. Keep diagnostic operand ownership and
existing validation, linking, loader, refusal, cleanup and publication behavior.
Update usage and the tool contract, with focused and real native CLI evidence.

## Result

[PR #47](https://github.com/dikini/ash-lang/pull/47) is retained on remote Main at
unsigned merge `1573ae8352089f2d1fa03d0d2b06bc9b190470cc`, with parents `354c76b`
and reviewed candidate `e3a7b5f`. Its full tree, source, configuration, tools,
declared environment, external inputs and selected artifact pins equal the
freshly gated candidate. The private local Main and immutable `ffi-base` remain
unchanged by this delivery.

[Independent retained verification](https://github.com/dikini/ash-lang/pull/47#issuecomment-6240781721)
confirms that result. [Issue #45 acceptance](https://github.com/dikini/ash-lang/issues/45#issuecomment-6240835155)
is closed with its original body preserved. This completion record and active-index
cleanup are carried by [PR #44](https://github.com/dikini/ash-lang/pull/44);
their documentation retention remains pending there.

[Independent re-review](https://github.com/dikini/ash-lang/pull/47#pullrequestreview-5559860887)
found no actionable issue. The fresh `cargo xtask verify` passed all seven
stages with zero receipt reuse: 139 test harnesses report 3,964 passed, zero
failed and one intentionally ignored calibration measurement. The final
canonical before/after pins agree for 1,736 repository files, ten external
inputs and 14 configuration paths. This gate covers issue #45; the final combined
semantics gate remains a separate TASK-0043 obligation.

Four regressions failed before the adapter. Focused parser, diagnostic, ordinary
CLI and builder controls pass. The real CLI fixture requires distinct
static-first, shared-middle and static-last symbols and returns `42` after source
removal. Omitting the last archive refuses linkage and preserves the destination.
Loader setup applies only to the generated child. Default/override cache
selection and OS paths retain their focused evidence. Formatting, strict Clippy,
Markdown, links and authority checks pass; two pre-existing tool-documentation
line-length findings remain.

- [x] CLI/parser and OS-path evidence, including mixed order and duplicates.
- [x] Real static/shared CLI execution and preserved failure behavior.
- [x] Current help/documentation, focused checks and independent review.
- [x] Verified retention and issue acceptance.

Receipts, logs, exact commands and pins remain in
`.worktrees/semantics-alignment-context-20261017/issue-45-native-inputs`.
The successful gate is `full-gate-after-counter-repair`; `integration` records
unsigned merge parents, remote readback and retained equality. The earlier
failed `full-gate` remains failed and is retained with its causal diagnosis.

## Findings

The diagnostic selector must preserve native-path operands even when they
resemble `--locale` or `--message-format`. OS paths remain `OsString`/`PathBuf`;
validation belongs to the existing build API.

Two existing native-image tests shared a global callback observer. Their
parallel pair reproduced a false count where each case passed alone. The
observer now follows the synchronous calling thread, preserving every refusal
and zero/two callback assertion. Three concurrent cases, 20 additional parallel
pairs and the fresh full gate pass without global test serialization or a
production change.

## Cleanup

Required red/green, review, gate and retained receipts remain available. The
compatible cache and live row/ABI branches are preserved. PM owns continuing
TASK-0043. Retention of this completion record remains pending in PR #44.

## Deviations

None. No language, native-input discovery, linker passthrough, rpath or work-limit
change was introduced.
