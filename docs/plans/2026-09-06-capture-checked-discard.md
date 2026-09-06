# Capture and Checked Discard Implementation Plan

> Execute within this task using subagent-driven-development, with one product
> writer and independent semantic then code/resource reviews.

**Goal:** Implement [CP-0016](../proposals/CP-0016-capture-usage-and-checked-discard.md).

**Architecture:** Extend the hidden resume owner with a nullary completion
operation. Infer stored-capture and per-effect latent-request facts separately;
compose requests with live owners up to the selected handler. Independently
check Core and reuse the explicit evaluator's moved continuation storage.

**Tech stack:** Rust, existing Ash syntax/type/Core pipeline and explicit machine.

**Owner:** [TASK-0026](../tasks/TASK-0026-implement-capture-and-checked-discard.md).

**Base:** `da3ea62a1eee5642ec16a11210ee643e33d56574`.

## Checklist and work boundary

- [x] Reconstruct baseline, compare approaches, explain and obtain approval.
- [x] Record accepted proposal and allocate unused task/plan IDs.
- [x] Finish baseline verification before product edits.
- [x] Step 1: explicit completion carriers and usage checks.
- [ ] Step 2: inferred capture summaries and independent Core checking.
- [ ] Step 3: execution, accounting and complete adversarial corpus.
- [ ] Step 4: specification, reviews, full gate and retained evidence.
- [ ] Local integration and clean-checkout lifecycle after checkpoint closure.

Use high reasoning for compiler, summary, semantic and resource work; medium
for mechanical documentation checks. No level above high. Serialize product
changes; parallelize only independent read-only review. Each step records a
RED witness before production edits and focused GREEN after them. Record
actual outcomes, not predicted counts. The original 9-unit forecast includes
all four steps and closure; it is not a measured ledger.

## Step 1: Explicit completion carriers and usage checks

Files: `src/lexer/token.rs`, `src/lexer/mod.rs`, `src/parser/grammar.rs`,
`src/parser/project.rs`, `src/surface.rs`, `src/resolved.rs`, `src/resolve.rs`,
`src/elaborate.rs`, `src/core/effect.rs`, `src/core/dialect.rs`,
`src/core/transform.rs`, `src/core/validate.rs`, and their existing visitors.
Tests: `tests/effects_syntax.rs`, `tests/effect_typing.rs`,
`tests/effect_diagnostics.rs`, `tests/effect_core.rs`.

1. Add acceptance of `let _ = discard` as nullary syntax and rejection outside
   a clause. Add structural mixed-branch, missing, double and escape cases.
2. Run each changed test binary and retain the failure showing missing discard.
3. Add a distinct surface/resolved discard with the existing hidden owner.
   Extend existing usage dataflow rather than replacing it. Give Core a
   zero-child discard operation with owner, handler, Unit and empty row.
   Cover each traversal, transformation, scope and usage validation site.
4. Keep unproved discard fail-closed until Step 2 supplies proof; do not
   substitute a literal Unit in executable Core or trust source-only checking.
5. Run `cargo test --test effects_syntax --test effect_typing --test
   effect_diagnostics --test effect_core` as one shell command (without the
   prose line break), plus focused unit tests. Self-review and commit only
   this coherent increment. Independent semantic then code review follow.

## Step 2: Inferred capture summaries

Files: relevant checked-function/import carriers in `src/resolved.rs`,
`src/elaborate.rs`, effect Core and `src/core/validate.rs`; a small dedicated
analysis module is allowed if it keeps the existing files simpler.
Tests: `tests/effect_typing.rs`, `tests/effect_core.rs`,
`tests/effect_diagnostics.rs`, and existing module fixture helpers.

1. Add paired direct/helper-hidden A/B tests: outward B crossing live A rejects;
   B handled inside A accepts; B requested after A completion accepts. Add
   same-instance delegation, unrelated-effect separation, imported helper,
   ordinary closure and recursive helper cases.
2. Run the new cases and retain RED witnesses for missing analysis.
3. Implement bounded summary inference. Track unrestricted stored captures
   separately from request-carried live/unknown obligations. Compose known
   calls with lexical handler/owner state; join branches and recursive groups
   conservatively. Preserve exact effect identity and instantiated arguments.
4. Add unknown higher-order/open-row negative cases and paired resume-only
   positives. Do not infer safety from a declared effect row alone.
5. Independently reconstruct/check summaries in Core; add forged metadata,
   owner, type, row and transformed-Core tests before implementing each gate.
6. Run focused tests, self-review, commit, then semantic and code reviews.

## Step 3: Runtime and resource boundary

Files: `src/eval/machine.rs`, effect dispatch/traces as needed, analysis and
validation budget paths. Tests: `tests/effect_runtime.rs`, `tests/effect_core.rs`
and module-local exact-budget tests.

1. Add a runtime test discarding `perform Ask.value () + 100`, then returning
   42 from its clause; assert 42 and no resumed suspended work. Add surrounding
   handler continuation and mixed-branch observations. Retain RED.
2. Consume the existing captured segment without cloning, produce Unit and
   continue the clause. Release all retained frame accounting consistently
   with iterative nested continuation disposal. No cleanup callbacks.
3. Add exact-limit success, one-unit-short atomic failure, retry, deep teardown
   and capture-cell release witnesses before adjusting those paths.
4. Run `cargo test --test effect_runtime --test effect_core` and the focused
   analysis/machine unit tests. Review semantic then resource/code behavior.

## Step 4: Specification and closure

1. Update only the specification areas named by CP-0016, with executable
   examples and actual diagnostic behavior. Branch truth remains prospective.
2. Create `docs/design/effect-ash/capture-discard-evidence.md` with the actual
   acceptance/rejection matrix, limits, runtime observations and review results.
3. Run independent high-reasoning semantic review, then high-reasoning
   Rust/resource review; medium-reasoning Markdown/link/authority audit.
4. Correct actionable findings with RED/GREEN tests. Run `cargo xtask verify`,
   `git diff --check`, changed-link and authority checks.
5. Retain the tested checkpoint commit, remove completed CP/task/plan and fix
   indexes, then follow AD-0011 for local integration and clean feature removal.
   Do not merge `main`, push or tag.

## Execution record

Baseline `cargo test --workspace --all-targets` passed on 2026-09-06, exit 0,
before the product writer began. No checkpoint completion claim is made here.

### Step 1 evidence

- RED: `cargo test --test effects_syntax discard -- --nocapture` projected
  `Name`, not `Discard`; the corresponding `effect_typing` and
  `effect_diagnostics` filters failed with `UnknownName`. The new diagnostic
  wording assertion then failed on the old resume-only wording.
- GREEN, independently repeated by the parent:
  `cargo test --lib --test effects_syntax --test effect_typing --test effect_diagnostics --test effect_core --quiet`
  passed 982 library and 28 focused tests, exit 0.
- `cargo fmt --all -- --check` and `git diff --check` passed.
- The corpus covers zero-child row/transform handling, owner/type/row/state
  tampering, completion barriers, mixed and double completion, ordinary-error
  precedence, and 16,384-deep exact/one-short/retry usage traversal.
- Independent high-reasoning semantic and Rust/resource reviews: compliant
  for Step 1, no must-fix issue.
- All-target Clippy exposed missing `Discard` leaf cases in predecessor test
  visitors in `tests/interfaces.rs` and `tests/interface_selection.rs`. After
  those two test-only corrections, independently repeated
  `cargo clippy --workspace --all-targets -- -D warnings` and
  `cargo test --test interfaces --test interface_selection --quiet` passed,
  including all 84 interface tests. Formatting and diff checks also passed.
- All otherwise valid discard still fails at module publication and Core
  validation. These gates are temporary; no usable discard claim is made.

The read-only summary audit found that module checking already builds ordinary
typed Core bodies, but currently erases its effect operations. Step 2 should
reuse one private capture-analysis engine over those bodies and final Core,
preserving effect nodes for the checking path that needs them. Independent
validation means deriving facts again from final Core, not writing a second
algorithm or trusting exported claims. A second source control-flow graph is
unnecessary. Keep ordinary global and implementation method roots until the
analysis finishes; missing callable evidence means unknown, not safe.
