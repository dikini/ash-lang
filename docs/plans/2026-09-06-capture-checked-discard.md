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
- [x] Step 2: inferred capture summaries and independent Core checking.
- [x] Step 3: execution, accounting and complete adversarial corpus.
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
   Retain the captured residual associated with each request, including
   restored handler boundaries and ordinary return to the caller. A resume
   must use that residual, not the owning handler's whole request set. Preserve
   this information across imports and keep callee consumption scoped to its
   own activation.
4. Add unknown higher-order/open-row negative cases and paired resume-only
   positives. Do not infer safety from a declared effect row alone.
5. Independently reconstruct/check summaries in Core; add forged metadata,
   owner, type, row and transformed-Core tests before implementing each gate.
   Include nested discard that skips outer completion, restored requests with
   a live owner, consumed-before-capture and restored-inner-handler positives,
   and corresponding imported-helper cases.
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

### Step 2 unresolved representation boundary

Selected-residual binding corrects the independently reproduced nonrecursive
prefix-replay defects. The parent subsequently passed 990 library and 60
focused tests, explicitly excluding two failing recursive activation tests,
plus all-target Clippy. Both recursive tests fail with
`TypeResourceExhausted`, not with their required acceptance or safety result.

An additional tests-only resume-only fixture with an opaque repeating request
also exhausts inference work. It has no recursive source function or discard.
Its handler clause performs `A`, resumes the repeating `H` request, then
performs `B`. Thus finite recursive-call summaries alone cannot establish
termination: handler-induced return continuations also accumulate.

Product edits were frozen at this point. The existing residuals are composition terms whose
identities can grow with return depth. Neither a loop alias nor request-key
history truncation establishes a sound finite replacement. A continuation
graph is a candidate, not a proved or implemented solution. Any replacement
must bound captured-continuation bindings as well as return positions, retain
acyclic prefix precision and activation-local consumption, and preserve the
accepted positive/negative corpus. No budget increase, precision restriction,
runtime implementation or integration is authorized by these test outcomes.

### Approved Step 2 redesign sequence

The user subsequently approved the larger private-analysis redesign. The
earlier freeze is lifted. The accepted CP-0016 behavior and complete checkpoint
gate remain unchanged. Use one fresh implementation agent at high reasoning;
the parent owns task documentation and independent review coordination.

1. Reproduce the two `recursive_activations` tests in `effect_diagnostics`
   and `unknown_request_loop_keeps_a_finite_resume_only_handler_summary` in
   `effect_typing`. Keep their actual RED results; neither a larger limit nor
   a safety rejection substitutes for required convergence and acceptance.
2. Replace the private control analysis in `src/core/capture.rs`. Derive
   control/frame positions from existing Core. Use finite graph identities for
   returns and captured bindings, not nested composition terms or histories.
   Request selection must retain the captured prefix through its nearest
   matching handler. Resume consumes the selected owner occurrence and
   reconnects that prefix to the clause's remaining work. Preserve live outer
   recursive owners and already-consumed current owners separately. Keep
   intrinsic opaque-request evidence local to the relevant capture; normal
   callee return must not retain an immortal unknown-owner marker.
3. Use a sparse, budgeted graph representation. State the finite allocation
   domain and explain capture/consume/splice transitions before relying on
   them for safety. Fresh/summary distinctions or frozen snapshots are tools
   for this obligation, not extra language mechanisms. Do not add a source
   CFG, a runtime value interpreter, or a second production analysis engine.
4. Preserve the value prepass, type/effect helpers and checking entry points
   where valid. In `src/resolved.rs`, `src/resolve.rs` and `src/elaborate.rs`,
   adapt private summary payload/retention only as required. Settle export
   substitution stability: either justify the closed request projection or
   retain the necessary handler/control information. The independent final
   Core pass still derives facts from actual Core, never a source proof flag.
   The imported specialization pair now reproduces unsafe acceptance when
   generic effect arguments become equal. Retain that pair, add its linked
   Core counterpart, and cover generic bodies whose internal discard proof
   would otherwise assume their type parameters can never coincide.
5. Run the three loop regressions first, then the source/raw-Core prefix pairs,
   restored-handler binding, unknown/known exact-effect pairs and imported
   suffix/caller-return tests. Add a repeated-request handler pair observing
   consumed owners before unwinding requests. Preserve diagnostic precedence.
6. Retain finite-work, exact/one-short/retry, deep success/failure teardown and
   compact import numbering evidence. Adapt `tests/architecture.rs` only for
   actual new carrier ownership. Run the library and focused effect tests,
   architecture guards, formatting, all-target Clippy and diff checks.
7. Freeze the resulting implementation for independent semantic review,
   then independent Rust/resource review. Fix and re-review findings. Retain
   a coherent Step 2 commit only after the gate passes; then execute the
   existing runtime Step 3 and complete Step 4.

The replacement retains complete control, rather than an evaluated request
projection. Consequently, publication with no local or retained imported
discard needs only structural compilation and authentication, not an
abandonment query. Callers that contain discard still query the retained
control after specialization. This does not publish a partial permission or
skip ordinary exact-once validation. The cyclic opaque-request test includes
discard and pairs safe post-resume work with unsafe pre-resume work, so this
simplification does not replace testing the cyclic abandonment query.

### Step 2 verified inference checkpoint

The parent independently passed 996 library and 68 focused tests, including
the seven unchanged runtime tests; all-target Clippy, formatting and diff
checks also passed. All 32 architecture tests passed in 272.23 seconds.

Independent semantic review passed. Resource review identified and then
verified fixes for partial callable-initialization cleanup, accumulated
binding-scan charging and filtered metadata-scan charging. Each has a
reproduced failure and passing small-stack or exact/one-short/retry regression.
Semantic approval still holds after these resource-only changes. The ownership
scanner now distinguishes Rust precise-capture syntax from imports; a
regression verifies real aliases before, inside and after the function still
resolve to their type owner. Independent review found no remaining issue.

This closes the inference gate, not CP-0016. Runtime discard, the specification,
the final full verification gate and local integration remain outstanding.
The signed Step 2 commit attempt timed out waiting for GPG and created no
commit. The user then authorized unsigned intermediate commits and signing
the integration merge. The verified inference checkpoint is retained in
`870d81b`. Runtime work continues separately; the repository signing setting
is unchanged, and the local integration merge still requires signing.

### Step 3 verified runtime checkpoint

The first three runtime witnesses failed with `InvalidControlState` before the
implementation and passed unchanged afterward. Five source tests now cover
abandonment, clause and surrounding work, inner discard before outer resume,
consumed boundaries, and mixed completion. Five machine tests cover exact
quota release/reuse, atomic malformed-state rejection, nearest activation and
32,768-frame success/failure disposal on a 64 KiB stack.

The parent independently passed 1,001 library and 73 focused effect tests.
The writer also passed all-target Clippy, formatting and diff checks.
Independent semantic review followed by independent Rust/resource review
approved the frozen runtime diff; each passed 23 machine and 12 runtime tests.
The implementation adds one discard action and reuses existing continuation
storage and iterative disposal. Specification, documentation review, full
verification, transition cleanup and local integration remain open.
