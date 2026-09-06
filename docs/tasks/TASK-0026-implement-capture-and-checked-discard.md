# TASK-0026: Implement Capture and Checked Discard

- ID: `TASK-0026`
- Status: active
- Related: [CP-0016](../proposals/CP-0016-capture-usage-and-checked-discard.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [execution plan](../plans/2026-09-06-capture-checked-discard.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

User-approved explicit discard and inferred capture-summary contract. Start
from integration commit `da3ea62a1eee5642ec16a11210ee643e33d56574` on local
branch `codex/capture-checked-discard`, in `.worktree/capture-checked-discard`.
The clean integration checkout was moved to this path before branching;
the integration ref and unrelated main checkout remain unchanged.

## Work

Implement the accepted proposal through test-driven source/Core/runtime
completion support, inferred capture summaries, independent authentication,
resource tests, specification and reviewed evidence. Keep one product writer.

## Progress

- Design explained and accepted in the task conversation on 2026-09-06.
- Isolated worktree prepared at the exact integration tip.
- Baseline `cargo test --workspace --all-targets` passed with exit status 0
  before product edits, including 979 library tests and the complete integration
  suite. The architecture source guard took 332.76 seconds; the deep-data
  binary took 151.65 seconds. Neither reported a failure.
- High-reasoning read-only agent auditing summary composition; parent owns
  proposal and task preparation.
- Step 1 carriers and fail-closed checks implemented. Parent verification:
  982 library tests and 28 focused effect tests passed; formatting and diff
  checks passed. Independent semantic and Rust/resource reviews found no
  must-fix issues. The broader build found two missing leaf cases in predecessor
  test visitors; both were corrected. All-target Clippy and 84 interface tests
  then passed in the writer's and parent's runs.
- Step 1 is retained in commit `f1e073a`.
- Step 2 inference is in progress. Its writer reports the initial local
  delimiter, helper, closure/factory and recursion cases passing through the
  shared Core analysis. Import transport, type substitution, uncertainty,
  tampering and resource accounting remain under construction and review.
  This is not a completed or independently verified capture checkpoint.
- The writer subsequently reports 988 library tests and 58 focused effect
  tests passing after adding finite residual equations and restoring the
  predecessor budget cases. The skipped-outer-completion and restored-live-owner
  regressions reject; consumed-owner, restored-filter, imported-suffix and
  caller-remainder pairs pass. Instantiating an unknown row to closed `{A}`
  no longer contaminates an unrelated `B` discard. Structural sites replace
  diagnostic spans as request identities, with compact exported numbering.
  These are writer-reported intermediate results, not parent verification
  or Step 2 completion. Ownership guards, final Core witnesses, formatting,
  lint and independent reviews remain checkpoint requirements.
- Before semantic review, the parent independently passed 989 library tests,
  72 focused effect/syntax/row tests, formatting, all-target Clippy and diff
  checks. The writer also passed all 31 architecture tests. Review then found
  a required precision defect: flattening nested suffix projections can replay
  a helper request before capture and reject safe discard. The admitted
  all-known-helper regression reproduces that rejection. Removing the rewrite
  alone exhausts inference work in that case and several existing cases;
  concrete residual transport is being examined. The earlier green results
  do not verify the current fix work. Step 2 remains uncommitted and incomplete.
- Review rejected replacing projection ancestry with a set of request keys:
  repeated nonrecursive helper calls can share a key without sharing a
  continuation position. The writer is checking transport of already selected
  residuals through derived wrappers, with symbolic projections at original
  computation roots. The writer's paired pre-capture/post-capture regressions
  now pass after concrete transport and two exact completed-owner annotation
  simplifications. A separate restored-handler witness confirmed another false
  rejection: its clause resumed captures from the original handler body instead
  of the selected residual. Binding the clause to its selected resumed flow
  corrects that case. The parent independently passed both safe regressions
  and the unsafe post-capture regression. The recursive activation pair still
  exhausts inference work; the checkpoint is not green.
- The writer reports 19 typing, 10 module, 5 Core-integration and 7 existing
  runtime tests passing after selected-residual binding. Its independent
  raw-Core pre-capture/post-capture pair also passes, using a fixture that
  satisfies ordinary resume-row validation before introducing discard.
  Recursive return tails still expand into fresh equations. A cyclic
  return-position representation is under review; no cycle implementation or
  completed Step 2 claim follows from these intermediate results.
- Product edits were frozen for a bounded representation-design checkpoint.
  The parent independently passed 990 library and 60 focused tests with the
  two recursive activation tests explicitly excluded, then all-target Clippy.
  Both excluded tests independently reproduce `TypeResourceExhausted`; they
  are not waived. Temporary tracing is removed. The design comparison is
  between a conservative finite request automaton at recursive call edges
  and a more precise finite continuation-store graph. Neither is implemented
  or an approved replacement precision contract yet.
- A subsequent tests-only witness also fails with `TypeResourceExhausted`:
  `unknown_request_loop_keeps_a_finite_resume_only_handler_summary`. An opaque
  repeating `H` request is handled by a clause that performs `A`, resumes, then
  performs `B`. There is no discard or recursive source function. This shows
  that a recursive-call-only request automaton cannot resolve the whole
  problem. Cyclic resumption bindings also need a finite representation.
  The earlier 990-plus-60 green run predates this additional failing test.
  No small complete finiteness argument has been established. Replacing the
  residual representation would affect most of the private `Flows` engine;
  product edits remained frozen at this larger design boundary.
- A subsequent read-only design audit identified two further obligations for
  the proposed replacement. Captured graph snapshots, owner occurrences and
  resume splices all need finite identities; bounding return positions alone
  is insufficient. Flow-sensitive owner state must preserve live outer
  recursive occurrences when the current occurrence is consumed. The proposed
  finite-store candidate has not been implemented or shown to preserve the
  full acceptance corpus. Also, the current portable graph erases handler
  decisions. Reusing that payload needs a substitution-stability argument,
  or the replacement must retain the relevant control information. No admitted
  source counterexample to that export property has been established; it is
  an open representation obligation, not another confirmed compiler defect.
  Existing value inference, type helpers, checking entry points and summary
  authentication remain reuse candidates. At the end of that audit, the larger
  redesign approval was unanswered and no rewrite had started.
- The user subsequently approved the larger analysis redesign. The approval
  removes the product-edit freeze; it does not weaken CP-0016, waive failing
  tests, increase work limits, or authorize integration before verification.
  Resume with one product writer and high-reasoning semantic/resource reviews.
  Replace the unbounded residual construction, retaining the surrounding
  checking and authentication machinery where its contracts still hold.
- The new writer reproduced all three loop failures and added
  `imported_handlers_are_selected_after_type_specialization`. The writer
  reports that the imported-summary checker accepts its unsafe equal-type
  case as well as its safe distinct-type case. Closed effect instances may
  coalesce after substitution; the replacement must therefore retain handler
  control for checking after specialization. This confirms the earlier export
  concern at module checking, not yet at independently reconstructed linked
  Core. Generic bodies containing discard also require safety without an
  unstated assumption that distinct type parameters remain unequal.
- The replacement now compiles. The parent independently passed both
  recursive-activation tests, then all 20 `effect_typing` and 11
  `effect_modules` tests, including the repeated-request and imported
  specialization pairs. The writer reports one remaining focused failure:
  the resume-only branch of
  `unknown_calls_retain_admitted_requests_after_resumption` exhausts work.
  This is an intermediate result; generic-body, linked-Core, resource,
  architecture and independent review gates remain open.
- The writer subsequently froze the replacement for review. The parent
  independently passed 993 library and 68 focused tests, including the seven
  unchanged runtime tests, plus formatting and diff checks. The cyclic
  opaque-request query now includes discard: known post-resume work accepts,
  while the live-owner variant rejects. Generic-body and linked-Core
  specialization pairs also pass. The deep query measures 2,437,770 internal
  checker work units over 388 control positions on a 64 KiB thread stack,
  with exact success, one-short exhaustion and fresh retry. This test uses
  an explicit measurement budget; the production limit is unchanged. These
  internal checker units are not project work-budget units. The parent then
  passed all-target Clippy and all 31 architecture tests; the latter took
  271.82 seconds. Independent semantic review passed with no actionable
  findings and independently reran 11 capture unit tests plus 56
  diagnostic/module/typing tests. Rust/resource review found three local
  issues: a deep type temporary lacks iterative cleanup if a later field copy
  fails during callable construction; accumulated formal-variable lookup is
  not fully charged; and filtered graph metadata scans are not charged for
  skipped control positions. The writer is correcting these paths with
  targeted small-stack and exact/one-short/retry tests before re-review.
  No semantic redesign or work-limit change is required by these findings.
- All three resource findings are fixed and independently re-reviewed; prior
  semantic approval still holds. The parent independently passed 996 library
  and 68 focused tests, all-target Clippy, formatting and diff checks, then all
  32 architecture tests in 272.23 seconds. The architecture scanner needed a
  narrow correction to distinguish Rust precise-capture syntax from imports;
  its new regression preserves real alias and carrier checks. Step 2's
  inference gate is complete. Runtime and whole-checkpoint closure remain.
- Runtime discard is implemented and independently approved by semantic and
  Rust/resource reviews. The parent passed 1,001 library and 73 focused tests;
  both reviewers passed 23 machine and 12 runtime tests. Exact quota reuse,
  failure atomicity and 32,768-frame teardown on a 64 KiB stack are covered.
  Specification, documentation review and the final checkpoint gate remain
  open; do not yet close CP-0016.
- After the signed Step 2 attempt timed out, the user authorized unsigned
  intermediate commits and signing the integration merge. The verified
  inference checkpoint is retained in `870d81b`; runtime work continues in
  separate files. The repository signing setting is unchanged.

## Verification

Record RED/GREEN commands and their actual outcomes in the task-owned plan.
Run the CP-0016 positive, negative, tamper, transform, budget and deep teardown
corpus, then `cargo xtask verify`. Require independent semantic review before
independent code/resource review. Check changed Markdown links and authority.
Only close transition artifacts after all required evidence is retained.

## Discoveries

Stored closure captures do not describe the obligations carried by a request
made during that closure's call. Request summaries must compose at calls and
respect the nearest handler boundary.

Review identified two additional control-flow obligations during Step 2.
A nested handler's discard may skip an outer owner's scheduled completion,
even when the captured segment does not contain that owner's clause boundary.
Handler completion must therefore account for discard exits, not simply copy
the normal body's consumption summary. Also, `resume` reinstates requests in
the captured suffix: handlers installed around it can observe those requests.
Their summaries must preserve restored live owners without replaying requests
that occurred before capture. Regression cases and paired safe cases are under
construction; these findings are not yet closed verification results.

Runtime inspection found that nested captured continuations occur only in
`Frame::ClauseBoundary` with `continuation: Some(...)`; ordinary runtime values
cannot contain the hidden capability. Under CP-0016, a proved-safe discard
therefore cannot abandon such a live nested owner. Step 3 should verify this
invariant and reuse existing moved-frame storage and capture accounting,
rather than introduce a second continuation representation. Consumed clause
boundaries hold `None` and do not by themselves prevent discard.

## Deviations

The user approved replacing the Step 2 residual representation after the loop
regressions exposed unbounded inference. CP-0016 and the completion gate remain
unchanged. The original milestone forecast assigns this checkpoint 9 of its
notional 100 units. That is a relative forecast, not an elapsed-work measure or
a new numeric authorization. Do not invent spent-unit figures or expand into
resource scope.
