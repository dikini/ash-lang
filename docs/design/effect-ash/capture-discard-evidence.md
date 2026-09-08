# Capture usage and checked discard

This informative report records the capture/discard checkpoint above the
scoped-evidence baseline `da3ea62`. Implementation, independent semantic,
Rust/resource and documentation reviews, full verification and transition
cleanup are complete. Local integration is recorded separately by merge
ancestry.
The [milestone closure report](milestone-closure-evidence.md) records integration
into `main` and final verification status. The specification defines language
semantics; this report retains checkpoint evidence.

## Retained boundary

CP-0016 was accepted at `52f7ae5`. The baseline and implementation plan were
retained at `8a921f1`; gated syntax, Core carriers and structural usage checks
at `f1e073a`. The approved finite inference redesign is retained at `870d81b`;
reviewed runtime discard and accounting at `ca73354`.
The specification and full-gate evidence are retained at `6ad72e9`.
CP-0016, TASK-0026 and the task-owned execution plan were then removed from
the product tree with their index entries. Git retains their accepted
transition, work history and verification records.
After GPG timed out, the user first authorized unsigned intermediate commits,
then authorized an unsigned local integration merge while away from the
desktop. The repository signing setting is unchanged; no signature is claimed.

`discard` is a reserved nullary expression with type `Unit` and empty immediate
row. Every normally completing clause path consumes its hidden capability once,
through resume or checked discard. Mixed branches are admitted when outgoing
usage agrees. Neither form duplicates, escapes or implicitly abandons a
capability. Discard continues the clause, without running suspended work or
performing cleanup.

Ordinary stored values remain unrestricted. A request may nevertheless carry
another clause's live obligation through its caller or a helper's internal
handler. Those request-carried obligations, not stored closure values alone,
determine discard safety. Consumed owners add no live obligation.

## Inference and validation

The compiler retains a private finite control graph for known function values,
including aliases, closures, factories, recursive groups and imports. It keeps
calls, requests, handlers, resume and discard control, not only an evaluated
outward-request list. Types and effect identities remain authenticated with
the defining export. Final Core validation reconstructs obligations from actual
linked Core after ordinary structural, registry, type, row and usage checks.

The abandonment query uses finite control and capture allocation sites with
distinct fresh and older owner occurrences. Capturing cuts at the nearest
matching handler. Resuming restores that selected segment and clause remainder;
it neither replays the pre-request prefix nor consumes every recursive
activation of a static owner. Generic type parameters may coincide after
specialization. Retaining handlers in summaries preserves that later choice.

Roots with no structurally reachable discard publish complete control summaries
without running an abandonment query. Their ordinary exactly-once checks still
run. A discarding caller queries retained callee control. This avoids needless
queries for resume-only code without exporting partial permission. An actual
cyclic discard-bearing safe/unsafe pair separately tests convergence.

Unknown higher-order calls and open rows fail closed when the relevant request
obligations are unproved. This uncertainty alone does not reject resume-only
code. Production work limits were not raised. There are no source capture
annotations, capture-polymorphic types, resource classes, cleanup callbacks,
foreign effects, replay, or escaping continuations.

## Behavioral evidence

- `tests/effects_syntax.rs` checks reserved nullary syntax. Completion cases in
  `tests/effect_diagnostics.rs` preserve the existing outside-clause,
  missing/double-use and capture reason family; unsafe capture requires
  `effect.discard-unsafe`, not resource exhaustion.
- `tests/effect_typing.rs` admits direct requests, known helpers, aliases,
  closures, factories, recursion, separate exact effect instances, mixed
  completion, handlers inside live clauses and requests after consumption.
- Negative cases cover direct and helper-hidden requests crossing a live
  owner, same-effect outward delegation, skipped scheduled completion,
  requests after restoration, opaque calls and open rows. Ordinary type errors
  retain precedence over capture checking.
- `capture-prefix-before.ash` and `capture-prefix-after.ash` under
  `tests/fixtures/effects/` move the live-owner-producing `badD` call from
  before the selected capture to its later suffix. Only the latter can be
  reached after restoration by the inner discarding handler; the earlier
  prefix must not be replayed. Raw-Core counterparts reject bypassing the
  source checker.
- Recursive-activation tests separate earlier consumption from a newer live
  activation. The opaque-loop pair accepts post-resume work and rejects the
  same outward request before resume. Repeated requests retain the consumed
  state while evaluating post-resume clause work.
- `tests/effect_modules.rs` checks imports, facade re-exports, summary identity,
  caller suffixes and handler selection after type specialization. Equal type
  instances can expose an internal live owner that distinct instances do not.
  Linked-Core tampering uses the admitted module registry and revalidates the
  same relation independently. Generic local bodies cannot assume distinct
  type parameters even before a concrete call.
- `tests/effect_core.rs` rejects forged owners, result types, rows, usage and
  safety. Identity and folding transformations revalidate the obligations.
- Five new cases in `tests/effect_runtime.rs` observe direct abandonment,
  continued clause work, preserved surrounding handlers, an outer live owner
  subsequently resumed, abandonment of consumed boundaries and both mixed
  completion branches. Traces distinguish discard from resume/restoration.

## Runtime and resource evidence

Runtime discard adds one explicit machine action using the existing moved
`CapturedContinuation`. It finds the nearest matching clause activation,
preflights nested live obligations and accounting, takes its existing option,
releases exactly the immediate frame count and returns unit. Only a live clause
boundary can retain another hidden continuation. Rejecting such a boundary
before consumption makes successful release shallow; existing iterative
disposal handles malformed deep captures on failure. No continuation
representation, runtime registry or pure-dialect frame was added.

The three initial runtime tests failed with `InvalidControlState` before the
implementation and passed unchanged afterward. Machine tests cover exact
two-cell capacity, one-cell failure, fresh retry and sequential reuse. They
check retained independent accounting, mismatched owners, nested live owners,
underflow and consumed nearer recursive activations without partial
consumption. A 32,768-frame witness covers exact/one-short/retry and successful
or failed teardown on a 64 KiB stack.

Inference resource regressions cover finite work, exact limits, one-short
failure, retry and deep success/failure disposal. A measured abandonment query
with 388 static control positions takes 2,437,770 internal checker work steps
under an explicit test budget on a 64 KiB stack. This is test accounting, not a
project work-unit total; the production type-work limit remains 327,680.

Independent resource review found three inference issues and verified their
corrections:

- Partial callable initialization cloned a deep type before another fallible
  field, leaving the temporary outside its iterative owner on failure. The
  result copy now precedes the deep type. A subprocess small-stack regression
  reproduced the abort before correction.
- Accumulated type-binding lookup omitted proportional scan charges. A
  96-variable witness exposed 295 charged steps for at least 4,560 membership
  probes. Exact/one-short/retry assertions now include the lookup work.
- Filtered metadata iterators charged only yielded entries, missing scans
  yielding nothing. Fallible precharged iterators now charge retained code and
  metadata before scanning; absent metadata still costs zero.

The architecture scanner mistook Rust precise capture `use<'a>` for an import.
Its correction skips only `use` followed by `<`. A regression proves genuine
imports before, inside and after the function still resolve carrier ownership.
Independent review found no weakened inventory check.

## Verification and review

The frozen inference checkpoint independently passed 996 library and 68 focused
tests, all-target Clippy, formatting and diff checks. All 32 architecture tests
passed in 272.23 seconds. Independent semantic and Rust/resource reviews closed
after the corrections above; semantic approval was reconfirmed for those
resource-only changes.

The runtime writer passed 1,001 library and 67 focused tests, all-target Clippy,
formatting and diff checks. Independent semantic review passed all 12 runtime
and 23 machine tests, with no actionable finding. Independent Rust/resource
review then approved the same diff and passed the same tests. The parent
independently passed 1,001 library and 73 focused tests.

Final whole-feature semantic review covered syntax, usage, transformations and
all proposal evidence categories. It found one specification omission:
`T-Discard` also needs to preserve completion of owners outside the captured
segment. The premise is now explicit, and the reviewer approved the correction.
Whole-feature Rust/resource review confirmed the nullary Step 1 carriers use
existing charged construction, iterative transforms and usage worklists, with
no additional finding. Its independent probes included 16,384-level exact
usage work, one-short/retry and disposal.

The documentation audit passed authority and formal-notation checks and all
132 relative links/anchors across eleven changed documents. New prose was
wrapped, and summary wording distinguishes dependency source bodies from
retained inferred control. Markdown lint passes with the existing long-line
exceptions; diff checks pass.

`cargo xtask verify` passed on 2026-09-06: formatting, metadata, all-target
build, all-feature Clippy, 2,156 tests across 62 binaries, and rustdoc with
warnings denied. This includes all 32 architecture tests in 266.76 seconds
and the 32 data/ADT tests in 103.93 seconds. No production work limit, stack
allowance or verification obligation was raised to obtain the result.

## Downstream pressure and limits

Stored capture and request-carried obligations remain separate analysis inputs.
Later resource scope can introduce actual obligation classes at that boundary;
this checkpoint does not choose acquisition, lifetime, cleanup or failure
combination rules. Retained exact identities and independent linked/Core
validation remain the relevant pressure points for proofs and existential
packages. Neither feature is implemented here.

The finite analysis may conservatively reject safe programs whose relevant
capture cannot be established, or exhaust the existing work budget. It never
turns unfinished analysis into discard permission. No additional inference
precision or general ownership mechanism is claimed by this checkpoint.
