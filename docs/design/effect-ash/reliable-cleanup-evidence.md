# Reliable cleanup evidence

This informative report records the verified reliable-cleanup implementation on
`codex/reliable-cleanup`, not current `main` semantics or completed milestone
integration. Syntax is retained at `390708e`; typed normal completion at
`1aabffe`. The complete owned-abandonment and reporting contract has passed
product verification. The [branch specification](../../../spec/README.md)
records the implemented transition; this report does not define language rules.

## Retained observations

The [syntax tests](../../../tests/cleanup_syntax.rs) cover full action expressions,
grouping, primary positions, malformed forms and reserved spelling. Exact
admission is 64 nested bodies or 127 nested action initializers; the next depth
rejects and fresh retries retain admission. Projection and disposal fit 256 KiB.

The [normal cleanup tests](../../../tests/cleanup_typing.rs) retain these witnesses:

- `initialization_once_inner_before_outer_and_saved_body_value` returns `42123`:
  initialization appends `1`, inner and outer actions append `2` and `3`, and the
  saved body value remains `42`.
- Contextual anonymous block/match results infer their latent effects. Mixed
  pure/effectful branches work in both orders; named callback rows remain
  invariant and unrelated function bodies do not enter the action accumulator.
- Capture/resume preserves armed and running owners. Safe action-local discard
  preserves completion; skipping a running action rejects.
- Normal reporting preserves the body value and emission order. Saved results
  and reported errors cannot export a cell dependency.

The [Core validation tests](../../../src/core/validate.rs) check cleanup owner,
callback and row forgery before and after both transforms, imported generic
open-row factories, exact validation work with fresh retries, and same-typed
callback substitution that changes stored resource dependencies.
The later seven-test cleanup Core gate also passes linked same-typed callback
substitution with distinct and coincident generic handler instances, forged
discard effects, and exact/one-short/fresh capture-validation work. The mutation
cases check original Core and both transforms; forged rows additionally fail
direct capture reconstruction. These tests passed their first run and do not
constitute a newly observed behavioral red-to-green correction.

The [runtime tests](../../../src/eval/machine.rs) check acquisition charges before
publication, capacity reuse, action-start charges, failure before invocation,
and deep normal completion/disposal. Actual evaluator-loop traces distinguish
failure after a first cell write from failure after a completed inner action;
neither replays that action nor starts the outer action during teardown.
Successful observation rejects a remaining live cleanup owner.

### Abandonment and reporting

The abandonment increment passed 11 focused tests in
[cleanup_abandonment.rs](../../../tests/cleanup_abandonment.rs), including the
complete `72211` source, nested live captures, structural order and the
body-local/enclosing removed-handler pair. It also admits a clause-local
handler around discard reached through forward and recursive helpers.
Additional witnesses cover one generic discard at two instantiations, imported
versus local node identity, and opaque callback rejection after lexical row
checking. These source tests do not establish independent linked-Core authority
or complete abandonment acceptance.

Eight [reporting tests](../../../tests/cleanup_reporting.rs) passed their first
behavioral run on that increment. They cover an empty failure list, ignored
failure values, one counted invocation without retry, distinct primary/error
types, an explicit error sum, independent typed collectors surviving discard,
abortive normal/drain reporting rejection and abandoned reported-cell escape.
Initial block-layout, integer-pattern and unused-handler mistakes were test
source corrections, not evidence of missing implementation behavior. The
normal cleanup suite also passed all 14 tests after pending cleanup rows were
excluded from premature local generalization.

The retained focused gate passed 143 top-level tests plus one resource
subprocess recheck: abandonment 11, partial acquisition one, reporting eight,
normal cleanup 14, effect typing 23, hook typing 25 and resource scopes 61.
The partial-acquisition witness returns `7123`: initializer prefix `1`, earlier
action `2`, then clause continuation `3`, preserving result `7`. The unacquired
action, later body and abandoned suffixes do not run. Nine predecessor fixtures
were migrated without changing their source bodies; outside-owner negatives
remain unchanged. This gate still reports unused completion-owner variants;
it is not strict-lint or full predecessor acceptance.

The exact documented CLI example also passes: exit zero, `72211 : Int` and a
newline on standard output, empty standard error. The first test extraction
omitted the source block's terminal newline; retaining that documented newline
corrected the harness without changing the program or language.

Separate interaction witnesses pass for overlapping activations of one recursive
cleanup site (`21`) and mixed cell/registration/action closing order (`110`).
The original combined recursive case exhausted capture-analysis work. It is
reproducible by replacing the mixed-order witness's innermost `()` body with a
match on `depth == 2`: the true arm returns `()` and the false arm calls
`visit (depth + 1)`. Its intended trace is `231110`; that
admission remains unproved. Splitting the independent acceptance witnesses did
not raise a compiler limit or change the analyzer to admit that stress case.

Focused closing-position tests also pass for captured cell overrides and hook
interpreters, each paired with a body-local handler that is outside the action's
closing context. Subscriber abandonment retains its prefix and cleanup, skips
pending publication callbacks and suffixes, and removes registrations before a
later publication. The corrected open-row test passes normal and discarded
callbacks with explicit exclusions, while missing exclusions still reject.
That correction retains same-tail lexical lacks during recomputation and opaque
request matching; independent forall authority is unchanged.

### Measured normal-completion bounds

These are retained test boundaries, not promises about all programs:

- Acquisition charges `2 + environment.len()` before publishing a frame or
  increasing the live-owner count. One less rejects with both unchanged; exact
  allowance succeeds twice on fresh machines.
- Starting the action charges two work units. One rejects before scheduling
  the action; two succeeds. Running completion still occupies owner capacity.
- A capacity of one is reused for three successive acquire/complete cycles;
  a second simultaneous acquisition rejects without adding another frame.
- The fresh-process small-stack test checks 24 nested cleanup scopes on
  256 KiB: capacity 24 completes with `42`, while capacity 23 rejects and
  disposes without raising the stack bound.
- Core owner validation measures its actual charge, checks one less, and
  succeeds twice with the exact allowance. Contextual row joining checks
  every allowance below its measured requirement and two exact fresh retries.
  Neither test establishes a universal fixed compiler-work formula.

The partial-effect tests measure runtime work at strict markers after a cell
write has returned and after the inner action has returned. Each failure run
visits the first marker once; only the latter case visits inner completion,
and neither visits outer-action start. Repeating a fresh test execution checks
determinism, not permission to retry an external release.

### Abandonment bounds

The focused runtime gate passes three new checks: exact/one-short/fresh
preparation for a nested capture containing two cleanup owners; shared capacity
across captured, armed and running states, reused across three cycles; and
failure traces during an owned drain after a write and after reporting. The
latter checks exact execution prefixes and prevents clause continuation or
replay. Its second stopping point reaches the outer action's start marker, so
it does not establish that the outer action was never entered.

The fourth check, 24-owner successful and partial draining on 256 KiB, passed
with its subprocess after two compiler stack corrections. Request operands now
use the resolver's existing worklist. Handler bodies use the elaborator's
existing worklist, whose small driver handles clause-checking reentry outside
the large ordinary task frame. No depth or stack limit changed and no handler
state machine was added. Stronger assertions that partial draining reaches the
selected inner markers passed in the consolidated rerun; these focused passes do not close the
complete resource obligation.

## Corrections and verification

An annotated replacement for the original anonymous factory witness was
rejected during review. The original test now passes without that annotation.
Semantic review then found the mixed anonymous-branch row defect; a scoped
worklist accumulator joins those requirements without weakening named values.

The retained 24-registration proof exceeded its unchanged 256 KiB stack bound
when the elaboration dispatcher grew. Extracting completion work into helpers
restored the bound; no new recursive evaluator or raised limit was introduced.
A separate task tried during diagnosis was removed.

Normal-completion semantic and Rust/resource reviews passed. Final focused
regressions passed 1,496 top-level tests plus seven subprocess rechecks. The
full architecture suite passed 32 tests, with a final exact manifest recheck.
Strict all-target Clippy, formatting and whitespace checks passed. Parent's
fresh library, cleanup and Effect Core check passed 1,173 top-level tests.
These are checkpoint gates, not the final full-contract `cargo xtask verify`.

The consolidated abandonment gate passed 34 top-level tests and two subprocess
rechecks without warnings. This includes duplicate acquisition ownership,
transaction rollback, cyclic row exact/fresh work, opaque exclusion identity,
the strengthened partial-drain markers, retained lacks-forgery negatives and
all six interaction tests. Independent high-reasoning semantic and Rust/resource
reviews passed. Documentation review corrected an overbroad callback statement:
closing suppresses pending callbacks from abandoned publications, not new
publications performed by cleanup through surviving hooks.

The first full verification passed format, build and strict Clippy, then stopped
at eight predecessor library expectations: 1,159 passed and eight failed.
Migration review distinguishes newly owned clause/resource closure from genuine
outside, running and malformed cases. The migrated library gate now passes all
1,167 tests without warnings, retaining outside-owner, running-completion and
malformed-accounting negatives. The exact inventory scan identified 14 missing
carrier fields and no stale fields; those entries have been added. The fresh
full gate passed strict Clippy, the library and all 32 architecture checks,
including the corrected inventory. It then stopped with a stack overflow in
the predecessor data/ADT test binary. The unchanged 512 KiB nested-pattern test
now passes after extracting recursive match resolution from the large ordinary
resolver dispatcher. Work-item size did not grow; the extracted helper preserves
the existing match order and scope rollback. No stack or depth limit has been
raised. Wider regressions and a fresh full gate remain required.

The subsequent predecessor sweep passed the full data/ADT suite, but stronger
execution of the unchanged prefix-after fixture found a stale nested Resume row.
The corrected source-only replay resets derived Resume caches after final type
identity, reaches closure through existing charged equations, and performs a
strict final sweep. Review caught and a failing test reproduced self-supported
stale labels in the first cached-seed approach; that approach was replaced.
The revised focused gate passed 75 top-level tests plus one subprocess, including
multi-round exact/one-short/fresh rollback, delayed and genuinely missing handler
members, stale-cache clearing, both transforms, open-row lacks, all migrated
module/diagnostic cases and an exercised opaque guard. Independent bounded review
passed: the least-seed finding is closed, provisional removal admits only missing
members, and the final sweep remains strict. The fresh full gate remains
required; none of these focused results closes acceptance alone.

## Final product verification

Fresh `CARGO_INCREMENTAL=0 cargo xtask verify` exited 0 on 2026-09-08:
2,545 top-level tests across 77 test binaries and eight separately printed
subprocess rechecks passed. This includes 1,169 library tests, ten CLI binary
tests, 1,365 tests across 74 integration targets, and the xtask test.
All 32 architecture tests, exact carrier inventory, formatting, build, strict
Clippy and warnings-denied rustdoc passed without warnings or errors. The log is
`/tmp/ash-cleanup-step3-full-verify-complete-20260908.log`; it is an execution
record, not a portable source artifact. The retained tests are linked above.
Independent semantic, Rust/resource and final bounded correction reviews passed.
Markdown lint with MD013 disabled, whitespace, local-link and manual
notation/authority checks passed. Local integration and lifecycle closure remain
separate gates.

## Acceptance evidence

The final full gate and independent reviews establish the following product
obligations. Earlier focused observations above retain the correction history.

| Obligation | Retained coverage | Product result |
| --- | --- | --- |
| CLEAN-01 | Syntax, contextual rows, shape errors, imported generic open-row factory; semantic review | Passed |
| CLEAN-02 | Once-only initialization/invocation, saved value, dependency escape; separate recursive same-site and mixed cell/registration/action traces; semantic review | Passed |
| CLEAN-03 | Owned cell/registration, nested live capture, consumed-clause association and skipped pending-publication/suffix tests; migrated library pass | Passed |
| CLEAN-04 | Running-action negative, safe local discard, capture/resume; migrated outside/non-owning-association and running-completion negatives | Passed |
| CLEAN-05 | Normal order; A-before-later-B resumption/abandonment, nested capture and mixed-owner traces; semantic review | Passed |
| CLEAN-06 | Source/cell/hook closing-position pairs; imported generic callback substitution; explicit open-row exclusions and missing-exclusion negatives; independent authority review | Passed |
| CLEAN-07 | Normal saved result and ordered reports; exact documented CLI `72211`; eight reporting variants listed above | Passed |
| CLEAN-08 | Pre-acquisition and action-start preparation; normal and abandoned partial-effect/no-replay traces; abandoned later initializer closes prior owner | Passed |
| CLEAN-09 | Core forgery, duplicate acquisition, both transforms, callback dependency substitution; abandonment row forgery, generic coincidence and least row replay | Passed |
| CLEAN-10 | Normal/abandoned exact work and fresh retries; captured/running capacity and reuse; deep success/partial drain; multi-round replay rollback; retained stack bounds | Passed |
| CLEAN-11 | Full predecessor corpus, strict Clippy, 32 architecture tests, exact cleanup CLI, specification/tools and notation/authority/link review | Passed |

The retained tests and independent reviews cover recursively owned abandonment,
structural draining, effectful discard rows and per-action surviving interpreter
checks. They retain outside-owner and running-drain negatives, distinguish
structural order from acquisition time, and cover generic/imported handler
coincidence. Product acceptance is verified; local integration remains open.

## Downstream limits to retain

Cleanup establishes an invocation attempt, not termination or successful native
release. Foreign partial acquisition and failed native release still require
provider-specific rules. No existential package, universal error domain or
owner-transfer rule is introduced. Captures retain their own state without a
global registry; escaping suspension remains outside this slice.

Arbitrary captured source handlers cannot simply be restored for cleanup: an
`Int`-answer handler with clause `(resume ()) + 1` needs the abandoned body's
result. Generalizing that boundary requires separate answer/control design.
Independent semantic review retained these foreign, proof, existential,
suspension and handler boundaries in the completed implementation.
