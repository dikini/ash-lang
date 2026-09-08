# Reliable cleanup evidence

This informative report records partial implementation evidence on
`codex/reliable-cleanup`, not current `main` semantics or completed milestone
acceptance. Syntax is retained at `390708e`; typed normal completion at
`1aabffe`. Owned abandonment and the complete reporting contract remain open.
The [branch specification](../../../spec/README.md) describes implemented
behavior; this report does not define language rules.

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

The [runtime tests](../../../src/eval/machine.rs) check acquisition charges before
publication, capacity reuse, action-start charges, failure before invocation,
and deep normal completion/disposal. Actual evaluator-loop traces distinguish
failure after a first cell write from failure after a completed inner action;
neither replays that action nor starts the outer action during teardown.
Successful observation rejects a remaining live cleanup owner.

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

## Outstanding acceptance

The accepted transition's evidence IDs remain open until their whole row is
proved. Existing partial coverage does not close a row:

| Obligation | Retained coverage | Still required |
| --- | --- | --- |
| CLEAN-01 | Syntax, contextual rows, shape errors, imported generic open-row factory | Full interaction audit |
| CLEAN-02 | Once-only initialization/invocation, saved value, nested actions, dependency escape | Repeated same-site activation and mixed registration/cell/action order |
| CLEAN-03 | None for admitted owned abandonment | Recursive live captures, consumed clauses, no replay or pending publication |
| CLEAN-04 | Running-action negative, safe local discard, capture/resume | Owned-drain completion and outside/non-owning-association checks after migration |
| CLEAN-05 | Normal structural action order and capture/resume | Timestamp-distinguishing abandonment and nested owned captures |
| CLEAN-06 | Normal outer/action-local handlers; body-local handler cannot discharge action row | Closing-position removed-handler checks, cell shadows, hooks, imports and generic coincidence |
| CLEAN-07 | Normal saved result, ordered reports, reported cell-escape rejection | Exact `72211`, distinct primary/error types, sums, independent effects, no implicit reporting/retry and abortive-report rejection |
| CLEAN-08 | Pre-acquisition and action-start preparation; partial-effect/no-replay trace | Abandoned later initializer, prior acquired owners and partial draining |
| CLEAN-09 | Normal Core forgery, both transforms, actual callback dependency substitution | Abandonment effects/context/order forgery and positive/negative generic coincidence |
| CLEAN-10 | Normal exact work, fresh compiler retries, capacity reuse, deep disposal | Closure traversal/retention/report charges, captured capacity and partial drain bounds |
| CLEAN-11 | Focused predecessors, architecture and strict Clippy | Full predecessor gate, exact CLI, final specification/tools and authority/link review |

The remaining evidence must cover recursively owned abandonment, structural
draining, effectful discard rows and per-action surviving interpreter checks.
It must retain outside-owner and running-drain negatives, distinguish structural
order from acquisition time, and cover generic/imported handler coincidence.
The exact failure-path program returning `72211`, complete reporting variants,
abandonment resource bounds, predecessor migrations and exact CLI checks are
not yet established by this report. Normal-only admission is temporary.

## Downstream limits to retain

Cleanup establishes an invocation attempt, not termination or successful native
release. Foreign partial acquisition and failed native release still require
provider-specific rules. No existential package, universal error domain or
owner-transfer rule is introduced. Captures retain their own state without a
global registry; escaping suspension remains outside this slice.

Arbitrary captured source handlers cannot simply be restored for cleanup: an
`Int`-answer handler with clause `(resume ()) + 1` needs the abandoned body's
result. Generalizing that boundary requires separate answer/control design.
The final review must reassess these foreign, proof, existential, suspension
and handler pressures against the completed implementation.
