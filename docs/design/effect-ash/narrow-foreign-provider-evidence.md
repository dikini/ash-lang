# Narrow checked foreign-provider evidence

This informative report records the implemented and verified native-buffer
increment on `integration/effect-ash-foundations`. The
[milestone closure report](milestone-closure-evidence.md) records integration
into `main` and final verification status.
Product checkpoint `3819a93` retains compiler admission, runtime execution,
conformance tests, specification, review and full verification.
The [specification](../../../spec/README.md) accompanies the implementation
and conformance tests. Unsigned local merge `c0f230f` passed full merged
verification. The clean feature worktree and branch were removed; their history
remains in the integration branch. No main merge, push or tag was performed.

The fixed adapter described below is historical evidence at the linked retained
commit. The current [source buffer library](../../../libraries/native_buffer.ash)
replaces it on the product path.

## Evidence coverage

The FOREIGN identifiers retain the accepted proposal's evidence obligations.
Independent contract, effects, provenance/proof and existential-pressure review
approved FOREIGN-01 through FOREIGN-09. Final Rust/resource quality review also
passed. Full verification and clean local integration close FOREIGN-10.

| ID | Established evidence | Review and closure |
| --- | --- | --- |
| FOREIGN-01 | [Syntax](../../../tests/native_buffer_syntax.rs), [modules](../../../tests/native_buffer_modules.rs), [imports](../../../tests/native_buffer_imports.rs), [typing](../../../tests/native_buffer_typing.rs), and [Core transforms](../../../tests/native_buffer_core.rs): closed builtin selection, targeted/renamed imports, facade-only and copied-API rejection, sealed provider, exact types and unchanged cells. | Contract approved. |
| FOREIGN-02 | [Native owner](https://github.com/dikini/ash-lang/blob/ea93b8701649806ab22b916fa0a5a9a91ebc5fd4/native-buffer/src/lib.rs), [runtime](../../../tests/native_buffer_runtime.rs), and [private boundaries](https://github.com/dikini/ash-lang/blob/ea93b8701649806ab22b916fa0a5a9a91ebc5fd4/src/eval/native_buffer_tests.rs): real zeroed allocation, length/access, conversions, index-before-byte checks and unchanged rejected writes. | Contract and resource reviews approved. |
| FOREIGN-03 | Private boundary tests cover injected null, pre-call work exhaustion, no body authority and release of a real unpublished owner after injected publication failure. Refusal-delivery tests cover committed initializer effects and no further allocation. | Contract and reporting reviews approved. |
| FOREIGN-04 | Runtime/private tests cover aliases, reentrant activations, retired-key rejection, active/captured capacity reuse and escaping closures. Imports cover generic value and selected-method captures versus copied values. | Ownership/provenance review approved. |
| FOREIGN-05 | [Interactions](../../../tests/native_buffer_interactions.rs) cover mixed structural order, inner cleanup access, resume/discard, recursive owner discard, skipped suffixes, action-local result wrapping and outside-owner/running-action rejection. | Contract review accepts these separate witnesses; retain the combined stress limitation below. |
| FOREIGN-06 | Interactions cover removed overrides versus surviving builtin/action-local interpretation. Imports cover exact/different generic hook instances, imported callbacks and positive/negative row-lacks cases. | Effects review approved. |
| FOREIGN-07 | [Linked validation](../../../src/evidence_validation.rs) checks nine independent resource mutations and constructor payloads. [Core validation](../../../src/core/validate.rs) mutates acquisition/method/brand/result/row/origin facts after both transforms. Rejections leave all six native counters zero; transformed positives execute `Success(5)` with one allocation and release. | Contract approved. |
| FOREIGN-08 | Private tests cover normal return, body failure, discard, partial publication and completed teardown releases. Injected teardown exhaustion preserves primary/secondary failure, marks cleanup incomplete and prevents source clause/suffix/cleanup writes. Row-storage fault matrices preserve actual storage causes. | Contract and reporting reviews approved. |
| FOREIGN-09 | Compiler and runtime tests retain exact/one-short/fresh budgets, proportional length charging, owner capacity/reuse, deep stack checks and shared Pure-locality evidence. | Contract and finite-work audit approved. |
| FOREIGN-10 | Isolated safe-owning adapter, CLI fixture, predecessor suite and ARM64 compile checks pass. Independent complete-provider contract, Rust/resource and documentation reviews passed. Full verification passed before and after unsigned local merge; transition and clean feature-worktree cleanup are complete. | Closed locally; no main merge, push or tag. |

## Native and injected observations

The first-party [adapter](https://github.com/dikini/ash-lang/blob/ea93b8701649806ab22b916fa0a5a9a91ebc5fd4/native-buffer/README.md) owns the private
pointer and calls C `calloc`/`free`. Its six tests include real successful
allocation, zeroed bytes, checked access and one release after moving ownership.
Root evaluator tests observe calls into that safe adapter and ownership drops.
Together these boundaries connect root ownership observations to actual C
release; root counters are not presented as direct C-call instrumentation.

Injected null is a separate failure witness, not evidence that the host allocator
actually exhausted memory. Normal execution, captured/discarded owners and
post-success publication failure use real buffers. Handles contain activation
keys, never addresses; retired-key rejection precedes access independently of
whether the allocator reuses an address.

The exact [CLI fixture](../../../tests/spec_examples.rs) prints
`Success(Success(42)) : Outcome<Outcome<Int>>` plus a newline, with empty standard
error and exit status zero.

## Disposal and failure boundary

The accepted transition distinguishes atomic native refusal from terminal
runtime resource failure. The prepared refusal result may be delivered only
without further allocation or new observable state; earlier initializer effects
remain committed. Insufficient retained disposal capacity is terminal.

The [disposal worklist](../../../src/eval/disposal.rs) reuses existing environment,
captured-frame, type and kind traversals. Eight inline slots handle small pending
sets; ordinary disposal may reserve spill storage fallibly. Refusal delivery
forbids that growth. Exhaustion preserves a fixed first failure and safely
abandons undismantled ownership, reporting incomplete cleanup rather than
recursively dropping it or retrying. No source cleanup or recovery traversal is
introduced. This does not promise that whole teardown cannot fail.

Each dismantled structural node is consumed once. Environment traversal follows
at most two outgoing edges per unique entry; shared entries are dismantled only
when their final owner is consumed. There is no repeated graph scan or frame
rotation. Existing small-stack tests pass with these traversals.

Independent contract review cleared refusal delivery and fail-stop disposal.
Separate Rust review found no additional ownership/disposal defect, but found
missing resource details on shared capture and native-request work failures.
The subsequent audit also found such sites in cleanup, registration, cell
admission and generic application while a native owner can remain live.
Those direct paths now retain resource details. Contract re-review found two
generic row-helper defects: detected clone reservations could panic,
and canonicalization could misreport storage refusal as work exhaustion. The
complete runtime row path now passes independent contract re-review, including
comparison inside canonicalization and tail membership. Independent Rust
quality review and full verification also passed. The bounded
writer must retain both
a legacy primary reason and the explicit resource cause when they
differ; an undetermined storage-reservation cause is not a claimed RAM quota.
The structured reporting mechanism handles returned failures from fallible
operations; it does not intercept process termination by infallible host
allocation APIs.

## Verification and limitations

On 2026-09-09, after the reporting correction and final validator/import QA,
parent verification passed:

- `cargo xtask verify`, including build, strict lint, workspace tests and rustdoc;
- 1,214 library tests, 14 CLI tests and 50 native integration tests, including
  the storage-fault matrices and native-owner source-effect-stop witnesses;
- `cargo check --workspace --all-targets --target aarch64-unknown-linux-gnu --locked`.

The merged checkout then passed `cargo xtask verify` in full. Final status-only
documentation changes were checked separately; they change no Rust or Ash code.

Changed Markdown has no new lint findings against the compiler checkpoint;
existing overlong lines remain, and table and formal-code line lengths were
excluded. Relative file links resolve after artifact cleanup, and referenced
specification headings were checked. Final contract and
Rust/resource reviews found no remaining findings.

ARM64 compilation is not native ARM64 execution or release conformance.
Native tests here ran on Linux x86-64. No other backend or simulated portability
fallback is claimed.

A combined recursive native-owner/cleanup witness exhausts checker work before
evaluation. In the recursive discard interaction, wrapping the native body in
`cleanup fn(ignored) { perform Record.digit depth } { ... }` reproduces it;
using `Buffer.length b` instead of `depth` also exhausts work. Removing only that
cleanup layer admits recursive native ownership and discard. Separate tests
cover cleanup access and mixed ordering. No limit was raised, and this combined
case is not claimed admitted.

Library-defined acquisition, a general FFI, files and fallible native close are
excluded from this slice. Fixed native `free` has no recoverable close result;
these observations do not generalize that rule to future file providers.
