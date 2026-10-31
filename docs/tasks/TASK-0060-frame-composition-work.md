# TASK-0060: Frame Composition Work

- ID: `TASK-0060`
- Status: active
- Related: [issue #196](https://github.com/dikini/ash-lang/issues/196), [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007](../decisions/AD-0007-typed-core-dialects.md), [generic-cell specification](../../spec/static-semantics.md#generic-cell-foundation), [elaboration](../../spec/elaboration.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

The existing dependency rules admit valid generic-cell compositions while
rejecting unsafe owner retention. Source checking and independent Core each
reconstruct their own capture proof. The developer owns the connected path
and Cargo slot; the independent reviewer checks the repair and frozen inputs.
The PM owns publication and integration coordination.

## Work

1. Measure capture work for the reported frame composition and identify the
   contributions before choosing the smallest correction with the reviewer.
2. Add a connected regression and reduce unnecessary work without increasing
   the production allowance or changing dependency, completion, ownership,
   provenance, work, depth or stack safety.
3. Check the exact source through checking, linking, independent Core and
   interpretation, plus relevant negative, transform and small native/image
   controls. Freeze the candidate and request independent review.
4. The next full-workspace checkpoint is the pinned Main integration candidate,
   before separately authorized Main integration. The PM coordinates the gate
   with the developer as Cargo operator. Focused PR checks are not that gate.

## Progress

Base: `c1b61c40a9ec78a6eeaaaaaf5d681ff16d294dfc`. The reported source is
SHA-256 `e1630800f89101e0c36bced59b0e23279712d03745c5884e04f2a5998dc20c4e`.
With normal limits it stops during source checking after charging 99,595,813
of 99,600,000 units. The final refused charge is 4,529 units for a linear
membership check among 4,528 recorded payload triples. This locates the last
refusal; it does not by itself establish the complete work required.
One frame and the original single-frame control pass; variants with two through
five calls refuse during source checking. Their inputs differ, so these
observations do not establish an asymptotic growth rate.

The [exact entry](../../tests/fixtures/frame-composition/main.ash) and its four
imported source modules are retained in the same fixture. The connected
public-driver regression in `compiler_work_reporting` fails with
`internal.resource.type-work` on this base under the unchanged limits. The red
run took 17.27 seconds including 2.03 seconds compilation.

The candidate keeps ordered payload replay and uses a separately paid index for
membership. The exact five-frame source now completes the public pipeline and
returns the five expected results. Source checking used 89,230,709 of
99,600,000 units; final elaboration used 77,006 of 7,968,000; independent Core
used 157,219,963 of 249,000,000. The connected rerun took 132.99 seconds,
including 13.50 seconds compilation. This does not determine the old run's
complete cost.

The same source variants were compared through the public driver. A refusal
shows only the partial charge paid before stopping.

| Calls | Base source work | Candidate source work |
| --- | ---: | ---: |
| 0 | 31,316,419 / 93,090,000 | 14,071,599 / 93,090,000 |
| 1 | 62,115,102 / 94,020,000 | 27,625,462 / 94,020,000 |
| 2 | 95,439,999 / 95,440,000, refused | 43,158,302 / 95,440,000 |
| 5 | 99,595,813 / 99,600,000, refused | 89,230,709 / 99,600,000 |

The original single-frame `Pair(0, 255)` control also passes, with source work
falling from 62,129,924 to 27,640,284 of 94,650,000 units. The candidate
comparison omits three- and four-call variants; it is not a complete curve.

## Verification

All Cargo checks use Rust 1.97.1, locked offline dependencies, one Cargo job,
an empty `RUSTC_WRAPPER`, and a disk-backed temporary directory.

| Check | Result |
| --- | --- |
| `cargo test --locked --offline --test compiler_work_reporting composed_frames_execute_through_independent_core -- --exact --nocapture` | Red on the base with the reported work refusal; green on the candidate with the phase counts above. |
| `cargo test --locked --offline --lib payload_membership_preserves_order_and_retries_after_refusal -- --nocapture` | Red on the base; green after the candidate, including full-key distinction, ordered replay, one-short/exact reset and retry; 18.26 seconds. |
| `cargo test --locked --offline --lib generic_cell_ -- --test-threads=1` | 49 passed, including Core transformations, hidden-retention rejection and private-image reconstruction; 23.48 seconds. |
| `cargo test --locked --offline --lib cell_core_ -- --test-threads=1` | 12 passed; 2.20 seconds. This filter overlaps the preceding command. |
| `cargo test --locked --offline --test resource_scope_typing --test resource_scope_runtime --test resource_scope_modules --test scoped_evidence_interactions -- --test-threads=1` | 102, 41, 17 and 54 passed respectively, including owner and escape negatives; 49.38 seconds. |
| `cargo fmt --all -- --check` | Passed; 5.51 seconds. |
| `cargo clippy --locked --offline --all-features --lib --test compiler_work_reporting --test resource_scope_runtime --test resource_scope_typing --test resource_scope_modules --test scoped_evidence_interactions -- -D warnings` | Passed; 15.53 seconds. |
| `cargo build --locked --offline --lib --bin ash` | Passed; 0.15 seconds. |
| Matching native/private-image control | `ash build --output <temp>/native-host --cargo-target-dir target <temp>/native-input.ash` passed; after moving the source, the host returned `42` with empty stderr. Build: 43.18 seconds. |

The native input was a copy of the existing nested-helper handler fixture,
SHA-256 `01abd26d5d58b9a40e9a78c46d8362a68b120c89b9d91e6dbff396a6c4aabf58`.
The matching compiler executable was SHA-256
`da236ec88a2838580d06e291c9be683e45e6b22d6414ba7f02ef62727f159057`.
The generated image and expected facts were 6,183 and 3,598 bytes. The image
control is small; it does not claim the separate scope of issue #197.

The last full workspace gate covered issue #195 candidate
`92be540d38ed8829ce20146e5f7667aa95d6bcad`; it is not a gate for this task.
The next fresh full gate remains pending at the integration checkpoint above.

## Discoveries

Temporary instrumentation of the existing capture charge wrapper, with the
normal source allowance, recorded 74,124,500 paid units across 45,287 payload
membership checks before refusal. State-key charges recorded 11,065,164 units.
The wrapper observed 99,419,246 units against the source ledger's 99,595,813,
an arithmetic remainder of 176,567. The wrapper omits direct charges and may
observe nested loans, so these charged-work buckets are not a proved disjoint
partition or CPU measurements. The instrumentation was removed.

The reviewer confirmed that any membership index must retain the ordered
payload replay, distinguish the complete port/resource/context key, reset at
all three existing replay boundaries, and reserve and charge storage before
publishing changes to either collection. It cannot cache escape permission.
The candidate uses the existing atom-membership pattern: the set stores only
exact triples; the vector remains the replay and diagnostic-order authority.
Both fallible reservations precede insertion, and reset pays for the allocated
set before clearing either collection. Independent review inspected those
allocation-failure paths; the executed test covers work refusal and retry.
Development used Terra 6.1/max and independent review used Sol 6.1/max. Exact
model runtime is not exposed; the times above are observable command wall times.

## Deviations

None. [Issue #197](https://github.com/dikini/ash-lang/issues/197) is separate.
