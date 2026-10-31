# TASK-0061: Parent-Path Executable Startup

- ID: `TASK-0061`
- Status: active
- Related: [issue #197](https://github.com/dikini/ash-lang/issues/197), [AD-0001](../decisions/AD-0001-implementation-environment.md), [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007](../decisions/AD-0007-typed-core-dialects.md), [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md), [generic-cell specification](../../spec/static-semantics.md#generic-cell-foundation), [elaboration](../../spec/elaboration.md), [build contract](../tools/ash.md#building-an-executable)

> This task organizes work. It does not define Ash semantics.

## Dependencies

Compilation and compiler-side Core transformations independently validate their results
before the final representation is packaged.
The user has accepted a different non-language trust boundary for compiler-generated
executables: the compiler serializes its verified representation, and the matching
linked host reconstructs that representation for execution without repeating its
semantic proof. Reconstruction still creates fresh runtime identities and pays its
bounded construction and native-binding work. It does not reopen source paths.
The developer owns the connected path and Cargo slot; the independent reviewer
checks the change and frozen inputs. The PM owns publication and integration.

## Work

1. Retain the exact reported interpreter and generated-host regression, including
   moving both the entry and import root before preparation and executing the
   linked host, plus the direct-cell `42` control.
2. Amend affected current decisions, specification, tool and API documentation
   for the accepted trust boundary. Keep compilation and transform validation,
   runtime capture semantics, bounded reconstruction and native bridge setup.
3. Reconstruct compiler-produced Pure and Effect images without repeating Core,
   capture or source-evidence admission. Preserve the data needed for faithful
   reconstruction and runtime relocation, with no new image-loading product path.
4. Run connected normal-budget execution, Pure and Effect image/bridge controls,
   affected #195 and #196 callers, compilation and transform negatives, and
   applicable refusal and provenance checks. Freeze the candidate for review.
5. The next full-workspace checkpoint is the pinned Main integration candidate,
   before separately authorized Main integration. The PM coordinates the gate
   with the developer as Cargo operator. Focused PR checks are not that gate.

## Progress

Base: `3f4def15076981f293aba9652f63d3852b5bff46`. It retains issue #196's
merged change and has the same tree as reviewed candidate
`f9a148f54144e707d2ac914e4c99f0cb06d8491a`. The issue's
[entry](../../tests/fixtures/parent-path-startup/main.ash),
[buffer module](../../tests/fixtures/parent-path-startup/buffer.ash) and
[direct-cell control](../../tests/fixtures/parent-path-startup/direct-cell-handler.ash)
have SHA-256 prefixes `17bde81d`, `e72e1274` and `9684a1a7` respectively.
On this base, the original parent-path interpreter
returns the reported value and type with empty stderr. Its generated host
builds but refuses startup with `core.validation.resource` after both entry and
import root are moved. The direct-cell interpreter and host return `42`.

On the base, the connected `program_build` regression reproduced the startup
refusal after compilation, interpretation and native linking. Its 93.48-second
red run used 18,742,466 / 68,230,000 source units, 50,604 / 5,458,400 final
elaboration units and 44,601,029 / 170,575,000 independent Core units. The
candidate executes the original parent result and the direct-cell `42` through
the public build path after their source paths move.

## Discoveries

The original image and expected facts contain 32,227 and 9,142 bytes, giving
4,881,542 startup units under the unchanged `118 * (image + facts)` policy.
The normal run exhausted that cumulative meter during independent capture
analysis. A separately authorized diagnostic using the same bytes and one
finite tenfold meter completed reconstruction and the repeated Core proof at
44,724,686 units. The source compiler's Core phase used 44,601,029 units on the
same source. This identifies repeated proof as the material cost; the diagnostic
is not evidence of normal-budget acceptance.

Two local approaches were investigated before the trust decision. A guarded
resume shortcut completed at 43,556,335 diagnostic units. An exact structural
sharing experiment completed at 21,477,086 diagnostic units, still above the
normal limit. Both experiments and their instrumentation were removed. Their
results do not alter capture semantics or grant permission to merge owner paths.

The user then confirmed that a linked executable carries the compiler-verified
representation as trusted compiler output. The compiler continues to validate
its final representation before encoding, including after any compiler-side
transformations. Startup reconstructs the encoded representation and runtime
bindings; it does not reprove source or Core facts. The exact normal-budget host
is the acceptance discriminator.

## Verification

All Cargo checks use Rust 1.97.1, locked offline dependencies, one Cargo job,
an empty `RUSTC_WRAPPER`, and a disk-backed temporary directory. The last full
workspace gate covered issue #195 candidate
`92be540d38ed8829ce20146e5f7667aa95d6bcad`; it does not cover issue #196 or
this task. The next fresh full gate remains pending at the integration checkpoint
above.

The final source and fixture set received these focused checks:

| Check | Result |
| --- | --- |
| `cargo test --lib build::image::tests:: --locked --offline -- --test-threads=1 --nocapture` | 28 passed, including nine normal-meter generic-cell image flows with exact/one-short/fresh retry, compiler-side identity/fold codec checks, and retained-control startup. |
| `cargo test --lib build::image::provenance_tests:: --locked --offline -- --test-threads=1 --nocapture` | 6 passed, including fresh identity, structural bounds and cumulative work retry. |
| `cargo test --lib build::native_image_tests:: --locked --offline -- --test-threads=1 --nocapture` | 4 passed, including linked bridge setup and repeated source-independent execution. |
| `cargo test --test architecture --locked --offline -- --test-threads=1` | 47 passed. |
| `cargo test --test program_build --locked --offline -- --test-threads=1 --nocapture` | 7 passed in 93.21 s, including the exact parent result and direct-cell `42` after moving their source paths, and the Pure host. |
| `cargo test --test program_build_native generated_pointer_hosts_preserve_native_calls_and_bytes_with_both_linkages --locked --offline -- --test-threads=1 --nocapture` | Passed for static and shared native linkage. |
| `cargo test --test program_build_native ordinary_binding_checks_null_length_and_cleanup_with_both_linkages --locked --offline -- --test-threads=1 --nocapture` | Passed for both native linkage modes. |
| `cargo fmt --all -- --check` | Passed. |
| `cargo clippy --locked --offline --all-features --lib --test architecture --test program_build --test program_build_native --test resource_scope_runtime --test compiler_work_reporting -- -D warnings` | Passed. |

Seven separate `cargo test --lib FILTER --locked --offline -- --test-threads=1`
checks passed for these filters:

- `generic_cell_image_role_allocates_a_fresh_identity_with_paid_retry`
- `retained_continue_authenticates_deferred_adapters_and_allocation`
- `retained_drain_revalidates_and_runs_after_core_transforms`
- `retained_same_typed_cleanup_callback_substitution_rechecks_release`
- `generic_cell_linked_hidden_retention_is_reconstructed_after_transforms`
- `generic_cell_inner_handler_outer_write_rejects_hidden_younger_capture_after_transforms`
- `generic_cell_possible_target_owners_rebuild_after_transforms`

`cargo test --test resource_scope_runtime helper --locked --offline -- --test-threads=1 --nocapture`
passed seven issue #195 helper tests.
`cargo test --test compiler_work_reporting composed_frames_execute_through_independent_core --locked --offline -- --test-threads=1 --nocapture`
passed the issue #196 five-frame test in 115.27 s. It used 89,230,709 /
99,600,000 source units, 77,006 / 7,968,000 elaboration units and 157,219,963 /
249,000,000 independent Core units, matching the prior result. Those caller
checks preceded an image-constructor rename and comment-only edits; neither
changed their behavior.

## Deviations

None.
