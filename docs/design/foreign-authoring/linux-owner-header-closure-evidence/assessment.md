# Ownerful in-process closure delta

Status: reviewed-input assessment, not an architecture choice, strict approval or
startup assignment. AD-0015 remains owner-free scalar only. The accepted owner
experiment contract authorizes separately assigned evidence gates, not ownerful
runtime semantics. Exact read inputs are in [inputs.json](assessment-inputs/inputs.json). No compiler,
linker, trace or native image ran for the assessment. The separately assigned
header query and syntax result below subsequently passed independent audit.

## What now exists

The fifth image is 71,022,184 bytes, SHA-256
52f09983205ecb2b524a3572fba267e79e28057c933f6408f7fde0f3ac42bc65.
Its complete 100,345,205-byte map is SHA-256
43348533a205d18534436b7c9bb932d6b86e733c3ec3162b8b86703f2fb4997b.
Static ELF facts and exact source/tool/generated before/after correspondence are
observed. The map has 78 LOAD records, 68 existing records covering 67 paths,
and 10 absent linker temporaries. This does not establish a fully hashed native
closure, source-to-installed-libc reproduction or absence of runtime loading.
The two source-requested symbols are malloc and free, not abs. Rust/runtime
allocation already existed in the scalar image, so this is not evidence that
allocator machinery is entirely new; the explicit native owner lifetime and
irreversible call/report/cleanup obligations are new to this binding class.

The exact generated main.rs declares `malloc(usize) -> void*` and `free(void*)`, with
fixed private coordinates and expected-facts association. Allocate accepts one
USize operand; readiness.returned arms the returned pointer before an ordinary
Ash reporting step. Free takes the admitted current address and returns void.
The source owner is dependency-free, opaque, nullable acquisition, consumes on
void teardown. No native read/byte/window callback is generated. Entry requests
size 8 and its handler returns stored source data 8; it does not read native memory.
The size 9 refusal branch exists in producer source but is not this fixed entry.

The selected source runtime reserves guard storage before native entry and arms
NonNull immediately after return (source_owner_runtime.rs:674–839). RawOwnerGuard
removes its address before invoking destruction (around 299); ordinary storage
close/drop/quarantine paths are around 372–415,492–506,545–634. These are reviewed
source mechanisms, not an observed fifth-image cleanup run. Process exit or a
printed completion cannot independently prove native destructor truth. The
private image startup decoder/fact/bridge correspondence path is build/mod.rs:
320 onward; generated main prints either output or error. Checked-profile
runtime admission and CP-0024 O/K completion do not follow from this legacy path.

## Transfer and additional obligations

| Boundary | Transferable support | Additional ownerful condition or unknown |
| --- | --- | --- |
| Whole static image | Same target/ET_EXEC/no INTERP/DYNAMIC mechanism and final-image pinning design | This exact evaluator/bridge/payload/runtime/native image and new LOAD census need their own receipt and approval; old scalar approval is inapplicable. |
| Locale/loading | Scalar audit's conditional built-in C locale/gettext/strerror reasoning; same libc.a hash | Preserve C locale in global/every thread and exclude direct/indirect plugin/NSS/charset loading across allocator/error/destruction paths too. Retained loader names are not observed loads. |
| Allocation | Existing runtime already allocates; exact bridge uses size_t and fixed 8 | Review/trust installed allocator initialization, arenas/thread/TLS, locking, native allocation failure and allocator diagnostics under the fixed context. No unexplored tunable/plugin/debug allocator configuration. Source correspondence is not supplied merely by header success. |
| Native ownership | Exact malloc/free signatures and generated current operand plan; real guard source | Trust nonnull allocation validity/extent/alignment, same allocator/free compatibility, valid live pointer exactly once, synchronous return and truthful declared consuming disposition. Runtime/native memory integrity remains trusted. Wrong/double/free-after-loss can corrupt or terminate the whole host. |
| Acquisition/report gap | Source reserves storage and arms destruction before report | Establish exact deployed producer/runtime applicability for null, allocation/report refusal, panic/unwind and abandoned source continuation. No claim native return implies source completion or that resource preparation cannot fail. |
| Teardown/shutdown | Existing finite startup/error/unwind/shutdown closure contract | Include native free, pending/abandoned guard close, registered destructors, partial initialization and allocator reentrancy/abort behavior. Whole host loss can prevent any cleanup; neither timeout/reaping nor process exit proves free ran. |
| Accounting/group | Scalar architecture has no owner groups | Later checked implementation must reserve/account the connected owner group before acquisition, preserve generation/identity/dependencies and one-attempt/quarantine rules. Legacy independent guard/storage evidence is not F4 checked group/O/K evidence. |
| Startup/finalizers | Review method for _start/_init/_fini/arrays/IFUNC/TLS/registrations transfers | Scalar constructor-array counts do not transfer to this image. Exact fifth initializers, thread/signal entries, registered cleanup, Rust panic/backtrace/unwind and shutdown conformity need their own bounded review or explicit trusted applicability. |
| Deployment/admission | Independent protected approval, administrator context association and sealed same-fd design can be proposed for reuse | None is provisioned/enforced by packaging. Host authority/supplementary groups retained; no isolation/availability/native truth guarantee. Changed image/context/policy must refuse before native initialization or allocation. |

The exact libc.a agrees with the earlier scalar audit's installed package, but
that audit's Ubuntu import is patches-unapplied and local Rust sources do not
reproduce precompiled std. Its 81-input manifest does not contain malloc.c;
there is no newly reviewed allocator implementation source here. The earlier
nine missing scalar temporary inputs are historical; this image has its own ten
missing temporaries, not an inherited completed closure. A small bounded name
selection in [map-examples.json](assessment-inputs/map-examples.json) records retained allocator/loading/exit names;
it is not a call-graph or all-path reachability proof. A future trace might
expose a violation, but absence in one run cannot discharge the closure premise.

## Smallest justified next action

1. Completed and independently audited: the separately assigned query found
   27 headers plus exact source; the subsequent syntax-only gate passed C
   target/prototype/size_t/pointer assertions with all 28 frozen inputs equal
   before/after and equal emitted dependency set/hash. See the [query receipt](query/discovery-receipt.json)
   and [syntax receipt](syntax/syntax-receipt.json). This is conditional installed-header
   evidence, not libc implementation or owner behavior. Original discovery
   remains post-query snapshots, not retrospective byte-history proof.
2. Prepare one [proposed finite ownerful closure applicability record](ownerful-premise.proposed.json) for independent
   review: exact producer/runtime/native/bridge/payload/image/map/header context;
   malloc/free assumptions above; C-locale/no-loading/startup/error/unwind/cleanup
   conformity; host-loss and checked-group exclusions. Use existing producer
   receipt plus independent approval, no new registry or self-authorizing flag.
   Ten absent temporaries and exact distribution/precompiled-runtime provenance
   are residual trust limits. Do not require a formal whole-libc proof or pretend
   digest equality proves these premises. An ownerful decision remains separate.
3. After the necessary exact review, a trusted diagnostic could ask only whether
   this exact legacy entry reaches acquisition/read/teardown/report from a sealed
   image under fixed argv/empty environment and bounded output/deadline/reaping.
   Preparation must freeze exact expected rendering from source and identify
   allocation-refused versus acquired/completed outcomes before approval. A
   successful printed report would not prove memory reads, destructor internals,
   checked O/K, reserved groups, host-loss cleanup, loading exclusion or isolation.
   It requires a new exact receipt/image/policy-specific approval; no old scalar
   or possible-loading approval can be silently reused or called strict.

This sequence advances actual ownerful evidence rather than substituting scalar
execution. F4 acquisition/call/copy/guard/quarantine/completion accounting, F6
immutable checked receipt/admission/approval/context enforcement and F7 isolation
still need connected product delivery and hostile/budget/fault tests. Declared
C-to-S dependencies, bytes/windows, SQLite and the full FFI milestone remain
visible; this bounded malloc/free assessment neither accepts nor removes them.
