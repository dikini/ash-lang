# Proposed bounded owner/resource in-process packaging experiment

> Historical experiment record. The user's 2026-10-24 smaller-boundary plan
> supersedes the assignments below. This document authorizes no further
> preparation, build, probe, installation or execution under the revised plan.

Status: proposed map-budget amendment for review. Prior build assignments remain
historical; this amendment does not assign another command. Preparation is authorized; this
text authorizes no build, candidate execution, provisioning, product change or
architecture acceptance. The lead must separately assign each gate below.

This is the owner/resource comparison under the existing
[Linux experiment](linux-profile-experiment.md), governed by
[DN-0057](../DN-0057-checked-ffi-module-boundaries.md),
[TASK-0050](../../tasks/TASK-0050-checked-ffi-regions-control-program.md) and its
[F2 plan](https://github.com/dikini/ash-lang/blob/a54e9215860cd9693d1a2dc9ff79e8f0f4a57e23/docs/tasks/plans/checked-ffi-regions-control.md#f2-validate-the-linux-execution-profile).
The historically accepted
[CP-0024](https://github.com/dikini/ash-lang/blob/a54e9215860cd9693d1a2dc9ff79e8f0f4a57e23/docs/proposals/CP-0024-checked-foreign-host-profile.md)
governed that earlier transition. [AD-0015](https://github.com/dikini/ash-lang/blob/2766e8260e2590d9ebdca7abd699115b3cd02a8a/docs/decisions/AD-0015-linux-scalar-inprocess-whole-images.md)
accepts owner-free scalar images only; its scope and approvals remain unchanged.

## Question and comparison

Can the existing generated whole-static GNU image package a minimal real opaque
native owner and direct Ash resource lifecycle, with an inspectable exact native,
evaluator, bridge and private-payload closure? What additional ownerful trust,
launch and shutdown premises would a later in-process architecture require?

Compare one existing-profile generated owner baseline with retained PR97's static
checked lifecycle. The baseline has legacy codecs and no checked host activation.
It cannot demonstrate checked O/K enforcement, quarantine, receipt admission or
native outcome truth. No option, flag or private path may bypass current checked
runtime/image refusal. A later ownerful architecture needs separate independent
review and owner acceptance; successful packaging does not select it.

## One fixed baseline

Use the repository's existing `tests/fixtures/source-owner/owner.ash`, frozen
before adaptation. Make only the native symbol-name replacements
`ash_owner_acquire` to `malloc` and `ash_owner_release` to `free`. Preserve its
opaque representation, complete Before/R/After formals, nullable acquisition,
State-only void disposition teardown, direct resource/provider implementation
and public generic acquisition codec. No Access, bytes, initialized extent,
callback, child-owner retention or SQLite declaration is added.

Use a separately frozen entry with supported qualified syntax:

```ash
import owner as Owner

main : Unit -> Owner.Scope<Unit, Unit, Int>
main () = resource Owner.Probe<{}, Fresh, {}> owner = 8 {
    Owner.read owner
}
```

The source read handler resumes its independent stored input; it does not read
uninitialized native memory. The eight-byte malloc allocation is opaque and free
receives the exact current pointer through the existing generated bridge. Both
native calls remain trusted libc operations. Reject an adaptation that cannot
prepare, check, link or generate through the public existing-profile path; do
not repair its semantics or substitute a synthetic authority fixture here.

The static checked comparator is the retained PR97 fixture at the selected
compiler commit: State<H,R>, exact host H, checked_scope, canonical checked
finish/report and required Trace continuation. Record the different source/ABI
contracts, codecs, effects and assumptions explicitly. Compare generated plan
and retained static contract coverage; do not claim the legacy executable
implements that checked comparator. The PR98 Borrow work is not a prerequisite
and is excluded from the frozen baseline.

## Frozen inputs and numeric limits

Before assigning a build, freeze the exact full compiler commit/tree and clean
source/configuration manifest; input and entry bytes; public CLI/build API and
commands; target and compiler/linker versions; exact runtime/native archives,
headers/configuration; and bridge-generator identity and requested plan inputs.
Bind missing inputs and source-correspondence assumptions honestly. A system
library path or package version alone is not a native-input digest.

After the separately assigned build, retain its actual generated root, bridge
sources and resolved plan, private payload and expected-fact digests, complete
link-map hash and final image size/bytes/digest. Compare the generated closure
with the pre-build frozen inputs before producing an execution receipt. These
outputs are not prerequisites that must exist before the build is assigned.

Use `x86_64-unknown-linux-gnu`, existing debug profile, the sole lead-operated
shared Cargo cache, `CARGO_BUILD_JOBS=1` and empty `RUSTC_WRAPPER`. Do not change
global RUSTFLAGS or disable build fingerprint guards. Any root-only whole-static
relink step must be frozen, reviewed and recorded separately from ordinary host
production; it is an experiment artifact, not a new supported build mode.

| Observation/admission item | Proposed finite bound |
| --- | --- |
| Whole static image | 128 MiB; refuse oversize before copy/inspection |
| Each adapted Ash source/entry or generated experiment text record | 1 MiB; report excess as unsupported |
| Producer receipt | 256 KiB |
| Independent experiment approval | 64 KiB |
| Closure manifest | 4096 records, 4 MiB encoded total |
| ELF program headers | 64 |
| Command output and each raw build log | 16 MiB each |
| Produced and retained complete link map | 128 MiB; map only, prospective amendment below |
| Build/relink diagnostic window | 20 minutes per assigned command, one build job |
| Optional later execution | 30-second child deadline, 16 KiB combined output |
| Baseline native allocation | One requested 8-byte malloc; not a native-memory quota |

The 1 MiB text-record bound applies to adapted Ash experiment inputs and
generated experiment text. The entire pre-existing selected repository snapshot, including compiler,
documentation, proof, historical evidence and archive blobs, is separate
producer input: retain every selected Git blob in a complete
per-file manifest and verify full size/hash/path-set equality before and after
each build phase. Do not omit or truncate compiler files to satisfy the record
bound, or substitute the smaller build.rs fingerprint census for the complete
snapshot. At selected commit 1a8ecef0b03ddc75a45254543bd8f6f0bb10969c,
all 2784 Git blobs are pinned; the separate build.rs content census has 177
inputs. Compiler files src/resolved.rs (1,793,508 bytes), src/elaborate.rs
(1,779,136 bytes) and src/core/validate.rs (1,688,770 bytes) exceed 1 MiB.
Five other selected snapshot blobs also exceed 1 MiB: KERNEL.md (1,674,762),
SourceScheduledCleanupInterfaces.lean (3,001,334), historical
resource-calibration/build-and-source.tar.gz (2,617,276),
lifecycle-postattempt-syntax-corrected-red.log (1,479,865), and
lifecycle-public-codec-semantic-controls.log (1,515,703 bytes). Full paths and
size/hash records for all eight, and all other blobs, remain in the complete
2784-entry producer manifest (96,452,672 file-content bytes). No old snapshot
blob was excluded from that clarified category. Their exact full hashes/sizes
remained assigned producer inputs. PR100 retained this source-category
clarification at 2ac8c393846715249de5a475a65e47bf1309bb54 before Stage1 was assigned.

Tool executables and ordinary build intermediates are separate from the final
candidate. Stream tool/input hashing against frozen expected sizes and hashes;
do not apply the 128 MiB final-image limit to tools/intermediates. The pre-Stage1
cache observation was 589,362,808 bytes and was not approved for reuse at that
time. The separately assigned selected-source Stage1 build later produced a
589,364,584-byte compiler, SHA-256
`5dca1b624bf206c44c6c4d3037675193800516eb936a0cf6420e67394e998d3e`;
its [historical correspondence record](linux-owner-inprocess-evidence/README.md#actual-assigned-results)
does not identify the current contents of a shared cache after later builds. The proposed map-only amendment below replaces the retained 64 MiB map category
prospectively. Earlier 16 MiB and 64 MiB observations remain unchanged. All
experiment text, manifest, receipt, output/log and final-image bounds otherwise
remain unchanged.
Sampled storage monitoring is not a quota or a zero-overshoot guarantee.

These are experiment record/tool bounds, not promises of host memory/CPU
containment or new product gas coefficients. Inspect bounded ELF headers and
segments without candidate execution: ELF64 little-endian x86-64 ET_EXEC, no
PT_INTERP/PT_DYNAMIC or unsupported dependency metadata. Structural static
format does not prove absence of runtime loading. Retain exact size/hash and
compact LOAD/header evidence, whole-map hash and omission qualifications.

## Prospective map-only budget amendment

PR102 retained the 64 MiB map-only policy at
88db679943c981458b829e1c430e9af290976d9f after two 16 MiB map refusals. A separately
reviewed per-file-class monitor then enforced map 64 MiB and watched logs/output
16 MiB. Both later static relinks also refused: third observed 68,108,288 map
bytes; fourth, using only additional --no-demangle output rendering, observed
70,373,376. Each retained prefix is exactly 67,108,864 bytes. These may be
incomplete maps at different termination progress; none has a full-map hash,
verified static candidate, passive ELF result or after-verification. All four
attempts remain failures. See the [new evidence and study](linux-owner-map128-evidence/README.md).

The fourth prefix shows that raw mangled section and symbol names now match,
but duplicated names, archive/object paths, extents and fill records still consume
the cap while inside .text. Complete fixed ordinary-producer ELF metadata has
131,160 symbol rows and 27,704,553 referenced-name bytes. Combining those complete
input facts with the observed fourth-prefix line overhead estimates 101,996,794
bytes (97.27 MiB) for a full-record map. It is a scaling model, not an upper bound:
static CRT, section grouping/order and unseen nontext details can differ.

Prospectively allow at most 134,217,728 bytes (128 MiB) for the complete produced
and retained map, about 31.6% headroom above that explicit model. This is a finite
operational choice, not fit, link-success or native-correctness assurance. Command
output and every watched build/native log keep their separate 16,777,216-byte
(16 MiB) caps. Final image 128 MiB, PH 64 and all other bounds remain unchanged.
Keep semantic/static flags and source/native inputs fixed, along with the existing
discarded-section suppression and mangled symbol rendering; remove no additional
active symbol/address/archive records. Require the full new map within its cap,
complete hash, recognized GNU/BFD framing/OUTPUT, nonempty LOAD and exact pinned
libc.a association. Missing linker temporaries remain producer/build-trust limits.
No partial prefix or narrower artifact substitutes for complete-map evidence.

For a later separately reviewed tuple, place only new experiment outputs in one
private, owned 0700 directory under the existing ignored shared Cargo target on
the project disk. This is not a new cache, checkout, source relocation or persistent
approval store. Leave selected source and stored Stage2 inputs unchanged. Observe
canonical parent identity, ownership and actual available bytes before/after;
capacity is not reserved. The known map/image/log/record footprint is 583,532,544
bytes, not a global intermediate bound. Rust/linker temporaries may still use
/tmp under the unchanged environment. Do not move/delete old artifacts or unrelated
scratch/cache files to claim compliance, and avoid cache pruning during live evidence.

The exact executed per-class monitor still caps the map at 64 MiB. This proposal
changes no monitor, collector or tuple. Before another assignment, independently
review new per-class code/tests and exact collector/config pins enforcing map
128 MiB versus logs/output 16 MiB, with bounded retention and full-map gates.
A self-test override or generic watched-file cap must not widen logs. Sampled
peaks can overshoot or miss changes; they are neither hard quotas nor proof of
unobserved maxima. Check current output space afresh, without claiming reservation.

Retain this amendment and bind its actual retaining commit/contract hash into a
fresh independently reviewed tuple before root assigns a free sole Cargo slot.
Preserve the earlier contracts, all four tuples/receipts and exact bounded-prefix
content. The two 64 MiB prefixes may be archived in deterministic gzip containers
with explicit compressed and decoded size/hash pins and bounded streaming
verification; container bytes are derived evidence, not byte-identical raw files
or complete maps. Historical receipts remain unchanged. No relink, inspection,
startup, provisioning, ownerful architecture or checked-runtime authority follows.

## Trust, owner groups and shutdown

The proposed in-process comparison retains host UID/groups/filesystem authority.
Native/runtime memory integrity, ABI/result/disposition truth, producer/build
correspondence, allocator correctness and no retention of this opaque pointer
outside the declared owner are explicit premises. The fixed trusted closure
must preserve built-in C locale and exclude unreviewed loading, plugins, NSS,
charset conversions, callbacks and registrations across startup, normal/error,
panic/unwind and cleanup paths, including init/fini, IFUNC and TLS. The scalar
source audit is relevant conditional evidence, not an ownerful approval or a
whole-libc proof. New producer/runtime/native inputs require fresh review.

The future checked owner mechanism must preserve distinct H versus ownership
group identity, provisional acquisition/guard authority, charged retained owner
records, quarantine/access retirement and exact required source continuation.
This experiment does not implement or prove them. Its single dependency-free
owner avoids inventing C-to-S group merging rules. Two owners sharing H are not
implicitly one group. A later architecture must state how host loss and delayed
shutdown retain control/storage reservations and what trusted process observes
termination; F4 owns O/K implementation and F6 connects admitted artifacts.

A native fault may corrupt or terminate this entire in-process execution host;
there is no per-library address-space, filesystem, syscall or resource isolation.
Forced process termination/reaping does not prove Free, source finish or local
K completion, and must not be reported as such. No effect replay, group recovery,
mode fallback, unconditional availability or independent native correctness is
promised. Fault injection, unbounded loops and arbitrary foreign artifacts are
outside this comparison. Isolated Stage B remains separately blocked.

## Three separate exact gates

1. **Contract review and build assignment.** Independent reviewer checks scope,
   supported source/ABI adaptation, input pins and proposed bounds. Root then
   assigns the exact source/compiler/command/cache snapshot to the sole build
   operator. No candidate startup is part of build/inspection. If a public build
   command executes its generated image automatically, do not use it.
2. **Packaging/inspection evidence.** Retain preparation, source checking,
   generation/link results and refusals; generated/native/runtime closure,
   fingerprint checks, ELF/size facts and correspondence comparison. Build a
   producer receipt. Root/reviewer assess the exact bytes and declared premises.
   A failed baseline or missing provenance remains a refusal, not evidence of
   checked runtime behavior. No strict approval exists merely because this gate
   passes.
3. **Optional separately authorized trusted diagnostic.** Only after exact
   artifact review may root independently approve the particular receipt/image,
   harness/policy and purpose. The approval must name this owner/resource
   diagnostic, trust/loading premises, target/context and numeric bounds. Neither
   prior scalar approval nor this contract is applicable authority. Copy bounded
   candidate bytes into an executable memfd; seal writes, growth, shrinkage and
   further seal changes; then hash and inspect the final immutable fd, match its
   image/receipt/policy associations against the exact independent approval, and
   execute that same fd with one fixed argv[0], empty environment, standard
   descriptors and unrelated FDs closed. Never reopen a candidate pathname after
   verification or execute on a hash taken before sealing.
   Require cleanup/reaping for every post-fork setup/refusal/timeout path. Preserve
   sandbox refusal; approved host-tool escalation for the same exact artifacts
   requires explicit authorization. Never modify host policy to obtain a pass.

The optional diagnostic can observe its existing-profile output, immutable image
identity and process lifecycle. Any substitutions/mutations are no-child
refusals unless separately approved; never execute an unapproved replacement.
No startup of unknown foreign code, new approval store, namespace, mount, cgroup,
quota, seccomp, UID/group policy or privileged helper is provisioned here.

## Contrary outcomes and retention

Preparation/type/header/bridge/link refusal identifies its first actual boundary;
no arbitrary error counts as native owner evidence. Missing archives, dynamic
linking, oversize image, unsupported runtime closure, stale fingerprint, missing
input or mismatched approval stops that gate. ELF success plus retained loader
routes requires explicit source/premise assessment; trace absence is not proof.
Sandbox EACCES remains a deployment result. A timeout, setup failure, unexpected
output or missing reap is retained as failure, never a successful native finish.

Retain source/command/configuration/tool/input pins, raw failure/status logs,
generated-source/private-payload hashes, complete receipt/approval associations,
compact ELF/map observations and exact diagnostic lifecycle records. Keep
binaries, archives, build cache and giant maps out of the repository. Clearly
label any omitted external artifact or unreconstructible input. Freeze new
receipts rather than rewriting prior scalar or isolated observations.

Remove disposable generated roots, binaries and temporary allocations only
after records and hashes are complete and independently checked. The native
pointer exists only in a later separately approved child process; parent cleanup
cannot claim its destructor ran. No persistent volume is created, and the shared
build cache remains under the sole operator's normal ownership. Evidence remains
experimental; retain no prototype loader/runtime on the product path.

## Delivery and later decision

The initial issue #58 delivery retained the owner/resource contract and an
informative Linux-experiment link, followed by PR100's build-monitor preparation
and source-category clarification. PR102 retained Stage1 compiler and Stage2 ordinary-generation evidence and the
first two Stage3 map-limit refusals. PR103 retained the third and
fourth 64 MiB refusals, bounded postmortem/complete producer-metadata study,
explicitly derived prefix containers and the 128 MiB map-only/output-
placement amendment. That delivery changed no F2 whole checkbox,
architecture scope or execution permission. Reviewer checks original record
preservation, authority links, exact input correspondence, finite class-specific
bounds, separate command assignment, contrary outcomes and disposal. A later
retry requires retained amendment bytes and a separately reviewed exact tuple;
this document does not assign it.

After separately assigned evidence, a later reviewed decision may select an
owner/resource in-process architecture and its residual trust/deployment
requirements. F6 still needs independent protected approval/context enforcement
and exact checked receipt/startup associations; F4 needs checked reservation,
guard, quarantine and completion implementation. F7 additionally requires the
external trusted credential setup and actual restricted worker/root/storage/
filter/limit/quota/fault/termination evidence. SQLite, C-to-S dependencies,
checked bytes/windows, whole F2/M1 and Main remain separate gates.

The [trusted-build preparation record](linux-owner-inprocess-probe/README.md)
retains the monitor, safe controls and selected-source correspondence. It is
informative preparation and does not assign a build or approve startup.

The [successful fifth packaging record](linux-owner-static-packaging-evidence/README.md)
retains the later complete-map/static-ELF observation and small original
receipts. It records no candidate execution, ABI/native-closure completion,
ownerful architecture selection or whole-F2 acceptance.

The [header and proposed closure record](linux-owner-header-closure-evidence/README.md)
retains separately assigned dependency-discovery and syntax-only observations.
It supplies conditional header/target correspondence and proposed ownerful
trust applicability, not architecture acceptance, native startup or whole F2.

The [trusted owner diagnostic record](linux-owner-diagnostic-evidence/README.md)
retains the later sandbox refusal, separate approval/setup history and one
explicitly approved host result. It observes the fixed legacy report under
trusted premises, not native truth, checked runtime or architecture acceptance.
