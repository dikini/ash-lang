# Proposed bounded owner/resource in-process packaging experiment

Status: proposed contract amendment for review. Preparation is authorized; this
text authorizes no build, candidate execution, provisioning, product change or
architecture acceptance. The lead must separately assign each gate below.

This is the owner/resource comparison under the existing
[Linux experiment](linux-profile-experiment.md), governed by
[DN-0057](../DN-0057-checked-ffi-module-boundaries.md),
[TASK-0050](../../tasks/TASK-0050-checked-ffi-regions-control-program.md) and its
[F2 plan](../../tasks/plans/checked-ffi-regions-control.md#f2-validate-the-linux-execution-profile).
Accepted [CP-0024](../../proposals/CP-0024-checked-foreign-host-profile.md)
continues to own semantic transitions. [AD-0015](../../decisions/AD-0015-linux-scalar-inprocess-whole-images.md)
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
| Retained raw build log and link map | 16 MiB each; compact extracts in repository |
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
blob is silently excluded from the prospective category. Their exact full
hashes/sizes remain assigned producer inputs. This prospective clarification must be reviewed and retained before assigning that build.

Tool executables and ordinary build intermediates are separate from the final
candidate. Stream tool/input hashing against frozen expected sizes and hashes;
do not apply the 128 MiB final-image limit to tools/intermediates. The observed
cached compiler is 589,362,808 bytes and is not approved for reuse. Keep all
experiment text, manifest, receipt, log/map and final-image bounds unchanged.
Sampled storage monitoring is not a quota or a zero-overshoot guarantee.

These are experiment record/tool bounds, not promises of host memory/CPU
containment or new product gas coefficients. Inspect bounded ELF headers and
segments without candidate execution: ELF64 little-endian x86-64 ET_EXEC, no
PT_INTERP/PT_DYNAMIC or unsupported dependency metadata. Structural static
format does not prove absence of runtime loading. Retain exact size/hash and
compact LOAD/header evidence, whole-map hash and omission qualifications.

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

The smallest issue #58 PR adds this proposed contract and one informative link
from the existing Linux experiment. Before: accepted AD-0015 owner-free scalar
scope plus isolated prerequisite failure. After: the same accepted authority,
with an independently reviewable owner/resource experiment question and explicit
future gates. No F2 whole checkbox, architecture scope or execution permission
changes. Reviewer checks authority links, exact input correspondence, supported
source/contracts, finite bounds, gate separation, contrary outcomes and disposal.

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
