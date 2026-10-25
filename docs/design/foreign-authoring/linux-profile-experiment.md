# Checked FFI Linux profile experiment

> Historical experiment record. The user's 2026-10-24 smaller-boundary plan
> supersedes the assignments below. This document authorizes no further
> preparation, build, probe, installation or execution under the revised plan.

This bounded experiment belongs to [DN-0057](../DN-0057-checked-ffi-module-boundaries.md)
and [TASK-0050](../../tasks/TASK-0050-checked-ffi-regions-control-program.md),
F2 in its [plan](https://github.com/dikini/ash-lang/blob/a54e9215860cd9693d1a2dc9ff79e8f0f4a57e23/docs/tasks/plans/checked-ffi-regions-control.md#f2-validate-the-linux-execution-profile).
The historical 2026-10-21 launch authorized local preparation and nonprivileged probes.
It accepts no architecture or semantics and permits no product implementation.

The later independently reviewed scalar architecture choice is
[AD-0015](https://github.com/dikini/ash-lang/blob/2766e8260e2590d9ebdca7abd699115b3cd02a8a/docs/decisions/AD-0015-linux-scalar-inprocess-whole-images.md), with
[conditional source/provenance evidence](linux-inprocess-probe/scalar-closure/README.md).
This is partial F2 architecture acceptance only. These experiment records remain
bounded evidence; strict per-image approval and production enforcement are
pending, and isolated/SQLite/owner scope remains open.

## Question and comparison

Can the proposed [Linux launch profile](minimal-ffi-launch-and-artifacts.md)
maintain the required authority boundary through first execution and re-execution,
while supporting bounded SQLite copying and connection/statement operations?
Compare the approved whole-image in-process host, the proposed isolated worker,
and refusal when required controls are unavailable. A subprocess alone is not
an isolated-profile success. In-process execution has host authority and retains
native memory-safety assumptions.

The worker, including startup, bridges and monitors, is potentially faulty.
Trusted launcher/supervisor/parent validators, approved build correspondence,
kernel and storage enforcement are explicit premises. Record them separately
from native result truth and source completion.

## Bounded stages

Stage A inventories this deployment and probes sealed-byte mutation refusal,
`no_new_privs` inheritance through exec/re-exec of a trusted Python interpreter,
user-namespace availability and cgroup delegation visibility. It executes no
foreign artifact, changes no host credentials or policy, creates no mounts or
resource domains, and runs no memory fault. A namespace probe may fail normally.
The current UID is an observation, never the selected worker UID policy.
The probe is disposable tooling; its output is evidence only for those checks.

Stage B needs a concrete deployment configuration: launcher implementation,
static test images, configured non-root UID/GID mappings, delegated controller
root and dedicated disposable storage. The repository does not yet contain this launcher/test realization, and this
probe establishes no complete delegated controller/storage configuration. The
[deployment prerequisite probe](linux-profile-probe/README.md#deployment-prerequisite-evidence)
subsequently identifies host user-cgroup delegation, but its attempted trusted
credential setup cannot clear supplementary groups. Its fail-closed result
starts no worker and leaves Stage B unexecuted. A deployment-supplied trusted
credential launcher and the remaining controls still need evidence. Do not
substitute ambient privileges or weaken controls to obtain a pass. The isolated
profile remains unavailable through this tested setup until proven otherwise.

Before Stage B code runs, freeze exact kernel, compiler/linker/native archives,
headers, image/receipt/bridge/contract digests, launcher/filter configuration,
UID/GID maps, storage ownership, quotas and numeric limit policy. No native
startup may precede isolation. Native faults require a contained test process.

## Independent in-process image-pinning comparison

A subsequent bounded assignment authorized a trusted self-authored static C
reporter to test common image admission independently of worker setup. Its
[source, exact approval, build provenance and observations](linux-inprocess-probe/README.md)
record sealed-fd execution after pathname replacement on the host and EACCES in
the filesystem sandbox. It retains host authority and tests no worker isolation,
SQLite, native fault, Ash evaluator or generated bridge. No host policy changed.
The original isolated Stage B remains unexecuted.

This comparison can inform a separately scoped scalar-only in-process
architecture. It accepts no AD or F2 checkbox. A real generated Ash whole-image
packaging comparison and explicit approval/trust/deployment policy still need
review before narrow architecture acceptance. The [requirement split](linux-inprocess-probe/requirements.md)
keeps those questions separate from isolated-worker prerequisites and downstream
F6 product admission/runtime evidence. Missing SQLite and worker group-clearing
authority do not automatically block every scalar-only in-process profile.

The actual [generated Ash static packaging comparison](linux-inprocess-probe/generated-ash/README.md)
links the retained evaluator, signed32 `abs` bridge and private payloads without
changing fingerprint guards. The resulting ET_EXEC has no interpreter/dynamic
section, but retained libc loading paths leave the proposed no-loading requirement
unmet. Packaging performed no image execution. Any separately reviewed trusted
diagnostic needs a distinct exact policy/approval/addendum and cannot convert
this unresolved requirement into architecture acceptance. The subsequent
[exactly approved scalar diagnostic](linux-inprocess-probe/generated-ash/diagnostic-addendum.md)
records host `Returned(7)` and sandbox EACCES under explicit known-loading and
host-authority premises; it leaves that requirement unmet.

## Proposed owner/resource in-process comparison

The [owner/resource experiment amendment](linux-owner-inprocess-experiment.md)
proposes one existing-profile generated malloc/free direct-resource baseline,
compared with retained static checked lifecycle facts. It preserves AD-0015's
owner-free scope and separates contract review, exact build/inspection assignment
and any later exact diagnostic approval. No candidate execution, provisioning,
checked runtime bypass or ownerful architecture acceptance follows from the
amendment alone. Isolated Stage B and SQLite remain separate.

## Proposed architecture requirements awaiting evidence

These requirements refine design questions; they are not an accepted AD.

| Boundary | Required realization and negative comparison |
| --- | --- |
| Credentials | Use nonzero UID/GID inside the worker namespace and no host-root mapping; empty supplementary groups and effective/permitted/inheritable/ambient capabilities; locked securebits/bounding policy prevents regain; `no_new_privs=1`. Trusted setup must establish invariants before foreign startup and verify the same after exec and re-exec. Test UID-0 and retained-capability configurations as refusals. |
| Image | Authorize exact producer receipt and final sealed static ELF bytes; deny interpreter/shared/plugin paths; execute the verified object without reopening a filename. Race replacement, reject changed bytes and unsupported receipt versions. |
| Root and descriptors | Dedicated private root, exclusive `/data`, bounded private `/tmp`; no old-root or management descriptors, host trees or inherited credentials. Test outside-file and descriptor access at startup and request time. |
| Syscalls | Versioned native-architecture default-deny filter installed before exec; deny x32, child/thread creation, sockets, cross-process inspection/signals, namespace/mount changes, io_uring, privilege changes and new executable memfds. Derive required allows from reviewed runtime/VFS needs; traces alone are insufficient. |
| Limits | Delegated cgroup v2 memory/swap/CPU/task controls, finite RLIMITs, quotas, tmpfs bounds, frame/log budgets, aggregate admission and independent deadlines. Test actual enforcement independently; file-size limit is not a volume quota. |
| Lifecycle | Fresh parent session, bounded compatibility before acquisition, no worker self-attestation of containment. Failure retires access and never retries effects; retain reservations until observed termination/reaping. Delayed reaping remains charged. |
| Library | Static SQLite with URI handling disabled and loadable extensions omitted; exercise WAL/journals/locks/temp/quota failure on the actual root and syscall policy. No database correctness inference from well-shaped replies. |

## Required Stage B observations

1. Capture trusted pre-exec setup facts and external supervisor observations.
   A cooperative credential reporter is diagnostic evidence, not the authority
   proving an arbitrary worker contained. Repeat after re-exec of the same image.
2. Exercise approved and substituted images, ABI mismatch, missing controls,
   unsafe volume aliases, and insufficient admission budgets before startup.
3. Attempt each denied authority at startup and during a request. Exercise
   actual memory, CPU, task, descriptor, storage, frame/log and deadline limits.
4. Run real SQLite acquire/copy/bind/reset/finalize/close; separately label
   injected malformed replies, plausible false replies, faults and lost replies.
   Lost finalize acknowledgement must not become native completion; prior
   admitted consumption must survive later payload loss.
5. Measure startup, bounded copying/transport and shutdown with exact sizes,
   repetitions and limits. Report failures and distributions without promising
   availability or recovery. Test delayed reaping and retained storage/journals.

## Retention, disposal and decision gate

Retain commands, exact inputs, failures and narrow findings in
[probe evidence](linux-profile-probe/README.md). Keep no prototype runtime on the
product path. Remove disposable images/volumes only after records are complete;
persistent journals need explicit recovery ownership. A successful Stage B
comparison can support a new AD allocated against full Git history; the next
observed available ID is AD-0015, but this document neither reserves nor creates
it. Contrary evidence returns to DN-0057/F1. The project lead must accept the
architecture before F6/F7 product work that relies on this realization. Stage A cannot satisfy that gate.
