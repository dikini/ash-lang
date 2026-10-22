# Linux launch profile and common artifact admission for minimal FFI

This refinement belongs to
[DN-0057](../DN-0057-checked-ffi-module-boundaries.md) and the
[copied-text and connection/statement cases](minimal-ffi-contract-cases.md).
It uses their [ABI profile](minimal-ffi-abi-profile.md) and
[checked representation](minimal-ffi-checked-representation.md). These choices
resolve this blocker's policy at design level, subject to review and delivery
evidence. They accept no architecture, define no current Ash semantics and
select no source syntax.

The accepted narrow owner-free scalar GNU in-process architecture is
[AD-0015](../../decisions/AD-0015-linux-scalar-inprocess-whole-images.md). It
selects exact-closure receipt/independent approval, protected deployment context
and immutable fd execution under explicit trusted runtime/native premises.
It supplies no strict per-image approval, product implementation or isolated,
SQLite or owner/resource acceptance. The remaining exploration below retains
its design status; current language truth still comes from the specification.
[AD-0016](../../decisions/AD-0016-linux-owner-inprocess-whole-images.md) later
selects the owner/resource extension of those mechanisms with finite trusted
native/allocator/closure premises. It grants no strict executable approval,
checked activation or isolated/SQLite deployment acceptance.

## Common obligations and platform mechanisms

The common FFI contract requires approved artifact provenance, binding to exact
checked contracts, immutable execution identity, explicit execution authority,
bounded control resources and honest reporting of session loss and termination.
These obligations do not require ELF, memfd, namespaces, seccomp or cgroups.
The artifact-admission rules below are common; the static-image packaging and
launch/enforcement mechanisms are the selected Linux realization. Another
platform supplies its own checked ABI and executor profile satisfying the same
common guarantees, or refuses the unsupported mode. Do not expose Linux
mechanisms in common source types, effect rows or dependency summaries.

## Trust boundary

Treat the entire isolated worker, including native startup, bridges, validators
and resource monitors, as potentially faulty. Trust the parent validator and
supervisor, launcher, artifact admission path, OS kernel and configured
storage/resource enforcement. Approved producers and native build tools remain
assumptions for correspondence between checked contracts and executable code.

Select separate processes with Linux namespace, filesystem, syscall and
resource restrictions. Never execute native code in the parent to inspect a
candidate worker. A process boundary alone protects neither ambient authority
nor resource availability.

| Property | In-process host | Isolated worker |
| --- | --- | --- |
| Authorized image | Required before launch. | Required before launch. |
| Published Ash values/access | Conditional on native code preserving host memory and runtime invariants. | Parent checks payload and local authority, assuming parent/kernel correctness. |
| Arbitrary native memory fault | Can corrupt or terminate the host. | Confined to worker address space under the selected OS boundary. |
| External authority | Host process authority. | Explicit storage grant and IPC endpoints only. |
| Database truth and native resource reports | Native assumptions remain. | Native assumptions remain; plausible false replies are possible. |
| Resource exhaustion | No independent per-library process limit. | Worker limits and parent admission bound assigned resources; no unconditional availability guarantee. |

Mode is fixed for a host activation. Missing isolation means refusal before
acquisition, never fallback to in-process execution. This policy adds no claim
about kernel compromise, side-channel elimination or external-effect rollback.
In-process execution requires a host policy explicitly accepting its larger
trust boundary.

## Common artifact-admission obligations

Require a bounded, versioned producer receipt binding:

- Image SHA-256 digest, size, execution role and target ABI.
- Checked-contract revision/digest and operation inventory, including original
  module identities and wrapper-summary closure.
- Bridge-plan digest and generator version; native archives, headers, flags,
  toolchain/linker identity and native configuration.
- ABI/prototype/constant checks, profile-specific dependency inventory and the
  association from each admitted operation to its executable entry.
- Compatible runtime/protocol and launch-policy versions, assumption identities
  and evidence references with their actual scope.

Receipt encoding is deterministic build data to specify during implementation;
unsupported versions fail admission. References resolve to checked originals,
not merely matching hashes supplied by an untrusted package.

Accept only an operator-authorized producer or explicit operator approval of
that exact receipt and image digest. Distributed receipts require signatures
verified against configured trust roots. Local builds can use a protected
local approval record. A package manifest, worker self-report or freshly
computed hash of arbitrary bytes creates no approval. Local-only deployment
needs no signing infrastructure but trusts its approval record's protection.

Authentication establishes authorized bytes and asserted build correspondence
under producer/toolchain trust. It proves neither native memory safety nor ABI
adherence of a falsely declared binary. Symbol names, ELF build IDs and SQLite
version strings are insufficient alone. Reproducible builds can strengthen
evidence later without replacing producer/operator authorization.

Each profile must establish which immutable executable bytes and dependencies
its executor actually uses, before foreign execution, and preserve the checked
operation association. A verified filename alone cannot establish that fact.
How an OS pins or loads those bytes is a platform mechanism, not common FFI
semantics. Shared-library profiles would need their own complete dependency
and loader-admission policy.

## Linux packaging and pinning

For this first Linux profile, statically link evaluator/bridges/SQLite into one
in-process execution-host ELF image and worker/bridges/SQLite into one worker
ELF image. Build the trusted launcher separately without the selected foreign
library. Reject scripts, ELF dynamic interpreters, shared-library dependencies,
runtime plugins and ambient library search. The Linux receipt additionally
retains the static link map and absence of runtime dependencies. These packaging
restrictions do not rule out other platforms or later shared-library profiles.

Read candidates within size limits without executing them. Check receipt and
admitted contract closure, then copy the image into private immutable storage.
Hash the final immutable image and compare with the approved digest. Execute
that same pinned object; never verify a path then reopen it. Select an
executable memfd sealed against writes, growth, shrinkage and seal changes
before final verification. Refuse if local execution policy cannot support
this. See [memfd](https://man7.org/linux/man-pages/man2/memfd_create.2.html).

Producer builds pin native inputs by content and link approved archives rather
than ambient search results. Fixed generated entries in the approved image
provide dispatch; same-spelled symbols cannot substitute another binding.
No constructor, initialization, native ABI probe or acquisition runs during
parent inspection. Do not execute candidate metadata queries as preflight.

Admit an in-process host as a whole image before it starts. Loading a library
into a running interpreter and checking it after constructors ran does not
satisfy this policy. Startup there has host authority. Adding a binding requires
building and admitting another execution image in this first profile.

## Storage and authority grants

Each isolated connection group gets one worker and either an in-memory
database or a dedicated persistent database volume. Mount the volume at
`/data`, with the selected database at `/data/db.sqlite`. The launcher manages
an exclusive storage boundary containing no unrelated files or outside
hard-link aliases. Reject arbitrary caller directories that cannot establish
those properties. Preparing an existing database for this volume is an
explicit storage operation, not implicit access to its original directory.

The worker may read/write/remove any files in its volume and can damage its
database. Include journal, WAL and related files: SQLite needs more than the
main file for supported operations. See its
[temporary-file inventory](https://www.sqlite.org/tempfiles.html). Quota the
volume. Supply a separate size-limited private `/tmp`, removed after reaping;
preserve the persistent volume and journals.

Create a private root exposing only the pinned read-only executable, granted
`/data`, private `/tmp` and necessary empty mount points. Data/temp mounts are
non-executable, with device/set-ID semantics disabled. Expose no host `/proc`,
`/sys`, home or device trees. Detach the old root and close every descriptor
that could reach it. The pinned image is the only executable file exposed.
Deny mount/namespace changes and filesystem-handle escape APIs after setup.

The wrapper accepts only its configured persistent database or explicit
`:memory:`. Reject caller-selected VFS, URI and other special filenames before
dispatch. Admit SQLite configurations with URI interpretation disabled and
loadable extensions omitted. This refines the ABI profile's configuration
assumptions without changing its signatures. SQL filtering/library settings
are not containment: faulty code still has the entire storage grant.

## Trusted launch sequence

Deployment supplies the launcher's namespace, mount and resource-controller
authority. Availability on every unprivileged installation is not promised.
Probe required controls and refuse launch if any is unavailable.

1. Check image, contracts, policy, grants and admission budget. Allocate a
   fresh parent-owned session/resource domain, private request/reply pipes
   and bounded diagnostic handling.
2. Run only trusted setup code in private user, mount, PID, network, IPC and
   UTS namespaces with a fixed UID/GID mapping and no host-root mapping.
   Supply only the mapped access needed for the granted volume. Complete privileged
   setup before dropping that authority. Assign the resource domain before
   foreign code runs.
3. Install root/grants, fixed working directory, restrictive creation mask
   and a small explicit environment. Remove loader/search overrides,
   credentials and inherited user configuration. Disable core dumps. Retain
   only designated pipe ends and diagnostic endpoint, closing parent/setup/
   management descriptors.
4. Drop capabilities, supplementary groups and setup privileges. Set
   `no_new_privs`; install an architecture-checked default-deny seccomp filter
   and verify limits. No foreign constructor or call runs before restriction.
5. Execute the pinned image from the private root. Never depend on worker
   self-restriction. Startup and SQLite initialization are already contained.
6. Check bounded protocol/contract compatibility and association with the
   expected process before acquisition. Readiness is compatibility data;
   trusted supervisor setup records establish enforcement, not worker claims.

Filters apply before exec and survive it. Permit image execution only within
the fixed executable root. Re-executing that same image need not be prevented
for containment: it creates no new session or parent authority. Losing native
state or emitting false replies is already inside the threat model. No other
executable file or child process is admitted.

## Syscalls and resource enforcement

Use a versioned allowlist for the fixed static runtime and SQLite VFS, not a
list learned from one successful trace. Permit required private-file I/O,
locking, bounded pipe I/O, ordinary memory management, clocks, entropy,
single-thread runtime signal handling and exit. The immutable root controls
executable file access. This does not promise to prevent code injection inside
a worker already running arbitrary native code.

Deny process/thread creation, namespace/mount changes, new socket endpoints,
process inspection/memory access, cross-process signals, key/BPF/performance
interfaces, new executable memfds, filesystem-handle opening and privilege
controls. Deny `io_uring` and alternate submission paths bypassing the policy.
Reject x32 and non-native syscall architectures. Allowing signal return grants
no signal-sending authority. Inherit no `/proc` or parent-inspection access.
The [seccomp documentation](https://man7.org/linux/man-pages/man2/seccomp.2.html)
describes inheritance and architecture checks. The concrete allowlist is a
reviewed delivery artifact; changes require evidence and policy review.

Use a parent-managed cgroup v2 domain per worker with memory maximum, zero swap
allowance, CPU rate limit and task limit one. Inherit no controller files or
migration authority. Add finite descriptor, address-space, file-size and
CPU-time limits, volume quotas, bounded tmpfs and startup/request/shutdown
deadlines. Parent admission caps worker count, aggregate assigned budgets,
frame buffers and diagnostic volume. Parsing and timers cannot wait on worker
progress. See [cgroup v2](https://docs.kernel.org/admin-guide/cgroup-v2.html).

Limits are explicit launch-policy values fitting host budgets; no numeric
default suits every database. CPU rate does not replace deadlines, file-size
limits do not replace quotas, and message bounds do not limit arbitrary native
allocation. Verify each control. Kernel failure and host-wide pressure prevent
unconditional availability or timely-reaping guarantees.

## Loss, shutdown and the worked cases

On malformed reply, timeout, death or mismatch, stop dispatch and invalidate
all session proxies. Terminate the complete worker resource domain and reap
before releasing mount/storage/limit reservations. Never reuse the session ID
or automatically replay. If termination is delayed, retain supervisor records
and reservations and report pending failure. Forced shutdown is not native
completion acknowledgement.

For copied text, admit image/contract before opening the connection. The parent
validates null or bounded UTF-8 bytes without native pointers. Crashes and
oversized streams publish no partial value; earlier copies survive. A
well-formed string may still be unrelated to the database despite approval.

For statements, parent proxies retain session, contract and exact C/S lineage.
Acknowledged finalize consumes its proxy even with native error. Lost replies
preserve every admitted status/disposition; only an unacknowledged transition
remains unknown. Session access is invalidated either way. Follow the
[canonical precedence table](minimal-ffi-transitions.md#common-outcome-precedence).
Reaping means process termination, not SQLite cleanup or
rollback. Keep persistent files/journals for explicit recovery, never delete
them as launcher cleanup.

The in-process image uses the same contracts and ABI without per-connection
address-space/filesystem containment. Record actual host authority and native
assumptions; sharing an approved native archive does not give it isolation.

## Closure evidence

Reject unapproved producers, changed bytes/contracts/receipts, dynamic
dependencies, wrong ABI, missing controls, unsafe grants and insufficient
budgets before launch. Race original-path replacement and verify execution
uses pinned bytes. Self-reported worker metadata cannot override admission.

Test startup and request-time attempts to access outside files/inherited
descriptors, create sockets/children, inspect the parent, change namespaces,
execute another image or exceed log/frame, memory, CPU, storage and deadline
limits. Re-executing the approved image cannot restore old proxies. Exercise
journal/WAL/temp use and quota failures. Inject loss around copy, acquisition,
finalize and writes; observe valid parent values and unknown completion without
replay. Native faults run only in contained test processes.

Containment claims require evidence on the actual kernel/configuration and
versioned launcher/filter/resource policy. Missing controls mean unsupported
deployment. Implementation tasks supply the syscall allowlist, receipt encoding
and enforcement tests; they cannot locally weaken authority or identity rules.
Syntax and persistent module serialization remain outside this refinement.
The [common exhaustion design](minimal-ffi-exhaustion-and-ownership.md) specifies
reporting and ownership preservation without prescribing these Linux mechanisms.
