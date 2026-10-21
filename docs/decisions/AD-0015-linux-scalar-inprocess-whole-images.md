# AD-0015: Linux scalar in-process whole images

- ID: `AD-0015`
- Status: accepted
- Related: [AD-0013](AD-0013-generated-native-bridges-and-program-builds.md),
  [CP-0024](../proposals/CP-0024-checked-foreign-host-profile.md),
  [DN-0057](../design/DN-0057-checked-ffi-module-boundaries.md),
  [TASK-0050](../tasks/TASK-0050-checked-ffi-regions-control-program.md),
  [launch refinement](../design/foreign-authoring/minimal-ffi-launch-and-artifacts.md)

## Decision

Select one initial architecture for owner-free scalar checked FFI: target
`x86_64-unknown-linux-gnu`, explicit `in-process` mode, and one whole static
ELF64 little-endian x86-64 ET_EXEC containing evaluator, bridges and native
inputs. Adding a binding requires another built and independently approved
whole image. No SQLite, native owners, callbacks, plugins, runtime shared-library
loading or isolated worker is accepted by this decision. CP-0024 supplies the
accepted semantic transition; this decision changes no language semantics.
Current checked runtime/image refusal remains correct until connected product
delivery passes its gates.

Use the existing producer receipt and independent protected approval mechanism.
A versioned exact-closure premise addendum binds the fixed producer/runtime/native
baseline and launch context. It is receipt data, not a registry, proof carrier,
self-approval flag or startup permission. The
[reviewed example](../design/foreign-authoring/linux-inprocess-probe/scalar-closure/closure-premise-example.json)
retains its experimental PROPOSED status. The example is an existing-profile
packaging baseline, lacks checked contract closure, and cannot authorize a
checked host.

The root orchestrator accepted this narrow choice on 2026-10-21 under the user's
explicit delegation to proceed autonomously and choose recommended answers,
after independent review of the exact proposal and premise record. The
[acceptance readback](../design/foreign-authoring/linux-inprocess-probe/scalar-closure/acceptance-receipt.json)
pins both reviewed inputs and the scope. Per-image strict approval, configured
store/context, product startup, isolated/owner/SQLite scope and whole F2 were
explicitly excluded. Repository delivery still requires final-head review and
retention. No executable is approved by architecture acceptance.

## Context and trust boundary

[Generated Ash evidence](../design/foreign-authoring/linux-inprocess-probe/generated-ash/README.md)
retains real evaluator/abs bridge/private-payload whole-static linking. A
[separate diagnostic](../design/foreign-authoring/linux-inprocess-probe/generated-ash/diagnostic-addendum.md)
returned `Returned(7)` from its sealed fd after pathname replacement and was
reaped. Its approval explicitly accepts possible loading; it is never applicable
to this strict policy. Retained libc localization/gconv loader paths are not
observed loading, and successful execution is not proof of all-path exclusion.

The operator accepts host authority and native/runtime memory-integrity and
producer/toolchain correspondence premises. Faulty native code can corrupt or
terminate the host. This architecture promises no filesystem, address-space,
syscall or resource containment, unconditional availability, native result truth
or source-completion proof. Isolated control failures never silently select
in-process mode.

The finite trusted closure must preserve built-in C locale in global and every
thread locale. It must perform no direct or indirect runtime code loading,
plugins, NSS dispatch, arbitrary charset conversion, unknown callbacks or
unreviewed registrations. Pinned runtime/native conformity covers `_start`,
`_init`, `_fini`, preinit/init/fini arrays, IFUNC resolution, TLS setup and
destructors, libc/Rust startup, constructors, signal/thread entries, dynamic
cleanup registration, error/panic/allocation/IO/unwind paths and shutdown.
Ordinary reviewed runtime callbacks remain within this closure; this decision
adds no source/native callback facility.

Keep three forms of support distinct:

- Structural/observed facts: ET_EXEC without PT_INTERP/PT_DYNAMIC, sealed same-fd
  identity, tested mutation/refusal comparisons, and the diagnostic result/reaping.
- Conditional source evidence: initial C global/thread locale and gettext's C
  branch skip catalog lookup and downstream gconv while that invariant holds,
  including Rust's `strerror` formatting route.
- Residual premises: the exact producer/source/build correspondence and full
  startup/runtime/native/error/cleanup closure obey the contract. Digests bind
  this reviewed premise; they do not prove it or formally verify whole libc.

The [source audit](../design/foreign-authoring/linux-inprocess-probe/scalar-closure/source-audit-conclusion.txt)
and [input manifest](../design/foreign-authoring/linux-inprocess-probe/scalar-closure/source-audit-input-manifest.json)
preserve limits: nine temporary compiler inputs are missing, the exact Ubuntu
source import is patches-unapplied, selected patch review is not a distribution
rebuild, and local Rust sources do not reproduce precompiled std. The observed
three init/two fini entries do not replace the other boundaries above. A trace
can expose a load, but absence in a trace cannot prove the contract.

## Receipt, approval and deployment

Producer data must bind final image digest/size, target, mode and role; exact
checked contract/operation/wrapper/assumption closure; bridge plan/generator;
runtime/native inputs, headers, configuration and toolchain; protocol and
launch-policy versions; exact versioned premise and fixed context. A changed
binding, runtime, artifact, premise or context requires applicable new approval.
F6 defines bounded deterministic encoding and charged validation; unknown,
malformed, mismatched, missing or over-budget records and associations refuse
before native startup, initialization or acquisition.

Select a preconfigured root-owned local approval directory, protected from the
ordinary nonzero runtime/producer identity through ancestors, ACLs, privileges,
namespace/mount substitution and open descriptors. Root independently installs
bounded approvals binding receipt/image/addendum hashes, target/mode/role,
policy/premise/context versions and explicit premise applicability. Digest names
are lookup keys; authority comes from the independent protected store. A package,
producer report, same-UID 0600 file, caller-selected path or unknown signature
cannot approve itself. No privileged helper, daemon or new registry is needed.

Accept only an administrator-established host user/mount/filesystem context
associated with protected launcher configuration. The launcher must establish
that association; apparent root ownership or numeric UID alone is insufficient.
Store records must be regular files opened through that verified association
without untrusted links. Runtime/native code receives no store-management or
approval-writing authority. Supplementary groups may remain in this mode.
No store or context is provisioned here. F6 must implement and test enforcement.

A distinct trusted approver account could also protect a local store but requires
another configured identity. Signed distributed approvals require key custody
and version policy. Defer both until deployment needs them. Admission consumes
a protected approval snapshot before activation; already active hosts have no
revocation promise. Future activations consult current approval state.

## Immutable image and refusal

Inspect without candidate startup or native metadata queries, under explicit
bounds. Require the fixed ELF target and no interpreter/shared dependency
metadata. These facts alone cannot exclude arbitrary runtime loading; the
reviewed closure premise above supplies the separate trusted obligation.
Static PIE or another target needs its own reviewed policy and evidence.

Copy to an executable memfd, seal writes/growth/shrinkage/seal changes, then
hash/inspect the final immutable object and match approved receipt/image
associations. Execute that same fd, never a reopened pathname. Fixed argv,
empty environment, standard descriptors, object policy and bounded admission
belong to the approved context. Refuse absent/mismatched/unknown policy,
premise, context or version and exhausted budget before startup. Unsupported
execution environments refuse; do not bypass their policy or fall back to
another mode. The retained sandbox EACCES is one such observation.

## Verification and remaining work

The mechanisms, trust and refusal obligations are accepted; no strict per-image
approval currently exists. Creating and enforcing one is a later per-image and
deployment gate. The possible-loading diagnostic approval cannot be relabeled.
An actual checked image needs its own complete CP-0024 receipt and approval;
the existing-profile baseline supplies neither checked permission nor runtime
proof. No new build, trace or execution follows from this decision.

F6 must provision/validate store and context, enforce bounded public receipt/image
admission, reconstruct startup/bridge/operation associations, and connect F4
reservation/guard/quarantine/completion/reporting. Connected positive, hostile
and budget tests must cover missing/writable/replaced store or context, stale or
changed approval, premise/version mismatch, source/contract/image/native-input/
mode substitution and unsupported context before acquisition. These are product
gates; architecture acceptance does not claim they already pass.

Isolated credentials, namespace/root/storage/syscall/cgroup/quota/resource-limit
and fault/termination evidence remain separate. SQLite requires static provenance,
configuration and real lifecycle/VFS evidence before either mode includes it.
Owner/resource execution and whole F2/M1 remain open. Main retains its separate
integration gates; this decision does not update the current specification.
