# Remaining architecture and implementation requirements

This informative F2 evidence split belongs to the [Linux experiment](../linux-profile-experiment.md).
It proposes no semantic change and accepts no AD or implementation. The
[reporter observations](README.md) establish trusted C image pinning only.

## Narrow scalar in-process architecture

A narrow architecture track can consider explicitly approved whole static
in-process scalar images without requiring SQLite or isolated-worker credentials.
It must state the larger trust boundary: native code retains host authority and
can corrupt or terminate the host if its memory/runtime assumptions fail. No
per-library containment or availability promise follows.

Before accepting that architecture, retain a reviewed comparison using an actual
generated Ash evaluator plus bridge and trusted scalar native code. The existing
AD-0013 generator is a candidate: `src/build/host.rs::build_prepared` retains
generated Rust/private image/expected facts and invokes one offline Cargo job.
An archive supplied by `--native-static` does not make the entire host static;
the current builder selects no whole-host `crt-static` policy. A disposable legacy
libc `abs(-7)` case could test packaging without enabling checked execution.
The sole Rust build operator must freeze its exact command, source/compiler pin,
static link map and input closure before a build. A new final receipt/image needs
new exact approval before execution. No such build is included here.

The AD must explicitly define approval authority/store protection and the trusted
producer/toolchain assumptions; whole-image dependency/plugin policy; exact pinned
execution mechanism; fixed activation mode; deployment prerequisites, inspection
bounds and fail-closed refusal. The reporter's trusted-session approval record is
not a production approval service. The host/sandbox execution contrast is a
recorded deployment limitation, not a reason to disable a security control.

A narrow AD may choose mechanisms and prerequisites before the full F6 product
implementation exists. Reporter success alone is insufficient Ash packaging
feasibility. Reviewer and lead own the architecture acceptance decision.

## Isolated-worker requirements remain open

Worker containment additionally requires trusted pre-startup nonzero UID/GID
mapping, empty supplementary groups, capability/securebits/bounding invariants
through exec/reexec; private namespaces/root and designated descriptors; explicit
exclusive storage and bounded temporary space; an architecture-checked
default-deny syscall policy; actual cgroup/RLIMIT/quota enforcement and aggregate
admission; startup/request fault confinement; and whole-domain termination/reaping
with reservations retained while pending.

The prior [deployment probe](../linux-profile-probe/README.md#deployment-prerequisite-evidence)
cannot establish empty groups in its attempted setup. A deployment-supplied
trusted credential launcher remains an external prerequisite. No relaxed group
policy or in-process fallback is implied by this evidence.

Static SQLite provenance/configuration and actual journal/WAL/locking/temp cases
are required before adding SQLite to either mode. Quota and storage containment
remain worker-profile obligations. Their absence does not forbid a separately
accepted libc scalar-only in-process architecture.

## Downstream F6 product evidence

An architecture decision does not implement checked runtime admission. F6 must
connect real public build/launch paths to bounded versioned receipts, independently
protected approval, actual image/static dependency inspection, immutable copying,
final hashing and execution of that same object before acquisition. Receipts must
bind exact original operation/contract/wrapper/assumption closure, bridge plans,
runtime/protocol/mode/policy and actual native inputs.

Startup and bridge tables must independently reconstruct operation associations;
matching names, replayed IDs, arbitrary flags or stale receipts grant no authority.
Positive connected scalar delivery and hostile source/contract/receipt/image/
dependency/mode/budget cases must exercise those boundaries. F4/F6 must also
connect reservation, guard/quarantine, native-fact/local-completion ordering and
reporting semantics. Native result truth and source completion remain distinct.

Existing checked host image/runtime refusal remains correct until the governing
implementation gates pass. Neither this evidence nor a future AD acts as a
private execution flag or closes whole F2 acceptance.
