# Trusted static image-pinning evidence

This is bounded [TASK-0050 F2](https://github.com/dikini/ash-lang/blob/a54e9215860cd9693d1a2dc9ff79e8f0f4a57e23/docs/tasks/TASK-0050-checked-ffi-regions-control-program.md)
evidence for the [Linux launch experiment](../linux-profile-experiment.md), retained
under [DN-0057](../../DN-0057-checked-ffi-module-boundaries.md). It accepts no
architecture or semantics and changes no product runtime. The trusted diagnostic
reporter is not an Ash evaluator, generated bridge, SQLite host or isolated worker.

## Observed result and authority

The 2026-10-21 probe built a trusted, self-authored C reporter as a static x86-64
ELF. It only prints an identity and its UID/GID/groups. Root inspected its source
and independently verified the exact receipt and A/B image hashes, then approved
those artifacts under the user's autonomous recommended-choice delegation before
execution. Normal tool approval separately authorized the same trusted probe
outside the filesystem sandbox. No credentials or host policy were changed.

The [original approval](recorded/operator-approval.json) is retained byte for
byte. Its limitation `sandbox local evidence only` is incomplete for the later
host run; the separately confirmed [authorization addendum](approval-addendum.json)
records that scope without rewriting or backdating the original. Both historical
observations still reference the original approval hash. These files are evidence
of trusted-session approval, not a protected production trust-root store or new
permission to execute a rebuilt artifact.

The [host observation](recorded/host-observation.json) records:

- A is ET_EXEC/x86-64, with no PT_INTERP or PT_DYNAMIC; its full-image digest
  matches the separately approved receipt after copying and sealing.
- The memfd uses flags 19 (CLOEXEC, ALLOW_SEALING, EXEC), mode 0500 and
  WRITE/GROW/SHRINK/SEAL mask 15. Five attempted mutations fail EPERM: pwrite,
  growth, shrinkage, adding a seal and shared writable mmap.
- The candidate pathname is atomically replaced by trusted image B after A is
  sealed. Execution through the same fd prints A, exits 0 and is reaped. This is
  one actual replacement interleaving, not concurrent race-stress evidence.
- Replacement before pinning, changed image, missing approval, unsupported receipt
  version and changed receipt refuse before reporter startup. Dynamic ELF, script
  and wrong-machine fixtures are rejected by the parser without execution.
- UID/GID remain 1000/1000 and supplementary groups remain
  4,24,27,30,46,114,122,986,987,1000, matching the parent. Host authority is retained.

The [sandbox observation](recorded/sandbox-observation.json) uses the same image,
flags, mode and seals, but fd exec returns EACCES; the child reports 125 and is
reaped, and the harness exits 78. The host harness exits 0. `vm.memfd_noexec=0`
is observed in both contexts; sandbox NoNewPrivs/Seccomp are 1/2 and host values
are 0/0. This distinguishes the tested execution contexts without identifying
the precise security-policy mechanism responsible for EACCES.

No startup fault, credential clearing, private root, syscall filter, cgroup,
quota, per-library limit or fault containment was tested. Absence of an ELF
interpreter/dynamic section proves this reporter's packaging; it does not prove
arbitrary static runtimes cannot load plugins. No native truth or source
completion guarantee follows from image pinning.

## Retained inputs and reconstruction limits

[The producer receipt](recorded/producer-receipt.json) retains exact source,
header, object/archive, build-script, compiler/cc1/assembler/collect2/linker,
image and link-map hashes and sizes. Its contract says there are no Ash/native
library operations; it grants no approval. [The whitespace-normalized ELF report](elf-report.txt)
and [compact LOAD records](link-map-inputs.txt) supplement that receipt.

[The payload manifest](manifest.json) hashes retained files and identifies the
original experiment manifest. Source and execution JSON bytes are unchanged;
README, this manifest and the approval addendum are later packaging records.
The raw ELF report, binaries, objects, system headers and full link maps remain disposable external
artifacts under `/tmp/ash-checked-ffi-inprocess` and are not committed. Their
receipt hashes identify them but cannot reconstruct unavailable bytes by
themselves. Exact reproduction needs the recorded toolchain/native inputs or a
new receipt describing any changes.

The recorded harness is disposable trusted-fixture tooling. Admission reads cap
image size at 1 MiB and receipt/approval inputs at 64 KiB; the ELF program-header
limit is 64. Main also copies the fixed trusted A/B fixtures and rereads approval
for hashing with unbounded `read_bytes`, so these are not uniform whole-harness
input bounds. Its managed child loop caps output at 4096 bytes and uses a 3-second
deadline, with kill/reap cleanup after the loop's cleanup region is installed.
Selector setup precedes that region. The successful/rejected exec children were
observed reaped; no general fault-cleanup or whole-lifetime bound is established.
This is not a hardened product loader.

## Reproduction

Do not run the recorded build script in place: it records the original absolute
experiment directory. Prepare a fresh disposable directory from these source
records, preserving the historical evidence:

```sh
probe_dir=$(mktemp -d /tmp/ash-inprocess-reproduction.XXXXXX)
cp recorded/reporter.c recorded/make_receipt.py recorded/pin_probe.py "$probe_dir/"
sed "s|^cd /tmp/ash-checked-ffi-inprocess$|cd \"$probe_dir\"|" \
    recorded/build.sh > "$probe_dir/build.sh"
(cd "$probe_dir" && sh build.sh && \
    /usr/bin/cc -O2 -fno-pie -no-pie -o reporter-dynamic-negative reporter.c && \
    /usr/bin/python3 make_receipt.py)
```

This prepares images and a new receipt; it does not execute a reporter. Compare
all inputs and final digests. Different paths, inputs or build-script bytes
produce a new receipt. Obtain explicit operator approval for that exact new
receipt and its images; create a corresponding `operator-approval.json` in the
new directory. Do not copy the historical approval as new authorization.
Only after that approval, run `/usr/bin/python3 "$probe_dir/pin_probe.py"` and
retain its output and exit status. A host run outside the filesystem sandbox
requires its normal tool approval. No new execution accompanied this packaging.

## Remaining scope

The [requirement split](requirements.md) separates narrow in-process architecture
readiness, worker-only prerequisites and downstream F6 implementation evidence.
The [generated Ash packaging comparison](generated-ash/README.md) now retains a
real evaluator/bridge static-link result and exact provenance. Its retained libc
loader paths leave the proposed no-loading requirement unmet. The separately approved
[trusted scalar diagnostic](generated-ash/diagnostic-addendum.md) observes
`Returned(7)` from the sealed generated image after pathname replacement, with
sandbox EACCES retained. Its known-loading/host-trust premises do not accept the
static runtime closure. No static
SQLite archive was found in the recorded standard/conda search paths, but SQLite
absence and the worker group-clearing blocker do not automatically block a
separately scoped scalar-only in-process architecture. No AD, F2 checkbox or F6
execution permission is accepted here.
