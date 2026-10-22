# Exact Stage 2 generation tuple — review only

No generation, relink or owner/native image startup has run. Stage 1 succeeded
under its exact assignment and independent audit. Its selected-source compiler
is 589,364,584 bytes, SHA-256
5dca1b624bf206c44c6c4d3037675193800516eb936a0cf6420e67394e998d3e,
with actual runtime fingerprint
6ed612090a3fadfbcc982c0cf41b210cb02e2d01af7db5a5958e63a6fc527a47.
The original Stage 1 receipts remain unchanged. Its compiler/source/Cargo package/
manifest/fingerprint correspondence and full selected input pins are bound here.
Historical pre-Stage-1 proposals are preserved separately and are not current
command authority. Root must independently assign this reviewed exact tuple
before any generation command runs; the shared cache is reserved meanwhile.

## Public path and effects

The exact argv in generation.monitor.json invokes the observed compiler's
public `build` action, target x86_64-unknown-linux-gnu, one existing shared cache,
the exact libc.a native static input, fixed ordinary-host output and entry.
The fixed existing-profile owner fixture changes only native link names
ash_owner_acquire→malloc and ash_owner_release→free. The entry requests one
8-byte allocation and reads independently stored data, not native memory.
It does not bypass checked runtime refusal or establish checked O/K/copy rules.

At selected commit 1a8ecef0, src/main.rs:195 execute_build calls build_path and
only prints the successful output path. src/build/host.rs:438–507 retains a new
.ash-build/ash-host-* project beneath the output parent: src/main.rs, private
src/program-image.bin and src/expected-facts.bin, Cargo.toml, rust-toolchain.toml,
Cargo.lock and native-build.log. The observed name must be collected, never
guessed. host.rs:510–555 uses offline one-job Cargo rustc, then
artifacts.rs:74–107 retires only the unique generated root package before output
publication. Shared dependencies and generated project/source/payload/log remain.
No resulting owner executable is invoked. Trusted Cargo/build-script/tool
processes do execute as compilation machinery; this is not foreign startup.

The generated Cargo dependency ash.path must point to the exact selected
snapshot. Profile, features and toolchain must correspond to the observed
compiler; generated main's embedded runtime fingerprint is checked against the
actual Stage 1 value. The initial generated root Cargo invocation is offline but
not locked because it must add its new package. selected-Cargo.lock.seed is the
pinned selected source lock embedded by the compiler and written by host.rs;
it is NOT an independently captured pre-Cargo generated lock. The generated
lock is observed only after resolution, with unchanged selected external package
versions/checksums checked against the seed. Retain these distinct observations.

## Exact monitor, verifier and collector boundaries

Every outer Python argv is canonical Python3.14 with -I -S -B and the exact
three-variable environment passed through a trusted subprocess launcher. The
compiler child receives its own complete exact environment, including empty
Rust wrappers and no global static flags. Preflight includes full 2784-file
source/archive correspondence, separate 177-file runtime-content census,
interpreter/monitor/compiler, Stage 1 proof records, native/tool/config/default
linker pins, exact owner/entry and lock seed. External reviewed tuple/manifest
hashes are the operator trust anchor, not self-authenticating JSON.

The before verifier refuses old ordinary-host/.ash-build outputs. The after
verifier repeats source/tool/compiler pins. The monitor owns the generated Cargo
and cleanup descendants, uses a 1200-second deadline, 16 MiB retained output and
sampled per-native-build.log limit, and requires real reaping. Sampled storage
checks can overshoot and do not quota shared-cache/intermediate writes.

Only after successful monitor and after-verifier results may the passive
collector inspect one new generated project. It checks selected runtime source,
embedded fingerprint, compile-time payload references, lock correspondence and
root executable retirement, then streams full hashes without executing outputs.
New generated text records remain within 1 MiB, logs within 16 MiB; manifest is
4096 entries/4 MiB and producer receipt 256 KiB. The ordinary host and private
binary payloads are observed intermediate sizes/hashes; the 128 MiB final static
candidate limit is not misapplied to them. No unbounded binary retention or
repository publication follows; the collector retains compact metadata only.
Bridge symbol names are only a structural cross-check; native operation/ABI
mapping and raw private payload/bridge correspondence require independent review.

## Success, refusal and next gate

The sequence stops on any mismatch or nonzero command, retaining exact failure
without changing limits, declarations, fingerprints or tooling. No fallback,
restart, download or second cache is authorized. The initial generated package
name, final generated inputs, ordinary host size/hash and generation receipt are
post-command observations that do not exist yet. Cleanup or compiler runtime
fingerprint failures are refusals, not partial success.

The exact public path and all currently known prerequisites are available by
source/read-only input checks. A machine-checked malloc/free header mapping is
not supplied by this experiment; ABI/source correctness remains a declared
producer/native premise. Actual source/preparation/tool/storage/link success
still needs observation. Retain readbacks before disposing only owned /tmp paths.
No shared-cache cleanup is authorized.

Stop after generation receipt. The next static relink requires a separate tuple
using the actual generated name/inputs. Passive ELF/static inspection follows
only under its own assignment. Ownerful architecture/closure evidence, exact
approval and immutable same-fd startup remain separate; AD-0015 is owner-free.

The before/after verifier also refuses .cargo/config and config.toml at the
Stage 2 root, experiment directory and experiment/.ash-build directory. These
are applicable ancestors of the generated Cargo working directory, independent
of the selected-source ancestors already checked. The fresh project comes only
from the reviewed producer; the collector rejects extra generated files,
including a project-local Cargo configuration. No ambient configuration from
the changed working-directory boundary is silently admitted.
