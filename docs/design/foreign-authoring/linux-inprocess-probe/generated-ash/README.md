# Generated Ash static packaging evidence

This bounded [F2 experiment](../../linux-profile-experiment.md) belongs to
[TASK-0050](https://github.com/dikini/ash-lang/blob/a54e9215860cd9693d1a2dc9ff79e8f0f4a57e23/docs/tasks/TASK-0050-checked-ffi-regions-control-program.md)
and [DN-0057](../../../DN-0057-checked-ffi-module-boundaries.md).
It changes no product code or source semantics and accepts no architecture.

## Result

The real generated Ash evaluator, signed32 `abs` bridge and private program/fact
payloads link as a 70,880,176-byte x86-64 ET_EXEC with no PT_INTERP or dynamic
section. The [ELF inspection](image-elf.txt) supports that packaging result.
The image SHA256 is `45417a6db6fc41bd17b372b47423e06c57ecf55973a0a848c51a14f456537405`.
Neither the ordinary image nor this static image was executed during packaging.

**The proposed no-loading requirement remains unmet.** Retained code includes
`dlopen`, `_dl_open`, `__libc_dlopen_mode` and `_dl_sym`. The
[direct-reference scan](loader-direct-references.json) includes character
conversion through `__gconv_find_shlib`; a bounded reverse scan reaches libc
localization/strerror paths. These scans do not prove runtime reachability or
its absence, including indirect/data references. Linker warnings name
`getaddrinfo`/`getpwuid_r`; their final entry symbols are absent and their warning
sections appear discarded, but the loader code remains. ELF headers alone do
not establish the intended static runtime closure.

The prior reporter's 1 MiB bound and approval do not admit this artifact.
Any separately authorized trusted diagnostic must have its own exact policy,
approval and observation addendum, explicitly retain host authority and possible
runtime-loading premises, and leave this packaging record unchanged. Such a
diagnostic cannot satisfy the proposed no-loading requirement or accept F2/AD/F6.
No execution or approval is claimed by the original packaging records. A later
[diagnostic addendum](diagnostic-addendum.md) records separate exact approval and
observations without changing the frozen packaging receipt.

## Frozen inputs and commands

The source commit is `83d050b40c92572b98b2d337f04126311373cd22` (retained PR #86),
tree `b22c8e6378b054e0c866faf5b2a171e89e06f16e`. Its unchanged 520-file
source/configuration aggregate is
`0a042cd9ffceb29b394b8f92c8ab6c91c3abf35e21c8c7d15d1756596538b8c5`,
with the same [retained manifest](../../../../tasks/evidence/checked-ffi-wrappers/source-configuration.json).
The [initial receipt](initial-preparation-receipt.json) records the actual
compiler build, exact command/environment, exit and raw digest. The compiler
SHA256 is `a6068524ee48775391f72c3e49234c46becff06da68541bf4126e9537ed56dab`.

The [initial fixture](initial.ash) refused parsing at `(0 - 7)` before generation;
the [raw refusal](parse-refusal.log) is retained. After explicit delegated root
authorization, the [corrected fixture](corrected.ash) uses the existing passive
signed foreign constant `Negative : CInt = -7`, then passes its ordinary Int
binder. The original input/plan were preserved. The [plan delta](plan-delta.json)
and [preparation receipt](preparation-receipt.json) pin the exact change and
reused matching compiler. The successful CLI build links but does not evaluate
the program.

The [generated Rust](generated-main.rs) retains the matching-runtime const
assertion, exact original bridge coordinates and typed `extern C` declaration
`abs(i32) -> i32`. [Generated-input hashes](generated-inputs.json) bind it and
both private binary payloads, Cargo manifest/lock and toolchain file. The
[static-build receipt](static-build-receipt.json) records the exact root-only
`cargo rustc` flags, unchanged generated inputs, ELF/map/image hashes and exit.
No global static RUSTFLAGS, fingerprint bypass or dynamic fallback was used.
The [complete verbose output](whole-static-build.log) retains linker warnings.

One Cargo job reused the existing shared target. This did compile target-specific
dependencies; no second cache was created. The compiler build, preparation and
static relink passed. That does not establish arbitrary native behavior.

## Retention and limits

The original [producer receipt](producer-receipt.json) is retained byte for byte;
it is experimental correspondence evidence, not an approval-store entry.
The [linked-input census](linked-input-census.json) hashes 67 available inputs
from 76 actual map LOAD records and observed tool files. Nine vanished temporary
objects are explicitly unavailable. This is not a complete intermediate-input
or runtime-loaded dependency census. The full map, symbols, binary images and
manifest copies stay local with [exact hashes](omitted-artifacts.json); no binary,
object or full map is committed.

Strict static-closure acceptance is refused/unresolved. Checked execution,
SQLite, isolation, whole F2, F4/F6 deployment and full-workspace/F-core evidence
remain pending. Any follow-up experiment is a separate bounded record.
