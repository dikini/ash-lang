# Legacy owner static packaging evidence

The fifth assigned packaging attempt succeeded after the retained map-only
128 MiB amendment. All six phases exited zero: before verification, monitored
static relink, after verification, candidate collection, separately monitored
passive readelf and final receipt. The candidate was never executed. This is
experimental F2 packaging evidence, not ownerful architecture, ABI, checked
runtime, isolation, startup or whole-F2 acceptance.

The [governing contract](../linux-owner-inprocess-experiment.md) was retained at
PR103 commit `5cb93a9fd03d963377b0a79bc2e18404c54c2c47`, with contract SHA
`c4aaeab72ca1d32971d4d12939828f6d56c69c600005ca57f586329e200f95bd`.
The [earlier compiler/generation record](../linux-owner-inprocess-evidence/README.md)
and [four-refusal study](../linux-owner-map128-evidence/README.md) remain
historical evidence. No failed attempt was relabelled successful.

## Actual result

[Execution readback](stage3/execution-readback.json), [receipt](stage3/static-receipt.json)
and [static manifest](stage3/static-manifest.json) retain the actual phase,
producer, map and ELF associations.

| Artifact | Complete bytes | SHA-256 |
| --- | ---: | --- |
| GNU/BFD map | 100,345,205 | `43348533a205d18534436b7c9bb932d6b86e733c3ec3162b8b86703f2fb4997b` |
| Static candidate | 71,022,184 | `52f09983205ecb2b524a3572fba267e79e28057c933f6408f7fde0f3ac42bc65` |

The map is complete, with recognized GNU/BFD framing, nonempty LOAD records and
the exact pinned libc.a association. Its hash equals both settled monitored
copies. It uses mangled symbol names and suppresses discarded-section
diagnostics, preserving active symbol/address/archive records. The map has
78 LOAD records: 68 existing records covering 67 paths were hashed; 10 absent
linker temporaries remain explicit producer/build-trust limitations. This is
not a fully hashed native closure or proof that native code never loads code.

Independent passive ELF inspection found ELF64 little-endian x86-64 ET_EXEC,
12 program headers and four LOAD segments, with no PT_INTERP or PT_DYNAMIC.
The private candidate has mode0400. File mode/hash collection is not immutable
sealed-fd admission or approval to execute.

[Before](stage3/snapshot-before.json) and [after](stage3/snapshot-after.json)
verification matched all 2,784 selected-source files, 96,452,672 bytes, and the
frozen tool/native/generated/configuration inputs. The source commit is
`1a8ecef0b03ddc75a45254543bd8f6f0bb10969c`. The historical Stage1 CLI produced
Stage2 inputs; current mutable cached CLI bytes were not reused or assumed.
The fresh root Cargo artifact and exact semantic/static flags are retained in
the actual records. Both monitors exited zero with all owned children reaped,
no escape, pending reap, truncation or limit failure.

## Retention and reproduction

[Retention index](retention-index.json) maps every copied original to its
external source and hash and every omitted inventory entry to its qualification.
The initial plan selected 33 originals, 259,446 bytes. The actual payload also
retains small [map128 monitor source](monitor128/build_monitor.py),
[tests](monitor128/test_monitor.py), [schema](monitor128/schema2.json),
[source delta](monitor128/source-delta.patch) and
[benign verification receipt](monitor128/verification-run/verification-receipt.json).
Its reduced-cap controls do not themselves prove real map capacity.

Original record bytes retain their execution-time absolute paths and historical
status labels. They are not portable commands or a new assignment. The original
inventories list external inputs/outputs that this compact repository record
deliberately omits. The complete map, its two monitored copies, candidate image,
compiler/cache/system archives and full source snapshot are not copied into Git.
Missing external bytes limit independent reconstruction from the repository
alone. The omission index preserves actual hashes, not a substitute proof.

The exact isolated interpreter, three-key outer environment, child environment,
argv, flags, input pins and class bounds are retained in the
[assigned tuple](stage3/tuple.json), [relink config](stage3/relink.monitor.json)
and [inspection config](stage3/inspection.monitor.json). Map128/log16/image128,
PH64 and other bounds passed for this observation. Monitoring samples sizes;
it is not a hard storage quota or proof of an unobserved peak. Project-disk
space was observed, not reserved. No command may be rerun from these records
without a new exact assignment and sole shared-cache slot.

## Remaining gates

The fixed legacy malloc/free bridge and stored owner payload connect this
packaging result to the existing resource baseline. They do not grant checked
O/K behavior, reservation/group accounting, guard/quarantine, copying,
completion or recovery semantics. Header dependency discovery, separately
frozen prototype/target checking, actual native implementation/loader closure,
shutdown and ownerful architecture premises remain pending. Exact immutable
receipt/independent approval/context/store/startup enforcement and any trusted
owner-host diagnostic require separate review and assignment. Isolation,
credential prerequisites, SQLite and whole F2/M1 remain open. All four original
issue #58 whole-scope checkboxes remain unchecked.
