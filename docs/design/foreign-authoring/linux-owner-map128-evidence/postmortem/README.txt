# Bounded map representation postmortem

Read-only evidence, not a retry or cap change. The third static relink refused
at its 64 MiB map cap. Observed map size was 68,108,288 bytes after termination;
that may be incomplete and is not a full-map size/hash claim. All five owned
children were reaped. Only the before verifier and failed monitored relink ran;
there is no after-verification, admitted candidate or passive ELF result.
Actual records remain in /tmp/ash-owner-static-stage3-map64, unchanged.

prefix-analysis.json describes only the three exact retained prefixes. The first
16 MiB attempt contains the discarded-section listing after byte 519242. Both
suppressed prefixes omit that listing and have Memory Configuration at 519242,
active map at 519386 and LOAD at 519416. The 64 MiB prefix has 78 LOAD lines,
including the explicit libc.a path. None has an OUTPUT marker; absence from
an incomplete prefix is not an assertion about a completed map. No .debug_info or
cross-reference header occurs in the 64 MiB prefix. The .rodata substring occurs
in a linker-script .rela.rodata input pattern, not an observed .rodata output-section
header. Its final lines
are still .text entries from the selected libash archive with expanded generic
Rust symbol names. The raw prefixes are referenced, not copied or changed.

Disjoint line heuristics account for all 67,108,864 retained bytes:

| Observed line category | Bytes |
| --- | ---: |
| Address plus rendered symbol | 30,582,433 |
| Mangled .text section name | 18,052,838 |
| Address/extent/input-object path | 15,071,454 |
| Fill record | 2,858,399 |
| Other | 533,787 |
| LOAD | 9,927 |
| Blank | 26 |

There are 62,692 adjacent section/next-addressed-symbol pairs. Their raw mangled
names total 17,352,868 bytes, versus 27,375,303 rendered bytes: a 10,022,435-byte
expansion within this incomplete prefix. One observed name grows from 654 to 2524
bytes. This is a pairing heuristic and representation comparison, not a simulated
new map or prediction that the complete map will fit 64 MiB.

The exact installed BFD manual (compressed SHA 2f7c363d, decompressed SHA d68694b3;
full pins in prefix-analysis.json) describes --no-demangle as controlling symbol
names in errors and other output, overriding default demangling. The preferred
prospective option is one additional root linker argument:
`-C link-arg=-Wl,--no-demangle`. Preserve existing discarded-section suppression,
every symbol/address/archive record in mangled form, all semantic/static flags,
source/native inputs, map 64/log 16 bounds and full-map/framing/LOAD/libc gates.
No environment change or semantic flag is proposed. Candidate bytes must still
be freshly observed; no byte-identity claim follows from diagnostic intent.

--no-print-map-locals is already the documented default, and all three prefixes
have zero (local) markers; it is not an evidenced further reduction. The manual's
--reduce-memory-overheads changes memory/speed and map-generation algorithm
tradeoffs, not specifically the large name renderings, so it is not recommended
for this output-size failure. Stripping more symbols, changing section retention
or raising the cap is outside this proposal. If a separately reviewed/assigned
representation-only attempt fails again, stop and retain its actual result.
The alternative remains a blocked packaging gate, not a fabricated full map.

No compiler/linker/readelf/header query or native candidate was run for this
analysis. Header preparation remains separate and unexecuted. The future exact
tuple/collector review and root sole-Cargo assignment remain required.
