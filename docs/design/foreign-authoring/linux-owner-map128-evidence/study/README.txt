# Complete producer metadata and partial map budget study

Read-only diagnosis. No retry, cap amendment, tuple, compiler/linker/readelf/header
query or native startup is authorized by this record. The fourth relink remains
a map-limit refusal. Its observed 70,373,376-byte file may be incomplete; the
third's 68,108,288-byte observation is likewise not a complete-map size. Different
sampling/termination progress prevents ranking those sizes as total output or
claiming the representation option enlarged the complete map.

## What the partial outputs establish

analysis.json pins and compares the third/fourth exact 64 MiB prefixes. Both are
still in the linker-script planned .text output section and have no OUTPUT,
.debug_info or cross-reference marker. The .rodata substring is an input-pattern
mention, not a .rodata output-section header. The third's last complete observed
input extent starts 0x1de84d0; the fourth reaches 0x1f59450. Those positions are
75.86% and 80.08% through the planned .text address extent, respectively, not
percent completion of map serialization, final linking or executable size.

| Disjoint retained-line category | Third bytes | Fourth bytes |
| --- | ---: | ---: |
| Address plus symbol name | 30,582,479 | 24,514,761 |
| Mangled .text section name | 18,052,838 | 21,625,914 |
| Address/extent/input-object path | 15,071,408 | 17,150,804 |
| Fill | 2,858,399 | 3,272,516 |
| Other, LOAD and blank | 543,740 | 544,869 |

These classifier patterns require an input field on extent lines. Thus 46 bytes
classified differently from the earlier broader third-prefix classifier are a
reporting distinction, not changed raw bytes. Each column still totals exactly
67,108,864 bytes. The script/record retain the precise classification rules.

The fourth prefix has 71,503 adjacent raw section/next-symbol pairs. Their name
bytes are 20,855,593 in each representation, unlike the third's 17,352,868 raw
versus 27,375,303 rendered bytes. This observes the intended no-demangle effect,
while still showing repeated raw names plus long archive/object-path/extent and
fill records consuming the cap. 71,585 raw addressed Rust names match actual
defined .text-function names in the complete ordinary producer ELF. That match
is useful correspondence, not a claim all ordinary symbols must survive the
static link or serialize in the same order. No full map or final image is inferred.

## Complete measured producer input

The fixed Stage2 ordinary host is 475,650,552 bytes, SHA-256
d5799c76fbf3be8b06a473906b4e73ce82b1fdf90db4a1b1923d958816fe0a61.
It was streamed and compared with that exact producer pin before and after
metadata reads; device/inode/size/mtime/ctime remained equal. Bounded Python
reads parse the 43 ELF64LE/x86-64 sections, .symtab and its linked .strtab.
No mutable shared-target file contents or native archives were read. This is
not protection against a hostile writer restoring bytes between observations.

The complete producer has 131,160 symbol rows and 27,704,553 total referenced-name
bytes (including repeat references). 95,748 defined .text-function rows carry
27,007,277 of those bytes. The linked string table is 27,835,713 bytes. Section
sizes/flags/addresses and symbol type/binding counts are retained in analysis.json.
The ELF is ordinary ET_DYN with unstripped DWARF, not an eligible final static
candidate. Its .text is 35,033,143 bytes; debug strings alone are 250,830,436 bytes.
Final-root static/strip flags, CRT selection and BFD ordering differ. We do not
use ordinary byte size, address order or symbol counts as a guaranteed bound on
the future static image/map. The final-image 128 MiB limit remains separate.

## Explicit estimate and finite recommendation

A transparent scaling model uses the fourth observed name/metadata mix:

- (67,108,864  - 2*20,855,593)/71,503 = 355.197 observed nonpaired-name bytes per pair.
- Using all 131,160 ordinary symbol rows for that overhead, plus twice their
  27,704,553 referenced-name bytes, gives 101,996,794 bytes (97.27 MiB).

This deliberately assigns function-like overhead even to nonfunction rows, but
it is still an estimate, not an upper bound. Input-section records need not map
one-to-one to output symbols; static CRT, aliases, linker-script/nontext records,
object grouping, ordering and unseen tail detail may differ. It explains why
64 MiB is too small for this observed runtime's full-record map without pretending
to know a complete output. The measured fourth prefix already consumed 64 MiB
before reaching the end of .text serialization.

If root chooses another experiment, recommend a prospective map-only 128 MiB
(134,217,728-byte) bound: about 31.6% headroom above this explicit complete-input/
partial-output model, rather than an unexplained multiplier of the last sampled
file size. Keep every active symbol/address/archive record, full produced-map
hash, framing/OUTPUT/nonempty LOAD/exact libc gates, diagnostic representation,
logs/output 16 MiB, final image 128 MiB and all other bounds unchanged. Fit remains
unknown. Any new limit failure must still stop and be retained as a refusal.
The alternative is to keep full packaging blocked; dropping records, hashing a
prefix as complete, narrowing the closure artifact or changing semantic flags
would not answer the current contract question.

This recommendation requires a separately reviewed/retained prospective contract
amendment, then new exact per-class monitor/collector code/tests and tuple/root
assignment. Current monitor b36fbefc permits only map 64 MiB; do not pass 128 MiB
through a self-test override or generic log cap. All four earlier limits/results
stay historical, never retroactively passing. No implementation is delivered here.

## Storage proposal without moving inputs

Read-only statvfs observed 907,739,136 bytes available in /tmp, versus 206,895,771,648
on existing /home/dikini/Projects/ash-lang/.worktree/generic-cells/target (device 66309).
The worktree's .gitignore contains /target/; its exact size/hash are retained.
For a later reviewed tuple, use one new private 0700 experiment-output parent
under that existing ignored shared target, such as the proposed path in
analysis.json. It has not been created. This is output placement inside the
same cache filesystem, not a second Cargo cache, checkout, compiler copy or
source/native substitution. Keep the generated Stage2/source paths unchanged.
Avoid cache-clean/pruning while such evidence is live.

At map 128 MiB, known raw map plus two monitors' retained map copies, candidate,
two outputs and bounded records sum 583,532,544 bytes. Current free space is not
reserved, quota, a global intermediate bound or proof of future availability.
A future tuple must observe/check canonical output-parent identity, ownership,
actual free space and actual file-class peaks before/after, preserving bounded
read/retention and cleanup. Rust/linker temporary files can still use /tmp under
the unchanged environment; project output placement does not eliminate that
requirement. No historical input/map/prefix, cache or scratch tree is moved or
deleted for this study.

analyze.py is the bounded read-only reproducer; analysis.json is the current
record. Historical-first-* preserves the initial complete-metadata observation
before adding the all-symbol-name total. No source/native/candidate execution
occurs in either generation. Header preparation remains separately paused.
