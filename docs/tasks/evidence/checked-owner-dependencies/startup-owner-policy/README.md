# Dependency reconstruction under the existing startup owner

This PR110 candidate uses the existing AD-0013 startup allowance, `22 * (image
bytes + expected-fact bytes)`, without changing a product limit, coefficient,
API or authority check. The original larger-image tests had required a complete
restore to fit a standalone helper default of 327680. The project lead corrected
that task/test premise: production startup shares one input-funded meter across
canonical decode, expected-fact admission and restoration, then continues to
later binding. These tests cover that reconstruction segment only.

Session 35541 ran seven exact Rust controls on artifact
`bd78f6c340f855efef3c88751439dfcc2e28bf16b56afb77c9c0c02fbe6e060a`
(607342560 bytes). All seven passed: borrowed replacement transport, the phantom
TypeApplication exact/one-short boundary, both original dependency selectors,
and the three unchanged earlier startup regressions. Independent audit
`8cfcad3a` verified the 7115 full / 623 runtime maps, tools, exact captures and
all cleanup receipts. Each child was reaped and its owned group absent.

| Current captured input | Segment work D | Existing 22B allowance | Remaining | Remaining % |
| --- | ---: | ---: | ---: | ---: |
| Row base | 315939 | 1176142 | 860203 | 73.14 |
| Full Row | 415967 | 1282820 | 866853 | 67.57 |
| Access | 541983 | 1585254 | 1043271 | 65.81 |

The smaller base still succeeds under the standalone helper default. Full Row
still returns `Validation(Resource)` and Access still returns `Resource` at
327680; these refusals are explicit assertions, not relabeled successes. The
segment positive, exact, one-short, nonzero-prefix, spent-meter and two-fresh
controls replay decode, fact admission and restoration on the same meter.
Semantic hostiles mutate the inner image after paid decode and fact admission,
then restore on that same remaining meter. The three unchanged older 327680
regressions used 316950, 309651 and 310302 units.

The minimal borrowed-map simplification replaces discarded argument cloning
with paid borrowed-map retention while preserving owned substitution results,
shadowing, row handling and the original comparison orientation. Its phantom
fixture contains 65 Type cells: the exact boundary changes from `3N + 4` to
`2N + 5 = 135`, including the retained map-slot charge. The single-Int boundary
remains seven. No shared Type equality or substitution engine is replaced.

Earlier flat-plan and registry-occurrence-index experiments did not make the
larger standalone tests fit. Current fixed-input diagnostic session 8570 measured
restore-only totals 340748 / 448873 under a local diagnostic allowance; its
inventory telemetry was empty for both required inputs. The index and all
temporary instrumentation were removed with independent byte-exact readback.
The final candidate retains no acceptance cache or registry inventory. Those
local diagnostic totals are not this segment's cost or evidence of savings.
Historical required-selector reds and their original controller qualifications
remain in the earlier evidence; no v13 numeric or artifact evidence transfers.

Session 28313 stopped during compilation at the operator's 8 GiB target bound:
zero tests, captures or artifact credit. Cleanup reaped the child and confirmed
its owned group absent. Five historical ELF files totaling 3064110920 logical
bytes were then renamed intact outside the watched build cache, preserving
hashes, device, inode, size and mtime. The retry explicitly monitors an 8 GiB
BUILD-CACHE cap plus separately pinned retained evidence. The maximum recorded sample of cache and ELF
file blocks was 8615809024 bytes; the evidence directory itself adds 4096
bytes. This is not an overall 8 GiB storage-quota claim. No file was copied or
deleted, no program meter changed, and the failed receipt remains unchanged.

Final session 83676 passes targeted Ash `clippy --keep-going --lib --tests --
-D warnings` and 40 distinct affected Rust regressions. These cover all ten
dependency cases, the canonical-owned/borrowed/decoder families, TypeApplication
and newtype boundaries, source-owner/full-formal authority, and the three earlier
startup controls. Audit `3dada60a` verifies all 32 valid receipts, exact captures,
source/tool maps and clean owned-group disposal. Rust bytes and the libtest
artifact are unchanged from 35541; the receipt map's owned-plan Markdown differs
only in prose. New evidence/spec/task wording is post-test documentation, not a
uniformly retested full-input map.

| Final captured input (83676) | Segment work D | Existing 22B allowance | Remaining | Remaining % |
| --- | ---: | ---: | ---: | ---: |
| Row base | 315949 | 1176230 | 860281 | 73.14 |
| Full Row | 415977 | 1282908 | 866931 | 67.58 |
| Access | 541993 | 1585342 | 1043349 | 65.81 |

These independently regenerated inputs have their own exact bytes and source
paths. The earlier table remains 35541 evidence, not a process-invariant cost.
Final unchanged startup controls use 316960, 309661 and 310312 units. Standalone
larger-image refusals remain at 327680. The maximum final recorded build-cache
sample is 4988350464 bytes, or 8052387840 with retained ELF file blocks.

The delivered static specification wording records opaque retained dependencies,
exact Current/declared-Enclosing finish operands and complete checked Access
Type/Row/window correspondence. It preserves the initialized-byte-child and
ordinary helper-transport exclusions. The startup-owner premise itself changes
no normative rule or product policy. Fresh full-original, full-kind, row,
source-context and authority checks remain required. Later executable/member
binding, evaluation, generated/native/protected execution and whole F3/F-core
acceptance remain open.

[index.json](index.json) and [verify.py](verify.py) retain and reconstruct compact
raw logs, receipts, captures, operators, maps, tested source snapshots, diagnostic
disposal and independent audits. No executable is imported into this evidence.
