# DN-0050: Native program gas estimates

- ID: `DN-0050`
- Status: calibration record; `100S` source, `161S` final elaboration, `345S` Core, `51P` preparation and `22B` startup accepted
- Related: [TASK-0040](../tasks/TASK-0040-ash-copying-sqlite-library.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md)

This note records the initial native gas calibration and subsequent larger
SQLite observations. The user approved preparation `24P` and initially startup
`7B`, then source checking `100S` and startup `11B` on 2026-10-15.
[AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md)
governs the accepted policy. The earlier policy-only review excludes these
revisions and the unfinished SQLite port. A subsequent independent local review
cleared only the revised policy and ordinary fallback after focused checks;
newer port work remains outside that clearance.

The human subsequently approved the full-workload 25% reserve coefficients
below: preparation `51P`, final elaboration `33S` and compiler Core `108S`.
Independent local review cleared that bounded implementation after focused
mechanism, normal-host and quality checks. The human then approved startup
`22B` from the complete persistence observation below; focused independent review cleared that startup-only revision. The human then approved final elaboration `161S` and compiler Core `345S` from the compact-generic observations below. These bounded clearances and diagnostic completions remain separate from whole-port review and retaining verification.

The current formulas are:

```text
source checking = 100 * canonical loaded source UTF8 bytes, including builtins
preparation     = 51 * (admitted source UTF8 bytes + validated main Core nodes)
final elaboration = 161 * canonical loaded source UTF8 bytes, including builtins
independent Core  = 345 * canonical loaded source UTF8 bytes, including builtins
startup         = 22 * (canonical image bytes + canonical expected-fact bytes)
```

Each total includes paid sizing and all subsequent work in its phase. Source gas
has no additional historical ten-percent margin. Resolution and other construction/constraint, allocation, depth, stack and
authority checks retain their existing policies. There is no static overall gas ceiling.

| Earlier observation | Input size | Complete measured work | Historical forecast |
| --- | ---: | ---: | ---: |
| Persistence source / run 517 | 42,851 bytes including 1,844 builtin bytes | 2,946,584 | 4,285,100 |
| Repeated source / run 539 | 37,603 bytes | 1,045,628 | 3,760,300 |
| Simultaneous source / run 541 | 37,605 bytes | 1,243,262 | 3,760,500 |
| Control host startup / run 532 | 207,022 image + facts bytes | 1,697,083 | 2,277,242 |
| Copied-column host startup / run 489 | 174,197 image + facts bytes | 1,265,014 | 1,916,167 |

These are existing observations at distinct code pins, not a same-version fit,
frozen holdout or current full-port accuracy claim. Persistence's three archived
user files alone contain 41,007 bytes; the admitted denominator also includes
builtin sources. The minimum 25%-reserve source coefficient from that row is
86; the human selected the conservative rounded coefficient 100. The earlier startup coefficient 11 was
`ceil(1.25 * max(work / bytes))` over those complete observations. The actual
meter still refuses work amplification. These revisions grant no authority.

## Complete persistence startup and accepted revision

The normal run-610 persistence host completed source checking, final elaboration,
independent compiler Core and native preparation, then exhausted its `11B`
startup meter. At the owning refusal, the cumulative meter and its nonoverlapping
remaining-credit loans held 3,823,113 of 3,823,127 units; a row substitution
requested 49 with 14 remaining. This was cumulative work exhaustion, not a
measured depth or allocation failure.

Run 614 used that exact saved host/image/facts and all checks, with one disclosed
finite diagnostic total of 8,388,608 assigned at zero. It consumed 6,072,727
units through final native binding admission and stopped before evaluation or
SQLite calls. Image bytes were 278,473 and expected facts 69,084, so `B` was
347,557. This diagnostic is not a native persistence pass.

| Startup fitting row | B | Complete work | Accepted `22B` forecast | Error |
| --- | ---: | ---: | ---: | ---: |
| Copied-column predecessor / 489 | 174,197 | 1,265,014 | 3,832,334 | +202.95% |
| Control-resume predecessor / 532 | 207,022 | 1,697,083 | 4,554,484 | +168.37% |
| Persistence / 614 | 347,557 | 6,072,727 | 7,646,254 | +25.91% |

The new maximum is 17.472607 work units per byte. Applying the same 25% reserve
rule gives `ceil(1.25 * maximum) = 22`; the human approved that total. A 50%
comparison gives `27B` and 9,384,039 units for persistence (+54.53%); it is not
adopted. These are fitting rows at explicitly different source/accounting pins,
not a same-version holdout or a universal complexity bound.

| Persistence startup stage | Charged work | Share |
| --- | ---: | ---: |
| Decode and framing | 368,035 | 6.06% |
| Canonical expected facts | 69,180 | 1.14% |
| Source plus registry restoration, combined | 182,227 | 3.00% |
| All original templates: reconstruction and independent checks | 652,769 | 10.75% |
| Main reconstruction | 931,230 | 15.33% |
| Fresh main Core validation, including capture | 3,852,656 | 63.44% |
| Post-Core restoration | 1 | <0.01% |
| Generated registration and final native binding admission | 16,629 | 0.27% |

Source and registry line markers coalesced; only their combined cost is known.
Original-view restoration and authentication also occur inside the template
block. These are logical charged visits, metadata reconstruction and validation
work, not SQL execution, database rows, disk I/O or CPU time. The persistence
client has eight lexical resource scopes (two connections and six statements),
versus two in copying and three in simultaneous statements; main graphs have
6,395, 2,107 and 2,492 nodes respectively. Exact Type/Row, owner, fresh window,
copy correspondence and capture checks remain per context. That supports the
larger structural demand but does not quantify each scope or substitution's
share, or establish removable redundant authentication.

The receipt `sqlite-persistence-complete-startup-614-20261015.json`, numeric table
`sqlite-persistence-startup-614-fit-table-20261015.json` and short report retain
exact source/configuration, binary, image/facts, observer and before/after pins.
The startup revision changes only its coefficient. Framing, canonical facts,
restoration, fresh Core/capture and binding share the existing cumulative paid
meter. Normal persistence verification follows focused checks and independent
review; all unfinished port and acceptance obligations remain separate.

## Revised policy verification

Focused checks pass for the canonical loaded-source census, duplicate import
credit, exact total without an added ten percent, paid carry, overflow and
fresh retries. Existing copy work/storage refusals remain terminal without an
ordinary report. Current normal generated hosts pass the product TEXT/empty/NULL/
invalid-UTF8/embedded-NUL query, TRANSIENT byte/text/null binding, retained control
resume, and imported buffer zeroing/length. These are focused observations, not
a full regression gate or completed SQLite acceptance.

At the preceding policy revision, full copying completed source checking at
2,176,588 of 4,183,000, then passed final elaboration and independent Core.
Persistence completed source checking at 2,950,458 of 4,320,900 but exhausted
the then-current final-elaboration allowance at 432,537. The later complete
measurements and approved coefficients below are separate. Those inputs include
the ordinary diagnostic policy and differ from the archived rows above. Bounded policy/fallback independent review passed; unfinished SQLite foundations
and later diagnostic integration remain outside that review.

## Full-workload calibration and approved coefficients

Three complete workloads now use the same accounting implementation and test
binary: `6af81238...`, configuration `452006fa...`. Runs 597/598 used source pin
`6b5fea5c...`; run 601's `068f748c...` differs only in this informative note.
All executable and meter bytes and modes match. `S` is the actual canonical
resident source UTF8 closure, including builtins, before final elaboration and
Core. `P` is admitted source bytes plus validated main Core nodes before
preparation.

| Client | S | Main nodes | P | Complete final elaboration | Complete independent Core | Complete preparation |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Copying / 597 | 43,313 | 2,107 | 45,420 | 279,909 | 597,511 | 1,148,886 |
| Simultaneous / 598 | 39,499 | 2,492 | 41,991 | 332,157 | 836,143 | 1,059,089 |
| Persistence / 601 | 44,698 | 6,395 | 51,093 | 1,165,115 | 3,852,068 | 2,071,102 |

The upper-envelope rule gave the following choices. The human approved the
25% column; the 50% column remains an unadopted comparison:

| Phase | Maximum complete work / input | 25% reserve, rounded up | 50% reserve, rounded up |
| --- | ---: | ---: | ---: |
| Preparation | 40.535925 | `51P` | `61P` |
| Final elaboration | 26.066379 | `33S` | `40S` |
| Independent Core | 86.179874 | `108S` | `130S` |

| Phase / client | 25% model forecast | Error against measured work | 50% model forecast | Error against measured work |
| --- | ---: | ---: | ---: | ---: |
| Preparation / copying | 2,316,420 | +101.62% | 2,770,620 | +141.16% |
| Preparation / simultaneous | 2,141,541 | +102.21% | 2,561,451 | +141.85% |
| Preparation / persistence | 2,605,743 | +25.81% | 3,116,673 | +50.48% |
| Final elaboration / copying | 1,429,329 | +410.64% | 1,732,520 | +518.96% |
| Final elaboration / simultaneous | 1,303,467 | +292.42% | 1,579,960 | +375.67% |
| Final elaboration / persistence | 1,475,034 | +26.60% | 1,787,920 | +53.45% |
| Independent Core / copying | 4,677,804 | +682.88% | 5,630,690 | +842.36% |
| Independent Core / simultaneous | 4,265,892 | +410.19% | 5,134,870 | +514.11% |
| Independent Core / persistence | 4,827,384 | +25.32% | 5,810,740 | +50.85% |

The approved totals at that revision were `51P`, `33S` and `108S`.
All three workloads contribute to fitting; none is an untouched holdout. The
25% and 50% reserves are engineering choices, not confidence bounds. No fitted
row underpredicts. Source-byte sizing is coarse: persistence determines every
coefficient and smaller contexts receive substantially more unused allowance.
Unused allowance is not consumed work. No static overall ceiling is proposed.

The measured final and Core totals exclude a prospective source-sizing loop.
The canonical resident source slice already exists before both phases. Each new
`S`-based ledger would pay one unit plus one per source before reading lengths,
then retain those charges inside its computed total. That adds 6/6/7 units to
these cases; it is proposed accounting, not measured prototype overhead. Paying
it does not change the rounded coefficients. There is no free census, reset or
spent-work top-up. Preparation totals already include their paid 6/6/7-unit
census and native-input prefixes of 150/300/150 units.

Each overridden diagnostic meter received one finite total of 4,194,304.
Persistence final elaboration and actual independent Core began at zero used
work; the other final/Core observations retained normal allowances. Preparation
changed only the actual meter's capacity once before image construction,
retaining every sizing and native-input charge. Complete Core values come from
the caller's cumulative meter after validation, not a remaining-credit loan.
Every original, registry, Type/Row, owner, window, capture and native-binding
check remained. Stops after whole preparation preceded generated-host
compilation, evaluation and native calls. These are diagnostic completions,
not normal passes or a proposed production cap.

The earlier run 599 completed persistence final elaboration at 1,165,168, then
stopped in the unchanged Core allowance. Its entry differs from run 601 only
by two same-width substitutions of the isolated database pathname, used for
initial open and reopen. Library, rows and builtin source hashes match; entry
bytes do not. The 53-unit final-work variation has no established cause. Keep
that observation separate from the paired run-601 row above.

Receipts `sqlite-complete-phase-gas-597-fullcopy-20261015.json`,
`sqlite-complete-phase-gas-598-simultaneous-20261015.json` and
`sqlite-complete-phase-gas-601-persistence-20261015.json` retain exact source,
binary, script and log hashes. The current numeric table is
`sqlite-full-workload-gas-proposal-v2-table-20261015.json`; its predecessor is
retained separately. An earlier observer attempt stopped on an instrumentation
guard before image construction and contributes no complete preparation row.
The preceding implementation used `100S` / `51P` / `11B`, final elaboration
`33S` and compiler Core `108S`; its bounded policy review passed. Normal copying,
simultaneous statements, buffer and blob controls passed, while persistence
reached startup and exhausted `11B`. Focused verification and independent review later cleared the `22B` revision, followed by normal file-backed persistence. Full-port acceptance and general prediction accuracy remain separate.

## Compact generic final-elaboration observations

The unchanged 96-level prerequisite chain and 256-argument nominal application
exhausted `33S` during final elaboration. Read-only inspection and exact first
refusal observations found one paid census and one direct elaborator meter;
no double debit or proven removable work justified a repair. The refusal sites
were evidence-type cloning and zonking during unification. A stop site alone
does not establish aggregate cost or dominance.

Runs 676/677 completed final elaboration with one finite diagnostic total of
4,194,304 each. Each retained its two already-paid census units and exact
unchanged source and 320 KiB stack. Both stopped before independent Core,
evaluation or native C. Their complete totals include the census; they are not
normal pipeline or native passes. Source `89d92fe4`, configuration `452006fa`
and the matching test binaries were unchanged before and after observation.

The human approved `Final TOTAL = 161S` using
`ceil(1.25 * max(complete Final / S))`. The maximum is
`228879 / 1781 = 128.5115104`; the upward integer coefficient is 161.
The 25% is an engineering reserve, not statistical confidence.

| Workload | S bytes | Complete Final | 161S | Surplus | Error |
| --- | ---: | ---: | ---: | ---: | ---: |
| Deep generic / 676 | 1,781 | 228,879 | 286,741 | 57,862 | +25.28% |
| Wide nominal / 677 | 2,759 | 260,085 | 444,199 | 184,114 | +70.79% |
| Archived copying / 597 | 43,313 | 279,909 | 6,973,393 | 6,693,484 | +2391.31% |
| Archived simultaneous / 598 | 39,499 | 332,157 | 6,359,339 | 6,027,182 | +1814.56% |
| Archived persistence / 601 | 44,698 | 1,165,115 | 7,196,378 | 6,031,263 | +517.65% |

The three archived SQLite totals are raw older-binary observations before the
paid resident-source census. Prospective additions of 6/6/7 units are separate
estimates, not measured current totals, and do not change the coefficient.
All five rows are fitting rows, with no holdout or same-version accuracy claim.
The byte proxy is deliberately loose for SQLite; unused allowance does not
consume work. The actual meter and all semantic, identity, depth, stack and
allocation checks remain. Normal complete-pipeline and retaining evidence are
separate from these diagnostics. Other phase policies are unchanged.

## Deep-generic independent Core observation

After final elaboration completed under `161S`, the unchanged depth-96 generic
witness exhausted independent Core `108S`. The normal first refusal was a work
charge during fresh kind validation: the validator had used all 192,346 units
of its remaining-credit loan, with the outer meter retaining the two paid census
units. The next charge requested one unit. This was not a depth or allocation
refusal; the stop site alone establishes no dominant redundant work.

Run 683 assigned one finite diagnostic total of 4,194,304 to the outer Core
meter, retaining used 2 before the validator derived its loan. Whole Core used
490,324 after successful validation, loan debit and validated-program
construction. The diagnostic stopped in the public owner's success branch
before evaluation. The exact 1,781-byte source, 320 KiB stack, compiler source
`e4a31c1e`, configuration `452006fa` and binary `91214bf3` matched before/after.
This is complete compiler-Core evidence, not a normal program or native pass.

The human approved `Core TOTAL = 345S`, using the same rule
`ceil(1.25 * max(complete Core / S))`. The maximum is
`490324 / 1781 = 275.3082538`; the upward coefficient is 345.

| Workload | S bytes | Complete Core | 345S | Surplus | Error |
| --- | ---: | ---: | ---: | ---: | ---: |
| Deep generic / 683 | 1,781 | 490,324 | 614,445 | 124,121 | +25.31% |
| Archived copying / 597 | 43,313 | 597,511 | 14,942,985 | 14,345,474 | +2400.87% |
| Archived simultaneous / 598 | 39,499 | 836,143 | 13,627,155 | 12,791,012 | +1529.76% |
| Archived persistence / 601 | 44,698 | 3,852,068 | 15,420,810 | 11,568,742 | +300.33% |

The current total already includes the actual two census units. The archived
SQLite totals predate the paid census; prospective additions of 6/6/7 are
separate estimates, not measured current totals, and do not change 345.
These four known fitting rows span different compiler versions and supply no
holdout or universal prediction bound. The 25% reserve is an engineering choice.
The byte proxy is loose for SQLite; unused allowance does not consume work.
All other budgets and all authority, fresh-validation, capture, depth, stack
and allocation checks remain. Normal complete-pipeline evidence and independent
review remain separate from the diagnostic.

## Initial accepted pilot and its calibration

Keep the actual cumulative work meter. Compute finite gas from resident input,
without a static overall ceiling or per-module resets:

```text
P = admitted source UTF8 bytes + validated main Core node count
B = canonical image bytes + canonical expected-fact bytes
preparation gas = 24 * P
startup gas     = 7 * B
```

`P` is available before image construction. Read resident string lengths and the
main arena length; do not reopen source paths, walk expanded Type/Row trees or
replay construction. A test-only sizing loop charges one unit for the node count
and one per source before reading its length. Its finite bootstrap is the actual
source count plus one. Carry this work inside the computed total, refuse
arithmetic overflow or a total below work already spent, and never reset or add
spent gas as a top-up.

Choose each coefficient as the ceiling of 1.25 times the largest FIT ratio.
Preparation includes the new sizing cost in the observed total:

| Coefficient | Largest FIT ratio | With chosen 25% reserve | Rounded upward |
| --- | ---: | ---: | ---: |
| Preparation `(previous whole work + sizing) / P` | 18.748480 | 23.435600 | 24 |
| Startup `whole work / B` | 5.423416 | 6.779271 | 7 |

There is no fitted intercept. The 25% reserve is an engineering choice, not a
statistical confidence bound. Neither proxy is a universal cost bound. The
actual meter refuses amplification or unexpectedly expensive validation.
Source whitespace, admitted unused source and valid unused framed records can
increase gas linearly. Trailing or unframed bytes receive no startup credit.
Compact DAGs receive no exponential credit.

## Observed totals, overhead and prediction errors

Complete baseline observations used one finite diagnostic allowance of 1,048,576
per whole phase, assigned once in debugger memory. Every accumulated charge and
existing check remained. Preparation completed through the public build path;
startup completed through final native-program admission and stopped before
evaluation or native calls. These are diagnostic completions, not normal-limit
passes. The profiling allowance is not a proposed policy cap.

| Workload / split | Source bytes / main nodes | Preparation including sizing / forecast | Error | Startup observed / forecast | Error |
| --- | ---: | --- | ---: | --- | ---: |
| Five-method SQLite `SELECT 42` / FIT | 19,798 / 761 | 385,450 / 493,416 | +28.01% | 561,573 / 724,822 | +29.07% |
| Imported buffer zeroing/length / FIT | 5,204 / 190 | 88,225 / 129,456 | +46.73% | 118,427 / 197,680 | +66.92% |
| Real TRANSIENT/blob fixture / frozen HOLDOUT | 13,504 / 337 | 255,019 / 332,184 | +30.26% | 321,643 / 481,950 | +49.84% |

Sizing added respectively 5, 4 and 5 work units: 0.00130%, 0.00453% and 0.00196%
of baseline preparation. Single measured loop times were 1.433, 1.282 and 1.223
microseconds, not a benchmark or CPU-to-gas conversion. Diagnostic restoration
setup was separate from sizing overhead. Preparation observations above combine
the completed baseline with this measured overhead; they are not a new complete
production execution of a changed admission path.

Three count-only stops at the actual `encode_effect_for_build` entry confirmed
all main-node counts and each source's text hash, length, order and module
basename against the saved images. Temporary directory names changed between
invocations. No limit was assigned and no image, host or C execution followed
these stops. The existing native-input prefix was 150 units for SQLite and blob,
and zero for buffer. It is already inside baseline whole preparation; sizing is
the only added cost. Adoption must retain that prefix in the same meter.

No row underpredicted. The holdout chose neither coefficients nor reserve. Its
assembled fixture is not the final product library. Full-library text/blob/null
binding, diagnostics, tail policy, persistence and simultaneous identities remain
unfinished and uncalibrated under TASK-0040. Do not report these errors as full
SQLite accuracy.

The five-method product's unchanged normal 327,680 allowance was exceeded by
57,765 preparation units and 233,893 startup units before sizing. Diagnostic
remaining allowances were 663,131 and 487,003. Earlier component sums did not
establish these complete totals.

## Initial tested boundaries and adoption work

Run 466 passed the test-only resident sizing prototype: checked addition and
multiplication overflow, refusal below already-spent sizing, paid loop reads,
exact/one-short sizing admission, an existing 11-unit prefix, fresh retries,
retained used work on finalization, and exhaustion of the remaining allowance.
Its optional artifact counts matched the three actual preparation-hook stops.
The adopted implementation retains that sizing algorithm before native-input
validation; the general source-compiler budget was unchanged in that initial
adoption. The later `100S` revision above is separate.

Run 464 separately passed the startup byte-proxy mechanism: canonical framing,
trailing/truncated input refusal, formula overflow, exact/one-short/prefix/fresh
retry, and compact-DAG metered refusal. A 65-record shared tuple DAG had 872
physical image/fact bytes and received 6,104 units, then refused expansion at
that allowance. This is mechanism evidence, not full Core/native calibration or
a whole-construction adversary result for the new preparation formula.

Run 467 passed the adopted implementation's sizing, overflow and prefix cases,
including an actual 150-unit prefix. A separate amplification test fed 512
repeated resident Type children into the real structural encoder under `24P`.
It refused at 792/792 units, preserving the 152-unit sizing/native-input prefix.
This is an encoder-stage test, not a whole-public-construction adversary claim.

The initial startup implementation uses its existing paid complete decoder, bounds/end-of-input checks and
canonical expected-facts comparison as the framing gate before restoration.
These charges stay inside `7B`, in the same meter through final native binding;
there is no second parser, free census or spent-work top-up. Existing source,
registry, Core, provenance, window and native-binding checks remain fresh.

Normal adopted-formula host tests then passed for the product `SELECT 42`,
imported buffer and frozen TRANSIENT/blob fixture. Fresh preparation totals were
385,438, 88,213 and 255,007. These are new executions; the earlier fit table is
not silently rewritten or refitted. For the exact passed product host,
preparation had 107,978 units remaining out of 493,416. A read-only stop before
evaluation measured startup through final native binding: 561,553 used of
724,766, leaving 163,213. It matched the saved embedded payload hashes and made
no limit assignment, rebuild or native call. Normal host execution had already
passed independently of that observer.

The earlier `4B + 3H` preparation fit used output image/fact size and host length
and was retrospective. Existing length writers require an already constructed
image, so that formula cannot fund construction. `24P` replaces it for the
prospective pilot; startup remained `7B` at that initial adoption. No exact output forecast or expanded
root inventory is needed for this simple input proxy.

## Larger product workload

The subsequent product library adds strict UTF-8 TEXT copying, embedded-NUL
output preservation and a second view family. Normal source, Core and native
preparation completed, but its generated host exhausted the unchanged `7B`
startup allowance before evaluation. This is an out-of-sample refusal, not a
native TEXT-copy pass.

One authorized observation of that exact saved host used a finite diagnostic
allowance of 2,097,152, assigned once at zero used work after ledger construction.
All charges and checks remained, and it stopped before evaluation or native C:

| Workload | Image + facts bytes | Approved `7B` | Complete startup | Shortfall |
| --- | ---: | ---: | ---: | ---: |
| Product TEXT/empty/NULL/invalid-UTF8/embedded-NUL columns | 174,197 | 1,219,379 | 1,265,014 | 45,635 |

Decode completed at 172,882 cumulative units, canonical fact authentication at
224,000, final Core began at 945,616 and finished at 1,255,897. Restoration
finished at 1,255,898; final native binding completed at 1,265,014. The finite
diagnostic allowance left 832,138 units. It is a measurement stopping allowance,
not a changed production formula or a normal host pass. That refusal subsequently motivated the approved `11B` revision above. This
record makes no universal sufficiency claim for either formula or future
full-library workloads.

The exact saved run-489 executable, image and facts were rehashed. Their receipt
is `sqlite-product-text-startup-total-diagnostic-489-20261015.json`. These
artifacts are separate from the disposed run-488 host; no byte-equality transfer
to that disposed artifact is claimed.

## Evidence scope

Checkpoint receipts retain exact source, configuration, binary, payload, script
and log hashes. The product FIT is in
`sqlite-gas-preparation-current-20261015-retry1.json` and
`sqlite-gas-startup-current-20261015.json`; corresponding `buffer` and
`blob-holdout` receipts cover the other rows. The numeric prospective table is
`sqlite-gas-prospective-input-sizing-and-errors-20261015.json`; the inventory
comparison is `sqlite-gas-prospective-prehook-equivalence-20261015.json`.

Product digest `5e40ad117b...` and corpus digest `0c9d1af4...` differed only by
this note and its index link at collection; executable/charge files and modes
were unchanged. Run 466's `af41eccd...` additionally includes the test-only sizing
prototype. Adopted-policy mechanism run 467 used `0e963a79...`; normal host runs
468–470 used `997a4409...`. Their only intervening changes were test logging and
artifact retention. The saved policy predecessor bytes match the original
manifest. Configuration was `452006fa...`. Only final totals support phase
attribution; intermediate source-line labels were ambiguous. One optional-field
error and one copied-executable mode error remain incomplete diagnostic attempts.

The Rust-backed copying/persistence/resume/bounded-NUL/forwarding
[baseline](provider-experiments/resource-calibration/sqlite-rust-summary.json)
supplies workload coverage and physical Rust build/runtime measurements. Its
lexical source counts and timings are not Ash gas. Older Ash public-driver
source, elaboration and Core calibration describes different phases.
