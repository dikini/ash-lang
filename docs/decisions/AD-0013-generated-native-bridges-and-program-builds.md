# AD-0013: Generated native bridges and program builds

- ID: `AD-0013`
- Status: accepted
- Related: [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [AD-0007](AD-0007-typed-core-dialects.md),
  [AD-0008](AD-0008-explicit-evaluator-machine.md),
  [AD-0011](AD-0011-milestone-worktree-lifecycle.md)

## Decision

Build whole Ash programs as native executables containing compiler-private
checked Core, the existing evaluator and generated typed Rust bridges for passive
foreign declarations. The [specification](../../spec/static-semantics.md#source-foreign-declarations)
defines the supported source boundary; the [tool guide](../tools/ash.md) defines
build inputs and invocation.

The target is `x86_64-unknown-linux-gnu`. Link static archives and ordinary shared
dependencies through the native linker. Generate `extern "C"` pointer calls and
actual void returns from the supported signatures. Do not introduce a generic
ABI engine, native Ash backend, stable Core wire format, compiled Ash library
format or runtime library resolver.

### Compiler, library and program responsibilities

The front end checks a passive source graph and independently validates typed
Core with immutable defining symbol facts. Imports preserve exact declaration,
operation and signature identities without performing native initialization.
Bindings supply profile, signature and native link name. Ordinary Ash functions,
handlers and cleanup supply protocol, null/length checks and lifetime policy.
The compiler does not verify native behavior or manage foreign ownership.

Program build takes the checked graph and explicit native inputs, emits typed
Rust bridges and an evaluator host, then compiles and links an executable.
Private images require the matching compiler/runtime version; no cross-version
compatibility is promised. Startup independently reconstructs and validates Core
and exact bridge registrations before evaluation. No live pointer is an image
constant. Ordinary source handlers retain nearest-handler precedence.

Bytes exposes one readonly pointer with managed backing retained through the
synchronous call. Address preserves a data pointer without integer conversion;
Unit results use actual void. Retention of a Bytes pointer beyond a call requires
the module to retain the original backing, and managed backing must not be
mutated or freed. No hidden length, terminator or inferred ownership is supplied.

### One canonical contract and explicit phases

Keep compile, prepare and build phases explicit. Immutable checked symbol facts
remain shared authority for module summaries, Core operands and generated bridge
plans. Binding tables authenticate the original symbol allocation and exact
signature rather than selecting by native link name alone. Independent Core
validation rejects stale or transformed correspondence.

Reuse keys include exact source/dependency identities, profile, compiler version
and native build inputs. Phase completion or cache reuse does not establish
external binary validity. Ordinary non-native execution remains available;
foreign execution requires an explicitly generated and linked host.

### Native preparation and startup gas

Use input-derived cumulative work allowances at the modular compiler phase
owners and for native preparation and startup. The accepted policy is:

```text
preparation gas = 850 * (admitted source UTF8 bytes + validated main Core nodes)
resolution gas  = max(327680, 80 * (canonical loaded source UTF8 bytes, including builtins))
source gas      = 10000 * (canonical loaded source UTF8 bytes, including builtins)
final gas       = 800 * (the same canonical source UTF8 closure)
builder gas     = max(327680, 8 * (the same canonical source UTF8 closure)), per program arena
rewrite gas     = 16 * (the same canonical source UTF8 closure), per compiler arena
Core gas        = 25000 * (the same canonical source UTF8 closure)
startup gas     = 118 * (canonical image bytes + canonical expected-fact bytes)
```

Source checking sizes the complete canonical loaded source closure before
checking. Count each loaded module once, including builtin sources, rather than
import edges or aliases. Pay one unit per source and one for the census in a
finite source-count-derived bootstrap, then carry that work inside `10000*S`
through every module, source copy, closed entry and retained provenance. This is
the total allowance; the historical ten-percent deficit does not apply.
Final elaboration and independent compiler Core each pay their own identical
resident-length census before work begins and carry it inside their respective
`800*S` and `25000*S` totals. Apply this at both Pure and Effect modular driver
entries. Their existing remaining-credit loans debit the same cumulative meter.
These totals have no historical extra ten percent.

The paid census also returns its canonical byte count for a separate `16*S`
rewrite meter, installed once when an empty compiler-owned arena is constructed.
All rewrites in that arena consume the same meter. A fresh compiler arena
inherits only the allowance, never spent work or unused Source/Final credit.
Reject multiplication overflow. There is no floor, intercept, refill or extra
margin. Generic builder, standalone and private-image defaults remain unchanged;
resolution, constraints and other construction budgets remain separate.

Program arenas also receive a separate primary payload-construction allowance
`max(327680, 12*S)` from that paid census. Install it before catalog precharges;
each arena starts with fresh independent primary and rewrite meters. Primary
construction remains excluded from the Source/Final reports. Standalone,
default and private-image primary limits retain their existing capacities.

On 2026-10-26 the unchanged 8,000-member recursive-group/call-chain test exposed
the fixed primary builder cap and repeated whole-arena variable searches during
closure preparation. One temporary, charged first-variable index per existing
batch preserves first-match and fallback behavior. With S = 438,691, Source work
fell from 519,069,391 to 7,149,428; Final previously exhausted 350,952,800 and then
completed at 2,296,950. Core completed at 10,731,616. The largest complete primary
arena used 2,680,644; a 25% fitting reserve requires 3,350,805, covered by
`8*S = 3,509,528`. Completion diagnostics used a finite `16*S` primary ceiling;
the normal selected `8*S` policy then passed the original test, including its
256 KiB worker, evaluation and evidence-envelope assertions. Phase coefficients,
rewrite ownership and runtime limits are unchanged.

The later unchanged 10,000-member cyclic-data witness at 320 KiB exposed the
primary `8*S` ceiling during cleanup-row replay, not aggregate Source
exhaustion. With S = 398,678 it refused a one-cell charge at 3,189,424. A finite
`16*S` primary diagnostic completed all original render/count/drop assertions;
its four independent primary arenas used `23`, `117`, `3,430,201` and
`3,430,528` cells.
Rewrite work remained separate. The largest complete owner requires 4,288,160
with the existing 25% reserve. The selected rounded primary coefficient is now
12: 4,784,136 here, 39.46% above observed use (28.29% of the allowance unused).
Source, Final and Core completed at 8,654,930, 2,320,736 and 15,063,023 cells.
No qualifying small replay optimization was established: provisional propagation,
strict removal and atomic rollback retain distinct obligations. All temporary
tracing and the diagnostic coefficient were restored before selecting the policy.
Standalone/default/private-image primary capacities, paid prefixes, independent
rewrite ownership and every other phase coefficient remain unchanged. Normal
uninstrumented verification is separate from this completion measurement. The
selected policy passes the original cycle witness with all three reported phases
complete at the same measured costs, all 25 driver tests, four policy tests,
57 builder tests and the exact/short/retry cleanup-row replay test.

Program resolution receives a fresh independent graph-wide allowance
`max(327680, 80*S)` after the existing paid canonical source census. Check the
multiplication before applying the floor. Standalone resolvers and explicit
caller budgets keep their existing limits; Source/Final/Core reports do not
absorb resolution work. The existing Structural diagnostic override and
resolution calibration report use this owner's selected allowance.

The unchanged depth-48, width-4 public-route test completed resolution at
643,634 cells with S = 11,791 under a temporary finite 655,360-cell diagnostic.
Its normal Source/Final/Core budgets and 320 KiB worker remained unchanged,
including exact/one-short constraint checks. The 25% fitting target is 804,543;
the rounded coefficient 80 supplies 943,280. Clone-before-lookup still checks
complete alternate effect declarations: avoiding the allocation without dropping
its charged authentication traversal did not offer a material work reduction.
The fixed standalone capacity and other phase coefficients are unchanged.

The connected R-core check restored the unchanged 24-owner Cell witness.
Escape payload checks now reuse the existing charged forward boundary walk and
omit only per-boundary captured prefixes they never consume. Every selected
owner and payload check remains, in the same order; ordinary capture prefix
reconstruction is unchanged. At S = 1,791, complete Source work fell from
21,142,054 to 13,215,994 (37.49%). Final completed at 29,736 and independent
Core at 33,035,808. Earlier normal and 2× Core refusals were truncated, not
fitting numerators. The final finite completion used 8× the former Source and
Core allowances and retained the original result 42, 24 distinct acquisitions
and exact reverse release assertions.

The 25% fitting targets are Source 16,519,993 and Core 41,294,760. Rounded
coefficients 10,000 and 25,000 supply 17,910,000 and 44,775,000 respectively
(about 35.5% reserve). This increases admitted work after the bounded saving;
it does not claim unchanged cost or a universal complexity guarantee. Canonical
source counting, paid census, cumulative phase owners, overflow and refusal
prefixes are unchanged. At that fitting checkpoint, Final 800*S, resolution 80*S
with its default floor, primary 8*S with its default floor, rewrite 16*S,
standalone, private-image,
constraint, depth and production stack limits remain unchanged. Normal-policy
verification is separate from these finite completion measurements. The
selected normal policy subsequently passed all 25 original driver tests, four
policy tests, 78 capture tests, five reporting tests and two observer tests.
This is focused evidence, not a complete workspace gate.

Preparation reads resident admitted source lengths and main arena length before
image construction. Pay one unit per source and one for the node count using a
finite source-count-derived sizing allowance; carry those charges inside the
computed total. Native-input validation and all subsequent emission work consume
that same meter. Refuse checked-arithmetic overflow or a total below spent work.

Startup derives only a private provisional meter from actual resident payload
lengths. Complete paid canonical decoding, bounds/end-of-input checks and the
independently emitted expected-facts comparison before semantic reconstruction.
Keep all framing, source/original/Core/capture and final native-binding admission
charges in the same meter. Invalid framing cannot reach semantic admission or C.
There are no per-module resets, spent-work top-ups or static overall gas ceiling.

These estimates do not prove a universal complexity bound or grant authority.
The actual meter still refuses amplified work. Valid unused framed records or
source whitespace can increase estimates linearly; compact DAGs cannot obtain
exponential credit. Standalone Core validation defaults, depth, stack, fallible
allocation and all identity/semantic checks remain unchanged. The compiler Core
formula does not grant additional startup work or alter generic validator APIs.
The established non-native Pure build policy is separate.

The user approved preparation `24P`, then source `100S` / startup `11B`, and
subsequently preparation `51P`, final elaboration `33S` and compiler Core `108S`,
then startup `22B`, final elaboration `161S` and compiler Core `345S` on 2026-10-15 after the bounded calibration and larger-workload and compact-generic observations in
[DN-0050](../design/DN-0050-native-program-gas-estimates.md). That note records
measured scope, errors and incomplete final SQLite coverage; it is informative.
Require focused connected normal-host and adversarial tests and independent
review of the implementation before transferring its verification.

On 2026-10-16, the project lead first adopted source `200S` under the user's explicit
delegation to choose recommended autonomous fixes. The unchanged 283-byte
recursive-hook regression required 42,836 units through complete Source
checking, including its paid census. The 25% reserve rule gives coefficient 190;
200 is the conservative rounded choice. Independent review cleared the finite
Source-only measurement and accounting before adoption. That revision changed
only the Source coefficient and retained the other then-current phase policies.
[DN-0050](../design/DN-0050-native-program-gas-estimates.md) records the measured
scope and historical comparisons. Normal execution, implementation review and
the integrated checkpoint remain separate verification obligations.

The project lead subsequently selected `300S` under that same delegated human
judgment after independent review of the larger product SQLite Source-only
measurement. The unchanged 39,033-byte constraint workload requires 8,510,624
units including its six paid census charges. Applying the same 25% reserve rule
gives a minimum coefficient of 273; 300 is the conservative rounded choice.
That revision changed only the Source coefficient. The finite diagnostic stopped before
linking, Final/Core checking or native execution; it is not a normal-policy or
whole-caller pass. Normal affected callers, implementation review, retaining
verification and the integrated checkpoint retain their separate gates.

The project lead later selected Source `800S`, Final `800S` and separate
compiler-arena rewrite `16S` under the same delegated judgment, after independent
review of all four complete SQLite phase observations. The 44,512-byte
persistence workload used 28,158,349 Source units, 26,809,274 Final units and
510,782 units in its largest rewrite arena. A 25% fitting reserve gives minimum
coefficients 791, 753 and 15; 800, 800 and 16 are the conservative rounded
choices. The fixed implementation rewrite default had independently refused
one unit at 327,680; Source credit did not fund it. The replacement preserves
that ledger separation and does not change the shared structural default.
These finite measurements stopped before independent Core, preparation or
native execution. They are fitting evidence, not a holdout, normal caller pass
or universal complexity guarantee. Normal verification and retained delivery
remain separate obligations.

On 2026-10-26 the project lead selected Source `2600S` and Core `5300S`
for the connected integer-residency and legacy Cell analysis. Final remains
`800S`. The exact 24-owner fixture used 3,595,764 Source units and 7,560,218
Core units over 1,791 canonical source bytes (2,007.685 and 4,221.227 units per
byte). Applying the existing 25% fitting reserve gives minimum coefficients
2,510 and 5,277; rounding upward to hundreds gives 2,600 and 5,300. The fitted
headroom is about 29.5% and 25.6%. This increases admitted work; it does not
claim unchanged analysis cost. Focused rediscovery dominated the measured work.
The finite diagnostic returned 42 and checked 24 unique Cell acquisitions with
exact reverse release order. It used larger diagnostic allowances, so normal
policy verification remains separate. Canonical source counting, paid census,
cumulative phase owners and checked overflow are unchanged. No floor, runtime
margin, refill, cross-phase credit or change to standalone, private-image,
constraint, runtime, depth or stack defaults is introduced.

On 2026-10-26 the closure-storage delivery recalibrated Source to `3900S`
and Core to `6200S`, retaining Final `800S`. The original 1,024-level
registration fixture completed at 4,886,806 Source units and 7,763,338 Core
units over S = 1,582 canonical bytes (3,089.005 and 4,907.293 units per byte).
The existing 25% fitting rule rounded upward to hundreds gives 3,900 and 6,200,
about 26.3% reserve each. The completion measurement used one diagnostic
Source allowance of twice normal; Final and Core retained normal allowances.
Its original sum, 1,025 registration/request counts, exact failure/retry and
256 KiB runtime-worker assertions passed; normal policy verification is separate.
Focused discovery used about 94% of both measured phases; copying used less than
0.7%, with no demonstrated safe root/state omission or raw-context growth.
This raises admitted work, not performance claims. Canonical S, paid census,
cumulative owners, overflow, all other phase/default capacities and production
stack settings remain unchanged. Two private disposal stress workers separately
use 128 KiB after observed 64 KiB failures and 128 KiB passes at unchanged depths;
this is fixed debug-frame headroom evidence, not a minimal or universal bound.

On 2026-10-26 the project lead also selected startup `65B`, preserving B as
canonical image bytes plus canonical expected-fact bytes. Of nine complete
imported-flow restoration observations, the recursive case used 406,477 units
for B = 7,873 (4,900 image and 2,973 fact bytes): 51.629239 units per byte.
The existing 25% fitting rule gives `ceil(1.25 * 51.629239) = 65`, above the
previous coefficient 22. This measures framing, fact comparison and complete
restoration; later native binding correspondence and final admission remain in
the same meter but were not measured by that restoration fixture. Actual native
caller verification is separate. The recursive case refuses the unchanged
327,680 standalone image allowance; the other eight measured cases fit it.
Normal `65B` restoration must retain all nine expected results and exact
short/retry checks. No standalone limit, extra runtime margin, refill or
Source/Core credit transfer is introduced.

On 2026-10-26 the closure-storage delivery selected startup `118B`. All nine
existing imported-flow fixtures completed with one diagnostic allowance of
`130B` per image, retaining framing, canonical fact comparison and restoration
in the same meter. The maximum recursive case used 772,224 units over
B = 8,206 (5,233 image and 2,973 expected-fact bytes), or 94.104801 units per
byte. The existing integer fitting rule gives `ceil(1.25 * 94.104801) = 118`,
about 25.4% reserve. An earlier normal `65B` run refused that case at
533,647/533,650 over B = 8,210; separately generated identity encodings account
for the different byte census, so these are not identical image bytes. In the
completed diagnostic, cases one and two refused the unchanged standalone
327,680 allowance and the other seven fit it. This fits complete restore-stage
work, not the later native-binding correspondence/final admission that retains
the same cumulative meter. Normal nine-flow and actual native verification
remain separate obligations. Canonical B, checked overflow, all other owners
and defaults, the supported image profile and the no-refill/no-transfer rules
are unchanged.

The project lead subsequently selected preparation `125P` under the same
delegated judgment after independent review of four complete preparation
observations. Here P retains its existing paid definition: canonical admitted
source bytes plus validated main Core nodes. Persistence used 4,984,019 units
for P = 50,905 (44,510 source bytes and 6,395 main nodes). Its ordinary fixture
substitutes a fresh database path, so those actual inputs are recorded separately
from the earlier 44,512-byte observation. A 25% fitting reserve requires integer
coefficient 123; 125 is the conservative rounded choice. The same cumulative
meter carries its census, native-input checks, image encoding and emission.
The finite measurements used `204P` and stopped before generated-host building
or evaluation; normal native verification and retained delivery remain required.
Source/Final/rewrite/Core/startup policies and every other check remain unchanged.

For the CP-0024 slim transition, the project lead selected preparation `850P`
under the same delegated calibration judgment after independent review. The
retained ordinary handled-row workload at depth 42 used 2,181,566 units for
P = 3,494; depth 43 used 2,330,800 units for P = 3,510 (3,401 source bytes and
109 main nodes). These measurements carry the paid source census through complete
image encoding and Rust emission; they exclude native-input path checks,
generated-host building and execution. Encoding and emission took about 28 ms
at depth 43. A 25% fitting reserve requires integer coefficient 831; 850 grants
2,983,500 units, about 28% above that observation. The former `125P` allowance
would require an 81% reduction in complete preparation work for this input.
Changing the coefficient avoids new encoding or caching machinery for this
measured cost. These two fitting cases are not a universal bound. The cumulative
meter still pays native-input checks, and all bootstrap, overflow, exhaustion,
depth and separate phase limits remain unchanged. Normal depth-42/43 preparation
and native startup verification remain required.

## Context

The earlier foreign experiments established useful bridge and evaluator evidence
but coupled it to numeric, owner, output, status, window and host policy. The
smaller boundary retains generated typed calls and existing compiler/evaluator
machinery while placing binding policy in ordinary Ash. Experimental lifecycle
or full SQLite results do not enlarge the supported ABI.

## Consequences

- Adding a binding within the supported mapping changes Ash declarations and
  native inputs. A new ABI shape or target requires separately authorized work.
- Native validity, retention and release remain binding assumptions. Address is
  neither a resource nor proof of allocation or lifetime.
- Ordinary resources, cells, cleanup, handlers, work/depth limits and independent
  source/Core/image validation retain their existing responsibilities.
- There is no mandatory header-checking tool, FFI-specific artifact protocol,
  protected approval or security receipt gate.
- Numeric ABI, out-pointers, callbacks, structs and foreign text/memory
  interpretation remain unsupported gaps.

## Verification

Require real pointer/void/Bytes calls, ordinary source-handler overrides, missing
binding refusal, null/equality, unsupported-signature rejection and ordinary
cleanup on normal, error and checked-discard paths. Exercise static/shared native
inputs, repeated source-independent embedded-image startup and malformed
Core/image/registration rejection without weakening validation.

The direct SQLite version/source-id getter canary is required. Non-null/equality
observations do not read its text or establish full database coverage. Numeric
and out-pointer requirements of open/prepare remain gaps. Inspect generated Rust
for exact typed pointer/void signatures and absence of library-specific policy
or a runtime C shim. Preserve normal depth-42/43 preparation and startup checks
under the gas policy above. Final-head independent review and the normal full
workspace gate remain required before integration and milestone closure.
