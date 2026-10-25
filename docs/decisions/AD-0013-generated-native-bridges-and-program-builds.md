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
source gas      = 2600 * (canonical loaded source UTF8 bytes, including builtins)
final gas       = 800 * (the same canonical source UTF8 closure)
rewrite gas     = 16 * (the same canonical source UTF8 closure), per compiler arena
Core gas        = 5300 * (the same canonical source UTF8 closure)
startup gas     = 22 * (canonical image bytes + canonical expected-fact bytes)
```

Source checking sizes the complete canonical loaded source closure before
checking. Count each loaded module once, including builtin sources, rather than
import edges or aliases. Pay one unit per source and one for the census in a
finite source-count-derived bootstrap, then carry that work inside `2600*S`
through every module, source copy, closed entry and retained provenance. This is
the total allowance; the historical ten-percent deficit does not apply.
Final elaboration and independent compiler Core each pay their own identical
resident-length census before work begins and carry it inside their respective
`800*S` and `5300*S` totals. Apply this at both Pure and Effect modular driver
entries. Their existing remaining-credit loans debit the same cumulative meter.
These totals have no historical extra ten percent.

The paid census also returns its canonical byte count for a separate `16*S`
rewrite meter, installed once when an empty compiler-owned arena is constructed.
All rewrites in that arena consume the same meter. A fresh compiler arena
inherits only the allowance, never spent work or unused Source/Final credit.
Reject multiplication overflow. There is no floor, intercept, refill or extra
margin. Generic builder, standalone and private-image defaults remain unchanged;
resolution, constraints and other construction budgets remain separate.

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
