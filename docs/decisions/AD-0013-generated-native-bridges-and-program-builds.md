# AD-0013: Generated native bridges and program builds

- ID: `AD-0013`
- Status: accepted
- Related: [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md),
  [AD-0007](AD-0007-typed-core-dialects.md),
  [AD-0008](AD-0008-explicit-evaluator-machine.md),
  [AD-0011](AD-0011-milestone-worktree-lifecycle.md)

## Decision

Build whole Ash programs as native executables containing compiler-private
checked-Core construction data/code, the existing evaluator and generated Rust
bridges for the program's checked foreign declarations. Libraries remain passive
Ash source dependencies. This records the converged build boundary. The separately
accepted CP-0022 authorizes the semantic transition; neither artifact claims
implemented tools.

The initial target is `x86_64-unknown-linux-gnu`. Link static archives and ordinary
shared dependencies through the native linker. Generate typed Rust call sites
for exactly the supported profile. Do not introduce a descriptor-driven ABI call
engine, native Ash backend, stable Core wire format, separate compiled Ash
library format or runtime dynamic loader for this milestone.

Ash source supplies signatures, representations, constants, foreign assumptions
and all library-specific protocol/conversion/lifecycle policy. Generated bridges
perform common native calls, marshaling and admitted guard/access transitions.
They contain no dispatch on SQLite, arena or native-buffer names. Replace the
handwritten manifests/adapters and runtime C shim on the product path as the
three Ash libraries become sufficient.

### Compiler, library and program responsibilities

The front end checks a passive source graph and produces independently validated
typed Core plus immutable canonical foreign contracts. Library exports preserve
defining identities and body-free checked facts. A library import contributes
required contracts/symbols without performing native initialization.

Program build takes that checked graph, the selected target and explicit native
inputs. It resolves the target profile, emits Rust bridges and an evaluator host,
then compiles/links an executable. The private Core representation follows the
matching compiler/runtime version. No cross-version compatibility is promised.
The host independently validates reconstructed Core before execution and checks
bridge registration against the original contracts before associated acquisition.

Execution runs that admitted program and creates fresh resource activations.
Prepared declaration/template data can be shared; runtime owners and foreign
calls cannot. Existing non-foreign `run_path` and `RunConfiguration` users remain
supported. Add compile/build/execute API phases and an `ash build` tool path;
define exact arguments and diagnostics with the authorized implementation task.
Foreign execution requires the generated linked host, not runtime compilation
hidden inside an ordinary call to `run_path`.

### One canonical contract and explicit phases

Use phase-specific Rust types for unchecked declarations, checked foreign
contracts, target-resolved bridge plans and linked executable bindings. A
constructor for the next phase consumes or borrows the appropriate completed
phase. Checked immutable contracts retain original authority; projections for
module summaries, Core operands and bridges refer to them rather than preparing
independent descriptions of the same occurrence repeatedly.

Cache/reuse keys include exact source/dependency identities, profile, compiler
version and native build configuration. A changed input invalidates its derived
plan. Phase branding prevents use of unfinished data; it is not evidence that
source, Core or an external binary is valid. Independent Core reconstruction
still checks authority and rejects stale transformed facts.

Native ABI arrays remain Type-only, with an authenticated projection from the
complete ordered Type/EffectRow source arguments. Bridge tables authenticate
original library, operation and signature/assumption facts, rather than matching
native symbol names alone. Required binding/conversion checks precede acquisition.

### Native preparation and startup gas

Use input-derived cumulative work allowances at the modular compiler phase
owners and for native preparation and startup. The accepted policy is:

```text
preparation gas = 51 * (admitted source UTF8 bytes + validated main Core nodes)
source gas      = 300 * (canonical loaded source UTF8 bytes, including builtins)
final gas       = 161 * (the same canonical source UTF8 closure)
Core gas        = 345 * (the same canonical source UTF8 closure)
startup gas     = 22 * (canonical image bytes + canonical expected-fact bytes)
```

Source checking sizes the complete canonical loaded source closure before
checking. Count each loaded module once, including builtin sources, rather than
import edges or aliases. Pay one unit per source and one for the census in a
finite source-count-derived bootstrap, then carry that work inside `300*S`
through every module, source copy, closed entry and retained provenance. This is
the total allowance; the historical ten-percent deficit does not apply.
Final elaboration and independent compiler Core each pay their own identical
resident-length census before work begins and carry it inside their respective
`161*S` and `345*S` totals. Apply this at both Pure and Effect modular driver
entries. Their existing remaining-credit loans debit the same cumulative meter.
These totals have no historical extra ten percent. Resolution, constraints and
other construction/rewrite budgets remain separate.

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
Source-only measurement and accounting before adoption. This changes only the
Source coefficient; the other phase policies and checks above remain unchanged.
[DN-0050](../design/DN-0050-native-program-gas-estimates.md) records the measured
scope and historical comparisons. Normal execution, implementation review and
the integrated checkpoint remain separate verification obligations.

The project lead subsequently selected `300S` under that same delegated human
judgment after independent review of the larger product SQLite Source-only
measurement. The unchanged 39,033-byte constraint workload requires 8,510,624
units including its six paid census charges. Applying the same 25% reserve rule
gives a minimum coefficient of 273; 300 is the conservative rounded choice.
This changes only the Source coefficient. The finite diagnostic stopped before
linking, Final/Core checking or native execution; it is not a normal-policy or
whole-caller pass. Normal affected callers, implementation review, retaining
verification and the integrated checkpoint retain their separate gates.

### Optional C/header verification

Provide a separate `ash check-ffi` authoring path which emits/compiles C checks
against supplied headers for exact symbol types, representation facts and
constant/sentinel values. Runtime program calls are generated Rust. C checks
create no source contracts, executable constants or stronger ownership authority.
No C header parser or C runtime shim is required to build an already authored
binding. The native Rust toolchain/linker remains required and may use a platform
linker driver; this does not promise a toolchain independent of all C tooling.

Verification inputs associate exact declaration identities with C type, symbol
and constant spellings from the supplied headers. The tool checks those mappings
against the source profile/representation facts before using them in generated
signature and value checks. These optional mappings carry no executable values
or ownership authority; changing them cannot change a runtime bridge plan.

The author supplies complete executable facts in Ash. Verification failures
refer to those declarations and checked facts. A header mismatch, missing native
symbol, incompatible target or unsupported ABI shape is diagnosed causally.
Successful linking does not prove that headers match a binary or that the binary
obeys declared retention, validity and consumption assumptions.

## Context

DN-0036 established resource/Core/evaluator and native lifecycle evidence, but
retained library-specific Rust manifests/adapters and a SQLite C sentinel shim.
Moving manifest text into Ash alone would leave the authoring objective unmet.
The selected generated-bridge route makes fixed signatures available to Rust
without introducing another compiler or evaluator.

The user selected Rust bridges, copying first, optional C verification, the
bounded Linux target, source libraries and a runnable evaluator host. A generic
ABI engine adds another calling-convention runtime without removing ownership
or conversion obligations. A native Ash backend and compiled library ecosystem
would broaden this milestone beyond its authoring objective.

## Consequences

- Adding a supported library changes Ash declarations and native inputs; adding
  an ABI shape/target changes common compiler/runtime support under its own scope.
- Binding authors can check headers separately from building clients; builds
  cannot obtain missing executable facts from verification output.
- A foreign program requires native host generation and linkage before execution.
  Ordinary Ash functions continue to run in the existing evaluator.
- Exact Core/contract identity and matching runtime versions are required; private
  embedding is not a stable serialized Ash artifact.
- Minimal arena uses common C allocation/release primitives, rather than requiring
  a C ABI shim for the experiment's Rust Arena backing. Typed storage is deferred.
- Native buffer requires explicit source caller migration. Cell stays unchanged.
- Preparation sharing and phase types address duplicated work without weakening
  independent validation or caching per-activation ownership.
- Implementation follows the proposal/task workflow and AD-0011. The milestone
  uses `integration/ffi-ash`; Main changes only at the final integration gate.

## Verification

Before adoption, review CP-0022's semantic account and complete member/access
forms against SQLite, native buffer and minimal arena. Then require a generated
executable for each library, static/shared link evidence, reproducible commands
and actual native ownership/access observations. Existing realistic copying and
persistence programs are comparison cases.

Inspect generated Rust to establish exact signature/origin mapping and absence
of library-specific policy or a C runtime shim. Reject malformed contracts, target
shapes, bridge registrations and reconstructed/transformed Core independently.
Run optional header verification separately, including a deliberate mismatch.
Measure preparation reuse and added checking work without altering depth limits.
Record exact source/configuration pins and run the full integrated gate before
the final Main PR and milestone closure.
