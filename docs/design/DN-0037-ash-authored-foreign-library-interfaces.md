# DN-0037: Ash-Authored Foreign-Library Interfaces

- ID: `DN-0037`
- Status: exploring
- Related: [DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md),
  [DN-0035](DN-0035-region-memory-management-and-verified-providers.md),
  [DN-0025](DN-0025-library-and-package-milestones.md),
  [DN-0042](DN-0042-native-interaction-and-efficient-data.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md)

> This design note records a separate foreign-library authoring program. It
> selects no new syntax and defines
> no current Ash semantics. It does not change DN-0036's experiment contracts,
> implementation plan or completion criteria. Later bounded work needs its own
> governing contract and the product workflow in the
> [artifact guide](../project/artifacts.md).

The selected build boundary is recorded separately in AD-0013. CP-0022 is the
accepted semantic transition. This informative note does not define current Ash.

## Agreed ffi-ash milestone

[The GitHub milestone](https://github.com/dikini/ash-lang/milestone/1) tracks the
bounded product delivery, without a deadline. [DN-0042](DN-0042-native-interaction-and-efficient-data.md)
remains the broader motivation and relationship map. GitHub owns assignment,
blockers, progress and PR status; this section records durable scope and order.

Deliver Ash-authored foreign declarations and library policy, generated **Rust**
native-call bridges, optional separate C/header verification, and a runnable
executable containing checked Core and the existing evaluator. Target only
`x86_64-unknown-linux-gnu`, with static archives and ordinary shared linkage.
Libraries remain passive Ash source. Build whole programs; do not add a native
Ash backend, separately compiled Ash libraries or a stable Ash/Core ABI.

Port copying SQLite, native buffer and minimal arena lifecycle. Native buffer
uses an explicit source-library migration and loses special compiler dispatch;
cell stays unchanged. Minimal arena uses generic allocation/release primitives,
not a new shim for the experimental Rust Arena backing. General borrowing and
typed storage, files, serialization, numeric additions, SIMD, callbacks, async
calls, dynamic loading and Lean proofs remain outside the milestone. Finite
copying access and call-duration input borrows are required, bounded mechanisms.

| Sequence | Issue and bounded outcome | Dependency |
| --- | --- | --- |
| 1 | [#1: FFI semantic and architectural contract](https://github.com/dikini/ash-lang/issues/1): CP-0022 and AD-0013, precise semantics and reviewed authoring/build boundary. | Review and acceptance before product implementation. |
| 2 | [#2: Source contracts, Core and generic execution](https://github.com/dikini/ash-lang/issues/2): authenticated source admission, access, ownership, validation and evaluator. | Accepted #1 contract. |
| 3 | [#3: Program build and interface verification](https://github.com/dikini/ash-lang/issues/3): embedded Core, Rust bridges, static/shared linkage and separate C checks. | #1; connected executable support from #2. |
| 4 | [#4: Ash native-buffer library](https://github.com/dikini/ash-lang/issues/4): preserved behavior, explicit callers and removal of special dispatch. | Verified common #2/#3 mechanisms. |
| 4 | [#5: Ash arena lifecycle](https://github.com/dikini/ash-lang/issues/5): real acquisition, configuration, usage, refusal and release. | Same common mechanisms; no typed storage prerequisite. |
| 5 | [#6: Ash copying SQLite library](https://github.com/dikini/ash-lang/issues/6): source declarations, constants, protocol, conversions and lifecycle; realistic programs. | #2/#3; complete after the contrasting library deliveries. |
| 6 | [#7: Milestone closure](https://github.com/dikini/ash-lang/issues/7): integrated verification, specification, migration and build/run evidence. | All complete issue outcomes verified on the retaining branch. |

Use [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md): persistent
`integration/ffi-ash` plus one active product checkpoint worktree. Main stays
unchanged until the separate final integration gate. PRs target that branch;
the final delivery PR targets Main. Preserve checkpoint histories with explicit
merges. Milestone commits and intermediate merges are unsigned; the final
merge into Main is signed, following the updated execution instruction.

Issues #2–#6 are connected stages of one CP-0022 product checkpoint. Keep its
accepted proposal and active worktree until the complete semantic transition,
three library migrations, tests, specification, review and verification close.
An intermediate verified merge can retain an issue's complete outcome; it does
not close the overall checkpoint, authorize proposal/worktree cleanup or make
partial milestone behavior current on Main. Final checkpoint cleanup follows
AD-0011 and the artifact policy.

The accepted contract authorizes one active repository TASK per implementation
issue, allocated as TASK-0036 through TASK-0041 in the
[task index](../tasks/README.md).
Tasks link their governing proposal/decision and issue, and contain bounded work,
dependencies, required verification and durable discoveries/deviations. Ordered
steps go in the existing Work section; add a task-owned plan only when needed.
Do not add a parallel daily-status document. Reciprocal issue/TASK/PR links carry
the delivery chain; remove completed tasks/plans under the artifact policy and
retain historical links through delivering commits and PRs.

Open draft PRs when changes are reviewable. Incremental PRs reference issues
without closing them. Close an issue explicitly only after its complete outcome
is verified on the retaining branch and its delivering PRs, integration commit
and verification receipt are recorded. Main semantics remain a separate gate.

Reuse native lifecycle/copy/control observations and focused negative regressions.
Use one Cargo job, connected checks during development and full architecture/
workspace verification at integration. Exact source pins and commands make
evidence reusable. The final Main PR includes implementation, normative updates,
Ash libraries, caller migration and reproducible build/run instructions.

## Question

What language, memory, host ABI and toolchain mechanisms let humans and AI
agents author reusable foreign-library interfaces in Ash, starting from the
foreign API and binary? Which facts can checking infer, which contracts must
authors express, and how can common infrastructure replace per-library
host-language manifests and adapters?

## Objective

For a declared supported foreign ABI profile, a library author should write
Ash code to refer to an existing foreign library, implement its binding and
provider policy, and link it during compilation. Native build requirements
and configuration may be declarative inputs. The author should not need a
hand-written Rust manifest, Rust adapter or C shim, or changes to the Ash
compiler or interpreter for that library. Compiler-generated glue may be an
implementation technique; it creates no extra safety authority.

The capability must be sufficient for humans and AI agents to author reusable
Ash modules bridging libraries supplied by the host operating system. They
should be able to work from the foreign API, documented Ash interfaces and
tooling, without inspecting or modifying compiler implementation details.

The compiler and interpreter provide common foreign-call, representation,
memory, ownership, initialization and linking infrastructure. Library-specific
symbols, contracts, protocol, conversions and error policy belong to the Ash
binding. Adding a library within the supported profile changes those sources
and native build inputs, not compiler dispatch code.

## Context

The [current specification](../../spec/README.md) defines passive source
modules and the closed builtin cell and native-buffer resources. It provides
no general FFI or foreign-representation guarantee. The
[elaboration contract](../../spec/elaboration.md#surface-erasure) authenticates
those builtin resources; ordinary declarations cannot manufacture their
authority. The [dynamic semantics](../../spec/dynamic-semantics.md) give
ordinary values evaluator-managed storage, without a source memory policy.

[DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md) governs
the ongoing SQLite and scoped-arena experiments. Their Rust-authored foreign
manifests, generated Ash declarations, identity-bound admission and native
adapters supply bounded evidence about contracts and resource composition.
The [execution record](provider-experiments/execution.md#current-checkpoint)
records the supported components and limitations. This machinery alone does
not establish Ash-authored foreign declarations or general host ABI calls.

The existing manifest could become an internal compiled representation; its
present Rust authoring interface is not a required public library API for this
program. Moving declarations into Ash and replacing hand-written adapters
remain separate questions with separate evidence.

The [DN-0036 readiness review](foreign-authoring/dn-0036-readiness.md) records
the verified Main capabilities, outstanding and worktree evidence, and the
selected first authoring target: a copying SQLite binding on one host ABI.
The selected execution direction generates Rust bridges and links a host using
the existing evaluator; AD-0013 records that non-language boundary. CP-0022
records the accepted source and operational transition. SQLite remains the first
complete foreign-library authoring case; native buffer and minimal arena acquisition,
usage and release test the same mechanism before its final SQLite delivery.
Unfinished general borrowing and wider Arena work are not prerequisites.
Native storage interfaces and region validity contracts remain distinct.

[AD-0007](../decisions/AD-0007-typed-core-dialects.md) requires typed Core and
independent validation; [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)
provides the explicit evaluator boundary. A generic foreign-call path must
preserve those obligations. [DN-0025](DN-0025-library-and-package-milestones.md)
explores packages and compiled artifacts without selecting a native executable
or object-file backend.

## Constraints

Reuse ordinary Ash types, effects, handlers, module contracts and resource
mechanisms where their checked meanings suffice. Identify each proposed
semantic extension and the corresponding surface and Core obligations.
Preserve passive imports and exact defining identities across module checking.

### ABI scope

The ABIs under consideration are host and foreign-library ABIs, for example
the C/library ABI on Linux or FreeBSD for a specified architecture and native
build configuration. Profiles identify the applicable calling conventions,
symbol linkage, primitive widths, aggregate layouts and library requirements.
These examples do not claim current support for both operating systems.

An Ash ABI is outside this program's scope. Ash value representations and
internal calls remain implementation details. Checked conversions marshal
values to and from the host representations required by foreign calls; an
ordinary Ash value need not have a C-compatible layout. The program does not
design stable Ash binary layouts, an external Ash calling convention or binary
compatibility between Ash modules or versions.

Compiled output may retain foreign symbol and host ABI requirements. Retaining
those facts or choosing an internal artifact format does not establish an Ash
ABI.

### Minimum C authoring case

Given the C header file or files and the compiled library binary, an author
must be able to develop its Ash interface and compile/link to the library
through the supported host ABI. Native inputs may include a static archive or
shared library. Target selection, calling conventions, native configuration
and link requirements must be expressible in Ash declarations or common
declarative configuration where required.

The walkthrough must not require the library's C source, a Rust manifest, a
hand-written Rust adapter or a hand-written C shim. The author reads the
supplied headers and declares the relevant signatures, types, layouts and
constants in Ash. Common infrastructure resolves the declared symbols from
the supplied native library and executes the resulting Ash binding.

The Ash binding states ownership, retention, invalidation, initialization,
failure and release assumptions that the headers do not determine. Missing
behavioral facts remain explicit author obligations, rather than invented
inference. Matching headers to a library and checking link requirements do not
prove the foreign implementation obeys those contracts.

### Author and compiler responsibilities

Authors understand the foreign language and API. They translate its interface
and behavioral assumptions into Ash declarations, contracts and wrapper code.
Ash understands those declarations and the selected host ABI; the compiler
and interpreter do not need to parse or understand C or another foreign
language. No header parser is a prerequisite for developing or using a binding.

Inference operates on Ash types, bodies and declared foreign contracts. It
derives their consequences without guessing facts from foreign syntax or
symbol names. Host ABI support supplies calling and representation rules;
foreign-language understanding remains with the author.

An optional external tool may translate headers into candidate Ash declarations.
Its output enters the same normal Ash checking path and creates no additional
authority. This assistance is separate from required compiler infrastructure.

### Memory and execution boundary

Use DN-0036's synchronous foreign-call and scoped-storage cases as initial
evidence. Arena owners remain scoped and cannot be packaged or transported
with their dependent values. Callbacks, asynchronous calls, process storage
transfer, reference counting and tracing need separately bounded design work.

## Candidate directions

### Follow the types before selecting syntax

| Role to specify | Required relationship |
| --- | --- |
| Foreign library requirement | Native build input, target ABI, supported configuration and link requirement. |
| Foreign symbol | Defining library, symbol identity, calling convention and complete foreign signature. |
| Foreign representation | Width, signedness, alignment, aggregate layout, encoding and address requirements. |
| Conversion or marshaling operation | Ash and foreign input/output types, effects, failure outcomes and storage obligations. |
| State and access contract | Owned and borrowed identities, retained dependencies, validity interval and conflicting operations. |
| Lifecycle contract | Initialization, partial establishment, consumption, refusal and required completion order. |
| Public binding contract | Exact types/effects, dependency/control relationships and defining origins sufficient for independent client checking. |

Specify which roles are source declarations, ordinary Ash definitions,
compiler-checked evidence, build configuration or foreign assumptions. Map
each candidate form to those typed roles, elaboration and Core behavior before
adding syntax. A matching name or constructor shape cannot create authority.

Infer kinds, substitutions, operand positions and structural dependencies from
checked Ash declarations and bodies where sufficient facts exist. Authors
derive foreign signatures and layouts from their understanding of the API.
Foreign retention, invalidation, consumption and failure behavior require
explicit contracts or derivation from primitives whose contracts already
state those properties. An ABI signature alone does not establish them.

### Program and dependencies

1. **Define a bounded host ABI profile.** Select initial scalar, opaque
   handle, byte-buffer and output-parameter cases from SQLite and native
   allocation. Identify the operating system, architecture and native build
   configuration. State unsupported ABI shapes and targets. Account for host
   calling conventions, representations, initialization and failure before
   lowering.
2. **Author checked foreign contracts in Ash.** Reuse ordinary declarations
   where their meanings suffice. Design missing state, binding and ownership
   contracts by following their types. Derive the canonical registration
   representation from checked Ash source and compare it with the current
   manifest. Preserve authentication, imports, independent validation and exact
   origins.
3. **Provide generic calls and conversions.** Design the common compiler/Core
   and interpreter path for the supported ABI profile. Separate raw foreign
   signatures from safe Ash-facing operations. Any emitted glue must be checked
   against the same signature, representation and effect obligations. Retire
   per-library runtime dispatch implementations as this path becomes sufficient.
4. **Connect memory and access.** Use the arena and borrowing experiments to
   establish stable storage, typed layout, initialization, pointer validity,
   retained access, independent copying and completion. Identify the generic
   primitives needed to write conversion and lifecycle wrappers in Ash.
   Keep opaque addresses and completion authority within their checked roles.
5. **Design compilation and linking.** Specify how Ash declarations contribute
   native library and symbol requirements to compilation, how the toolchain
   resolves them for a target, and which facts survive in compiled output.
   Decide how the interpreter executes the same checked bindings through common
   infrastructure. Missing symbols, incompatible ABI/configuration and unsupported
   targets need causal diagnostics. Imports remain passive; initialization has
   an explicit execution and ownership contract. Coordinate artifact choices
   with [DN-0025](DN-0025-library-and-package-milestones.md), which does not
   yet select a native executable or object-file backend.
6. **Rewrite and compare the bindings.** Express the selected SQLite bridge
   and native allocation boundary in Ash using the generic mechanisms. Compare
   with the retained adapters on the same valid, rejection and failure cases.
   A walkthrough of a contrasting API tests transfer without requiring another
   complete library implementation in the initial experiment.

Moving manifest declarations into Ash and eliminating hand-written adapters
are distinct checkpoints. Neither supplies the other's evidence. The current
bounded provider work continues to supply the source/type/Core/native evidence
needed to design them; this program does not silently change P-1's admitted
foreign-call mechanism.

## Evidence and experiments

### Evidence for the authoring objective

Use an unchanged Ash compiler and interpreter to build an Ash-authored binding
against the selected native library, starting with its C headers and binary.
Compile and link its declared symbols, check clients from its public contracts,
and execute real calls with the required memory and completion behavior. No
library-specific hand-written Rust/C glue or compiler modification may be
necessary for this claim.

Retain paired failures for wrong symbols, representations, conversions,
ownership, retained access, initialization and completion. Check generic Core
independently before and after transforms. Measure generated code, copying,
storage and authoring effort. Optional external header tooling must not hide
missing semantic contracts or become a prerequisite for hand-authored Ash
bindings. The compiler/interpreter authoring test consumes the authored Ash
interface and native library, without reading foreign-language declarations.

An authoring walkthrough must demonstrate discovery of supported host ABI and
library inputs; declaration of symbols, representations and semantic contracts;
implementation of conversions, effects, handlers and lifecycle policy in Ash;
independent client checking; compilation/linking; and real execution. Include
a failed declaration or ownership case and its repair from the diagnostic.
Record every step that still requires compiler knowledge or host-language code.
An unexplained exception prevents the authoring-capability claim for that case.

Human-readable documentation and diagnostics and machine-readable build,
binding and diagnostic information should expose the same contracts. Tooling
should distinguish inferred facts, explicit declarations and foreign
assumptions, identify unsupported cases, and report native inputs and link
failures reproducibly. Evaluate these interfaces with human and AI-assisted
authoring workflows. Both use the same public Ash mechanisms and verification
boundary.

### Outputs and adoption

Produce the typed foreign-call model, candidate source/build forms, inference
and explicit-contract boundary, operational semantics, target/linking design,
worked bindings and tooling comparison. Record all remaining primitives and
foreign assumptions in the adoption report and FFI blueprint.

Language changes follow a change proposal; converged compiler, runtime and
linking choices follow architectural decisions and authorized tasks. Product
checkpoints retain implementation, tests and corresponding surface/Core
specification changes together. Current Rust-based experimental evidence must
remain labeled by its actual support until the Ash-only objective is proved.

Any later prototype must name its question, supported ABI cases, comparison
criteria and retention conditions before implementation. Retain successful
typed mechanisms and reproducible counterexamples as design evidence. Replace
or discard failed machinery when the comparison justifies it. Retention does
not establish language truth or authorize integration into the product.

## Open questions

- Which host ABI profile is sufficient for the first binding, and which
  representations and calling conventions does it exclude?
- Which foreign declarations can reuse ordinary Ash forms, and which typed
  contracts need new source forms or Core rules?
- Which consequences can checking infer, and which foreign behavior must
  remain an explicit assumption in the public binding contract?
- Which memory and conversion primitives let authors implement initialization,
  retention, invalidation and release safely in Ash?
- How should compilation and the interpreter share checked symbol and ABI
  information, native build inputs and link diagnostics?
- Which documentation, diagnostics and external assistance make the workflow
  usable by humans and AI agents without compiler implementation knowledge?
