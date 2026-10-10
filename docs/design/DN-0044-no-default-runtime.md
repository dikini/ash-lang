# DN-0044: No Default Runtime

- ID: `DN-0044`
- Status: exploring
- Related: [DN-0017](DN-0017-resource-management-and-storage-policy.md),
  [DN-0030](DN-0030-typed-compiler-macros-and-hooks.md),
  [DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md),
  [DN-0035](DN-0035-region-memory-management-and-verified-providers.md),
  [DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](DN-0042-native-interaction-and-efficient-data.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This note is a working document for continued design. It records a long-term
> aim and an initial sketch, not a ready design. It is informative: it defines
> no current Ash semantics, accepts no architecture, and authorizes no
> implementation or prototype. The alternatives, contracts, and evidence below
> remain open to revision as the design develops.

## Question

Can Ash compile programs without a mandatory runtime, while libraries supply
the storage, control, and platform services a particular application needs?
Can compiler-supplied defaults and checked lowering make ordinary value
construction participate in that model without requiring explicit allocation
syntax or complex policy inference?

The working aim is that Ash impose no ambient allocator, collector, scheduler,
or runtime initialization. A program would select the services it needs and
could omit the corresponding machinery when those services are unnecessary.
Generated arithmetic, copying, checking, and cleanup code still occupies space
and performs work. Its presence must be accounted for even when no separate
runtime service is required.

## Context

### Motivation

Embedded and near-embedded applications make a mandatory runtime costly in
code size, memory use, and supported platforms. Selecting a fixed arena or
static storage could make a smaller application possible. Memory safety alone
would not establish bounded memory use, bounded work, or a real-time guarantee;
those claims need their own contracts and evidence.

A future native backend could also produce Ash libraries linked by other
languages. The host application should be able to call an exported function
without automatically starting an Ash evaluator, scheduler, or collector. Ash
could establish guarantees for checked code under stated foreign-entry and
provider contracts. This would not protect the entire process from arbitrary
foreign memory corruption or establish an external Ash ABI by itself.

Larger applications could opt into libraries providing managed storage,
scheduling, or other services. Several policies might coexist in one program.
The aim is to make the required services selectable and their assumptions
explicit, while preserving the guarantees each admitted composition claims.

### Current foundation and boundaries

The [current dynamic semantics](../../spec/dynamic-semantics.md) define an
evaluation heap, arbitrary-precision integers, lexical functions, ordinary
aggregate allocation, and recursive data. Ordinary allocation is not a
source-selectable storage effect. An empty source effect row therefore does
not imply allocation-free execution.

[Resource checking](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
tracks dependencies through values, captures, and operation metadata.
[Resource execution](../../spec/dynamic-semantics.md#scoped-cell-execution)
moves owned scopes through capture and resume; checked discard completes owned
abandoned resources. These are foundations for the proposed direction. Current
cell and native-buffer providers are sealed builtin relations, rather than
general library-authored memory or runtime providers.

[Elaboration](../../spec/elaboration.md#effect-core-lowering) currently retains
ordinary construction in shared value/computation families. Pure Core admits
no inhabited effect operations, and Effect Core retains exact computation
rows. Making ordinary construction effectful would cross those boundaries;
it is not already a supported lowering choice.

[AD-0007](../decisions/AD-0007-typed-core-dialects.md) requires typed dialects,
declared transform boundaries, and independent validation.
[AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md) selects the
current evaluator machine. These decisions do not select a native backend or
require a native executable to carry that evaluator.

### Relationship to other design work

[DN-0035](DN-0035-region-memory-management-and-verified-providers.md) owns the
broader memory-policy exploration, including implicit construction, storage
dependencies, provider verification, and allocation context across calls.
This note adds the no-default-runtime objective and a simpler initial route:
supply policy defaults to compilation before considering complex inference.
It does not settle DN-0035's lifetime or memory-model questions.

[DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md) explores Ash
calling foreign libraries. It explicitly excludes a stable external Ash ABI.
Foreign callers invoking compiled Ash add a separate entry, representation,
storage, and control boundary.
[DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md) supplies
pressure from captured control and completion; this note selects no suspension
or scheduling model. [DN-0030](DN-0030-typed-compiler-macros-and-hooks.md)
explores library participation in compilation without establishing the
configuration mechanism proposed here.

## Constraints

These are criteria for comparing candidates, not accepted language rules:

- Preserve checked authority, storage dependencies, and required completion
  through lowering and specialization.
- Preserve immutable sharing, closures, recursive data, and mathematical
  integer behavior wherever a candidate claims ordinary Ash compatibility.
- Make service requirements and unsupported target cases identifiable. A
  fixed-storage configuration must not silently introduce an auxiliary heap,
  collector, scheduler, or platform service.
- Separate policy selection from the acquisition of provider state and backing
  storage. Passive imports must not acquire runtime initialization semantics
  merely because they expose a provider library.
- Account for payload storage, provider metadata, closures, captured control,
  failure delivery, and cleanup when claiming a capacity or cost bound.
- State foreign assumptions and the trusted storage primitive boundary.
  Ordinary method signatures alone do not verify a provider's safety laws.

This note does not choose source syntax, machine integer semantics, a general
borrow system, an object-file format, or a stable ABI. It does not require
automatic lifetime inference, escaping suspension, multi-shot control,
parallelism, or a collector before the initial direction can be explored.

## Candidate directions

### Initial sketch: supplied defaults and checked lowering

The initial working preference is:

1. The application selects a library-provided policy as a compilation default.
2. Ordinary construction keeps its surface presentation. A typed lowering
   makes the required storage operations and provider relationships explicit.
3. Explicit scopes can override that default for scratch storage or other
   policies when their lifetime and completion contracts permit it.
4. The chosen provider realizes storage and reclamation. The compiler checks
   the required contracts and lowers or specializes the corresponding calls.
5. Services absent from the resulting program can be omitted from its artifact.

A supplied default is a policy choice made by the application. It need not be
a built-in allocator or a hidden process-wide runtime. The provider algorithm
could be selected statically while the caller supplies backing memory at entry.
Library selection, provider installation, and state acquisition still need a
specified relationship; this sketch chooses none of their source forms.

### Default lifetime and explicit precision

One conservative starting point would give ordinary values a single
application-owned storage domain. This avoids discovering short lifetimes
automatically and resembles the current retention of the evaluation heap.
It can retain unused storage for a long time, so it does not establish a useful
fixed-capacity bound for every application.

An invocation-owned arena is another option, especially for a foreign entry
that returns a scalar or writes into caller-owned output. Results referencing
that arena cannot outlive its completion. Caller-owned result storage could
support longer-lived results, under an explicit ownership and release contract.

Explicit nested scratch scopes could reclaim temporary storage sooner.
Checking an explicit scope's escape and completion rules is distinct from
inferring where every scope should be introduced. More precise placement or
reuse inference can be considered later when a concrete workload justifies it.

### Where storage effects belong

Uniform Core treatment leaves several semantic options:

| Option | Potential benefit | Question or cost |
| --- | --- | --- |
| Ordinary checked allocation effects, with surface elaboration inserting requests | Reuses effect and provider vocabulary; observable failure can be represented explicitly. | Hidden syntax still needs truthful function contracts; general handler behavior can constrain optimization and require control support. |
| A later typed storage dialect, with defaults supplied at its boundary | Keeps logical value construction separate from physical storage decisions; permits a checked native lowering. | Needs a preservation account relating storage, failure, and observations to the preceding dialect. |
| Provider requirements plus specialized construction operations | Can select direct calls or primitive storage without general continuation machinery. | May need a distinct operation contract and must demonstrate which existing mechanisms it actually reuses. |

These options can overlap. Sharing an operation representation does not settle
whether physical allocation has the same observable meaning as an ordinary
source effect. Keeping surface syntax also does not guarantee that every
current signature remains sufficient. Module summaries and compiled artifacts
must retain whatever requirements their consumers need to check.

### Storage policies worth comparing

| Policy | Useful case | Main pressure |
| --- | --- | --- |
| Static storage or verified stack placement | Fixed configuration and temporary bounded data. | Layout, recursion, escaping results, and captured control. |
| Fixed arena or pool | Embedded applications and caller-supplied buffers. | Exhaustion, fragmentation, metadata, and retention until completion. |
| Growable arena | Invocation or request processing with bulk release. | Backing acquisition, growth failure, and peak retained storage. |
| Reference-counted storage | Shared values needing earlier reclamation. | Count maintenance, overflow, cycles, and destruction work. |
| Traced storage | Long-lived shared or cyclic graphs. | Root completeness, collection work, and possible reference relocation. |

A policy need not offer every capability or the same costs. An arena can
reclaim cyclic data in bulk without finding unreachable cycles. Reference
counting alone does not reclaim every cycle. Moving collection needs an update
contract for every retained reference, including hidden captures.

One managed policy for ordinary values, with explicit providers only for
specialized values, remains a simpler comparison baseline. It preserves more
of the existing construction model but may impose services on all ordinary
programs. A restricted freestanding profile is another baseline: it could
admit only supported constructions or require explicit storage for selected
features. Such restrictions must be stated rather than inferred from a target
label.

### Compiled library requirements

Policy specialization could occur when compiling the final artifact, through
provider parameters at callable boundaries, or by producing separate instances
for selected policies. These choices trade code size against indirection,
separate compilation, and reuse. Selection time is separate from the lifetime
of each provider activation.

An exported library would need a contract covering symbols, calling convention,
representations, required services, backing storage, result validity, release,
and failure. Opaque handles, copying, caller-owned outputs, and checked borrowed
views are options with different obligations. A synchronous entry could handle
its effects internally. Suspension could instead use an explicit polling or
state-machine protocol. Crossing arbitrary foreign frames would require a
further control and platform contract.

## Semantic questions and corner cases

### Observable allocation and failure

Consider constructing an unused pair and then returning an integer. If its
allocation is unobservable, removing the pair can preserve the result. If a
provider reports exhaustion at that allocation, counts requests observably,
logs, or suspends, removing it can change behavior.

Candidate contracts include terminal exhaustion outside ordinary source error
handling, recoverable allocation failure carried by a checked effect, or a
capacity guarantee established before entry. The appropriate contract might
depend on the provision, but its interaction with ordinary construction and
optimization must be specified. Current internal capacity failure is not
already a recoverable construction effect.

Local state encapsulation gives evidence for hiding effects proven
unobservable. It does not justify erasing arbitrary provider behavior.
Placement freedom, bounds on consumed memory, exact allocation counts, and
guaranteed failure points are different promises.

### Results, closures, sharing, and recursive construction

Allocating an outer tuple in caller storage does not extend the lifetime of
its contained values. A returned closure can retain a table in a shorter-lived
region even if the closure record itself survives. Its own construction,
captured storage, and allocations when later invoked may involve different
contexts. Binding an existing value should not silently relocate or deep-copy
its data.

Recursive data adds initialization and partially constructed graph obligations.
A failure during construction must account for what has been published and
what remains owned. Region completion, individual reclamation, and effectful
resource cleanup need distinct contracts and a defined order.

### Provider and control foundations

A provider may need memory for bookkeeping, diagnostics, or failure results.
If those constructions request the same provider recursively, installation or
allocation can fail to establish a usable base. Candidate foundations include
preallocated state, explicit backing storage, an outer provider, and checked
primitives that do not request the operation being implemented.

Handlers and continuations also consume storage. Simple provider operations
might lower to direct calls, while suspension requires saved control and its
ownership. Lexical scoping or one-shot resumption alone does not prove that
this storage disappears. A scoped resource captured by control remains owned
while suspended; a textual block boundary is not itself a release event.

## Research and implementation references

These sources supply precedents and comparison questions. None establishes
that the proposed Ash composition is already safe or practical. Implementation
documentation was consulted on 10 October 2026; versioned links identify the
particular implementation documentation used where available.

- [Rust `core`](https://doc.rust-lang.org/stable/core/) separates a
  heap-unaware, platform-independent foundation from higher services, while
  documenting possible code-generation support symbols.
  [Rust `alloc`](https://doc.rust-lang.org/stable/alloc/) adds heap-owning
  facilities without requiring the full standard library. This supports the
  separation of services, but does not supply Ash's proposed scoped selection.
- [Rust `GlobalAlloc`](https://doc.rust-lang.org/core/alloc/trait.GlobalAlloc.html)
  explicitly permits allocation calls to be skipped, merged, or replaced by
  stack storage. It also warns about allocator re-entrance. This is a concrete
  contract for optimization and provider foundations, rather than a rule to
  import unchanged into Ash.
- [Zig 0.15.2 memory documentation](https://ziglang.org/documentation/0.15.2/#Memory)
  describes allocating functions accepting an allocator, including a fixed
  caller-owned buffer. Its
  [C library export example](https://ziglang.org/documentation/0.15.2/#Exporting-a-C-Library)
  supplies a foreign-callable artifact precedent. Zig leaves lifetime and
  ownership correctness to the programmer; Ash would need checked contracts.
- [Tofte and Talpin, *Region-Based Memory Management* (1997)](https://doi.org/10.1006/inco.1996.2613)
  develops type-and-effect region inference without assuming a collector,
  tested in MLKit with higher-order functions and recursive data. The
  [authors' retrospective](https://elsman.com/pdf/retro.pdf) and
  [MLKit manual](https://melsman.github.io/mlkit/pdf/mlkit-4.3.0.pdf) supply
  implementation context. These sources show functional programming can use
  regions, but do not make its inference machinery a prerequisite for
  compiler-supplied Ash defaults.
  [Aiken, Fähndrich, and Levien (1995)](https://www.microsoft.com/en-us/research/wp-content/uploads/1995/06/afl-pldi95.pdf)
  shows that more precise region placement can reduce retention, sometimes
  asymptotically. Safe lexical regions do not by themselves ensure small memory
  use.
- [Walker, Crary, and Morrisett, *Typed Memory Management via Static Capabilities*](https://www.cs.cmu.edu/~dpw/papers/capabilities-toplas-abstract.html)
  gives a typed intermediate language with explicit memory operations and
  statically checked permissions. Its safety checking does not require complex
  analysis of region lifetimes. This is evidence for separating explicit Core
  contracts from optional high-level placement inference, not a ready Ash
  provider interface.
- [Leijen, *Koka: Programming with Row Polymorphic Effect Types* (2014)](https://arxiv.org/abs/1406.2061)
  establishes local-state encapsulation analogous to Haskell's `runST`: local
  mutable-reference effects can disappear from an outer contract when their
  heap identity cannot escape. This concerns encapsulated state, rather than
  hiding arbitrary allocator behavior or all ordinary value allocation.
- [*Generalized Evidence Passing for Effect Handlers* (2021), extended report](https://www.microsoft.com/en-us/research/wp-content/uploads/2021/03/multip-tr-v2.pdf)
  compiles handlers to ordinary C without special continuation primitives.
  Selected paths avoid constructing continuations; full yields still represent
  them explicitly. This separates optional control machinery from the costs of
  operations that actually need it.
- [*Lexical Effect Handlers, Directly* (2024)](https://www.mc-pony.com/assets/documents/lexa-oopsla2024.pdf)
  treats tail-resumptive handlers as ordinary calls without reifying resumptions
  or allocating new stacks; general handlers in that strategy allocate stacks.
  [*Zero-Overhead Lexical Effect Handlers* (2025)](https://doi.org/10.1145/3763177)
  moves exceptional-effect handling work into runtime stack walks. These are
  different cost tradeoffs; efficient ordinary paths do not imply an absent
  runtime or zero total code size.
- [*Yarrow: Reconciling Effect Handlers and Region-Based Memory Management*, v2 (2026)](https://arxiv.org/abs/2607.15876v2)
  formalizes regions with one-shot and multi-shot control in Iris/Rocq and proves
  case studies. It addresses the disruption of region lifetimes by captured
  control. This is semantic and proof evidence, without a demonstrated native
  backend or measured embedded footprint.
- [OCaml 5.5 effect limitations](https://ocaml.org/manual/5.5/effects.html)
  prevent an effect from crossing a C callback boundary. This supplies a
  concrete foreign-control constraint, not an impossibility result for all
  implementations. [`libmprompt`](https://github.com/koka-lang/libmprompt)
  explores library-supplied delimited control compatible with C/C++ stacks,
  but requires 64-bit virtual address space and commits at least 4 KiB per
  active prompt. Its repository marks it incomplete and unsuitable for
  production; it is a comparison for control support, not an embedded solution.
- [*FP²: Fully in-Place Functional Programming* (2023)](https://webspace.science.uu.nl/~swier004/publications/2023-icfp.pdf)
  proves allocation-free, constant-stack execution for a specified calculus
  under uniqueness conditions, with an implementation in Koka. It suggests a
  route to checked reuse for selected programs. It does not show all ordinary
  functional construction can omit storage services.
- [Rust foreign linkage](https://doc.rust-lang.org/reference/linkage.html#staticlib),
  [panic policy](https://doc.rust-lang.org/reference/panic.html), and
  [undefined behavior](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)
  expose the packaging, failure, and foreign assumptions behind a callable
  native library. They motivate separate Ash contracts for entry and failure;
  linkage alone does not establish safety across a foreign boundary.

## Evidence and experiments

Further discussion can refine the contracts before code is needed. Useful
comparison cases include:

| Case | Evidence to seek | Contrary outcome |
| --- | --- | --- |
| Allocation-free exported computation | Artifact requirements contain no allocator, evaluator, scheduler, or initialization service; account for generated helpers. | An omitted service is still an undeclared link or startup dependency. |
| Ordinary data under a fixed provider | Backing memory and metadata respect the declared budget; exhaustion has the stated result. | Hidden heap fallback or unaccounted provider/control storage. |
| Repeated scratch computation | Completion permits storage reuse while preserving the same logical result. | Retention grows across completed iterations or surviving data becomes invalid. |
| Returned closure or shared graph | Captured and nested storage remains valid under the declared result contract. | Only the outer allocation survives, or hidden copying changes the contract. |
| Unused construction near exhaustion | Optimized and unspecialized executions agree under the chosen observability rules. | Optimization changes a promised failure, report, or request count. |
| Provider installation and failure | Initialization, bookkeeping, error delivery, and cleanup have a terminating storage path. | Allocation recursively invokes itself or failure reporting needs unavailable storage. |
| Foreign entry and callback | Data validity, ownership, control transfer, and cleanup obey the boundary contract. | Suspension crosses unsupported foreign frames or retained results outlive storage. |

Measure artifact size, required symbols and initialization, peak storage,
metadata, allocation and copying, and completion work. Separate semantic
preservation, memory safety, bounded capacity, and performance observations.
No particular optimizer success should be the sole basis of a claimed
freestanding guarantee; accepted configurations need a stated executable
meaning and service requirements.

This note does not yet authorize a prototype. If one becomes useful, first add
a bounded governing question, supported cases, comparison criteria, and
disposal or retention conditions. Experimental code would remain evidence;
product adoption would follow the proposal or decision and task workflow.

## Open questions

- Which allocation observations are part of the contract, especially
  exhaustion, counters, logging, and suspension?
- Do storage effects belong in source computation contracts, a later Core
  dialect, provider requirements, or some combination?
- Where are defaults supplied, and which requirements survive separate
  compilation and foreign export?
- What initial lifetime is sufficient for ordinary values and entry results?
  How do explicit overrides affect closures and existing aliases?
- Which provider laws are checked, proved, tested, or trusted, and how do those
  guarantees connect to actual storage primitives?
- How are control storage, recursive construction, partial failure, and
  required cleanup represented without introducing an implicit runtime?
- Which concrete workload justifies additional placement, reuse, or capacity
  inference beyond supplied defaults and explicit scopes?

As work continues, update the candidate descriptions and references with their
actual evidence and limits. Keep unresolved choices visible. A converged
language change belongs in a change proposal; a converged non-language choice
belongs in an architectural decision. This document remains the exploration
space rather than a substitute for either artifact.
