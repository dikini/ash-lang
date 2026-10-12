# DN-0045: Native Compilation and Interactive Execution

- ID: `DN-0045`
- Status: exploring
- Related: [AD-0001](../decisions/AD-0001-implementation-environment.md),
  [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md),
  [AD-0010](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md),
  [DN-0002](DN-0002-core-representation.md),
  [DN-0030](DN-0030-typed-compiler-macros-and-hooks.md),
  [DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md),
  [DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0044](DN-0044-no-default-runtime.md),
  [DN-0046](DN-0046-agent-semantic-exploration-and-feedback.md)

> This note is informative. It explores native compilation and interactive
> execution for human and AI programmers. It defines no current Ash semantics,
> accepts no backend or lowering architecture, and authorizes no implementation
> or prototype. The comparisons below need separate scope before execution.

## Question

How should Ash compile to machine code while supporting both ahead-of-time
(AOT) artifacts and interactive development? Which backend and Ash-owned
intermediate representations should it use, and where should continuation-
passing style (CPS) enter the pipeline?

Ash is intended for human and AI programmers. Both native delivery and rapid,
trustworthy feedback are design goals. Priority should follow representative
programming workflows and deployment needs, rather than treating compilation
speed and runtime performance as an audience choice.

## Context

### Current language and architecture

The [specification](../../spec/README.md) defines passive source modules,
rank-1 functions, interface evidence, effects and scoped resources. Linking
produces one validated program around the entry module's `main ()`; imports
have no runtime initialization. [Effect Core](../../spec/elaboration.md#effect-core-lowering)
retains exact computation rows and operation identities over shared ordinary
value and computation families.

[Current execution](../../spec/dynamic-semantics.md) includes mathematical
integers, lexical closures, ordinary aggregate storage and recursive data.
Ordinary allocation is not a source-selectable effect. An empty outward row
therefore establishes neither allocation-free execution nor absence of
internal continuation capture. Pure type operations erase, while Effect
execution retains lexical instantiation needed for exact operation matching.
Native lowering must preserve that distinction or justify specialization.

[AD-0001](../decisions/AD-0001-implementation-environment.md) selects Rust,
an initial interpreter, backend-independent shared representations and
isolated unsafe runtime, FFI or backend adapters. It expects later REPL, AOT
and JIT paths to reuse suitable components. It does not select a native backend.
[AD-0007](../decisions/AD-0007-typed-core-dialects.md) requires independent
validation and direct executability of retained semantic Core dialects.
Transforms declare their dialect boundaries and preserve causal provenance.
[AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md) selects explicit
first-order evaluator control, without accepting a native calling convention.

### FFI and storage pressure

[DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md) explores generated
typed native bridges linked into a host using the evaluator. This direction
does not compile Ash functions to machine code. Its checked target, signature,
conversion, access and completion contracts could serve both execution paths;
native lowering would still need independent verification. Foreign-library
ABIs and a stable external Ash ABI remain separate questions.

[DN-0044](DN-0044-no-default-runtime.md) explores selectable storage, control
and platform services. It is not an accepted storage design. Initial native
compilation needs a stated implementation for ordinary values and captured
control, while preserving room to compare service policies later. Compiled
code does not imply a collector, scheduler or evaluator, but required bigint,
allocation and completion services must be accounted for.

## Constraints

- Preserve values, strict evaluation order, lexical capture, recursive data,
  exact effect selection, resource dependencies and required completion.
- Keep backend types outside Core and shared transforms. Validate Ash-owned
  lowering boundaries before handing their results to a backend adapter.
- Retain current mathematical `Int` behavior. Machine-width fast paths need
  checked fallback or a proof that their range is sufficient.
- Preserve sharing and cycles wherever the native path claims compatibility.
  A reclamation policy must address the graphs it admits.
- Keep development and release modes semantically consistent. Necessary
  checking, ownership and control lowering cannot depend on optimization level.
- Preserve source relationships through lowering for diagnostics and debugging.
  Partial editor information must remain distinct from an accepted executable.
- State target and foreign-boundary assumptions. AD-0001's x86-64 and ARM64
  application-class reach supplies pressure; an initial Linux x86-64 comparison
  would not establish portability or introduce a microcontroller requirement.

## Candidate directions

### Shared services and two delivery paths

The working preference is one shared checking and lowering foundation, with
different compilation policies and artifact delivery:

```text
source -> resolution and checking -> validated Pure / Effect Core
       -> Ash control and representation lowering -> backend adapter
           -> native objects -> linked executable or library
           -> native code installed for interactive execution
```

This is a boundary sketch, not a fixed pass order. Pattern compilation,
specialization, closure conversion, control lowering and storage layout can
interact. Each retained boundary needs an explicit input, output and validation
contract. Neither full monomorphization nor CPS-to-Core reconstruction is a
prerequisite selected here.

AOT should support native delivery, reproducible builds and substantial
optimization. Interactive execution should reduce time to a useful result,
using less optimization and reusing unaffected work where sound. A JIT
generates and installs machine code during a session; incremental compilation
avoids repeating unaffected compiler work. These solve different costs.

Compiler state can persist without retaining every program's live state.
Source versions, imported facts, target settings and compiler options must
determine reuse. An edit to a type, effect or evidence fact can invalidate
consumers even when their text is unchanged. Explicit, resettable execution
contexts are a candidate starting point; hot replacement of code referenced
by live closures, handlers or resources needs a further lifetime contract.

### Human and AI feedback needs

Human interaction should make types, effects, dependencies and small execution
results available while a programmer develops an idea. AI interaction should
offer the same compiler knowledge through compact, structured observations,
with enough causal information to choose the next edit or experiment.

| Feedback capability | Human use | AI use |
| --- | --- | --- |
| Fast local checking | Keep consequences close to the edit | Reject invalid assumptions before broader generation |
| Small executable probes | Explore examples and debug behavior | Test a hypothesis or obtain a counterexample |
| Semantic queries | Understand types, evidence and dependencies | Retrieve checked facts instead of inferring them from text |
| Source-linked diagnostics | Explain a failure and its cause | Make a precise correction from structured evidence |
| Explicit execution state | Understand which experiment produced a result | Repeat, batch or compare experiments against known inputs |

[AD-0010](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md)
already separates human presentation from a schema-versioned JSON automation
contract. Future editor and agent interfaces should consume compiler-owned
facts rather than reconstruct semantics from rendered diagnostics.

The main measurement is time to a reliable answer: checking, lowering, code
generation, execution and reporting. Measure cold and warm runs, small edits,
broad invalidations and selected test workloads. A faster code generator may
still lose when slower generated code dominates execution; repeated front-end
work may dominate both backends. No universal latency target follows from the
human and AI distinction.

LSP is an intended tooling direction, not an implemented Ash service established
by this note. [DN-0046](DN-0046-agent-semantic-exploration-and-feedback.md)
depends on these shared checking, source-version and execution boundaries to
explore an agent interface combining navigation, semantic search and probes.
That dependency does not make completed optimizing AOT or JIT a prerequisite
for every interactive capability: the interpreter can supply early experiments.

### Backend alternatives

| Route | Capability | Comparison question |
| --- | --- | --- |
| Ash-owned lowering IRs to LLVM | Optimizing CPU backend, native objects and ORC JIT execution | Can one adapter meet both delivery and feedback goals? |
| Ash-owned lowering IRs through MLIR to LLVM | Progressive dialect lowering, rewrite infrastructure and reusable domain transformations | Does a concrete workload justify the additional framework and conversions? |
| Ash-owned lowering IRs to Cranelift | Rust implementation, AOT and JIT, emphasis on compilation speed | Does faster code generation improve the complete programming loop enough to justify it? |

LLVM's [object tutorial](https://llvm.org/docs/tutorial/MyFirstLanguageFrontend/LangImpl08.html)
and [ORC documentation](https://llvm.org/docs/ORCv2.html) establish that one
backend can support both delivery paths. Its [code generator](https://llvm.org/docs/CommandGuide/llc.html)
offers different optimization levels. These capabilities do not establish
Ash's latency. LLVM with a low-optimization development policy and an
optimizing release policy is the initial comparison preference.

[MLIR](https://mlir.llvm.org/docs/Rationale/Rationale/) is a framework for
multiple abstraction levels, not merely a tensor system. Its documented
[LLVM target](https://mlir.llvm.org/docs/TargetLLVMIR/) progressively converts
operations and translates them to LLVM IR. It does not supply Ash's handler
semantics. DN-0030's structured kernels could motivate its reusable lowering
machinery; ordinary compiler transformations could also justify it with evidence.

[Cranelift](https://cranelift.dev/) prioritizes compilation speed and supports
native AOT and JIT. Both interactive and standalone needs can be met by either
LLVM or Cranelift. Two native adapters become a candidate if measured
workflow costs justify their maintenance, rather than following automatically
from having two delivery paths.

### CPS and explicit control

Keep structured Effect Core as the semantic representation and compare a
separate control-lowering dialect. The [current handler rules](../../spec/dynamic-semantics.md#effect-handlers-and-completion)
move a one-shot, non-escaping capture through the nearest accepting exact
handler. The clause executes outside that segment. Resume restores its nesting,
then returns to any remaining work after the resume expression in the clause.

Discard completes recursively owned captures in structural order without
executing abandoned suffixes or restoring captured source handlers. Running
[cleanup](../../spec/dynamic-semantics.md#scoped-cleanup-actions) remains
required completion and may itself be captured and resumed. A control IR must
represent these boundaries; an ordinary return continuation alone is insufficient.

| Control route | Benefit | Obligation or cost |
| --- | --- | --- |
| Uniform CPS | One explicit control convention and a useful comparison baseline | Transform ordinary paths too; still represent delimited control, ownership and storage |
| Selective CPS | Keep proven ordinary paths direct and materialize saved control where needed | Sound classification and adapters for indirect or effect-polymorphic calls |
| Direct code with explicit yield propagation | Portable ordinary calls with saved state at yielding boundaries | Propagate requests and reconstruct the correct continuation and handler context |
| Direct code with a segmented-stack runtime | Transfer one-shot stack segments while retaining ordinary calls | Dedicated stack, target, foreign-boundary and ownership machinery |

Selective lowering must examine actual control behavior, not only outward rows.
A closed row can hide internal capture. Unknown higher-order calls and open
rows need conservative treatment. Existing [control summaries](../../spec/static-semantics.md#effects)
are relevant evidence, but do not yet define a native calling convention or
prove a selective-CPS analysis sufficient. Type and row specialization must
also preserve exact identities that may become equal.

Control convention and continuation representation are separate choices.
Uniform CPS, selective CPS and explicit yielding can all use first-order
continuation records. Local continuations can lower to blocks and branches;
CPS need not allocate a closure for every continuation. Captured control needs
explicit storage and completion ownership. If transfers become machine calls, bounded
stack use requires guaranteed tail transfers or a trampoline. LLVM's
[`tail` and `musttail`](https://llvm.org/docs/LangRef.html#call-instruction)
have different guarantees and ABI constraints. The evaluator decision does not
already establish a language-wide native proper-tail-call guarantee.

[Generalized Evidence Passing](https://www.microsoft.com/en-us/research/wp-content/uploads/2021/03/multip-tr-v2.pdf)
demonstrates an effect-handler translation using explicit yielding and
tail-resumption optimization in a C backend. It provides a comparison mechanism,
not a compiler-correctness result for Ash. DN-0033's one-shot experiments
likewise inform ownership obligations within their stated proof scope.

The working preference is explicit control lowering with selective direct
paths. A uniform CPS baseline should challenge that preference before it
becomes an accepted architecture. Supporting interactive use selects neither
CPS nor a particular continuation runtime by itself.

## Evidence and experiments

A separately scoped native experiment should distinguish backend integration
from control strategy. Begin with one backend and compare control candidates
on the same programs; compare a second backend only with sufficiently equivalent
lowering and service contracts to attribute differences.

The corpus should cover closures, recursive and shared data, mathematical
integers beyond machine range, polymorphic and indirect evidence calls, exact
effect matching after specialization, nested capture, work after resume,
recursive discard and cleanup reporting. Add the completed checked FFI case
when its governing contract is available. It is not evidence for callbacks,
borrowing or an external Ash ABI that the FFI work excludes.

Require independent lowered validation and differential execution against
retained Core for values, strict order, effect selection and completion.
Compare development and release policies, long control chains, native-stack
growth, continuation allocation and peak retained storage. Record target,
compiler and dependency pins; no platform claim follows from one host run.

Feedback comparisons should include finding and fixing a type or resource
failure, inspecting an indirect call, probing a small function, editing an
imported declaration and running selected tests. Record useful-answer latency,
source freshness, diagnostic quality, compilation cost, execution cost and
artifact size. Human exploratory tasks and agent repair loops should receive
separate observations rather than one assumed audience multiplier.

[DeLine and Fisher](https://www.microsoft.com/en-us/research/publication/supporting-exploratory-data-analysis-live-programming/)
found preference and fewer errors for live exploratory-data updates, with
comparable numbers of self-rated insightful results. [SWE-agent](https://arxiv.org/html/2405.15793v3)
found that action and feedback design affected repository-repair outcomes.
Their tasks support comparing useful feedback; neither study establishes an
Ash speed threshold, a required REPL model or a backend choice.

Retain source pins, cases, measurements and contrary findings as design
evidence. Dispose of prototype machinery after the comparison, or retain it
only as an explicitly isolated experiment with a reproducible scope. Product
retention requires an accepted architectural decision and task; a semantic
delta requires a change proposal, implementation, tests and specification update.

## Open questions

- Which Ash-owned lower boundaries make control, storage and source provenance
  independently reviewable without duplicating whole-program facts?
- Can LLVM meet both workflow goals before a second adapter becomes worthwhile?
- Which source and imported-fact changes invalidate cached checking and native
  code, and how should incomplete editor snapshots report their status?
- Which continuation representation preserves all completion rules with the
  least compilation and execution cost? Are existing summaries sufficient for
  selective lowering, especially across indirect and generic calls?
- Which initial ordinary storage policy preserves sharing and cycles while
  keeping DN-0044's service-selection questions open?
- How should compiled Ash libraries express entry, result lifetime, required
  services and failure without prematurely promising a stable external ABI?
- Which interactive experiments need native execution for faithful ABI and
  representation evidence, and which are adequately served by Core execution?
