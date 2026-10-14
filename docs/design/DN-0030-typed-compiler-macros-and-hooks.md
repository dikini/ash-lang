# DN-0030: Typed Compiler Macros and Declarative Hooks

- ID: `DN-0030`
- Status: exploring
- Related: [AD-0001: Implementation Environment](../decisions/AD-0001-implementation-environment.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [DN-0009: Effects, Handlers, and Continuations](DN-0009-effects-handlers-and-continuations.md), [DN-0011: Modules, Providers, and Resolution](DN-0011-modules-providers-and-resolution.md), [DN-0017: Resource Management and Storage Policy](DN-0017-resource-management-and-storage-policy.md), [DN-0019: Primitive Feature Composition](DN-0019-primitive-feature-composition.md), [DN-0026: Effect Ash Resource-First Milestones](DN-0026-effect-ash-resource-first-milestones.md)

> This work-in-progress design note records an unfinished exploration. It is
> informative, does not define current Ash, accept an architecture or language
> change, select a backend, or authorize implementation.

## Question

Can Ash libraries define typed compiler transformations and specialized code
without making library operations compiler intrinsics? Which declarative hooks,
registration scopes, and selection policies would let the compiler consider
those transformations at appropriate phases while preserving Ash semantics,
typed Core boundaries, diagnostics, separate compilation, and target choice?

The exploration is motivated by general compiler macros as well as future
data-parallel libraries. It does not assume that numerical compilation should
determine the general mechanism.

## Current boundary

The current [specification](../../spec/README.md) defines a rank-1 language
with passive statically linked modules, nominal data and `newtype`, interfaces,
and scoped exact evidence. It includes exact effect rows, requests, lexical
handlers, non-escaping one-shot resume/discard, scoped cells and native buffers,
synchronous runtime hooks, and cleanup. The builtin resources are closed
compiler-owned APIs; they do not establish general library-defined providers
or FFI.

Compiler macros, declarative compiler hooks, optimization annotations, staged
evaluation, a native code backend, arrays/tensors, floating-point types, and
fixed-width source integer types remain outside the specification. In
particular, synchronous runtime hooks do not supply compiler-phase hooks, and
lexical handlers do not have the compile/link behavior hypothesized below.

[DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md) retains
bounded provider, SQLite, and scalar Arena experiments on `main`, using
Rust-authored contracts and native adapters. They are experimental evidence,
not product adoption. [DN-0019](DN-0019-primitive-feature-composition.md)
retains a separate Float composition prototype. Neither experiment implements
this note's macro or staged-handler model.

The implemented foundation is typed Core with independent validation and the
specified effect/resource contracts. This note's transformations,
registrations, selection policy, phase behavior, and specialized kernels
remain open design work. No macro prototype or product implementation is
claimed. See the [scope summary](README.md#implementation-and-evidence-boundaries)
for related notes' implementation and evidence boundaries.

[AD-0001](../decisions/AD-0001-implementation-environment.md) permits MLIR as a
future lowering target but requires LLVM, MLIR, Cranelift, and other backend
types to remain outside Ash Core and its shared transformations. Backend
adapters consume Ash-owned lower representations. A library transformation
that eventually uses MLIR must preserve that boundary.

[AD-0007](../decisions/AD-0007-typed-core-dialects.md) gives the exploration a
transferable structure: retained Core dialects are closed and typed;
transformations declare input and output dialects, preserve or rebuild causal
provenance, and submit their result to independent validation. Construction
APIs do not replace validation. This decision does not accept a macro system,
an optimization dialect, effects, handler semantics, or concrete continuation
modes.

[DN-0009](DN-0009-effects-handlers-and-continuations.md),
[DN-0011](DN-0011-modules-providers-and-resolution.md), and
[DN-0026](DN-0026-effect-ash-resource-first-milestones.md) provide exploratory
pressure from effects, ordered handlers, providers, continuations, resolution
at different stages, resources, and future dynamic composition. They do not
make the staged-handler model below current or accepted Ash.

## Motivating direction

Ash is intended to remain a general-purpose functional language rather than a
numerical DSL. A later library should nevertheless be able to express regular
data-parallel work, including array and table pipelines, specialized kernels,
multicore execution, and SIMD lowering.
[Repa](https://discus-lang.org/papers/2010-rarrays/repa-icfp2010.pdf),
[Accelerate](https://www.acceleratehs.org/documentation/users-guide/language.html),
and [Data Parallel Haskell](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSTTCS.2008.1769)
provide different evidence that useful parallelism requires the compiler to
retain bulk operations, shapes, reductions, or nested parallel structure
rather than recover them from arbitrary scalar recursion.

MLIR is relevant because its dialects retain several abstraction levels. A
future Ash-owned structured-kernel representation could lower through MLIR
[`linalg`](https://mlir.llvm.org/docs/Dialects/Linalg/), tensor,
[bufferization](https://mlir.llvm.org/docs/Bufferization/), vector, loop, GPU,
or [LLVM](https://mlir.llvm.org/docs/TargetLLVMIR/) dialects without making
those dialects Ash semantics. MLIR supplies transformation and lowering
machinery; it does not decide which Ash computation is a kernel, whether
parallel execution is legal, or which candidate optimization should run.

The same macro and hook mechanism should also support non-numerical examples.
A mechanism justified only by Linalg would not establish that it belongs in a
general compiler.

## Working distinctions

The brainstorm currently separates the following concerns:

| Concern | Question answered |
| --- | --- |
| Compiler-structure type | What meaningful program or compiler structure does a value represent? |
| Macro type | Could this transformation consume the available structure and produce a structure accepted by a later phase? |
| Availability | Is the macro definition visible to this compilation? |
| Registration | At which compiler hook is the macro a candidate? |
| Scope | In which program region is that registration active? |
| Selection policy | Should an applicable candidate run, and in what order with other candidates? |
| Validation | Does the produced structure satisfy its independent invariants? |

These questions must not collapse. In particular, aligned types establish only
that a macro could be used. They do not decide whether it is registered, where
it is active, whether it is profitable, or whether the compiler should select
it.

## Typed compiler macros

The working meaning of *macro* is broader than surface-syntax expansion:

```text
macro = function from one meaningful typed compiler structure
        to another meaningful typed compiler structure
```

The function's input and output types describe possible composition. Examples
could include resolved syntax to resolved declarations, structured patterns to
decision Core, one typed Core dialect to another, a linked program to a
specialized program, or an Ash-owned structured kernel to backend IR. These are
examples of type relationships, not accepted type names or compiler phases.

A macro may require compiler effects such as diagnostics, authenticated fresh
identities, declared build inputs, or target facts. Such effects describe what
the macro may request while running. They do not select the macro or grant it
authority to forge Core facts.

Compiler structures may become available at different times. A function that
requires a linked-program structure cannot run before linking produces one. A
function requiring target facts cannot run before a target is selected. This
type-level availability still does not schedule the function; a hook and
selection mechanism do that separately.

Macros are independent of providers. Ordinary library code, compiler tooling,
handlers, or providers may use them. A provider is one important consumer: a
SIMD provider might call general fusion, tiling, or structured-kernel lowering
macros while implementing its compile or link behavior. The macro mechanism
does not own the provider relationship or become active merely because a
provider exists.

Two correctness obligations remain distinct:

- A generative macro can define a program fragment through its validated
  expansion.
- An optimization or lowering macro transforms an already meaningful program
  and therefore needs evidence that it preserves or implements the applicable
  observations in addition to structural type compatibility.

Input and output types can expose some preservation obligations. They cannot by
themselves establish arbitrary semantic equivalence. Independent validation,
differential execution, laws, proofs, or other evidence may be required; this
note does not select one universal method.

## Declarative compiler hooks

The preferred current direction is declarative registration. A compiler hook
names a stable representation boundary and its invariants rather than a Rust
function or incidental pass position. A registration makes one macro a
candidate at one compatible hook under a stated scope. Registration does not
mean unconditional execution.

Possible hooks might occur after resolution, after typed elaboration, before
pattern compilation, after handler elaboration, after linking, before kernel
lowering, or before backend lowering. This list is illustrative. Concrete
examples must justify both the retained boundary and the structures exposed by
it before Ash accepts a hook catalogue.

A hook should provide enough information to answer:

- which input structure and invariants are available;
- which output structures may continue through the pipeline;
- which program region the candidate may inspect or replace;
- which compiler facts and effects the macro may request;
- how provenance and diagnostics cross the boundary;
- how the output is validated; and
- how failure or non-selection returns to a defined fallback.

The exploration currently favors collecting registrations declaratively before
running a phase. An effect scope, module, build description, backend, or
explicit macro use could contribute a scoped registration without mutating the
candidate set during traversal. This preference requires comparison. It is not
an accepted ban on dynamically established compiler context.

## Scope and compilation unit

The same transformation at a wider scope receives different authority and
creates different invalidation and correctness obligations:

| Scope | Available knowledge | Main constraints |
| --- | --- | --- |
| Expression or handler region | Exact local computation and installed context | Unknown callees and surrounding code remain opaque. |
| Definition | One typed body and its captures | The declared external contract must remain valid. |
| Module | Private bodies, exports, and imported summaries | Imported implementations cannot be assumed. |
| Separately compiled package | Published IR or summaries | ABI, cache, version, and invalidation boundaries matter. |
| Linked program | Selected modules, handlers, and providers | High-level bodies or summaries must survive until this stage. |
| Closed whole program | All reachable definitions and resolved identities | The closed-world claim fails when loading or unresolved providers remain. |
| Backend region | Concrete target, ABI, and data layout | The result may be target-specific and less portable. |

These scopes may justify different compiler-structure types rather than one
generic Core value with an unchecked scope flag. The exact type inventory is
open. The useful property is that a macro cannot inspect facts its input
structure does not expose.

Possible registration scopes include global compiler configuration, a module,
a definition, an explicitly delimited program region, an installed handler,
an effect operation family, a provider, or a backend. These mechanisms may
coexist. Importing a package, making a macro available, activating a
registration, and selecting a macro are separate events whose exact
relationships remain unresolved.

## Effects, handlers, providers, and phases

A related working hypothesis gives every installed handler distinct compile,
link, and runtime behavior. The phase distinction belongs to the handler, not
to each individual effect operation.

Under this hypothesis, explicit handler installation defines a delimited
compile-time context. Handler identity and order determine which interpretation
surrounds the scoped computation. A provider supplies implementation or
resource details required by that interpretation. Compile behavior may retain
or transform meaningful structure; link behavior may use whole-program and
target facts; runtime behavior executes the residual operational work.

For example, an installed `SimdArray` handler could delimit a pipeline of array
operations. Its provider could supply implementations for some operations in
that context. Compile behavior might preserve a structured kernel, link
behavior might select and specialize an x86-64 or ARM64 implementation, and
runtime behavior might manage buffers and invoke the resulting kernel. These
names and behaviors are examples, not proposed Ash syntax or accepted
semantics.

Continuation and resource modes constrain every phase. Candidate modes include
exactly-once, at-most-once, duplicable, abortive, and escaping behavior, with
corresponding capture, discard, replay, lifetime, and resource obligations. A
parallel array handler need not duplicate the continuation surrounding the
whole pipeline. One candidate instead duplicates only an eligible element
computation, joins the parallel work, and resumes the outer continuation once.

Effects and handler scopes are possible ways to contribute macro
registrations, but macros remain independent. Other global, module, local,
link, or backend mechanisms may register the same typed transformation.

## Annotations

Annotations entered the discussion as a possible convenience for directing
specialized compilation. The preferred ideal is that they are unnecessary:
effect identities, handler installation, provider relationships, compiler-
structure types, macro types, registrations, and scope may already expose the
required facts.

If later evidence justifies annotations, deleting an optimization annotation
should preserve program meaning. An annotation must not replace effect,
continuation, resource, type, or Core validation. This note does not reserve
syntax or accept an annotation mechanism.

## Candidate registration and selection directions

### Explicit macro application

An Ash program or library explicitly applies an imported macro. This makes use
and local scope visible, but explicit source use alone does not address module,
link, whole-program, or backend pipelines.

### Scoped declarative registration

A module, definition, handler installation, effect context, provider, backend,
or build description contributes a declarative candidate registration for a
bounded region. This retains inspectable scope without requiring every source
operation to invoke the macro directly. It leaves ordering and selection to a
separate policy.

### Global declarative pipeline

Compiler or package configuration registers candidates globally at named
hooks. This can support whole-program optimization and stable default
pipelines, but import-driven ambient behavior, ordering, reproducibility, and
incremental invalidation require explicit evidence.

These directions can coexist. No direction yet determines whether one
applicable macro should run. Possible policies include an explicit pipeline,
a provider or backend policy, compiler defaults, target rules, a cost model,
bounded search, or mandatory expansion for a construct whose meaning requires
it. Selecting none must remain valid for an optional optimization with a
fallback. The exploration has not selected priorities, conflict resolution,
iteration to a fixed point, or a cost model.

## Data-parallel example

A first comparison can use one regular pipeline:

```text
map f -> map g -> filter p -> reduce combine initial
```

Place the same computation in progressively wider contexts:

1. all operations inside one explicitly handled region;
2. operations split across private definitions in one module;
3. operations split across exported definitions in separately compiled
   modules;
4. those modules linked with typed bodies available;
5. those modules linked through summaries only;
6. a closed program with a concrete SIMD target; and
7. a program whose provider selection remains until runtime.

A custom optimization kernel can also be a library macro explicitly used by an
Ash program. The macro receives meaningful typed compiler structures and
returns another meaningful typed structure. A portable candidate would produce
an Ash-owned structured-kernel representation; a backend-phase candidate could
lower such a representation to MLIR Linalg. The comparison must not assume
that either boundary is correct before measuring it.

For each placement, record:

- which macros are type-compatible;
- which hooks and scopes can register them;
- which bodies, summaries, effect facts, continuation modes, resource facts,
  target facts, and provider identities are visible;
- which fusion, specialization, parallelization, or vectorization is legal;
- what changes trigger recompilation or relinking;
- which fallback remains when no candidate is selected;
- how failures identify the macro, registration, transformed region, and
  originating Ash source; and
- whether pre- and post-transform observations agree where equivalence is
  required.

A second, non-numerical case should exercise the same hooks. Handler
specialization, provider erasure, pattern compilation, or protocol-state
elimination are possible candidates. The comparison should reject a hook model
that works only because array operations have a convenient scalar shape.

## Constraints

- Current Ash semantics remain authoritative and unchanged.
- Backend-specific types do not enter Ash Core or its shared transformations.
- Macro applicability, registration, scope, selection, execution, and
  validation remain distinct.
- Handler order is preserved unless checked evidence justifies a reordering.
- Effect-row membership alone does not prove operation commutativity.
- A transformation cannot duplicate or discard a continuation, capture, or
  resource without the applicable checked permission.
- Every produced retained Core representation receives independent validation.
- Transformations preserve or rebuild causal provenance for diagnostics.
- Separate compilation does not silently become a closed-world build.
- Optional optimization has a defined non-selection path.
- Imported packages do not gain ambient compiler authority merely by being
  imported unless a future accepted design explicitly defines that behavior.

## Intentional exclusions

This note does not select MLIR, LLVM, Cranelift, a machine ABI, an array model,
a numeric type family, a macro syntax, annotations, quotation syntax, a plugin
ABI, dynamic native plugins, a compiler-structure representation, a hook
catalogue, an optimization policy, a cost model, or handler and continuation
semantics. It does not authorize a prototype or product implementation.

## Evidence and experiments

The next design work should specify examples before mechanisms. The array
pipeline above should compare local, module, separate-compilation, link,
whole-program, and backend scopes using the same semantics and observations.
Only after that comparison should a later note propose the smallest compiler
structures and hooks required by the cases.

If executable evidence becomes necessary, a separately authorized disposable
prototype should test one named question, such as whether a typed library macro
can preserve enough kernel structure across a module boundary for a Linalg
lowering without exposing MLIR in Core. It must compare at least one rejected
unsafe transformation and one non-selected fallback. Retain measurements and
counterexamples; discard prototype machinery unless a later decision and task
adopt it.

## Open questions

- Which first non-numerical macro gives a structurally different comparison?
- Which compiler structures should libraries inspect directly, and which need
  abstract validated construction and traversal APIs?
- Which phase boundaries are stable enough to become public hooks?
- Does importing a macro registration make it available, active, or neither?
- How do nested global, module, handler, effect, provider, and backend scopes
  compose?
- Which registrations define required expansion, and which offer optional
  optimization?
- Who selects among several compatible macros, and how are order, conflict,
  repetition, termination, and resource budgets controlled?
- What semantic evidence must an optimization or lowering macro return beyond
  a structurally valid output?
- Which typed bodies or summaries may cross separate-compilation boundaries?
- How do macro definitions and registrations participate in cache keys and
  incremental invalidation?
- Which compile-time effects may a macro request, and how are declared build
  inputs and reproducibility enforced?
- How do diagnostics retain both macro-definition and macro-invocation
  provenance through several transformations?
- How do link-time optimization and future dynamic loading coexist without a
  false closed-world assumption?
- Which target facts are available before native linking, and which require
  residual runtime dispatch?
- Can custom kernels preserve ordinary Ash fallback behavior without requiring
  annotations or compiler-known library names?
- How do floating-point reassociation, reduction laws, failure, cancellation,
  and resource cleanup constrain data-parallel selection?
