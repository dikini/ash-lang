# DN-0048: Pure Core Kernels and Parallel Lowering

- ID: `DN-0048`
- Status: exploring
- Related: [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md),
  [DN-0030](DN-0030-typed-compiler-macros-and-hooks.md),
  [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md),
  [DN-0034](DN-0034-one-shot-kernel-soundness-and-practicality.md),
  [DN-0040](DN-0040-floating-point-semantics-and-representation.md),
  [DN-0042](DN-0042-native-interaction-and-efficient-data.md),
  [DN-0044](DN-0044-no-default-runtime.md),
  [DN-0045](DN-0045-native-compilation-and-interactive-execution.md)

> This note is informative. It records a candidate direction: Pure Core first,
> an Ash-owned typed kernel IR, an optional interaction-net view, and later
> SIMD/GPU lowering. It defines no current Ash semantics, accepts no backend
> architecture, and authorizes no implementation or prototype. Experiments need
> separate scope before execution.

## Question

Can Ash expose enough typed iteration, dependency and sharing structure to
compile pure map/filter/reduce pipelines to SIMD and GPU execution while
preserving strict evaluation and the surrounding effect and cleanup behavior?

The working direction is to own the semantic kernel boundary in Ash. Give it
a scalar reference execution, preserve its evaluation obligations through
transforms, and choose a hardware schedule separately. Interaction nets may
help describe local dependencies and sharing; they need not become the
mandatory compiler IR or execution engine. Source proof constructs and more
general commutative effects remain future work.

## Context

### Current authority

The [Core dialect boundary](../../spec/elaboration.md#effect-core-lowering)
distinguishes Pure Core, with an uninhabited operation family and empty rows
throughout, from Effect Core. A computation with an empty outward effect row
can still contain handled effects, resource scopes or cleanup. Its row alone
does not establish the stronger Pure Core boundary.

The [dynamic semantics](../../spec/dynamic-semantics.md) evaluates function
before argument, bindings before their bodies, and aggregate operands from
left to right. A match evaluates its scrutinee once and runs only the selected
arm. Pure computations can diverge. Mathematical `Int` operations do not
silently become fixed-width arithmetic.

[Continuation capabilities](../../spec/static-semantics.md#effects) are
one-shot and cannot be ordinary duplicated or escaping values. Captured
control moves ownership. [Cleanup](../../spec/dynamic-semantics.md#scoped-cleanup-actions)
has an armed/running/done lifecycle; abandonment closes owned scopes rather
than executing their abandoned bodies. Copying an ordinary handle or a
closure containing a cleanup callback creates no new owner or cleanup duty.

[AD-0007](../decisions/AD-0007-typed-core-dialects.md) requires independent
validation, declared dialect boundaries, causal provenance and reference
executability for retained semantic Core dialects.
[AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md) supplies the
explicit evaluator baseline. Neither decision selects interaction nets,
SIMD, GPU execution or a native backend.

### Related exploration and downstream pressure

[DN-0030](DN-0030-typed-compiler-macros-and-hooks.md) already uses
`map f -> map g -> filter p -> reduce step seed` to explore typed transforms,
library-defined kernels and backend boundaries. This note narrows that
pressure to a candidate kernel contract. It does not select the hook or
registration mechanisms discussed there.

[DN-0032](DN-0032-algebra-of-scoped-resource-composition.md) distinguishes
operational behavior from conditional composition laws. Effect rows describe
requirements; their unordered presentation is not permission to exchange
computations. [DN-0045](DN-0045-native-compilation-and-interactive-execution.md)
places Ash-owned lowering within broader native compilation exploration.
[DN-0042](DN-0042-native-interaction-and-efficient-data.md) identifies missing
collection and representation questions; there is no current primitive
kernel collection contract to assume from the names `map` or `filter`.

Interaction nets offer local rewrite and sharing structure. SIMD/GPU lowering
also needs regular iteration domains, supported scalar operations, layout,
memory access and target synchronization. A dependency graph by itself does
not supply those properties.

## Constraints

- Start with actual validated Pure Core code. Do not admit Effect Core merely
  because a node has an empty outward row.
- Preserve required evaluation, values, termination behavior and selected
  branches. Producing the right answer on terminating examples is insufficient.
- Preserve source effect order, exact handler selection, one-shot control and
  ownership at the host boundary. No source concurrency is introduced here.
- Separate semantic completion from early value availability and from device
  submission. Cleanup follows completion of the work that uses its resources.
- Keep types, shapes, initialization, provenance and transform obligations
  independently checkable before backend lowering.
- Preserve mathematical integers. Numerical and storage contracts must state
  their target assumptions, failure behavior and fallback boundary.
- Treat laws as scoped transformation permissions. Purity alone grants neither
  associativity of a reducer nor arbitrary speculation of branches.

## Candidate directions

### Compiler boundary and alternatives

The candidate path is:

```text
validated Pure Core + authenticated pipeline meaning
    -> Ash KernelStructured: typed operations + scalar reference semantics
    -> fusion, dependency analysis and optional interaction-net view
    -> target legality, layout and schedule selection
    -> scalar loops | SIMD tiles | GPU kernels
```

`KernelStructured` is a working IR name. The alternative paths are direct
Pure Core lowering to ordinary loops, or an interaction-net execution path
used for the whole eligible program. Direct lowering has fewer retained
representations, but may obscure pipeline meaning before useful transforms.
A universal net path exposes sharing, but still needs to recover iteration
and layout and carries the burden of general control and storage semantics.
Compare these against the structured boundary rather than assuming an extra
IR is worthwhile.

Extraction needs the meaning of the actual function bodies or an authenticated
library contract. Recognizing the spelling `map` is insufficient. Initially,
restrict element data to finite acyclic first-order values and callbacks to
known Pure Core bodies with explicit ordinary captures. General cyclic values,
function-valued elements and observable graph topology need separate treatment.

The kernel validator would check scalar types, captured values, shapes,
selected-element order, dependency dominance, initialized output ranges and
source origins. Target validation additionally checks representability,
aliasing, bounds, control flow and synchronization. A Pure Core function can
be unsuitable for a device; unknown callees or unsupported captures keep the
scalar path.

### Typed map/filter/fold sketch

The following are compiler notation, not proposed source types or proof syntax.
Lengths may be static or established at entry.

| IR type | Meaning |
| --- | --- |
| `Seq<A,n>` | Finite ordered sequence of `n` initialized immutable values. |
| `ScalarFn<A,B>` | Available Pure Core callback and its explicit captures. |
| `StageDone<s>` | Every required evaluation of `s` completed normally. |
| `Mask<n>` | One predicate result for each input position. |
| `Selection<n,m>` | Ranks for one exact mask, with `0 <= m <= n`. |
| `Filtered<A,n>` | Internal package of `m` and a sequence `Seq<A,m>`. |

A stage completion witness is compiler bookkeeping, not a source continuation
capability. A ready element does not establish that its whole stage completed.

```text
kernel pipeline<A,B,C,R,n>(
    xs: Seq<A,n>,
    f: ScalarFn<A,B>, g: ScalarFn<B,C>,
    p: ScalarFn<C,Bool>, step: ScalarFn<(R,C),R>,
    seed: R, enter: StageDone<entry>
) -> R {
    ys, df = MapStrict(enter, xs, f)
    zs, dg = MapStrict(df, ys, g)
    filtered, dp = FilterStable(dg, zs, p)
    unpack filtered as (m, selected: Seq<C,m>)
    result, dr = FoldLeft(dp, selected, seed, step)
    Return(dr, result)
}
```

The reference interpreter runs each stage from left to right and completes it
before the next: every `f`, then every `g`, then every `p`, then the fold. The
fold starts with `r[0] = seed` and computes
`r[j+1] = step(r[j], selected[j])`. Empty selection returns `seed`.
`reduce` is represented as this ordered fold unless stronger laws justify a
different operation.

The parameters are already evaluated values. The enclosing Core application
tree determines when input, callback factories, captures and seed expressions
run; their source order need not be the visual pipeline order. Evaluate them
once before extraction or dispatch, and reuse those values for scalar fallback.

Stable filtering can expand into these operations:

```text
flags, dt = TestStrict(dg, zs, p)
selection, ds = ExclusiveRanks(dt, flags)
selected, dc = CompactStable(ds, zs, flags, selection)

rank[i] = count of true flags at positions less than i
m       = count of true flags
flags[i] implies selected[rank[i]] = zs[i]
```

All `n` predicate calls are required. Ranks belong to those exact flags;
substituting an unrelated mask invalidates the selection. Physical output may
reserve capacity `n`, but only its initialized prefix of length `m` is a
sequence result. Its unused tail contains no source values.

### Strictness, local gates and sharing

Separate three facts in a dependency or net view: `Ready(v)` means a value is
available; `Done(e)` means a required evaluation returned normally;
`Own(o)` means a unique control or resource obligation is held. None implies
either of the others. Stage completion joins the required `Done` facts even
when a downstream result does not use every value.

Candidate local gates have these meanings:

| Gate | Admission and completion condition |
| --- | --- |
| `Eval` | Evaluate a demanded scalar computation under its validated dialect. |
| `After` | Release ordered source work only after its predecessor completes. |
| `Select` | Require selector value and completion; demand its chosen arm. |
| `ForkPure` | Start independent demanded Pure Core work; keep its join. |
| `Join` | Complete only after every required child completes normally. |
| `UseOwner` | Transfer a unique obligation without copying or erasing it. |

These are semantic gate contracts, not a complete interaction-net signature
or rewrite system. A formal net encoding still needs typed ports, an explicit
translation of multi-input gates into local active pairs, rewrite rules and
a scheduling contract. Fair scheduling of required work is a premise of the
parallel interpretation.

`ForkPure` does not require totality when both children are already demanded:
if either diverges, the join never completes. It cannot fork an unchosen match
arm, a function body merely because its closure exists, or work conditional on
a filter result. `Select` requires both `Ready` and `Done` for its selector;
an early boolean value cannot bypass divergent scrutinee work. In a pure
region, physical scheduling may overlap work while
logical completion retains its source obligations. It must never release a
later source effect early. Speculation past an unresolved guard needs a
separate totality and target-safety argument.

Strictness forbids deleting an unused divergent initializer or replacing
`ignore(loop())` with its eventual constant result. Likewise, all-rejected
filter output does not license skipping preceding maps or predicate calls.
For `map f -> map g -> filter p`, all three callbacks are demanded for each
input. For `filter p -> map g`, `g` is demanded only for survivors. Moving it
before the filter can introduce divergence.

Fusion may avoid materializing intermediate sequences, provided it retains
all demanded scalar evaluations and their completion joins. Pure scheduling
can make later element work available before an earlier logical stage finishes;
the kernel still cannot return through a missing completion dependency.
Observable allocation failure or bounded execution budgets require a stated
target contract; equivalence of pure values and divergence does not settle
those resource observations.

Sharing completed ordinary values is distinct from sharing evaluation. A
shared computation must satisfy every use's demand obligation and preserve
termination and admitted observations. Fans or erasers cannot copy one-shot
capabilities or dispose of owners. A change in cyclic graph representation
can affect current observation; the initial finite acyclic subset avoids
claiming a general graph equivalence.

In the optional net view, maps expose independent demanded work and joins;
filter exposes tests, prefix dependencies and stable compaction; `FoldLeft`
is an ordered accumulator chain. A permitted tree reduction changes that
chain only under its own law contract. Local confluence of an interaction-net
system does not by itself establish equivalence to strict Ash or optimal
sharing. Lévy-optimal reduction concerns a particular account of duplicated
lambda reduction work, not device occupancy, memory traffic or elapsed time.
Differential interaction nets and their formal sums are a possible later
research direction, with no role required in the first kernel boundary.

### Purity, commutativity and reduction permissions

Use the validated Pure Core boundary initially, without requiring source proof
constructs. Record transform laws as compiler obligations, supported by
specific arguments and positive and negative evidence. Formal proofs can
later replace or strengthen that evidence.

Commutative computations concern exchanging independent evaluations while
preserving the ordered pair of their results and the admitted observations.
They do not mean that function composition commutes, or that a reducer is
associative. Dependencies still forbid exchange. Extension to effects must
identify the actual handlers, owners, failure behavior and observations for
which an exchange law holds; an effect label or row cannot grant it.

An arbitrary `step: (R,C) -> R` remains sequential. For the narrower homogeneous
case `op: (R,R) -> R`, associativity can permit contiguous nonempty chunk
reductions followed by ordered combination. The law must preserve definedness
as well as values for partial computations. Apply the original seed exactly
once at the left boundary. It need not be an identity. Empty chunks can carry
a validity flag; inventing a padding value or seeding every block requires an
additional identity law. Commutativity is needed only when input order changes.

Future laws worth proving or disproving include:

- Pure exchange and `ForkPure` join adequacy, including divergence and demand.
- Map fusion and filter fusion with their exact callback obligations.
- Stable scan and compaction, including shape and initialization preservation.
- Associativity, identity and optional commutativity of specific reducers.
- Safe masking: inactive lanes perform no forbidden source work or memory access.
- Numeric and layout refinements, including every intermediate representation.
- Host completion, unique continuation consumption and cleanup lifetime.
- Net translation correctness, sharing equivalence and any separately stated
  optimality claim.

### SIMD and GPU schedules

SIMD can tile the iteration space by a width `W`, with an active mask for
`i < n`. Each active input performs its demanded map and predicate work.
Prefix counts within a tile, plus counts from preceding tiles, preserve stable
output positions. The fold remains ordered unless its separate law permits a
tree. An ordinary result selection is not an execution mask: evaluating an
inactive branch can diverge or access invalid memory.

A GPU candidate uses an element kernel for maps and flags, a hierarchical
global prefix scan, stable compaction, and an ordered fold or authorized tree
reduction. Unordered atomic reservations do not implement stable filtering.
Tail threads avoid user callbacks but supply appropriate invalid or zero
partials where a collective requires participation. Workgroup barriers and
collectives require valid uniform participation. A general fold may stay on
the host or use a sequential device loop; accelerating maps and filtering
does not depend on making every reducer parallel.

MLIR is one adapter candidate. Its [Linalg dialect](https://mlir.llvm.org/docs/Dialects/Linalg/)
exposes iteration, indexing and reduction structure and supports fusion,
tiling and vector lowering. Its [GPU dialect](https://mlir.llvm.org/docs/Dialects/GPU/)
exposes launch dependencies and waits. These facilities are evidence about
possible lowering mechanisms; they do not discharge Ash's semantic or
ownership obligations or select MLIR as the backend.

Current mathematical `Int` needs bigint support or a checked machine-width
fast path whose bounds cover all intermediate results. Bounds for the original
left fold need not cover a reassociated tree. Ranks, dimensions and byte
offsets also need checked representations. Floating-point semantics remain
[exploratory](DN-0040-floating-point-semantics-and-representation.md); no
implicit reassociation or target arithmetic contract follows from this note.

### Host control, effects and cleanup

Keep the source continuation and resource owners on the host. A candidate
dispatch protocol evaluates operands once, selects a supported plan, prepares
storage, submits transfers and kernels, waits for required completion,
materializes the result, completes transport and temporary-storage duties,
and only then returns through the retained source continuation.

Device dependency tokens represent implementation work completion. They are
not Ash continuation capabilities and introduce no source suspension or
concurrency. Submission is not `StageDone`. Inputs, captures, output and
scratch storage must remain live until device access ends. Enclosing cleanup
cannot reclaim them merely because a launch returned.

Any enclosing live continuation capability stays with its host owner until
resume or discard consumes it. Kernel sharing never creates a second
capability. Ordinary evaluator return frames are not automatically source
continuation capabilities.
Owned abandonment must obey current inner-to-outer closure and running-cleanup
protection. The initial kernel performs no source effects and cannot capture
that control itself. General parallel Effect Core reduction is outside this
boundary: overlapping resource acquisition, effect order, failure order and
cleanup order can all change observations.

Pre-dispatch rejection can use scalar fallback with cached operands. After
device submission, failure handling must first settle outstanding work and
storage ownership under an explicit adapter contract. Blind restart is not a
completion protocol. Recoverable native failures and terminal resource reports
must retain their specified distinction; reliable cleanup does not promise
successful recovery from every terminal internal failure.

## Evidence and experiments

### Existing evidence and limits

Current specification and accepted Core decisions supply the source boundary
and reference behavior. They supply no kernel extractor, interaction-net
translation, vector backend, GPU backend or performance result for this design.

[Sinot's call-by-value token-passing encoding](https://lsv.ens-paris-saclay.fr/Publis/PAPERS/PDF/sinot-tlca05.pdf)
is prior work for evaluation-controlled nets; its parallel variant synchronizes
application after function and argument evaluation.
[Lamping's optimal reduction algorithm](https://doi.org/10.1145/96709.96711)
is prior work for sharing lambda reduction. Neither establishes an Ash theorem
about exact handlers, one-shot capabilities or cleanup. The gate contracts
above are candidate obligations, not a correctness proof.

The intended correctness argument has three boundaries. First, extraction
relates a recognized strict Core pipeline to the scalar kernel interpreter.
Second, each transform preserves values, demand and completion, with additional
laws for any reassociation or speculation. Third, target execution refines the
kernel under its stated numeric, memory, scheduling and failure assumptions;
the host protocol preserves the surrounding effect and ownership behavior.
A simulation or observational-equivalence result at one boundary does not
automatically establish the other two.

### Bounded comparison if separately authorized

The first experimental question would be whether an Ash-owned structured
kernel retains useful transform and validation information beyond direct Core
lowering, and whether a net view adds useful dependency or sharing information
without obscuring regular iteration.

Compare scalar reference execution, fused scalar loops, SIMD tiles and then
GPU execution on the same finite corpus. Add a net view only as a separate
comparison. Measure compilation cost, generated storage, transfers, kernel
launches and end-to-end execution alongside semantic checks. Count sharing
work separately from hardware performance.

Required comparison cases include empty, singleton and partial-tile inputs;
all-kept and all-rejected filters; stable output order; nonidentity seeds;
associative noncommutative reducers; diverging required maps whose values are
later rejected; divergence in selected versus unselected branches; reducers
that ignore their input value; masked bounds; integer intermediates; and
completion before enclosing cleanup. Finite timeout tests can expose errors
but cannot prove preservation of divergence.

Validate every retained semantic boundary independently and retain causal
origins. Check result, termination obligations and failure/lifetime behavior
under declared limits. Unsupported input must remain on the scalar path.
No speedup claim is useful without the transfer and completion costs or without
identifying which programs the target admits.

Discard prototype code when the bounded comparison ends unless a separate
decision retains it. Retain useful corpus cases, counterexamples, scoped
measurements and conclusions as design evidence. Promotion to product work
requires the appropriate decision, semantic proposal if needed, and active
implementation task; an encouraging experiment does not supply that authority.

## Open questions

- Which existing library pipeline bodies can establish the first extraction
  contract, and what finite data representations should the comparison admit?
- Should the kernel boundary be a retained executable Core dialect or a
  separately validated lowering IR with a scalar interpretation?
- Which strictness obligations remain explicit after fusion, and which can the
  validator reconstruct without fragile per-transform bookkeeping?
- Does a net view improve sharing or scheduling over an ordinary typed
  dependency graph enough to justify its translation and validation costs?
- What numeric, allocation, execution-budget and device-failure contract makes
  accelerated execution compatible with the admitted source observations?
- How should future law evidence be attached to a specific callback and
  representation without requiring source proof constructs now?
- Which commutative effect families, if any, can later cross this boundary
  without changing source resource capacity, failure or cleanup behavior?
