# Resource analysis algebra study

> Informative DN-0036 study owned by
> [TASK-0035](../../tasks/TASK-0035-resource-analysis-relevance-and-fusion.md).
> The [execution plan](analysis-plan.md) names implementation gates. Equations
> below describe proposed implementation equivalences, not new Ash rules.

## Semantic model and measured pressure

The compiler must preserve exact lexical Type/Row instantiation, resource
identity and inferred control obligations. See current
[type instantiation](../../../spec/dynamic-semantics.md#type-instantiation-and-erasure)
and [static semantics](../../../spec/static-semantics.md).
[AD-0007](../../decisions/AD-0007-typed-core-dialects.md) retains independent Core
validation; [AD-0008](../../decisions/AD-0008-explicit-evaluator-machine.md) retains
inspectable lexical environments. DN-0036 extends the implementation only in
its bounded experimental branch.

The current pipeline combines immutable typed syntax, finite value equations,
value and control graph construction, contextful live propagation, cleanup
inference/checking and public summary publication. Source checking and final
Core reconstruction call this machinery independently. These concern boundaries
do not require independent enumeration of every identical structural input;
their conclusions and authentication boundaries remain distinct.

Completed baseline receipt 274 establishes real contextual volume. In copying's
source analysis, 1,498 of 1,534 Invoke contexts are type applications; their
callees return Function nodes. Four exact wrappers account for 14,936 of
16,894 Invoke-origin lifetime slots. Evidence Calls independently account for
1,498 contexts and 14,778 lifetime slots. These populations are not additive
costs, first-pass slot measurements or proof of equivalent environments.

The wrappers are `read_null`, `read_empty`, `finish_copy` and `read_first` in the
exact source receipt. They carry one to five captured ports. Empty-environment
or simple forwarding shortcuts therefore do not cover the dominant class.
The NUL case has corresponding counts and its own source coordinates. Neither
String content nor SQL result size explains this static contextual volume.

## Typed stage inventory

The following are descriptive signatures of existing responsibilities. They
do not propose new Rust public APIs. Each borrowed slice denotes one exact
original revision and operation projection.

| Stage | Input | Output and completion boundary | Current source |
| --- | --- | --- | --- |
| Structural inventory | Typed nodes, globals, selected methods, domain | Exact binder/parameter maps, resource/discard flags | `capture.rs::build_capture_graph` |
| Finite values | Nodes, binder maps, imported callables | Completed ordered `Value` summaries; recursive rounds finish first | `capture.rs::solve_capture_values` |
| Lexical capture projection | Body root, term parameters, method routes, capture cuts | Ordered free binders after bound-binder filtering | `capture.rs::free_values_with_methods` |
| Metadata projection | Same original nodes, type/row binders, operation projection | Ordered surviving Type/Row identities, qualified subtree facts | `capture.rs::FunctionMetadataPreparation` |
| Evidence capture projection | Body root, original method/adapters, capture cuts | Ordered graph capture coordinates and original symbol actions | `value.rs::Graph::abstract_captures` |
| Value graph construction | Nodes, all three projections, imports, selected evidence | Original Expr/slot recipes and provenance | `value.rs::Graph::build_in_domain` |
| Control graph construction | Nodes, completed finite values, original value ports | Control code, callable/type inventory, source roots | `capture.rs::compile_with_boundary` |
| Contextual propagation | Graph, exact contexts, live ports | Growing ordered atoms/edges and completed transfer stamps | `value.rs::Analysis`, `control.rs::Analysis` |
| Cleanup and publication | Completed required equations and checked rows | Inferred cleanup requirements, validated capture summaries | `capture.rs::cleanup_requirements`, `check_builder` |

Source capture publication calls cleanup solving before `check_builder` in
`elaborate.rs::capture_completed_module_roots`. Final Core calls `check_nodes`
from its independently authenticated nodes. Fusing implementation traversals
cannot substitute a source-produced permission for that independent derivation.

## Candidate equivalence laws

### Composing maps

For total pure `g : A -> B` and `f : B -> C` over the same functor:

```text
map f . map g = map (f . g)
```

This can eliminate an intermediate carrier and one enumeration. The proposed
wrapper/evidence study must identify the actual A/B/C, exact environments and
coordinate-preserving transports before applying this law to its recipes.
Equal types, scalar results or equal current atom sets cannot replace those
inputs.

Fallible maps need a stronger law. Suppose `g(x1)` succeeds, `g(x2)` fails with
G and `f(g(x1))` fails with F. Separate left-to-right stages report G; interleaved
fusion reports F. Therefore value-level map composition alone does not preserve
the compiler's first error, source labels or publication. Fuse total structural
preparation, preserve the original validation barrier, or prove an appropriate
error/ordering equivalence for the selected carrier.

### Moving a map into its consumer

For a sequence, total pure `g` and an ordered accumulator step:

```text
foldl step z (map g xs)
  = foldl (\acc x -> step acc (g x)) z xs
```

The accumulator can consume a producer's structural recipe directly, avoiding
the mapped collection. Preserve source order and every required owned result.
For graph recipes, establish whether any independent consumer or focused query
observes the intermediate node before removing it.

### Product folds

For total independent folds over the same ordered input:

```text
(foldl a a0 xs, foldl b b0 xs)
  = foldl (\(u,v) x -> (a u x, b v x)) (a0,b0) xs
```

The components retain their types and results. A scope-sensitive structural
version carries inherited binders and selected evidence explicitly. The shared
driver is eligible only where each projected event stream agrees with the
original collector, including duplicate/reference order and per-concern cuts.

### Restricting an unfold by demand

Let `produce : A -> B`, `keep : B -> Bool` and a cheaper exact demand test
`needed : A -> Bool`. If `needed x = keep (produce x)` for every admitted x,
and producing a rejected x has no required observable obligation, then:

```text
filter keep (map produce xs)
  = map produce (filter needed xs)
```

The producer's dependency closure, errors and publication are part of the
precondition. Demand for one concern can be absent while a Function body's
other validation obligations remain. Unknown/open facts retain conservative
demand. An uncalled exported function or currently empty port is not a proof
of irrelevance.

### Unfold/fold elimination and fixed points

A producer/consumer composition over an acyclic structural carrier can compute
its final accumulator without retaining the entire intermediate tree. Recursive
bindings, live Unknown dependencies and cyclic graph edges require a separate
equation/fixed-point argument. Establish the actual domains, monotonicity,
termination, demanded projections and refusal boundaries before combining
solver stages or adopting a dependency-driven schedule.

## Source-grounded opportunities and contrary evidence

### F-1: wrapper and evidence transport composition

The dominant measured class is a type-wrapper Function returning another
Function. Current Call transfer constructs an exact Invoke context, installs
formal/actual and captured-port edges, and links the original body output.
Inner Function evaluation publishes its Closure with that Invoke creation and
feeds the mandatory symbolic body root. Evidence separately constructs its
exact Call context and installs capture/dictionary routes.

Study composing their immutable routing equations while retaining every live
environment edge. Required inputs include both original Function IDs, ordered
formal/captured metadata ports, the exact Type/Row substitution, original
evidence selection and the target creation context. Output remains a recipe
for the original contextual ports, not a cached Closure or atom set.

The main open condition is whether any intermediate coordinate/publication is
observable to control discovery or a focused cut. Keep those coordinates until
a preservation argument proves their removal. Common already owns a private
study of this class; this task supplies the typed composition and law review
rather than starting a second implementation.

### F-2: lexical and evidence capture product

For ordinary Functions, TypeAbstractions and handler clauses, current value
construction calls the lexical free-value collector, metadata collector and
abstract-evidence collector on the same body root. This is a concrete product
fold opportunity, with important projection differences:

- Lexical collection stops below a selected method replacement. Abstract
  evidence collection currently still descends there.
- Capture-port cuts contribute no free lexical binder, but contribute a
  retained abstract capture coordinate.
- Term binder filtering and Type/Row binder filtering have different domains.
- Abstract collection allocates symbols/evidence slots after lexical and
  metadata installation; moving those actions earlier changes graph IDs.

A candidate shared structural walk needs separate concern demand/visited state
and ordered output accumulators. It can collect an immutable evidence recipe
and replay it at the original publication point. A single visited set or one
global pruning decision is invalid for these different projections. Metadata's
existing compact subtree preparation should be reused; adding its traversal to
an already sufficient product may cost more than it saves.

This source opportunity has no whole-owner benefit measurement yet. It ranks
below the measured F-1 contextual volume until its gross work is known.

The first implementation slice uses these descriptive carriers:

```text
Body = (original nodes, root, operation projection)
LexicalInputs = (term parameters, method routes, capture-port cuts)
AbstractInputs = (original method records, adapter routes, capture-port cuts)
Projection = (ordered free binders, ordered deferred abstract recipe)

collect : (Body, LexicalInputs, AbstractInputs) -> Result Projection Failure
install_lexical : (Graph, ordered free binders) -> Result Graph Failure
install_metadata : (Graph, existing metadata output) -> Result Graph Failure
replay_abstract : (Graph, deferred abstract recipe) -> Result Graph Failure
```

These are proposed internal roles, not claims about current Rust signatures.
The recipe retains only capture ports and original method sites, plus an
abstract-phase invalid-input marker if needed. It allocates no graph symbol or
evidence slot. Replay consumes the original records and adapter routes.

The preservation argument has three obligations. Project the shared LIFO
visitation trace separately for lexical and abstract concerns, retaining each
concern's own visited state and cuts. Apply the original complete bound-binder
filter to lexical references, preserving their duplicates. Finally, replay
abstract actions after lexical and metadata installation, in original order,
using the original deduplication and adapter traversal. An abstract-only
invalid subtree must not preempt an earlier lexical or metadata failure.

A shared DAG node may first occur below a lexical method cut and later on an
active lexical path. An unqualified union visited set would lose that later
lexical visit. Per-concern visited bits preserve it while allowing common
child enumeration when both concerns are active. Charge recipe retention and
replay, the new state and all continued evidence-only walks. Completed-owner
measurements must establish whether this trade is beneficial.

### R-1: demand before contextual expansion

Infer a concern's required inputs from exact checked facts and backwards
dependencies. Test whether an immutable routing equation can carry a symbolic
input until its particular projection is required, without eagerly multiplying
contexts. All exported/uncalled body checks, complete Type/Row identity,
dictionary routes, captured-control obligations and late owners remain.

This is a relevance hypothesis. The current census proves contextual volume;
it does not prove those vertices irrelevant. A positive restriction law and
an actual suppressed producer operation are prerequisites to implementation.

### P-1: fixed-point scheduling

The finite-value solver scans all nodes until no result changes. Its scan
skeleton is O(rounds * nodes), with additional per-value work. A dependency
schedule could avoid unrelated reevaluation, but it must account for dynamic
callee targets, imported results and recursive substitutions. It must reach
the required completed result and preserve diagnostics. No measured saving or
accepted solver replacement follows from this source observation.

Common's dirty-edge study addresses the live graph's empty-prefix scans.
Share a completed event/phase design with that work; do not install an
independent cursor or duplicate observer.

## Initial execution result

The first source inventory establishes F-1 as the measured composition question
and F-2 as a concrete structural product with distinct concern cuts. It rejects
unqualified fallible map fusion, one global visited set, scalar-based owner
erasure and a second generic body-plan cache. R-1 remains a hypothesis requiring
an exact demand law. No shared Rust implementation or compiled rewrite result
is claimed.

The external evidence archive is
`/home/dikini/.codex/ash-provider-evidence/common-resource-support-2026-10-04/requested-root-metadata-160/`.
Receipt inputs are `author/context-prefix-measurement-runner-274/return.json`,
`bounds/actual-residual-decisions-274/report-corrected.md` and
`author/fanout-census-274/report.md`. Task progress distinguishes later retained
implementation from this read-only analysis.
