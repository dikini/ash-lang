# Resource analysis algebra study

> Informative [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md)
> study retained after TASK-0035 execution was superseded. The
> [disposition](analysis-closure.md) records retained and rejected results.
> Equations below describe proposed implementation equivalences, not new Ash rules.

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

### Bottoms, demand and Rust formulation

Algebraic equational reasoning remains the derivation method. Use fission to
expose typed stages and dependencies, and fusion to eliminate repeated work.
Types, demand and behavior at bottom supply the laws' premises; then express
the derived algorithm in Rust. Explicit deferred inputs, continuations or
worklists can express the required demand in an eager language.

The main semantic distinction is behavior at bottom, `⊥`: a computation
that is undefined or does not terminate in the chosen semantic model. A rewrite
can agree on all total results yet change which partial computations it demands.

For example, in a lazy model choose `h`, `a` and `b` as constant-zero functions.
The algebra equation `h . a = b . fmap h` holds, but a fold that must inspect its
input satisfies:

```text
h (fold a ⊥) = 0
fold b ⊥     = ⊥
```

The total finite-input induction below intentionally excludes this case. To
extend a law to partial values, prove definedness as well as value equality and
state its strictness/continuity conditions. For the usual fold-fusion theorem,
strictness of `h` means `h ⊥ = ⊥`; Gibbons explicitly notes strictness conditions
in [sections 2.5–2.6](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/fission.pdf).
Otherwise justify totality for the admitted inputs or derive a formulation that
preserves the required demand without imposing that theorem unchanged.

An explicit `Err`, an analysis `Unknown` or a not-yet-populated graph port is
not automatically semantic bottom. The least fact in a dataflow lattice and
nontermination are distinct unless a model explicitly relates them. Preserve
returned errors and relevant panic/unwind observations separately.

The equations below therefore need both a semantic argument and a Rust
execution/cost argument for their chosen formulation. Rust
evaluates ordinary call operands before entering the call, in source order;
see the [Rust Reference](https://doc.rust-lang.org/reference/expressions.html#evaluation-order-of-operands).
An eager recursive fold computes child results before the parent algebra can
discard them. To avoid that work, test demand before descending or creating
the context, using an explicit control path, worklist or deferred computation.

Rust's [iterator adapters are lazy](https://doc.rust-lang.org/std/iter/index.html#laziness).
`iter.map(g).map(f)` pulls through both adapters when consumed; it does not
materialize two collections. In contrast, collecting the first map into a
`Vec` completes that phase before a later consumer starts. Removing that
collection interleaves producer and consumer actions and changes intermediate
lifetimes. The fallible-map counterexample below concerns such a phase barrier,
not a barrier inherent in chained iterator adapters.

A direct Rust accumulator fold evaluates each update eagerly. Deferred fields
or steps require an explicit representation. A directly recursive unfold that
builds an owned tree similarly constructs that tree eagerly; streaming requires
an iterator, worklist or other deferred representation. The finite total
structural equalities below remain usable, but do not by themselves establish
productivity, definedness on partial inputs or space behavior.

For each rewrite, name the actual schedule and preserve required error,
publication and destruction order, including relevant panic/unwind boundaries.
Product fusion changes two complete concern passes into interleaved updates;
deferred recipes may be needed to keep the original fallible phase. Account for
moves, clones, allocations, retained borrows, accumulator/recipe storage and
stack depth. Lower the mathematical recursion to the compiler's bounded
iterative machinery where deep inputs require it.

Neither an iterator nor an `Environment -> Summary` closure automatically
memoizes results. Replaying it for each context can retain the original growing
factor. Any sharing must be explicit and justified by the exact input-dependence
proof. Do not count an already-streaming map chain as eliminated traversals or
claim an asymptotic gain from removing a fixed number of materialized passes.

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

### Derivation method for the next batch

The user selected equational reasoning and inductive decomposition as the next
priority. F-2 establishes a constant-factor reduction. The larger objective is
to remove repeated work whose frequency grows with program structure, demanded
contexts or solver rounds.

Gibbons's [Fission for Program Comprehension, sections 2.5–2.6](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/fission.pdf)
describes recovering recursive structure, fold fusion and eliminating an
unfold/fold intermediary. The following is this study's derivation framework
for Ash, not a claim that its effectful graph solver is already a tree fold.

Start with a finite, well-founded ordered structural model. Let `F` describe one
layer, `Tree` its recursive carrier, and `in : F Tree -> Tree` its constructor.
For total functions and a lawful `fmap`, use these types and obligation:

```text
a : F A -> A
b : F B -> B
h : A -> B

h . a = b . fmap h
```

The obligation permits an induction over the input constructor:

```text
h (fold a (in children))
  = h (a (fmap (fold a) children))
  = b (fmap h (fmap (fold a) children))
  = b (fmap (fold b) children)
  = fold b (in children)
```

The second equality uses the algebra obligation; the third uses map composition
and the inductive hypotheses for the children. Check each constructor, including
binding and nullary cases. Where inherited scope matters, the carrier can be
`Environment -> Summary`; the environment includes exact Type/Row substitutions,
term ownership, selected evidence and concern demand. Original node identities
remain labels. Equal current results do not identify environments.

If the obligation fails because the parent lacks a child fact, strengthen the
inductive result to a product of primary and auxiliary facts. Derive one algebra
over that product and project the requested result afterward. The auxiliary
component is justified by a specific repeated subcomputation, rather than a
general cache. Include its construction, merge and storage costs. A growing
descendant set copied at every parent can retain quadratic work even when the
driver visits each node once.

For producer/consumer elimination, let `u : Seed -> F Seed` and `a : F A -> A`.
When the generated structure is finite and total, the fused equation is:

```text
solve seed = a (fmap solve (u seed))
solve = fold a . unfold u
```

Removing the intermediate structure alone need not change the asymptotic bound.
An Ash candidate must name the repeated producer or consumer work it removes.
For graph inputs, preserve sharing by original identities and the exact inherited
state. Treating a shared DAG as a tree can itself create exponential work;
combining summaries with different inherited environments is unsound. Cycles
require a fixed-point argument, not structural induction alone.

Fallible preparation and live installation are separate obligations. Equality of
completed results must also preserve required validation, diagnostic order,
symbolic roots, live dependencies and observable publication. A pure routing
equation does not by itself authorize deleting an intermediate queried port.
The first F-2 experiment retains its phase barrier for precisely this reason.

### Cost obligations and candidate ranking

Use explicit independent parameters: original nodes `n`, structural edges `e`,
requested roots `q`, exact demanded contexts `c`, solver rounds `r`, and produced
facts or live updates `p`. Do not hide an increasing environment or summary size
inside a constant local step.

| Candidate family | Existing cost skeleton | Desired elimination and proof gap |
| --- | --- | --- |
| Contextful wrapper/evidence transport | Shared static preparation plus routing/install work for each exact context | Compose inherited routing equations and demand before materialization; prove which intermediate work is unobserved without merging distinct required environments or losing live edges |
| Nested root/body analysis | Sum of visited body sizes; nested chain can give `T(n) = T(n-1) + Theta(n)` | Strengthened child results could give a constant local step, but prove scope/DAG/order laws and account for summary merges and output size |
| Whole-graph finite-value rounds | `Theta(r*n)` node-scan skeleton plus value copying, joins and instantiation | Derive dependencies and update consumers incrementally; prove fixed-point equality, dynamic target discovery and ordered diagnostics |

The first row has measured contextual volume, but the existing immutable
capture topology is already shared. A second topology cache cannot eliminate
that contextual factor. The second row is a source-grounded candidate family,
not a measured explanation of the remaining SQLite cost. A linear-time target
is conditional on bounded local combination and output; explicit output may
itself be quadratic. The third row describes the actual scan in
`solve_capture_values`, not proof that its current round count dominates.

For a fixed-point projection, first identify complete ordered domains and the
equation systems. One possible semantic proof uses strict continuous projection
`p` and continuous operators `Phi` and `Psi` with `p . Phi = Psi . p`; preservation
of the bottom and directed limits then transports the least fixed point.
Ash's current ordered values and diagnostics still need their own preservation
argument. Monotonicity, projection closure and scheduling independence are
obligations to establish, not assumptions imported from mathematical sets.

Before selecting the next Rust slice, provide a typed decomposition, failed
fusion obligation, strengthened accumulator or demanded projection, constructor
or fixed-point proof, and before/after recurrence. Name a growing input family
that could falsify the claimed bound and reuse completed original-program
evidence to rank its practical importance. Keep Common's existing wrapper and
queue studies coordinated; introduce no competing traversal or observer.

### Observed wrapper recurrence

Common's Bounds study reconstructs the copying source context parents in
receipt 274's historical observed lane. Independent rechecking of its raw rows
confirms eight wrapper counts across seven successive links:

```text
2 -> 8 -> 20 -> 44 -> 92 -> 188 -> 380 -> 764
N(d+1) = 2*N(d) + 4
```

At each measured link, every previous type Invoke has a sibling Evidence Call
with the same parent. Both channels parent one next-wrapper Invoke each. The
four additional parents are context zero, two symbolic Function roots and one
ordinary term Invoke. This is a causal account of published context counts;
it does not establish equivalent environments, removable live dependencies or
current candidate counts.

If an inductive source argument extends this recurrence to a family of depth
`d`, its solution is `N(d) = (N(0)+4)*2^d - 4`. The finite receipt alone is not
that proof, nor a theorem about total checker cost. It gives the next derivation
a concrete target: explain whether already-bound lexical captures are being
expanded again as deferred type/dictionary recipes. An ordinary-term-only
shortcut cannot remove the observed pair of multiplying channels.

For a qualifying wrapper family, test whether the derived representation can
instead establish `M(d+1) <= M(d)+k`, with bounded local work and fixed `k`.
That would give linear context growth in depth. The proof must account for
growing capture/input sets, live updates and required output: sharing a recipe
while replaying it along every old path does not establish this bound. No such
improved recurrence is established yet.

The study input is `bounds/wrapper-channel-cause-study-6a9/parent-bijection.json`
under the external evidence root below. Its raw source is
`author/context-prefix-measurement-runner-274/observed-copying-combined271.json`,
SHA-256 `ffb3168e786e81e6a77c811d56bed9764916f48dc2bdaf77c8a1595dc2243af6`.

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
evidence selection and lexical creation environment. A candidate must first
distinguish these proposed roles within the current mixed capture list:

| Candidate role | Inductive obligation |
| --- | --- |
| Already-bound lexical value | Prove independence from the new type/dictionary inputs; retain the saved lexical environment and all live incoming updates |
| Type/Row-dependent metadata | Retain the complete free-input support and apply the exact substitution |
| Deferred method or dictionary recipe | Retain the selected evidence and formal inputs; specialize in the required environment |

These roles are a proof question, not a new annotation or an implemented
classification. Equal current values, same-shaped types or a different internal
closure number prove neither input independence nor dependence. TypeAbstraction,
formal-dependent and dictionary-dependent recipes remain specialization cases.

The next law may relate different internal graph representations. Define a
relation between old and candidate states, including correspondence of required
query paths. Show that processing each required input/update preserves that
relation and agrees on body validation, owner escape, inferred control and
diagnostics at their observation boundaries. Preserve original source/owner
identities, actual lexical control environments and complete Type/Row/evidence
inputs. Internal Invoke/Call/Closure allocation ordinals need not be identical
if that correspondence proves the required observations and live edges agree.
This refinement relaxes an implementation proof criterion, not Ash semantics.

The main open condition is whether any intermediate coordinate/publication is
required by control discovery or a focused cut, and how a changed representation
serves that query. Keep the existing route until the correspondence is proved;
there is no authorization to merge environments or suppress symbolic roots.
Common owns the role/phase study and any implementation handoff. This task
supplies the inductive law and review rather than a competing implementation.

#### Separate the output and symbolic-root projections

The follow-up source review uses Common's frozen `value.rs` revision
`6a900a2c22206274e056cb93a53ff0b20d94d7d01084171e9353eb88f92c1e17`
and `bounds/wrapper-evidence-fusion-proof-6a9/proposal.md` in the external
evidence archive. It identifies two distinct observations of inner Function
construction, which a strengthened inductive result must retain.

Let `V(q,c)` denote the live value equation at original capture coordinate `q`
in exact environment `c`. Let `R(G,q)` denote that capture's port in the symbolic
root for `G`'s body. `Graph::start` seeds this port from `V(q,0)` and admits the
body with Unknown formal inputs. Each later `FunctionCaptureInstallation` of
`G` at creation `c` adds a live edge from `V(q,c)` into `R(G,q)`, then publishes
`Closure(G,c)`. These are separate actions, not one output-value projection.

For the proposed wrapper, `c` is the outer type Invoke `I`. Evidence routing
then constructs specialized environment `E`, installs exact dictionary routes
and publishes `Closure(G,E)`. `ReadyClosure::publish` does not itself add the
Function-construction root feeds. Control discovery later calls `root_context`
and `port` for required body roots; provider and resource checks also inspect
closure capture projections. Root contributions therefore cannot be discarded
merely because ordinary source calls consume the specialized Evidence output.

Replacing the removed generic feed with the specialized capture is not a
general algebraic identity. A symbolic countermodel is:

```text
V(q,0) has no owner
V(q,I) reaches owner A
V(q,E) reaches owner B after dictionary replacement

original root contribution:    A
substituted root contribution: B
```

Exact evidence replacement can change a captured dependency; the existing
`topology_graph` law retains different binding routes for Evidence 8 and 9.
The countermodel falsifies unconditional feed substitution. It is not a newly
executed Ash program, a demonstrated lifecycle failure or proof that a suitable
representation relation is impossible. A semantic rejection still needs a
required query that distinguishes the representations.

Fission exposes a stronger logical result: specialized output equations,
generic root-feed equations and correspondence for required queries. Their
producers share the original typed structure but inherit different inputs:

```text
prepare    : OriginalShape -> Result PreparedRouting Failure
generic    : (PreparedRouting, ExactEnv) -> Result RootFeedEquations Failure
specialize : (PreparedRouting, ExactEnv, DictionaryEnv)
             -> Result OutputEquations Failure
```

These are candidate internal roles, not new APIs or implemented carriers.
`OriginalShape` includes authenticated Function/capture/method provenance;
`ExactEnv` includes the saved lexical and complete Type/Row inputs. Equations
retain live input coordinates rather than current atoms. Preserve every
creation contribution, late update and original source owner. Neither the
output nor the generic projection is the union of all free input owners: an
input type owner can be absent from the returned Function's captures.

The next inductive proof must either derive both projections from this shared
routing result or show the generic contribution redundant under every required
root/query observation. Alias/Merge ordering, current formals, dictionary
replacement, opaque cuts and Function output capture sets are separate cases.
Conserve the original fallible publication barrier and account for cycles with
the actual fixed-point relation; the total structural induction does not settle
them. Keeping the original generic expansion as a fallback can preserve its
behavior, but may retain the multiplying channel. Removing only the intermediate
Closure allocation therefore establishes no improved context-growth bound.

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
`author/fanout-census-274/report.md`. The [disposition](analysis-closure.md)
distinguishes later retained implementation from this initial read-only analysis.

## F-2 measured candidate

Common compiled and measured the first product-fold candidate after importing
the reviewed plan. The existing metadata producer, contextual solver, control
graph and validation policy remain unchanged. A shared iterative walk emits
ordered lexical free binders and sparse abstract Port/Methods steps. Original
method and adapter actions replay after lexical and metadata installation.
The implementation charges concern state, recipe retention and replay.

Normal connected receipt 280 passes 1,635 Ash library cases, 40 adapter cases,
six native-buffer cases, 230 public integration cases and the original realistic
resume case. It includes a graph-construction regression for the shared-DAG
cut counterexample and exact metadata/adapter/evidence allocation order.
Independent review verifies the source law, formatted successor and raw logs.

The following diagnostic completed-program comparison uses the authenticated
Outcome 279 candidate as its baseline. It runs the four original programs and
native assertions, with temporary completion allowances restored afterward.
These are separate work-budget owners, not additive runtime costs:

| Program | Source work | Source raw change | Independent Core work | Core raw change |
| --- | ---: | ---: | ---: | ---: |
| Copying | 1,214,621 | -1,997 | 909,269 | -5,259 |
| Bound-NUL copying | 1,214,621 | -1,997 | 909,264 | -5,259 |
| Persistence | 599,918 | -5,051 | 1,618,759 | -7,309 |
| Captured resume | 203,519 | -1,298 | 290,599 | -1,786 |

Resolution, module linking, linked-interface checking and final elaboration
are exactly unchanged for all four programs. Persistence's source raw change
includes a separately observed -51 original binder-capacity debit; the remaining
change outside that debit is -5,000. Preserve the raw total and both components;
neither component is a quota discount or a replacement total.

The candidate adds temporary key/mask state, wider pending entries and a sparse
ordered recipe for one body. It introduces no per-context or per-slot cache.
Allocation bytes and peak resident memory have not been measured, so this
result establishes reduced charged work, not reduced memory or an asymptotic
improvement. At this measured checkpoint, Source checking still exceeds
327,680 for copying, NUL copying and persistence. Persistence also exceeds
independent Core and final elaboration. The candidate is a partial reduction.

Retention review passes, conditional on the full integrated repository gate.
The raw measurement archive is `requested-root-metadata-160/author/f2-candidate-only-measurement-runner/`
under the external Common evidence root. Its `return.json` hash is
`df5f900004db12f7a629d4cf2bd5661411cd9271e3ceba865f0f3e2821642ad4`.
The formatted candidate and normal logs are in `f2-product-candidate-280/`
under `/home/dikini/.codex/ash-provider-evidence/common-resource-support-2026-10-04/`.
The [later disposition](analysis-closure.md) records F-2 retention and the
user-selected calibrated ordinary admission. These F-2 measurements alone do
not establish ordinary acceptance or completion of the optimization objective.
