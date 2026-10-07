# Resource analysis relevance and algebraic fusion plan

> Execution plan owned by [TASK-0035](../../tasks/TASK-0035-resource-analysis-relevance-and-fusion.md),
> under [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md).
> Candidate laws and experiments are informative. This plan creates no language
> rule or accepted compiler architecture.

## Goal and execution boundary

Reduce the analysis work preventing original copying, bound-NUL copying and
transaction/reopen persistence from running at ordinary compiler limits.
Investigate early relevance and algebraic simplification as complementary
directions. Treat the pipeline as typed compositions whose equivalence laws
can justify eliminating intermediate structures, traversals or propagation.

Use the existing compiler, typed Core, evaluator, root Cargo workspace and
SQLite integration programs. This task owns implementation slices handed off
by Common, which coordinates shared files, engine windows and integration.
SQLite retains native/library ownership; arena retains its agreed syntax slice.
This task owns its plan and algebra study in `.worktree/algebraic-resource-analysis`.
Coordinate each shared-file handoff, engine window and original-branch merge.
Do not interrupt another writer, copy targets or install private compiler
overlays in their worktree.

## Starting evidence and success criteria

Rebase each candidate on the latest verified original checkpoint coordinated
by Common. The following is the historical comparison baseline, not a claim
that later Common changes are already verified.

The verified original checkpoint is `4324883`, tracking unsigned code merge
`7bd1c1c`. Receipt 259 passes the complete repository gate, including 1,633
library and 43 architecture cases. The expanded SQLite programs belong to a
separate coherent snapshot; their acceptance is not implied by that gate.

Completed diagnostic measurements on that baseline are:

| Program | Source checking | Independent Core | Normal-program outcome |
| --- | ---: | ---: | --- |
| Copying | 1,328,833 | 951,107 | Typing work refusal |
| Bound-NUL copying | 1,328,833 | 951,102 | Typing work refusal |
| Persistence | 621,950 | 1,658,241 | Typing work refusal |
| Captured resume | 207,434 | 298,216 | Pass with actual native assertions |

Source and final-elaboration allowances are separately 327,680; independent
Core is 983,040. Depth limits remain unchanged. Persistence also exceeds final
elaboration, with completed repeated totals 376,941–376,978. Keep separate
budget owners and nested costs separate. Capacity variation is not a quota
discount or evidence of a candidate saving.

Receipt 274 adds a completed, independently neutral graph census and residual
partition. Copying's source analysis has 1,498 type-application Invoke contexts
and 1,498 Evidence Call contexts over its lifetime. Four wrappers dominate
Invoke slot volume. Ordered propagation performs 214,165 empty edge checks
across the first and later source passes. Readiness-watch pruning has a
negative estimated direct benefit and remains parked. These observations
identify opportunities, not removable work or proved lower bounds.

A retained rewrite must preserve original outcomes, exact authority, ownership
and live dependencies and show a positive complete-owner result. Report small
case regressions and preparation/storage costs. A materially useful partial
reduction may be integrated; it does not complete the three normal-program
acceptance gates. Final workstream acceptance requires all original programs
at normal limits, including the separate persistence owners.

## Batch 1: typed inventory and law selection

Files: this plan, [analysis-algebra.md](analysis-algebra.md), TASK-0035 and their
indexes. Read `src/core/capture.rs`, `src/core/capture/value.rs`,
`src/core/capture/control.rs`, source capture publication in `src/elaborate.rs`,
and final reconstruction in `src/core/validate.rs`.

1. Describe immutable source carriers, inherited environments, finite value
   equations, value/control projections, contextful ports and publication.
   Name inputs and outputs of each candidate composition; a list of functions
   without their dependency boundaries is insufficient.
2. State laws for map composition, producer/consumer elimination, product folds
   and demand restriction. Give both applicability and a concrete failing
   precondition, including first-error ordering for fallible maps.
3. Identify fixed-point boundaries explicitly. Neither a cyclic dependency
   graph nor a scope-sensitive fold is an ordinary list map by assumption.
4. Read the complete receipt 274 census and contrary evidence before ranking.
   Share the source inventory with Common's wrapper and dirty-edge studies;
   avoid duplicate observers, alternate compilers and unmeasured caches.
5. Record a selected candidate, its exact file/contract owner and the smallest
   preservation argument that can falsify it. Preserve rejected alternatives.

Acceptance: reviewed typed inventory, source-grounded candidate equations,
explicit unknowns and a coordinated next implementation slice. Documentation
checks require no Cargo build. Integrate the reviewed plan and findings through
an unsigned real merge preserving unrelated original drafts.

After the first F-2 result, prioritize a derivation that removes an increasing
factor. Use the algebra study's constructor equations, strengthened inductive
results and cost obligations. The next candidate must name its growing input
family and before/after recurrence, including local summary/output costs.
A second constant-factor pass fusion can be useful, but does not by itself
establish the larger objective.

Derive the actual Rust execution schedule as well as value equality. Distinguish
materialized collection phases from lazy iterator adapters; put demand checks
before eager child/context work. Include strict accumulator evaluation,
fallible/publication/destruction order, ownership costs and bounded stack use.
Deferred closures and iterator replay provide no automatic memoization.
Treat totality and behavior at bottom as semantic obligations, distinct from
cost and scheduling. Alternative formulations are available; state the law's
strictness conditions or prove its applicability on the admitted total inputs.

## Batch 2: establish relevance before expansion

Primary read/write boundary, subject to Common handoff:
`src/core/capture/value.rs`; related preparation in `src/core/capture.rs`.
Source checking and Core validation remain separate callers.

1. Use the existing exact function/type-application/evidence census to identify
   the input dimension a consumer actually needs: ordinary value flow, owner
   dependence, Type/Row metadata, selected evidence, control or public summary.
2. Define demand against exact original expressions, binders and checked
   interface facts. Unknown or open information retains conservative demand.
   A scalar result, empty current atom set or unused entry call is insufficient
   to exclude capture, dictionary, exported-body or close obligations.
3. Prove a restriction law for the chosen dimension: restricting the producer
   before expansion must yield the same demanded projection as restriction
   afterward. Establish the dependency closure and late-update behavior.
4. Retain all symbolic Function roots/body checks. Separate a dimension's
   unnecessary transport from the requirement to validate the complete body.
5. Implement only after the equation names the exact suppressed operation and
   an actual beneficiary. If the evidence cannot support early exclusion,
   record that result and proceed with fusion instead of guessing semantics.

Acceptance: original relevant positive/negative programs agree, and completed
measurements show the removed producer work plus all new classification costs.
The same-sigma/same-row/different-capture witness remains mandatory.

## Batch 3: compose wrapper and evidence preparation

Primary candidate boundaries, owned by Common unless transferred:
`Graph::build_in_domain`, type abstraction/application construction,
`CallTransferInstallation`, `CaptureTransferInstallation` and
`prepare_capture_topology` in `src/core/capture/value.rs`.

1. Follow the measured class: a type-wrapper Function returning an ordinary
   Function, with the exact outer formals, inner captures, Type/Row metadata
   and selected dictionary routes. Preserve original source coordinates.
2. Express the current two transports as typed operators on immutable routing
   recipes and live original ports. Derive a composed recipe for the common
   structural work. Do not compose or cache current atom answers.
3. Establish a representation correspondence for symbolic roots, required
   queries and focused cuts. Preserve source/owner identities, actual lexical
   creation/control environments and complete Type/Row/evidence inputs.
   Internal Invoke/Call/Closure allocation ordinals may change only when the
   correspondence preserves required observations and all live updates.
   Determine which intermediate ports are observable before removing them.
4. Preserve readiness and first-publication ordering. Finish all fallible
   preparation before publishing a completed recipe; a refusal must not turn
   a partial mapping into authority. Unknown dependencies remain live.
5. Compare one candidate to its current verified baseline using the existing
   completed four-program procedure. Count new preparation, retained storage,
   cold/access cost and small-case effects. Avoid a new profiling subsystem.

Acceptance: a source preservation argument and connected native/source checks,
followed by positive completed-owner savings. If observable ports prevent
producer elimination, retain the boundary and consider immutable preparation
fusion without promising the larger saving.

## Batch 4: product folds over immutable structure

Granted first candidate boundary: `free_values_with_methods` and an additive
internal structural-product producer in `src/core/capture.rs`, plus
`Graph::abstract_captures` and their Function/TypeAbstraction/clause call sites
in `src/core/capture/value.rs`.

Leave the existing `FunctionMetadataPreparation` producer unchanged and consume
its existing output at the original phase. This first slice adds no body cache,
context or slot metadata, graph-transfer change or validation policy.

1. Identify the structural projection each collector uses. Lexical collection
   stops at selected method replacements; evidence collection can continue
   below them. Metadata has its own binder exclusions and completed subtree
   facts. A single global visited set would conflate these concerns.
2. Propose a shared iterative structural producer with separate typed
   accumulators and per-concern demand/visited state. Preserve each projection's
   original discovery order, duplicates and cuts. Share child enumeration only
   when the active projection states justify it.
3. Keep graph allocation and result publication in their original phases.
   If a shared walk collects evidence recipes early, replay their authenticated
   actions after lexical and metadata slot installation so IDs and provenance
   remain unchanged. Include any retained recipe's memory and work cost.
4. Reuse existing preparation rather than stacking another body-plan cache on
   `SlotPreparation`, `CaptureTopology` or compact metadata roots.
5. Select this batch only if its measured gross opportunity justifies the
   preservation/retention cost. It is a candidate, not a prerequisite to every
   subsequent delivery.

Acceptance: identical ordered per-concern results and original malformed-source
rejection, followed by completed program savings. A warm root cache alone is
not this product-fold experiment.

## Batch 5: incremental fixed-point formulation

Conditional candidate boundary: `solve_capture_values` in
`src/core/capture.rs`; ordered live propagation in
`src/core/capture/value.rs`; value/control exchange in
`src/core/capture/control.rs`.

1. Establish the domains, orders, equations and actual monotonicity of the
   selected solver. Do not assume independent product components when one
   reads another's growing state.
2. Separate static structural discovery from contextful propagation. Consider
   one change stream feeding multiple concern accumulators, with exact dirty
   dimensions and retained completion boundaries.
3. Replace whole-structure rounds only when a dependency-directed schedule
   reaches the same required fixed point. Preserve deterministic source and
   notification order where diagnostics or first publication depend on it.
4. Reuse Common's dirty-edge work rather than introducing a competing cursor
   representation. Retain current symbolic roots, self/cyclic/late updates,
   exact reader identities, and refusal behavior.

Acceptance: the same fixed-point conclusions on actual source/Core programs,
with complete work and memory evidence. Claim an asymptotic improvement only
for the measured/modelled family that actually eliminates repeated rounds or
expansion. Fusing a fixed number of linear passes is a constant-factor and
allocation improvement unless further structure establishes otherwise.

## Verification and integration for implementation batches

Coordinate one Cargo job and one test thread with Common. First run the
connected original targets, with no edited assertions or reduced fixture:

```bash
CARGO_BUILD_JOBS=1 cargo test --locked -p ash --test provider_sqlite_copying --test provider_sqlite_sessions --test provider_sqlite_control --no-fail-fast -- --test-threads=1
```

The coherent SQLite snapshot is required for these targets; the plan's isolated
baseline does not yet contain the larger targets. Common/SQLite choose the
verified merged source or explicit coherent transfer before running them.
Use existing capture, provider-control, owner-row, module, malformed-Core,
transform and deep-input suites as the affected boundaries require. Add a
focused regression only for a demonstrated bug or an otherwise unobservable
preservation boundary.

If original cases still exhaust work, use the existing temporary completion
procedure for comparison, then restore sources and normal limits unconditionally.
Retain all raw outcomes and six owner totals; do not retry for favorable
capacity or silently normalize them. Fresh source mtimes must accompany
temporary restoration before the coordinated build.

After connected checks and independent review, make unsigned commits and a
real merge into `codex/provider-experiments`. Preserve both histories and all
unrelated working bytes. Run the mandatory integrated gate once per retained
connected delivery:

```bash
CARGO_BUILD_JOBS=1 cargo xtask verify
```

Consumers import the verified original checkpoint before their acceptance
reruns. Report completed features, measured reductions and remaining failures
separately. No merge into `main` belongs to this experiment.

## Exclusions and completion

Do not change surface semantics, add capture annotations, erase Effect type
applications, merge distinct owners/environments, weaken independent Core,
raise production limits or change charges merely to admit a fixture. Keep
native library policy, arena allocation implementation, concurrency, processes,
RC/GC and foreign callback ABI outside this task.

The task remains active while its selected rewrites and normal-program gates
are outstanding. Record rejected candidates and evidence in the algebra study.
On completion remove this task-owned plan under the artifact policy; retain
reusable findings in the governing design documentation or adoption artifacts.
