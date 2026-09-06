# Safe Resource Scope Implementation Plan

> Execute in this task with subagent-driven development, one product writer,
> and independent semantic then Rust/resource reviews after each increment.

**Goal:** Implement [CP-0017](../proposals/CP-0017-safe-non-foreign-resource-scope.md).

**Architecture:** Reuse exact lexical evidence, shared nominal/effect identity,
the finite capture engine and the explicit evaluator. Add one sealed cell API,
scope-owned runtime cells, and inferred stored resource dependencies. Preserve
effect instantiation before adding dynamic acquisition bindings; keep Pure
execution and ordinary local-newtype erasure unchanged.

**Tech stack:** Rust; existing Ash loader, syntax/resolution, type/evidence,
typed Core and loop-driven evaluator.

**Owner:** [TASK-0027](../tasks/TASK-0027-implement-safe-resource-scope.md).

**Base:** `387c4eff925d1d4fdbad08c3eb3c02028bb01035`.

## Work and review boundary

- [x] Read current authority, inspect implementation and compare alternatives.
- [x] Obtain approval for scope-owned release with reusable access.
- [x] Isolate the active checkout under `.worktree/safe-resource-scope`.
- [x] Fresh full baseline gate, before product edits.
- [x] Step 1: instantiated Effect execution across abstraction boundaries.
- [x] Step 2: sealed builtin cell API and acquisition syntax carriers.
- [x] Step 3: acquisition typing, exact provider authority and Core structure.
- [x] Step 4: stored resource dependencies and carried scope obligations.
- [ ] Step 5: cell allocation, exact dispatch, retention and release.
- [ ] Step 6: complete adversarial/resource/abstraction corpus and reviews.
- [ ] Step 7: specification, evidence, full gate and transition cleanup.
- [ ] Local integration, merged-tree verification and clean-worktree lifecycle.

All compiler/runtime implementers and semantic/resource reviewers use high
reasoning, never above high. Mechanical documentation checks use medium.
The parent owns proposals, plans, specification, staging, commits and branches.
Implementation agents own only their assigned product/test files. Review is
read-only. There is never more than one product writer.

Use unsigned commits with a per-command override, leaving configuration alone.
Do not push, tag or merge main. Follow AD-0011 after the whole checkpoint closes.
The original 16-unit forecast is not a spent-work budget; report concrete gates
and remaining work rather than inventing notional units.

Each step begins with a test that fails for the missing behavior. Run the
unchanged witness after the smallest coherent implementation, add the owning
negative/resource checks, self-review, then freeze for semantic review followed
by Rust/resource review. Reproduce each actionable finding before fixing and
re-review it. Only the parent commits reviewed checkpoints.

## Step 1: Instantiated effect execution

**Files:** `src/eval/machine.rs`, `src/eval/value.rs`, a small dedicated
effect-instantiation module only if it simplifies ownership, and
`tests/effect_runtime.rs`. The narrow Effect abstraction-form invariant also
uses `src/core/validate.rs` and `tests/effect_core.rs`. The parent updates
relevant dynamic/spec wording.
The required method-adapter corpus also exposed an omitted effectful-function
case in `src/evidence_validation.rs`'s interface-substitution comparison.
Repair that structural case with its owning charged work and negative controls;
do not redesign evidence validation.
The adapter then exposed incomplete method-parameter renaming in Core's owning
rewrite seam. Include `src/core/dialect.rs` and `src/core/effect.rs` to rewrite
expression rows and Effect operation/pattern metadata through the existing
fallible callbacks, with exact/negative/transform evidence. Do not relax Core
validation to accept stale method binders.
The full gate also exposed a 256 KiB stack regression in ordinary checking:
retained runtime values enlarged the driver's frame for its later inline Effect
phase. Include a narrow `src/driver.rs` phase-helper extraction and keep the
existing `tests/data_and_adts.rs` witness in a fresh subprocess, so reused larger
thread stacks cannot hide the bound. Do not raise the limit or serialize tests.

1. Retain the confirmed generic-helper and returned-closure regressions. The
   smallest complete program has `helper<T> : T -> Int ! {E<T>}`, performs
   `E<T>.ask ()`, and is called as `helper 0` under an `E<Int>` handler returning
   42. Run `cargo test --test effect_runtime generic -- --nocapture`; require
   the reproduced `InvalidControlState`, not a source error.
2. Preserve validated instantiation through Effect type application, lexical
   closure creation/application, recursive templates, handler entry and
   captured/restored control. Resolve request instances under request context
   and handler instances under saved handler context. Do not weaken exact
   equality, inspect runtime argument values to infer types, or use a mutable
   global substitution. Pure type operations remain erased.
   Independently admit only inert function/constructor values or variables,
   transparent type-operation wrappers, or already-authenticated generated
   method-adapter abstraction bodies in Effect Core. This matches source
   lowering and permits retained lexical abstractions without deferring source
   effects. A merely empty row is insufficient. Ordinary polymorphic
   constructors retain their existing behavior. Test rejected unproved Core
   forms and both transforms; do not add a general aggregate specializer.
3. Add distinct Int/Bool requests, higher-kinded arguments, row-bearing function
   arguments, factory closures called after return, nested type applications,
   generic recursion and generic implementation/method adapters. Preserve
   strict order and predecessor effect traces.
4. Make new context ownership fallible/bounded where it retains or scans
   proportional work; add exact/one-short/retry and deep context/type teardown
   under the owning existing machine/resource contract. Avoid a source-visible
   type value or a generic runtime reflection system.
5. Run `cargo test --lib --test effect_runtime --test effect_core --test
   effect_modules --test effect_typing --test effect_diagnostics` as one shell
   command, all-target Clippy, formatting and diff checks. Obtain both reviews.

This is a prerequisite for the approved acquisition semantics, not permission
to change all pure evidence erasure or implement resources in the first commit.

## Step 2: Builtin API and source carriers

**Files:** `src/module.rs`, `src/driver.rs`, module/resolve/resolved fact owners,
`src/lexer/{mod,token}.rs`, `src/parser/{mod,grammar,expression,project}.rs`,
`src/surface.rs`; new `tests/resource_scope_syntax.rs` and
`tests/resource_scope_modules.rs`, plus existing module/CLI tests.
The fixed API's public effectful methods also require a narrow `src/interface.rs`
repair: `charge_equal_types` omits the effectful-function case and therefore
rejects equal source/checked method signatures during ordinary export freezing.
The identical filesystem module reproduces the failure. Preserve the helper's
successful-work contract and exact row equality; do not redesign publication.
After publication, ordinary import admission also checks operation signature
kinds before registering the retained nominal kinds those signatures may use.
Move that value-kind check after nominal registration in `src/resolved.rs`,
preserving the earlier parameter-identity checks and malformed-summary rejection.

1. Write direct `@builtin.cell` import, qualified/targeted API use and unknown
   builtin/root-conflict negatives. Observe the current root-resolution failure.
2. Admit one compiler-owned module origin and its fixed nominal/interface/effect
   facts. Preserve graph budgets, deterministic module identity, source
   provenance and canonical summary closure. Do not privilege a source file,
   spelling or copied module text. Do not add a general builtin registry.
   Reuse the ordinary parser/resolver on fixed compiler source, with a private
   builtin origin in the module identity. Use one fixed API descriptor for the
   complete relation. Hidden constructor visibility alone is insufficient:
   independent Core must reject ordinary construction/pattern matching for
   the builtin handle family, including retained private constructor facts.
3. Add the reserved `resource` expression and contextual `cell<R>` form with one
   handle binder, initializer and block. Test projection and scope ownership;
   require builtin dependency only when acquisition is used.
4. Check generic `Handle<R>`, `Provider<R>` and `Ops<R>` schemes through direct
   and facade imports. Reject source constructors, source impl/with provider
   introduction, fake module origins and detached/tampered hidden facts.
5. Until Step 3/4 proof exists, keep acquisition unavailable at executable
   validation; do not lower it to an ordinary newtype or silently erase it.
   Reject at resolution before publishing a resolved acquisition until its
   later checks exist. The eventual brand uses a rigid resolved type variable,
   owned by the resource Core node rather than a generalized abstraction or
   nominal representation declaration.
6. Run syntax/module/fact tests, existing module/CLI tests, library tests,
   Clippy/fmt/diff and both reviews. Record actual new carrier owners in the
   architecture inventory without weakening scanners.

## Step 3: Static acquisition and Core authority

**Files:** `src/resolve.rs`, `src/resolved.rs`, `src/kind.rs`, `src/elaborate.rs`,
evidence selection/audit/validation owners, `src/core/{effect,dialect,mod,
validate,transform}.rs`; `tests/resource_scope_typing.rs`,
`tests/resource_scope_core.rs`, and module/evidence tests.
The 256 KiB nested-acquisition witness requires loop-driven resource checking.
After removing that new recursive driver call, its trace reaches the existing
`perform` operand check, which also re-enters the large driver. Include the narrow
`perform` operand/check/finish scheduling correction, preserving operation
signature checking, ordinary operand diagnostics and exact row/result construction.
Retain an ordinary `perform` control and leave handler behavior and limits alone.
The helper/facade positive also exposes a nominal-closure comparison that treats
route-local access as defining metadata: a direct opaque type and an identical
hidden fact reached through a helper disagree. Exclude access from that closure
comparison while retaining canonical identity, shape and provenance checks.
Keep name exposure and access merging unchanged; cover both import orders,
an ordinary opaque-type control and hidden-name/constructor rejection.

1. Add typed acquisition with Int initializer, rigid Type identity, opaque handle
   binder, exact generated Provider evidence and identity-local effect removal.
   Write positive helper forwarding plus wrong-initializer, binder scope,
   wrong-handle/provider and outward type/row escape negatives first.
2. Add authenticated acquisition-origin facts separate from source lexical
   methods. Reuse existing abstract-before-lexical selection and complete-goal
   validation. Ordinary source evidence cannot mint the sealed relation.
3. Add an Effect Core resource-scope operation and the minimum inert authority
   facts its validator needs. Retain explicit initializer-before-scope order,
   identity, handle, provider and effect ownership. Pure Core admits no resource
   node. No resource payload is encoded as a constructible ordinary value.
4. Independently check complete kinds, scope, result/row equations and authority;
   cover owner/provider/type/operation/source tampering. Both transforms preserve
   the relationships and revalidate. Keep unproved stored escape fail-closed
   until the next step completes its proof.
5. Run focused source/Core/evidence tests, library tests, Clippy/fmt/diff and
   independent reviews. Review ambiguity/diagnostic precedence explicitly.

## Step 4: Stored dependencies and control obligations

**Files:** `src/core/capture.rs`, `src/core/capture/control.rs`, source summary
publication/admission and final Core validation; resource typing/Core/module
tests and existing capture/discard fixtures.

1. Begin with a resource captured by an identity-free returned closure, then an
   aggregate and a helper/factory return. Pair each with copied Int and constant
   closure acceptance. A type-only local-nominal escape check is insufficient.
2. Extend inferred values with resource dependencies and symbolic argument
   relationships. Track aggregate fields, pattern projections, captures,
   ordinary/recursive calls and imported summaries. Keep copied scalar results
   dependency-free; preserve live outer dependencies across an inner scope.
3. Include semantic effect/identity captures, not merely syntactic handle uses.
   Authenticate retained metadata and propagate it through generic instantiation
   without source capture annotations or loss at generalization.
4. Add scope-owner obligations to the existing finite capture/control engine.
   Distinguish recursive activations, nearest handler boundaries and selected
   restored segments. Check normal scope exit and values transferred across
   handler boundaries, not just a resource block's final syntax node.
5. Reject discard that abandons or skips release, including affected owners
   outside the immediate captured segment. Admit inside-scope safe discard,
   outward resource-free requests followed by resume and consumed clause owners.
6. Run resource analysis even in programs with no discard. Final Core reconstructs
   facts independently from actual control; transformed/forged summaries cannot
   authorize escape. Unknown relevant flows fail closed without rejecting all
   known abstractions or ordinary resource-free predecessors.
   Replace Step 3's publication guard only after this proof exists. Exercise
   full resource-bearing checked-module publication, linking and acquisition
   binder ownership; Step 3's private linked-header fixture is not evidence for
   that complete path. Retain the final executable guard until runtime support
   is present.
7. Require finite-work, exact/one-short/retry, wide aliases/import scans and deep
   success/failure teardown. Run all capture/effect/resource tests, architecture,
   library tests, Clippy/fmt/diff and both independent reviews.

## Step 5: Runtime cells and generative activation

**Files:** `src/eval/machine.rs`, `src/eval/value.rs`, Step 1 identity context;
`tests/resource_scope_runtime.rs` and machine tests.

1. Write read/write observation (42), two independent cells, nested release and
   repeated-access tests. Require runtime RED before implementing the operation.
2. Keep each mutable Int payload owned by its live resource scope, including
   when that scope moves into a captured continuation. Runtime access handles
   are non-owning activation keys. Unused closure environment entries and the
   ordinary observed heap must not keep payload ownership after release.
3. Create a fresh key after initializer evaluation. Bind the acquisition identity
   in lexical effect context, preserving outer closures under same-site nested
   activation. No first-class identity witness or global provider lookup.
4. Dispatch the trusted cell interpreter by authenticated API and exact active
   identity. Check operand handle agreement before reading/writing. User handlers
   preserve ordinary exact lexical interception without gaining provider origin.
5. Release once on normal scope return; move through capture/resume without
   cloning. Discard defensively rejects a live resource obligation before
   consuming any capture. No callback or general cleanup transition.
6. Test live-cell capacity exact/one-short/retry/reuse, allocation failure without
   partial authority, retained control, deep normal/failure disposal and resource-
   free pure locality. Add acquisition/read/write/release observations to tests.
7. Run resource and predecessor effect runtime/Core tests, library tests,
   Clippy/fmt/diff and both independent reviews.

## Step 6: Complete interaction and adversarial corpus

Use fresh high-reasoning semantic review of the complete proposal matrix,
then high-reasoning Rust/resource review. Test actual same-site reentrancy,
closure-only identity capture, generic/imported factory flows, returned evidence
methods, opaque/aggregate transport, outward request payloads, skipped scope
completion and independent acquisitions. Cover malformed linked/Core authority
and both transformed executable programs. Fix findings test-first with one
writer and re-review; no requirement may be replaced by blanket rejection.

## Step 7: Specification and local closure

The parent updates every CP-named specification and tool area, adding executable
examples and their required harness checks. Create
`docs/design/effect-ash/resource-scope-evidence.md` with actual observations,
resource formulas, review corrections and limitations. Update design/trajectory
status without claiming main integration. Reassess simplification and downstream
proof/existential/hook pressure without implementing those features.

Run `cargo xtask verify`, Markdown lint, changed-link checks, manual authority
and formal-notation review. Use a medium-reasoning independent documentation
audit. Retain the verified checkpoint, then remove CP/task/plan and index entries.
Recreate the integration worktree, merge locally with an explicit unsigned merge,
verify the combined result, prove ancestry and cleanliness, and remove the
completed feature worktree/branch. Preserve main's unrelated edits and all
remote refs/tags.

## Execution record

Two read-only audits found the stored-resource and activation-context gaps.
Independent contract review is closed: the proposal now explicitly rejects
owner-relative request-payload escape and includes both positive controls.

The first full baseline run exposed stale absolute executable paths in Cargo
artifacts retained across the worktree move. Rebuilding the disposable `ash`
package cache restored all 74 specification-example tests without source or
test changes. The fresh `CARGO_INCREMENTAL=0 cargo xtask verify` then passed
formatting, metadata, build, Clippy, all 2,156 tests in 62 binaries, and rustdoc
before product edits.
Step 1 implementation and review corrections are in progress. The original generic
helper and returned-closure tests reproduced `InvalidControlState`, then passed
unchanged. The focused suite passed 1,094 tests; all-target Clippy with warnings
denied and formatting passed. Exact/one-short/retry and depth-32,000 tests cover
instantiation ownership and the repaired operation-metadata rewrite. Semantic
review found an existing empty-row callback panic in required forwarding cases.
The full gate found four missing architecture-inventory entries and raw mutation
of the new iterative owner. Those corrections pass their exact checks and
semantic re-review is closed. Rust/resource review then found uncharged
row-argument staging in the shared substitution helper. Its narrow correction
passes 1,101 focused tests, Clippy and formatting; resource re-review is closed.
The next full gate passed all 32 architecture tests, then aborted on a stack
overflow in `data_and_adts`. All 32 tests in the same binary pass serially, but
normal concurrency reproduces the abort. The isolated synthesized-type-wrapper
test also aborts alone on its 256 KiB stack, during a shallow chain of
elaboration frames. A fresh build of the integration baseline passes the
isolated test; the current revision fails it. The driver's frame grew by 96
bytes while the two largest elaboration frames stayed unchanged. Extracting the
later Effect phase reduced that driver frame by 17,728 bytes. The fresh-process
256 KiB witness went RED to GREEN; independent review closed the correction.
The frozen revision passed 1,133 focused tests, Clippy and formatting. The fresh
`CARGO_INCREMENTAL=0 cargo xtask verify` passed 2,183 tests in 62 binaries,
formatting, metadata, build, Clippy and rustdoc. Both independent reviews are
closed. The documentation audit corrected three stale erasure/frame statements;
seven affected documents pass Markdown lint with the line-length exception for
existing formal rules and tables, and all 29 local link targets exist. Step 1
is retained in unsigned commit `8810a44`.

Step 2's first three module tests reproduced the missing builtin import,
unknown builtin path and reserved-root preflight behavior. The loader now
admits the fixed API through ordinary parsing and checking with a private
builtin identity. Source provider introduction and ordinary handle construction
reject; targeted and facade imports preserve the defining facts. Resource syntax
projects, but acquisition still rejects before resolved publication. Direct
targeted import of only `Handle` satisfies the dependency check; facade-only
access does not.
Resource execution and lifetime checking remain later steps.

The frozen Step 2 revision passed the parent's focused 1,123-test gate in 11
binaries and the fresh-process 256 KiB wrapper regression.

Semantic review closed without actionable findings, including independent
method-only facade/direct-import probes. Rust/resource review also closed
without actionable findings; eight targeted equality/builtin checks passed. The
final ownership scanner passed after the test-helper correction, completing
passing evidence for all 32 architecture checks without scanner changes. Parent
all-target Clippy, formatting, Markdown lint and diff checks passed.
Step 2 is retained in unsigned commit `0ae5203`; its worktree was clean after
the commit and the main/integration refs are unchanged. Step 3 is active with
one high-reasoning writer, beginning with acquisition typing and independent
Core authority. Executable resource admission stays closed pending the later
stored-dependency and runtime steps.

Step 3's six initial source regression groups reproduce the resolution guard.
The implementation boundary scopes the rigid identity and handle over the body
only, reuses lexical selection with a distinct acquisition origin, and preserves
ordinary source `with` eligibility. Internal typed-structure positives do not
authorize checked-module publication: that stays explicitly unavailable until
Step 4 supplies stored-dependency analysis. No retained proof-status carrier
or public unchecked-success API is needed.

Step 3's first frozen writer gate passed 1,034
library tests and 344 tests in 21 integration binaries; the parent's independent
gate passed 1,137 tests in 11 binaries. Both 256 KiB controls and parent all-target
Clippy passed. Architecture has the earlier full 32-check pass and a current
31-check refresh excluding the unchanged mutation test. Private linked-header
and full-transform fixtures cover the intermediate structural boundary without
publishing or executing a resource program. Both independent reviews must close
before the parent retains this increment.

Semantic review closed after correcting escape locations and related acquisition
labels, including the distinction between returned values and immediate outward
effect rows. The corrected parent gate passed 1,212 tests in 13 binaries and
all-target Clippy. Rust/resource review found two new error paths retaining raw
deep-type clones. Existing iterative guards now cover them; exact failure/retry
tests observed the missing disposal visits before correction and pass unchanged
afterward. Resource re-review closed both findings. The final parent gate passed
1,214 tests in 13 binaries, workspace all-target Clippy, and the fresh Pure
256 KiB regression. Step 3 is complete within its explicit structural boundary;
stored-dependency proof and runtime support remain Steps 4 and 5.

Step 3 is retained in unsigned commit `64647d8`, with a clean worktree after
commit and unchanged main/integration refs. Step 4 is active with a fresh
high-reasoning writer, beginning with the existing summary/control extension
seams and paired stored-escape and ordinary-value controls.

Step 4's first unchanged witness reaches the publication guard instead of
rejecting a returned identity-free closure that captures the cell behind an
internal exact handler. Copied integers, constant closures and closures that
capture only copied integers provide the paired controls. The implementation
extends the existing callable summaries with stored dependencies and symbolic
argument/projection relationships, and the existing finite control engine with
resource-owner occurrences. It introduces no source capture language or public
proof carrier. Runtime admission remains closed until Step 5.

The first control tests also cover owner-relative request payloads, safe inner
discard, outward abandonment, skipped scope completion and recursive scope
occurrences. The writer reports 22 resource-typing tests and 70 predecessor
capture/effect tests passing. This remains an incomplete proof boundary.

A bounded design check addressed the next value-summary gap: invoking a
resource-capturing callback may return a dependency-free constant closure.
Whole-value dependency sets cannot express that distinction or field selection.
The selected implementation refinement specializes the existing value graph
with flat slots keyed by Core site and a context of distinct static call sites.
A repeated call site folds to an existing context and joins conservatively;
closure captures and aggregate fields refer to slots, not nested environment
snapshots or growing projection paths. Every retained context, edge and scan
must be charged. Required pairs cover storing versus invoking a callback,
selecting dependent versus independent fields through imports, and two outer
wrapper calls sharing one inner factory site. Recursive uncertainty cannot
authorize escape or abandonment; the required recursive positives still apply.
This design check is not the increment's final semantic or resource review.

Handler value flow uses the same finite context rule with static call and
request-to-clause dispatch symbols. Context keys never embed request slots or
prior contexts; a selected event retains its originating result slot only as a
flat reference. Selected operands flow to clause patterns, resume arguments flow
back to the suspended request, and resumed computation results flow to the
resume expression. Known operations select their own clauses. Value closure and
control-edge discovery alternate until stable before checking safety; bottom,
resource-free values and opaque uncertainty remain distinct. This retains the
existing control engine rather than adding a second evaluator.

The imported generic projection witness exposed a publication seam: pure module
checking skips capture summaries, so a pure helper cannot convey its
argument-to-result relationship to a resource-bearing importer. Step 4 therefore
retains data summaries for pure helpers as well. Having a data summary must not
select Effect execution; the owning lowering family supplies that distinct
internal dialect fact. Pure execution and erasure remain unchanged. Cover the
imported projection pair, resource-free pure import/execution, and charged
summary publication/admission before opening the resource publication boundary.

The mixed-kind callback test also exposed an existing pattern-admission defect.
A fresh archive of `64647d8` rejects both the resource witness and a resource-free
tuple/open-row relay with `InvalidPayload`; its unary relay control executes
`42`. The debugger trace reaches Effect `match_expression`, then `admit_pattern`,
which hardcodes `allow_effectful = false` for pattern payload types. Result
admission already uses the owning family's allowance. Include the narrow repair
that carries this allowance through match-arm/pattern admission, preserving Pure
rejection, existing work/depth limits and iterative failure ownership. Retain
both original witnesses, a Pure negative and admission-boundary controls.

The contextual request/resume pair now has writer RED-to-GREEN evidence. The
joint analysis initially exceeded the unchanged work limit for 24 nested scopes;
phase measurements located the failure in initial value closure, before control
discovery. Repeated full scans delayed newly demanded children and revisited
unrelated slots. A dependent-slot worklist now schedules new slots, edge targets
and readers of growing facts, including transitive dependency reads. The writer
reports the existing 32 resource tests and 15 predecessor capture tests passing.
A new imported-projection request-payload pair still exposes a reachability gap
after a cell read. This remains active implementation evidence, not completion
of owner-relative checking or the increment's independent reviews.

The imported-projection request pair subsequently went RED to GREEN after the
writer distinguished externally undefined method binders from unresolved local
computations. Treating those external methods as opaque exposed excessive
control exploration in two valid cases. Read-only tracing identified the missing
source-analysis seam: ModuleCheck builds lexical method bodies and stages exact
selections, but method occurrences reference a shared body-free placeholder.
The graph needs each occurrence's selected method relationship, not a global
alias by method identity. Borrow staged publication facts without filling source
slots early; keep the existing evidence audit and atomic publication gates.
Generic and imported constrained helpers also need their abstract method inputs
connected to the selected methods at each call. Final Core must continue to
derive the relationship from its independently authenticated lowered structure.

Parent-owned source fixtures cover a returned closure whose selected lexical
method captures the cell, paired with copied-integer and constant methods.
A second pair selects the same method in disjoint evidence blocks and returns
either the dependent or independent closure. All five reach the publication
guard on the exact `64647d8` archive, confirming ordinary typing before the new
lifetime checks. Current implementation outcomes remain to be established.

The direct selected-method bridge passed the writer's 35-test resource suite;
the parent independently reran that compiled checkpoint with 35 passing tests.
The copied-integer and constant controls remain admitted to the publication
guard, and the two earlier work-limit failures disappear when cell methods use
their actual generated bodies. The writer then passed the disjoint-selection
and imported constrained-helper pairs using abstract method inputs and
occurrence-specific callable specialization. Implementation selections and
their prerequisite adapters remain unfinished source-summary paths.

A further owner-relative recursive pair exposes a limit of folded value contexts.
At the second recursive entry through one call site, middle and inner scopes
share the same resource-site/context atom. A callback owned by middle may cross
inner to a handler still inside middle; a callback owned by inner may not.
Both source fixtures pass ordinary typing on the exact `64647d8` archive. The
writer reproduced the incorrect rejection of the inherited callback and retained
the paired regression. Existing recent/older control frames distinguish those
occurrences, but the stored dependency has already lost the distinction before
the owner comparison. An occurrence-provenance refinement is under assessment.
No shared-key exemption, raised limit or partial publication is authorized.

The bounded refinement uses the existing value/control rules in a focused-owner
query. At a reachable acquisition entry, retain actual incoming callable,
aggregate and evidence structure in a pre-focus namespace; those values predate
the fresh owner. Give the designated body a focus root unavailable to ordinary
calls, and mark only its handle and identity metadata. Descendant acquisitions
remain unrelated to that marker, while inherited captures preserve it. Carry
the focus marker on the actual resource frame occurrence through aging,
capture and restoration. Check it when that occurrence closes or is crossed.
Relabeling already-merged slots or replacing known incoming structure with
unknown values would not establish this proof. Cover all possible designated
activations and preserve the failing local-payload control. Triggering refinement
only on ambiguous folded-owner candidates may bound cost; measure it against
the unchanged work limits and nested-scope corpus before accepting the change.
This parameterizes the current solver and adds no source lifetime mechanism.
An absence proof must use converged input facts. Control discovery currently
checks payloads before the joint value/control revision stabilizes; defer any
ambiguous-owner acceptance until convergence, or invalidate and rerun it whenever
the input revision grows. A partially populated entry is not a proof of absence.

Implementation-only modules now retain method body summaries through the same
private carrier as ordinary globals. Flat transient prerequisite adapters use
the staged exact evidence graph, with the hidden method binder and ordered head
arguments followed by the method-local argument suffix. The first direct pair
passed after adding the hidden binder to enclosing callable inputs; the nested
pair required those inputs through the prerequisite adapter graph as well. The
parent independently reran the six-case test successfully. Parent CLI probes
also pass a nested adapter with a method-local parameter, and the resource-free
implementation-only import executes 42. These checks do not establish final
publication, recursive owner precision or executable resource support.

A bounded publication review identified the next atomicity regression: stage a
valid selected occurrence in an earlier implementation method, then fail capture
checking in a later method of the same module with no ordinary globals. Assert
the earlier selection remains unpublished, and use a fresh corrected fixture
for successful summary publication. The existing ordinary module-failure test
rejects before staging and cannot establish this later boundary. The parent
also ran the source-reading ownership scanner: it reports five new unmanifested
fields and no stale entries; their exact profiles remain part of Step 4's gate.

The expanded non-owner resource checkpoint passes 40 tests and its nested-stack
child in the parent's independent run; the recursive-owner regression is
explicitly excluded, not fixed. Executing the method-local nested adapter chain
then exposed an existing Core validation defect on the exact `64647d8` archive
and the current build, in both Pure and Effect pipelines. Concrete prerequisite
validation uses global method-catalog presence to choose whether a nested child
must have an adapter anchor, although the failing occurrence retains that child
as a concrete source. Diagnose and repair this exact representation boundary
without weakening source authentication. Retain the original chain execution,
paired owning-family and transformed/tampered Core tests, and exact-work/retry
controls. The simpler Pure adapter control is not evidence for this chain.

The method-only post-staging failure regression now passes in the parent's
independent run, together with the five-test publication gate and the existing
pre-staging module-failure test. Bounded diagnosis confirmed that evidence
construction and lowering already select anchored adapters by method-level
polymorphism. Matching that predicate in Core validation preserves the two exact
authentication paths and makes both original chain programs execute 42 in
parent Pure and Effect CLI runs. It introduces no fallback for a missing required
polymorphic anchor. Fresh transformed/tampered and exact-budget checks are still
required before this prerequisite closes.

The parent reran the concrete-source, exact-work and tampering gates, and the
rebuilt ownership scanner passes its fixed-point check. The broader gate aborted
in the existing 64 KiB deep capture-equation test, also independently reproduced
by the parent. GDB identifies the enlarged `Graph::build` entry frame. Extract
sequential adapter/import construction phases; preserve the exact test, stack,
work budgets and iterative teardown before continuing owner refinement.

Restored execution needs active request-result and computation slots even when
an acquisition entry already contains a captured Clause/Event. A finite mapping
from frozen context IDs to active counterparts can supply those slots, but
pre-entry lexical reads must remain frozen. Re-running their Alias/Bind
initializers would recreate old closures and aggregates with active captures and
reintroduce false owner dependencies. Keep saved creation references separate
from active execution/result contexts; new mappings and links participate in the
existing worklist and convergence checks. Retain both the restored recursive
owner pair and a pre-entry request whose handler acquires a cell and resumes
with a value later sent outward, paired with copied and constant values.

The graph-construction phase extraction now passes the exact 64 KiB regression
in the parent's independent rerun, without changed limits. The broader library
gate is being rerun before focused-owner implementation. For restoration, key
active roots by frozen context and static continuation cut/role: one old context
can have incompatible completed-versus-pending roles in folded saved frames.
Freeze completed child values before `Next.next - 1`, not the in-progress child.
Use explicit result links into each restored cut's pending slot and enclosing
result destination. This remains finite static context, not a runtime history or
nested environment snapshot; ordinary calls cannot manufacture the restore root.

The broader library run completes with 1,040 passes and four budget-test
failures. Duplicate-route checks now include retained-summary type comparison
work without changing their exact constraint totals or route snapshots; the
parent reran the 36-test duplicate gate and cumulative module-budget test
successfully. The exact `64647d8` archive passes its original cross-stage
snapshot. The new snapshot adds 90 units at each of four dependent resolution
stages: 18 retained nominal re-admissions per importer, each charging shape,
parameter record, Kind and two Origins. Checking, linking and linked-evidence
validation costs are unchanged. The parent independently reran the corrected
exact/one-short/fresh-retry gate; the writer then passed all 1,044 library tests.

The pre-entry resume callback that internally handles a generic operation also
exposes stale solved inference during enclosing-clause row recomputation. A
resource-free generic-call witness reproduces the same Core-build error on the
exact `64647d8` archive. Normalize the current handler's emitted suffix, including
operation metadata, and its output row after all clauses constrain inference
but before recomputation. Reuse checkpointed type/row rewriting with non-strict
zonking; preserve genuinely unresolved inference for later checking. Do not
relax exact instance matching or invoke final whole-builder normalization early.
The rewrite is progressive, so failure propagates to the existing poisoned or
discarded builder; only the existing row-recompute rollback is transactional.
Retain runtime 42, hidden/copy/constant, instance-separation and one-short/fresh
exact-budget publication tests for this prerequisite.

The bounded normalization is implemented. The parent independently reran the
resource-free callback execution and wrong-instance rejection, the resource
hidden/copy/constant callback test, and the exact row-recompute gate
successfully. The normalization exhaustion/fresh-owner retry test and both
strengthened nested concrete-source validation tests also pass independently.
The writer's post-normalization library run passes all 1,045 tests, and the
non-owner resource source gate passes 44 tests plus its small-stack child.

Owner restoration also needs the completed-function-before-suspending-argument
pair. A factory creates a function before an operation suspends its argument;
the clause acquires a resource, recursively revisits the factory with a local
callback, and resumes. Returning the factory's earlier inherited capture is
safe; returning the resumed resource-dependent argument must reject. The
resource-free predecessor executes 42 on the feature and exact `64647d8`
executables. The safe term-capture resource variant reaches the baseline
publication guard but currently fails internally in feature control analysis
when popping an unconsumed clause. Preserve this regression while correcting
restoration; do not bypass clause consumption or owner checks.

Bounded GDB diagnosis identifies copied older resource-prefix addresses joining
their original live-clause tail with a rebound consumed-clause tail. Distinguish
the rebound prefix without rewriting other references to the original live
prefix. Retain a direct heap test of both references and the passing nonrecursive
source pair. Static free-input subtraction and frozen completed-value helper
tests pass independently, as do the compiled 1,047-test library gate and
44-test non-owner source gate with its small-stack child. The recursive-owner
source test remains failing; the helper stage is not a completed owner proof.

The first complete query now compiles with acquisition-entry collection,
convergence-delayed focus queries, marked resource frames and restored result
ports. The parent reran the 44-test non-owner source gate and its small-stack
child successfully. The inherited recursive-owner case changes from false
escape to type-work exhaustion; the writer reports continued escape rejection
for its local counterpart. The trace reaches control-state copying in a focused
discovery pass. Each entry query converges after about two passes; repeated
queries continue through unrelated outer control after the marked owner exits.
Stop each such path at its marked owner's exit, retaining post-convergence
body/result checks and all live-owner seeds. Preserve default limits, exact
work accounting and both closed publication guards.

Owner-exit stopping saves little of the dominant replay cost. Bounded review
supports retaining exact visited states across value rounds, replaying reached
calls directly (including bottom targets), and recording every payload-crossing
obligation for converged checking. That scheduling correction is implemented;
the parent reran the 44-test non-owner source gate and its small-stack child
successfully. The inherited query covers more entries but still exhausts the
unchanged limit. Measure and replace linear context interning with a charged
exact index over the same flat transition vectors; preserve stable identities,
folding and distinct seeds, with narrow/wide and exact-boundary tests.

The exact context index passes its focused boundary tests and the original
recursive-owner source pair under unchanged limits. The parent ran all 46
source tests and their small-stack child at that checkpoint. A separate fixed
completion region closes the direct older-prefix alias regression while
retaining original live-prefix references.

The restored owner pair still exhausted work in repeated normalization of
unchanged stack/heap successors. Bounded review supports an enqueue tail that
skips normalization only for call targets, choice children and final sequence
children with no frame push; all root/stack/heap mutations still normalize.
The corrected restored pair passes. The parent reran 47 source tests and their
small-stack child with the completed-factory test explicitly excluded.

The remaining completed-factory failure is false resource escape, not the
earlier internal control error. Frozen completed values remain intact; shared
older control addresses mix known outer and descendant contexts, attaching a
descendant handler's result to the outer resume. Check a finite allocation
context partition and preserve stable provenance across restoration and
segment copying. Do not suppress selected result edges or substitute context
equality for resource-owner proof. Publication and runtime gates remain closed.

Bounded review selects immutable allocation context on all control addresses,
drawn from existing value-context IDs. Fresh clause addresses use their dispatch
context; older/copy/consumption operations retain source provenance. Restoring
execution contexts does not retag allocation addresses. This does not claim to
separate already-folded recursive contexts; source verification remains pending.

Scalar-successor enqueue equivalence and read-only final dependency gates pass
independently. A renewed 64 KiB regression comes from the enlarged analysis local
sharing a caller frame with graph construction. Moving the final control-query
phase into a helper restores the unchanged test; the parent passes all 22
capture tests at that helper checkpoint. Whole-increment verification is still
required after the allocation-context change.

The allocation-context revision fails the original and restored inherited-owner
controls with type-work exhaustion. Its source gate passes 45 of 47 tests with
the completed-factory test excluded; that excluded test also exhausts. These
results supersede earlier source passes for the current revision. Several
focused queries complete before their cumulative work reaches the unchanged
limit. A sorted-heap stack-pop path retains exact reachability pruning and
passes the parent's differential exact/one-short/fresh-retry test, but does not
resolve the completed-factory exhaustion by itself. Before further product
changes, review whether coarse candidate-discovery addresses and precise
focused-query addresses preserve conservative candidate coverage and saved
continuation inputs. All entry seeds and ownership obligations remain required.

The parent's post-sorting rerun passes 46 of 47 source tests, excluding the
completed factory: original inherited ownership passes again, while restored
ownership still exhausts. The current 24 capture tests pass independently.
Hold phase-local address coarsening until recent-address singleton preservation
through segment copies is established. Instead, measure per-query reuse of
fully prepared identical static cuts; every later result-port join remains
required, including joins that add new dependencies.

Prepared-cut cache hits preserve a later resource-bearing result edge in the
parent's focused test. Both remaining source controls still exhaust; initial
cache-publication boundary coverage is pending. The sixth factory query now
starts at 295,180 charged type-work units, compared with 324,435 before sorting
and cut reuse. These measurements do not count notional milestone effort.

Review also requires a direct copy-state invariant check: distinct recent
addresses from different source regions can map to one destination with the
same site/context. Preserve all alternatives without claiming a singleton;
no source-level clause omission has yet been reproduced. After the bounded
corrections, consolidate legacy resource proof into the contextual engine.
Retain returned-parameter callable-target propagation for resource-free
predecessors, and make missing resource data/ports fail closed.

The parent passes both initial cut-publication and cache-hit/late-edge exact
boundaries. A complete source rerun passes 46 of 48 tests, retaining the two
known work-limit failures. The factory has seven entry states for two candidate
keys, not an unbounded sequence; the sixth check exhausts before the seventh.
The mixed-region copy witness went RED to GREEN by marking collided copy
destinations as older while preserving all tails. Bounded review accepts the
correction; existing-recent aging and staging preflight checks still need their
final evidence before legacy dependency consolidation.

The parent passes the consolidated 27-test capture gate, including explicit
recent-destination aging, older-tail preservation and unchanged stack/work
boundaries. Copy staging is precharged. Legacy stored/captured dependency fields,
handle-taint scans and request-payload fallback are removed; callable targets and
returned-argument substitution remain. Contextual metadata uses a dedicated
charged variable set. Missing-data/port negatives and the full source rerun
remain required before accepting this consolidation.

The fresh consolidated source gate remains 46 of 48. Missing-context and
wide-copy preflight tests pass independently; the present-data/missing-port
combination still needs explicit coverage. Bounded scheduling review permits
unchanged-choice suppression only for already-expanded exact call states.
Preserve first expansion of every new state, late callback propagation and
joint value convergence. Measure replay cost before implementation, and retain
all seven factory entry checks.

The parent passes the consolidated 1,059-test library checkpoint and the
expanded missing-port and returned-callable controls. The proposed call-choice
cache was not added: its measured saving was only 5,613 units through five
focused checks. Structural pruning is the larger measured cost; discard the
invalid `value::close` bucket from the loop-line profiler.

Singleton pop pruning now preserves the full traversal's result by testing only
whether the old root remains reachable. Multiple-edge and live-capture roots
retain the full traversal. The parent passes 30 capture tests and 48 of 49
source tests; both owner pairs pass. Only the factory's seventh check still
exhausts, starting at 308,995 charged type-work units. Measure one lower-bound
lookup plus a charged equal-address scan next, preserving all returned edges
and the unchanged work limit.

The parent passes the edge-range and wider singleton-pop exact tests. A transient
address-range index inside the remaining full traversal now admits the factory
without dropping checks: the parent passes all 49 source tests and their
small-stack child. The index preserves complete equal-address groups and all
live capture edges, precharges staging and mutates the heap only at final
retention. Fresh internal index/library verification and the rest of Step 4's
publication, linking, independent-Core and review requirements remain open;
runtime execution is still unavailable.

The parent independently passes the fresh 1,062-test library and 51-test source
gate. Source publication now succeeds only after dependency/control proof.
Real ordinary-export and implementation-only modules both publish, import and
link to the separate final Core execution guard. The latter required charged
canonical ordering of the private method catalog: builtin/source dependency
order is not identity order. Duplicate rejection and exact identities remain
unchanged. Full linked-owner, tamper, exact-boundary and independent-Core gates
remain open before Step 4 review. A bounded same-site dispatch investigation
found no reachable mismatch and requires no identity redesign.

Fresh parent verification passes 1,064 library tests and 11 Effect module tests,
including real linked-resource ownership, exact constraint/type boundaries,
one-short failures, two fresh retries and surplus/detached-owner negatives.
Mixed-namespace duplicate rejection also passes; bounded semantic review found
no defect in the private ordering repair. Old source-guard assertions in the
Core and module suites reproduced the expected migration failures. Their
correction passes the parent's fresh 63-test resource integration gate and
unchanged small-stack child. Direct acquisition requires real module-checking
success; CLI execution retains its separate internal guard.

The parent independently passes real published/linked Core through original,
identity and folding validation to that guard. Both transforms reject a
same-typed result substitution that changes a constant closure into one that
captures the resource. Request-payload tampering, exact real-Core work,
source-publication atomicity and final reviews remain open. Runtime cells have
not started; this is not Step 4 closure.

The request-payload variant reaches a predecessor registry-order failure before
dependency checking. The parent reproduces it with no acquisition: importing
the cell API plus declaring an ordinary effect fails on both current and Step 3
baseline, while removing only that import returns `42`. Debugger evidence finds
the numeric cross-module effect-order predicate incompatible with dependency
order across builtin/source namespaces. Correct that owning check while keeping
exact per-module declaration order, duplicates, indexed lookup, sources and
charged work intact; retain the unchanged payload witness and resource-free
regression. Do not introduce an identity exception or relax provider authority.

The per-module ordinal correction passes the parent's 1,067-test library,
including duplicate/gap/reversal and exact-work checks. Bounded semantic review
supports retaining dependency order and the existing indexed identity checks.
The parent independently passes the complete real Core result/payload test:
exact work, original validation, both transforms and same-typed dependency
tampering. Late source-publication exhaustion leaves an earlier pending
selection private; exact fresh retries publish. Full focused gates and the
required final semantic then Rust/resource reviews remain before Step 4 closure.

The frozen full focused gate passes 1,269 tests plus the unchanged small-stack
child, all 32 architecture checks, strict Clippy and formatting. Fresh semantic
review nevertheless identifies a strict-readiness rejection bug: match, call
and tuple result equations retain values from work skipped by safe discard.
The parent also reproduces the same cause in a primitive operand and nested
acquisition initializer. Correct readiness through existing value-reader
wakeups, preserving metadata-only merges and latent closure creation. Retain
each discard positive and resume/escape negative before semantic re-review;
Rust/resource review follows only after that finding closes.

Semantic re-review closes the readiness finding. The parent passes the new
five-shape source/domain checks and all six CLI probes; safe discard reaches
the final guard and paired resumed dependency escapes still reject. The fresh
library passes 1,068 tests, with resource Core/module/typing gates at 1/11/53
plus the unchanged small-stack child. A fresh high-reasoning Rust/resource
review now owns the frozen snapshot; the corrected full focused gate continues.
Strict Clippy and formatting pass. No Step 4 commit is authorized by these
partial review results alone.

The corrected full gate passes 1,271 tests plus the unchanged small-stack child.
Rust/resource review requires proportional preflight before new value/control
staging buffers reserve or copy, and iterative ownership for the copied method
body type across a fallible quantified-parameter clone. Retain wide insufficient-
staging/exact/retry and deep failure/retry evidence; the review established the
recursive-drop path, not an observed overflow. Correct these ownership/work
boundaries without changing semantics, limits or query coverage, then re-review.

The parent independently passes all 57 wide tests after proportional precharges
at the seven reported staging sites, including six new boundary tests. The
method-type test now provides an observed pre-fix overflow in an isolated 64 KiB
child, not merely an inferred drop path. The actual method-root helper retains
its body in the existing iterative owner through parameter-copy failure; the
unchanged deep failure and two fresh retries pass. Full corrected gates and
Rust/resource re-review remain open; Step 4 is not yet committed.

The corrected full focused gate passes 1,278 tests plus the unchanged small-stack
child, including all 32 architecture checks. Both independent reviews are
closed; Rust/resource re-review independently passes the 15 relevant tests.
Strict Clippy, formatting, diff checks, Markdown lint and all five local links
pass. Step 4 is accepted for an unsigned local commit. The seven prepared
runtime probes still reach the final execution guard; Step 5 must implement
cell ownership, exact activation dispatch and release before opening it.
