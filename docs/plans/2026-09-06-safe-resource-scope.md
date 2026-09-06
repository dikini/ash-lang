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
- [ ] Step 3: acquisition typing, exact provider authority and Core structure.
- [ ] Step 4: stored resource dependencies and carried scope obligations.
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
Step 2 is ready to retain. Acquisition typing, lifetime checking and runtime
execution remain unimplemented.
