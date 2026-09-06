# TASK-0027: Implement Safe Resource Scope

- ID: `TASK-0027`
- Status: active
- Related: [CP-0017](../proposals/CP-0017-safe-non-foreign-resource-scope.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [execution plan](../plans/2026-09-06-safe-resource-scope.md)

> This task organizes authorized work; CP-0017 owns the semantic transition.

## Dependencies

Baseline: `387c4eff925d1d4fdbad08c3eb3c02028bb01035`, the locally integrated
capture/discard checkpoint. Its full gate passed 2,156 tests; integration
revalidation passed 1,153 tests. Recheck the baseline before product edits.
The user approved scope-owned release with reusable cell access on 2026-09-06.

## Work

Implement CP-0017 using one product writer at a time, test-first bounded
increments, semantic review followed by Rust/resource review, and final
documentation verification. Use high reasoning for compiler/runtime and
semantic/resource reviews, medium for mechanical documentation work; never
exceed high. Keep commits unsigned per the user's instruction. Use the local
`.worktree/safe-resource-scope` checkout and retain local integration only.

## Progress

- Read-only semantic and implementation-boundary audits completed.
- The user approved the concrete resource contract after those audits.
- Moved the clean integration checkout to the active feature worktree and
  created `codex/safe-resource-scope`; integration remains at the baseline.
- Fresh full baseline verification passed before product changes.
- Accepted proposal, task and implementation plan recorded.
- Independent contract review required explicit owner-relative checking of
  dependent request payloads sent to outer handler clauses. CP-0017 now records
  that rule and the copied-payload/live-outer controls; no temporary lending
  discipline is introduced.
- The reviewer confirmed that the revised contract closes the reported gap.
- Moving the worktree exposed stale executable paths in Cargo's retained
  package cache. Rebuilding that cache restored all 74 specification-example
  tests without changing source or tests. The fresh full baseline gate then
  passed with `CARGO_INCREMENTAL=0 cargo xtask verify`: 2,156 tests in 62
  binaries plus formatting, metadata, build, Clippy and rustdoc.
- Step 1's first frozen revision passed 1,094 focused tests, all-target Clippy
  with warnings denied, and formatting. Review corrections are in progress;
  no resource acquisition code has been implemented yet.
- The full Step 1 gate passed build/lint and library tests, then exposed missing
  architecture-inventory entries and raw mutation of an iterative owner. Four
  inventory entries and the narrow owner-method correction now pass their exact
  architecture checks. Semantic re-review closed the empty-row finding; the
  corrected focused suite passed 1,097 tests plus Clippy and formatting.
- Rust/resource review found one charge-before-staging omission in the shared
  type/row substitution helper newly used by runtime instantiation. The bounded
  correction passed 1,101 focused tests, Clippy and formatting. Independent
  resource re-review closed the finding with five targeted tests.
- The next full gate passed all 32 architecture checks, then aborted on a stack
  overflow in `data_and_adts`. The same compiled test binary passes all 32 tests
  serially but reproduces the abort with normal concurrency. The isolated
  synthesized-type-wrapper test also aborts alone on its 256 KiB thread stack;
  its trace shows accumulated elaboration frames, not recursive traversal.
  A fresh baseline build passes that test; the current revision fails it. The
  driver's frame grew by 96 bytes through its later inline Effect phase.
  The narrow phase-helper extraction reduces that frame by 17,728 bytes. Its
  fresh-process regression went RED to GREEN without changing the stack limit
  or concurrency. Independent review closed the correction; 1,133 focused tests,
  Clippy and formatting passed.
- Step 1's fresh complete gate passed: `CARGO_INCREMENTAL=0 cargo xtask verify`,
  2,183 tests in 62 binaries plus formatting, metadata, build, Clippy and rustdoc.
  Both independent reviews are closed. Documentation review corrected three
  stale erasure/frame statements; seven affected documents pass Markdown lint
  with the line-length exception for existing formal rules/tables, and 29 local
  link targets were checked. Step 1 is retained in unsigned commit `8810a44`.
- Step 2's first three module tests reproduced the missing builtin import,
  unknown builtin path and reserved-root preflight behavior.
- The fixed API parsed and resolved, then reproduced an existing export-freezing
  failure for public effectful methods. Identical filesystem source also fails.
  The paired type comparison in `InterfaceConstraintBudget::charge_equal_types`
  omits `EffectfulFunction` and rejects matching signatures. Step 2 includes the
  narrow structural repair and its exact-work/row-identity controls.
- After that repair, importing the ordinary API reproduces a second omission:
  summary admission checks operation value kinds before registering the nominal
  kinds those operations use. Step 2 moves those kind checks after registration,
  preserving the earlier parameter-identity checks and malformed-fact rejection.
- Step 2 now admits the fixed builtin through ordinary parsing and checking,
  preserves its origin through targeted/facade imports, rejects source provider
  introduction and ordinary handle construction, and projects resource syntax.
  A direct targeted import of only `Handle` satisfies the acquisition dependency
  check; facade-only access does not. Acquisition still rejects before resolved
  publication; this is not an executable resource checkpoint.
- The frozen Step 2 revision passed the parent's focused gate: 1,123
  tests in 11 binaries, covering library, resource syntax/modules, CLI, module
  loading/resolution/visibility/elaboration and existing Effect Core/modules.
  The fresh-process 256 KiB wrapper regression also passed.
- Semantic review closed without actionable findings. Independent CLI probes
  also passed imported constrained forwarding and method-only facade use, and
  distinguished direct method-only acquisition availability from facade-only
  access. Rust/resource review also closed without actionable findings; its
  eight targeted equality/builtin checks passed. All 32 architecture checks have
  passing evidence: the final unchanged ownership scanner passed after the
  test helper used `pop` followed by immediate iterative disposal. Parent
  all-target Clippy, formatting, Markdown lint and diff checks passed.
- Step 2 is ready to retain. Acquisition typing, lifetime checking and runtime
  execution remain unimplemented.

## Verification

Use the proposal's positive, negative, abstraction, repeated-acquisition,
tamper, transform, exact-boundary/retry, deep teardown and locality corpus.
Run focused gates after each increment and `cargo xtask verify` at closure.
Verify changed documentation, links and artifact authority manually.
Only close CP/task/plan after the full implementation and evidence are retained.

## Discoveries

At the baseline, generic effect type applications erased instantiation before
runtime request selection. A generic `E<T>` helper under `E<Int>` failed with
`runtime.invalid-control-state`; monomorphic and internally handled controls
passed. Returned requesting closures failed similarly. CP-0017 explicitly corrects
this prerequisite and the corresponding blanket type-erasure wording.

Source-generated type abstractions contain inert values, transparent type
operations or authenticated method adapters, but Effect Core previously
admitted arbitrary bodies. Delaying those
arbitrary bodies could delay effects. Step 1 therefore independently enforces
the actual lowered forms before retaining lexical abstractions. This preserves
source order and avoids a general runtime aggregate-specialization mechanism;
Pure Core and source generalization are unchanged.

The method-adapter corpus found another prerequisite omission: linked evidence
comparison handles pure function signatures but omits the effectful-function
case when substituting interface parameters. Even a non-generic implementation
with a generic effectful method is checked, then rejected as
`evidence.validation.unknown-identity`. Step 1 includes the narrow structural
comparison repair, with charged substitution and exact-row negative controls;
this does not change interface selection or authorization.

After that comparison repair, the same generic adapter reached Core and
exposed incomplete method-parameter renaming. The function type used its fresh
generated binder, but the body row still used the resolved method binder.
The owning Core rewrite seam handled ordinary types and type-application row
arguments but skipped expression rows and Effect operation/pattern metadata.
Step 1 corrects that seam with the existing charged callbacks and tests the
complete relationship; independent validation is not relaxed.

Independent semantic review reproduced valid ordinary and generic-method
forwarding of a pure lambda through an open-row helper. Zonking that row to
empty normalizes its function wrapper to a pure function, but two existing
callbacks assumed an effectful function and panicked. Step 1 handles both
canonical forms and retains the empty/nonempty controls. The reviewer found no
additional semantic defect in lexical runtime contexts or the abstraction gate.

The resource reviewer measured width-dependent allocation under constant
admitted work: a nonempty lexical context substituting a function type with
one wide effect instance spent four units before exhaustion, while staging
grew with argument width. The shared substitution helper flattened known/lacks
arguments before charging their visits. Step 1 must preflight that staging or
stream it through bounded state; both known and lacks rows require controls.

Ordinary closure environments retain unused preceding bindings, while ordinary
heap cells persist into observation. Resource payload ownership must therefore
stay with the acquired scope; non-owning access handles must not extend it.
Capture analysis currently has callable targets and clause owners only. New
stored dependencies and resource-owner obligations must be inferred even when
resource-bearing code contains no discard.

## Deviations

No scope expansion is authorized. The original 16/100 milestone forecast is a
relative weight, not a spent-work ledger or a new numeric budget. Do not invent
work-unit totals or borrow hooks, cleanup, FFI or a general ownership system.
