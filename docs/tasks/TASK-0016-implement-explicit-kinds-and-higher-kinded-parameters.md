# TASK-0016: Implement Explicit Kinds and Higher-Kinded Parameters

- ID: `TASK-0016`
- Status: active
- Related: [CP-0009: Explicit Kinds and Higher-Kinded Parameters](../proposals/CP-0009-explicit-kinds-and-higher-kinded-parameters.md), [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), the [approved design record](../plans/2026-08-26-explicit-kinds-design.md), the [approved Task 9 binder-authority design](../plans/2026-08-27-linked-core-resolved-binder-authority-design.md), the [detailed Task 9 execution plan](../plans/2026-08-27-linked-core-resolved-binder-authority.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [AD-0009: Ordered Resolved-Global Binder Authority](../decisions/AD-0009-ordered-resolved-global-binder-authority.md), and the [execution plan](../plans/2026-08-26-explicit-kinds-and-higher-kinded-parameters.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0009 is the accepted transition authority. The current specification owns
  implemented Ash until this product branch lands implementation, tests, and
  normative updates together.
- This branch starts from explicit-import checkpoint `a1647ff`, which is now
  integrated as `main@a1647ff`. The predecessor-order restriction is therefore
  satisfied; this branch remains separate and unmerged while the increment is
  active.
- The predecessor supplies explicit implementation selection and re-export,
  stable declaration and evidence identities, body-free summaries, linked
  authentication, independent Core validation, graph-wide resource budgets,
  and the retained [explicit-import evidence](../design/lib-ash/imports-evidence.md).
- A fresh `cargo xtask verify` passes in the dedicated `lib-ash-kinds` worktree
  before production changes. The branch remains separate and unmerged.
- Every behavior change uses a witnessed red-green-refactor cycle. Production
  Rust follows `rust-skills`; unexpected failures use
  `superpowers:systematic-debugging`. Intermediate commits are unsigned.

## Work

Execute the linked plan to:

- retain kind and explicit type-binder syntax with contextual `Type`, exact
  interface arity, recovery, spans, and legacy headers;
- replace saturated nominal applications with one canonical unary semantic
  application while preserving n-ary source syntax and simultaneous n-ary
  Core scheme instantiation;
- make kind operations, application operations, and their disposal stack-safe
  and exactly charged;
- assign canonical fixed kinds to declaration and inference binders and derive
  local nominal kinds before checking any type-bearing declaration fact;
- kind-check every monotype and interface argument, preserve exact explicit and
  implicit binder policies, and retain deterministic structured failures;
- extend first-order inference, eligible local generalization, interface and
  implementation matching, termination, overlap, orphan ownership, and
  inference-free evidence selection to fixed higher kinds;
- retain and authenticate kinded body-free summaries, hidden closure, imported
  facts, linked evidence, Core binders, transformations, and independent Core
  validation before evaluation;
- preserve erasure and evaluator state-machine behavior while mechanically
  migrating nominal-shape inspection;
- establish a closed type-bearing site inventory, exact resource formulas,
  one-short and atomic failure witnesses, 256 KiB-stack deep and wide coverage,
  complete summary, linked, and Core tampering, and library and CLI diagnostics;
- migrate every predecessor-valid omitted annotation and implicit global or
  implementation binder without edits while recording deliberate stage and
  reason changes; and
- reconcile the specification and explanatory documentation from implemented
  behavior, retain `docs/design/lib-ash/kinds-evidence.md`, complete independent
  reviews and the full gate, then remove transition artifacts without creating
  a `lib-ash` tag.

This task excludes method-local type parameters, multi-parameter interfaces,
associated outputs, functional dependencies, defaults, packages, kind
inference, kind polymorphism, type lambdas, higher-order unification, source
`forall`, explicit term type application, higher-rank source values, runtime
kind values, a compatibility grammar, a second semantic type representation,
and evaluator semantic or state-machine changes. The absence of kind inference
is the accepted phase-dependent semantic boundary of this increment, not a
permanent language principle.

## Progress

- The approved design record narrows the second prepared `lib-ash` increment.
- Three independent proposal reviews covered semantics, representation and
  pipeline ownership, evidence, resources, migration, and lifecycle. Review
  corrected exact binder policies, interface-argument kind checking, transient
  inference-kind ownership, Core-instantiation distinctions, and the complete
  evidence gate before CP-0009 was accepted.
- The dedicated worktree starts from `a1647ff`; baseline build and full
  repository verification pass. CP-0009 is accepted, the task and execution
  plan are authorized, and the branch remains based on the integrated
  predecessor and unmerged.
- The execution plan orders the closed type-site inventory and resource
  formulas early so omissions fail during implementation rather than closure.
- Task 2 retains contextual kind syntax and exact explicit binder lists across
  nominal, interface, equational, operational, and implementation headers.
  Parser evidence covers right-associated kinds, exact spans, omission versus
  explicit `Type`, token-complete recovery, every header-owner boundary,
  line-end and end-of-file termination, and contextual `Type` as either a kind
  atom or an ordinary implementation-head name. Mechanical resolver changes
  preserve predecessor semantics until kind resolution begins in Task 4.
- Task 2 passed independent semantic and parser-quality review after recovery
  ownership, synchronization context, exact `>` diagnostics, owner-token
  preservation, and contextual-name ambiguity were corrected. Focused tests,
  the full all-feature workspace suite, Clippy with warnings denied,
  formatting, all-target checking, and diff hygiene pass on the final change.
- Task 3 replaces the saturated `AppliedNominal` representation with one unary
  `Application` tree throughout production code. Resolution folds source
  arguments left while preserving the predecessor's saturation and failure
  boundary until Task 4. Type operations, paired application provenance, both
  retained Core transforms, independent Core validation, and evaluator nominal
  inspection use that tree. Core `TypeApplicationNode` remains the distinct
  simultaneous n-ary outer-scheme instantiation operation.
- Task 3 also closes the source-derived type-carrier and kind-site inventories.
  The production-wide recursive-owner guard rejects raw destructive mutation;
  exact resource and 32,768-level, 256 KiB-stack witnesses cover canonical
  operations, retained payloads, replacements, and normal error exits. Two
  independent reviews approve the final semantics and ownership boundary. The
  focused suites, full all-target and all-feature workspace suite, Clippy with
  warnings denied, formatting, all-target checking, test enumeration,
  `cargo xtask verify`, Rust documentation, Markdown lint, and diff hygiene pass
  on the final change.
- Task 4 assigns every declaration binder one canonical fixed `Kind` and makes
  present explicit binder lists complete and ordered. Omitted annotations and
  absent global or implementation lists receive `Type` in this phase; this is
  the accepted no-inference boundary, not a permanent language principle.
  Checked schemes and body-free summaries retain the ordered identity-kind
  pairs.
- Task 4 also adds iterative, budgeted Kind operations and one total resolved
  kind stage. The stage freezes local nominal and interface environments before
  declaration checking, uses owner-specific declaration environments, leaves
  the resolved-stage inference environment empty, authenticates direct
  body-free kind facts, and admits partial constructors where the enclosing
  rule accepts their residual kind. The public resolution pipeline has one
  fail-closed kind gate before it constructs a `ResolvedModule`.
- The new stage takes ownership of predecessor saturation and type-parameter
  application failures. Value-boundary failures now use
  `kind.expected-type`, non-function applications use `kind.not-applicable`,
  and application-domain or interface-argument mismatches use
  `kind.argument`. Structured diagnostics retain expected and found kinds,
  causal occurrence spans, and relevant declaration spans. Exact budgets,
  one-short atomic failures, and 32,768-level or 32,768-wide tests on 256 KiB
  threads cover Kind operations, synthesis, environments, provenance, body
  traversal, diagnostics, and teardown. The architecture inventory closes the
  new carriers and enforces the sole public gate.
- Task 4 closure authenticates declaration order as a complete, duplicate-free
  partition and authenticates constructor-provenance cardinality before any
  consumer uses the frozen environments. The kind stage stops at the first
  candidate owned by the later method-local, determination, or
  prerequisite-only check, so a later declaration cannot preempt that owner.
  Rendering and surface-kind conversion now publish and test their
  one-state-per-node resource formulas. The unused predecessor arity reason is
  removed; `resolve.type-kind` remains only for using an interface identity as
  an ordinary value type.
- Task 5 makes each Core outer scheme one ordered identity-kind carrier in
  `Type::Forall` and gives `TypeAbstractionNode` an independently retained copy
  of the same pairs. Elaboration, both Core transforms, interface selection,
  and evidence comparison preserve and authenticate those pairs. The existing
  n-ary `TypeApplicationNode` remains simultaneous outer-scheme instantiation;
  its arguments remain canonical unary monotypes.
- Independent Core validation now derives nominal constructor kinds from the
  immutable registry and checks binder ownership, order, scope, scheme and
  abstraction agreement, argument kinds, simultaneous substitution, and the
  kind-`Type` boundary for ordinary annotations. Inference escape and nested
  schemes remain invalid in monotype positions. Core evaluation values,
  frames, lookups, transitions, and runtime behavior are unchanged.
- Task 5 necessarily extends the plan's file scope into `src/types.rs` for the
  canonical `Type::Forall` carrier and into the private interface/evidence
  selector path that supplies the selected parameter kind during elaboration.
  This is the recorded carrier-scope deviation; it does not pull later linked
  authentication or inference integration into this task.
- Core construction and transform rebuilding remain bounded by
  `TYPE_WORK_LIMIT`. Independent Core validation retains one cumulative ledger
  across all passes with the accepted validator-local capacity
  `3 * TYPE_WORK_LIMIT`, or 983,040 units. The unchanged depth-96 interface
  witness uses 275,398 predecessor units plus 145,151 required Kind units, or
  420,549 total. The unchanged width-32,767 Core validation witness uses
  `22 * width + 7`, or 720,881 units. Exact and one-short tests cover the local
  capacity and operation boundary without a reset or separate Kind allowance.
- Task 5 semantic review found that structural registry admission still
  rejected valid higher-kinded payload applications before kind synthesis.
  The corrected split leaves application shape, domains, residual kinds, and
  the final kind-`Type` obligation to total kind synthesis while structural
  admission retains depth, nominal existence, ownership, inference escape,
  and nested-scheme checks. Exact direct-registry tests cover owner-parameter
  application, partial nominal arguments, and wrong-domain ownership; repeat
  semantic review approves the correction.
- Task 5 resource and Rust review found recursive error-path teardown in
  transform temporaries retained across later fallible work. Transform result
  types, type-application argument buffers, extracted tuple or constructor
  children, and rebuilt match patterns now remain in iterative owners until
  their terminal transfer. Four 32,768-deep probes on 256 KiB stacks cover a
  missing function remap, a one-short result clone after argument retention,
  parent-clone failure after child extraction, and a missing arm-body remap.
  Repeat resource and Rust review approves the correction with no unresolved
  finding.
- Task 6 gives every fresh inference identity one fixed `OMEGA` entry before
  publishing the identity in a type. Ordinary fresh variables receive `Type`,
  scheme instantiation copies each binder's declared kind, and constructor
  pattern variables copy the corresponding nominal parameter kinds. Missing,
  duplicate, and conflicting entries are internal invariant failures. Eligible
  local generalization copies the same fixed kind into an elaborator-owned
  generated `DELTA`; it does not add inferred or polymorphic kinds.
- First-order unification authenticates candidate kinds through the existing
  total Kind engine before publishing a solution. It accepts same-kind nominal
  constructors and partial applications, traverses both application children
  for unification and occurs checking, and does not synthesize type lambdas.
  Fused zonking authenticates reachable solved variables without a separate
  pre-scan. Solution, authentication-cache, generated-binder, and identity
  updates are transactional. Invariant, mismatch, infinite-type, and resource
  failures roll back only records published by the failing operation and
  preserve pre-existing state.
- The full workspace gate exposed imported hidden and opaque nominal identities
  as one missing candidate-kind source. Their authenticated body-free facts now
  produce a private checker-view `XI` sidecar containing only the frozen Kind
  and causal span. One canonical lookup serves materialized and non-materialized
  nominals during solution authentication. Hidden and opaque identities remain
  absent from nominal declarations, constructors, structural parameter
  lookups, checked summaries, and linked registries.
- An eligible anonymous-function local now generalizes a function-kinded and a
  `Type`-kinded inference variable into one ordered outer scheme. The retained
  Core abstraction and both outer `Forall` carriers agree on those kinds, a
  later occurrence instantiates them with `Pair<Int>` and `Bool`, and no scheme
  appears below a term-function arrow. Recursive and otherwise ineligible
  locals remain monomorphic.
- The public higher-kinded relay exposed a necessary predecessor boundary in
  linked value-scheme validation. Task 6 replaces exact nominal saturation at
  that boundary with one predecessor-owned structural pass followed by the
  canonical total Kind judgment for global, interface-method, and
  implementation-method value types. One graph-lifetime `XI` and owner-specific
  `DELTA` are reused across those facts; `OMEGA` is empty. Malformed retained
  facts remain `evidence.validation.*` failures. Higher-kinded evidence
  matching and exhaustive linked-fact authentication remain assigned to Tasks
  7 and 8.
- Task 6 resource evidence, refined by Task 7's shared Kind state machine, fixes
  scalar solution work at 17 units and deep solution work at
  `9C - 3D + 8`, where `C` is the candidate's type-cell count and `D` is its
  function depth. Generalizing `n` variables costs
  `3n + sum(3 + 2|K_i|) + Z(T)`. Linked validation separates 18 structural
  units, 20 Kind-judgment units, and four owner-`DELTA` type units for the
  higher-kinded `keep` scheme. After Task 7's shared-worklist refinement, its
  deep Kind judgment costs `6D + 3`, and
  graph-lifetime nominal retention costs
  `sum_nominal [2 + sum_parameter(|K| + 1)]`. The checker-view sidecar uses the
  same per-nominal formula, `2 + sum_parameter(|K| + 1)`: one record, one final
  `Type`, and each parameter Kind plus its `Arrow`. Exact, one-short, atomic,
  32,768-deep 256 KiB-stack, and unrelated-`OMEGA` witnesses cover each boundary
  without increasing a production limit or predecessor fixture.
- Independent Task 6 review found a deep candidate crossing a fallible
  occurs-check without an iterative owner, transaction logs that could remove
  pre-existing state on invariant failure, a duplicate linked structural pass,
  and resolution-only metadata for the shared Kind engine. The corrections add
  deep and tampered-state regressions, retain one structural pass, and enforce
  phase-neutral engine ownership plus live transient-site anchors. Repeat
  semantic and Rust/resource review approves the production and evidence
  boundaries with no unresolved important finding.
- Task 7 makes implementation matching candidate-only, rigid, first-order, and
  kind-preserving. Canonical defining binder records supply fixed Kinds;
  matching authenticates each newly created substitution without refining a
  goal variable. Overlap independently freshens both candidate heads, and both
  operations traverse the function and argument children of canonical
  applications. They do not add type lambdas or higher-order unification.
- Selection builds one canonical environment for each complete inference-free
  goal and preserves abstract, exact-current, then concrete candidate priority.
  Candidate ingress authenticates identities, canonical binder ownership,
  scope, methods, and prerequisites before atomic publication. The checker view
  carries authenticated body-free Kind mirrors for imported interface and
  implementation binders without duplicating Kind snapshots in evidence
  substitutions.
- Linked validation now checks each selected root and every retained
  substitution, including exact-current evidence, against canonical interface
  and implementation binder Kinds. Declaration prerequisites receive one
  structural admission and one owner/canonical Kind judgment. A pending goal
  uses a one-unit proof derived from its already authenticated prerequisite and
  exact same-Kind first-order substitutions instead of resynthesizing the goal.
  Task 8 retains body-free and hidden closure, non-direct routes, exhaustive
  imported-summary and evidence-carrier tampering, and newly independent
  post-body fields. Task 9 retains linked Core authentication.
- Exact Task 7 resource evidence records imported checker-view binders at
  `sum_i (1 + |Kind_i|)` type-work units, a width-`W` match at `18W + 8`
  constraint and `W` type-work units, and the final-substitution precharge
  prefix at `15W + 8`. Cloning `N` substitution arguments costs
  `N + sum_i |Type_i|` type-work units. Scalar match, overlap, and selection
  fixtures cost 24/5, 42/5, and 156/20 constraint/type units. Declaration
  head-plus-prerequisite authentication costs 12/4. Selected-root evidence
  costs 73 constraint units as `59 + 9 + 4 + 1`; exact-current evidence costs
  107 as `87 + 15 + 4 + 1`.
- Deep matching and overlap over `K = 2D + 1` Kind nodes cost `2K + 18` and
  `2K + 22` constraint units. The shared Kind engine costs `6D + 3` for a valid
  deep linked value and `6D - 1` for the residual mismatch. After retained
  origin and registry-row authentication, the complete public linked path costs
  `9D + 63 + O + 2`, where `O` is generated-origin depth and the final two
  units visit the resolved-global identity row and parameter. At `D = 32,768`
  and `O = 16,384`, 311,361 units fit the production default on a 256 KiB
  stack. Exact and one-short failures publish no partial selection,
  substitution, candidate, or linked capability.
- Task 8 authenticates every kind-bearing checked, summary, imported, hidden,
  selected, and linked fact before publication. Transparent constructor
  families retain their physical schemes only through the checked-summary to
  imported-fact transfer; those schemes are disposed before linked Core, which
  retains no redundant scheme carrier. Hidden and opaque nominal kinds remain
  frozen body-free facts rather than materialized private declarations.
- Task 8 tampering covers canonical binders, nominal families, interface and
  implementation facts, global and method schemes, prerequisites, selected
  roots, substitutions, route identities, post-body mirrors, and occurrence
  evidence. Each malformed fact fails at linked evidence validation before
  Core. Exact, one-short, retry, deep, wide, and 256 KiB-stack probes preserve
  the graph-wide budgets and dispose accepted and rejected states.
- Task 9 retains one private ordered resolved-global owner fact for each
  non-empty checked global scheme. The shared registry carries only the stable
  term owner and ordered resolved parameter identities; canonical variable
  records remain the only kind, spelling, and origin authority. Linked Core
  validation derives the owner only from an immediate `RecursiveBind` member
  initializer, requires exact owner and parameter order once, and rejects a
  sequential `Bind` or an unconsumed fact.
- Task 9 keeps generated Core type binders local. Complete capture-free
  generated identity substitution across one abstraction, its outer `Forall`,
  body, and applications is valid alpha-renaming. The original generated
  identity, span, and allocation ordinal are not external authority. Identity
  traversal and literal folding rebuild independently from the original
  validated program, share the immutable registry, and pass fresh module-aware
  validation.
- Ordered resolved-global retention costs `2S + R` type-work units for `S`
  non-empty owners and `R` identities, plus the charged owner-uniqueness index.
  Core matching costs `2R + K_R + S`, including canonical Kind comparison.
  Empty, missing, extra, duplicate, reordered, wrong-owner, wrong-position,
  nominal, interface-only, and unconsumed mutations reject without raising or
  resetting a limit.
- User approval of the converged Task 9 design is retained as
  [AD-0009](../decisions/AD-0009-ordered-resolved-global-binder-authority.md).
  The decision governs the compiler authentication boundary while the
  specification states only its observable validation relationship.
- Task 10 closes the diagnostic and public resource matrix. Structured library
  and CLI failures retain exact primary spans, expected and found kinds,
  declaration and route labels, stage ownership, and deterministic reason
  codes. Deep and wide public witnesses cover parsing, resolution, kinding,
  inference, matching, evidence, Core, observation, and accepted or rejected
  teardown on 256 KiB stacks. No production limit or evaluator behavior
  changes.
- Task 11 proves predecessor migration and the linked product corpus. Every
  predecessor-valid omitted kind annotation and absent global or
  implementation binder list remains valid without edits. Explicit `Type`,
  explicit list order, contextual nominal `Type`, partial higher-kinded
  application, exact linked implementation selection, imported constructor
  scheme transfer, summary disposal, Core transformations, independent
  validation, library observation, and CLI observation all have direct tests.
  Three repeat `gpt-5.6-sol`/`xhigh` reviews passed with no unresolved finding.
- Task 12 executable examples exposed a pre-specification resolver defect:
  parameterized declaration families were allocated in category order rather
  than the documented module-wide source order. `8c11cd3` installs declaration
  identities first, allocates every source type binder once through the
  cross-family declaration order, and then resumes the established
  dependency-safe family phases. Exact resolver, linked Core, architecture,
  resource, teardown, formatting, and Clippy gates pass; independent semantic
  and resource reviews pass. The ordered linked-owner design and strict Core
  forgery check remain unchanged.
- Task 12 now reconciles the specification and retains the informative
  [explicit-kind evidence report](../design/lib-ash/kinds-evidence.md). The
  report records 755 kind sites at `8c11cd3`: 697 physical fields, 33 contextual
  uses, and 25 transient work owners. The no-kind-inference boundary is stated
  as phase-dependent, not as a permanent language principle. The complete
  `lib-ash` milestone remains open and untagged. Final independent review,
  complete verification, retention, and lifecycle cleanup remain assigned to
  Task 13.

## Verification

Each plan checkpoint records focused RED and GREEN commands. Completion
requires reading the complete output of:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --workspace --all-targets --all-features
cargo clippy --locked --workspace --all-targets --all-features -- -D warnings
cargo test --locked --workspace --all-targets --all-features -- --list
cargo xtask verify
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Manual and independent review covers every CP-0009 evidence requirement,
including authority labels and links, contextual syntax, exact binder sets and
order, total `DELTA`/`OMEGA`/`XI`/`IOTA` kinding, canonical application,
scheme-versus-monotype separation, summary and Core authentication, failure
ownership, resource formulas and teardown, migration, exclusions, and the
unchanged evaluator state machine.

## Discoveries

Proposal review established that interface applications cannot use the
ordinary kind-`Type` value rule: their arguments must synthesize the selected
interface parameter's declared kind. It also established that total kind
synthesis needs a transient fixed `OMEGA` entry for every inference variable,
even though zonking removes those variables before summaries and Core.

The canonical unary semantic application and the existing n-ary Core
`TypeApplicationNode` are different operations. The former is structural type
syntax; the latter simultaneously instantiates one complete outer rank-1
scheme. Tests and validation must keep that distinction explicit.

Canonical application also makes a retained result type deep enough that
`Observation` needs iterative teardown. Implementing `Drop` prevents Rust
callers from moving its public fields directly. CP-0009 now records the
consuming `ObservationValue` and `ObservationParts` API that preserves captured
evaluation heaps and transfers or dismantles result types without recursive
drop. It also records that `TypeContext::insert` dismantles a displaced binding
fact instead of returning a raw recursive type that callers can ignore, and
that automatically dropped checked facts expose their structural types through
borrowing accessors rather than mutable raw fields. Public carriers without
automatic `Drop` remain caller-managed and use `discard_type_iteratively` when
disposing a potentially deep extracted type.

The type-bearing site map and additive resource formulas are implementation
inputs, not retrospective documentation. The architecture guard and exact
budget probes therefore precede summary and Core expansion.

After the linked value-scheme prerequisite moved, the Task 6 public
instantiation program could evaluate through the predecessor's structural
unifier, so it did not prove fixed inference kinds. The genuine `OMEGA` RED
evidence observes registration and exact copied kinds at the inference boundary
and separately rejects missing, duplicate, and conflicting entries.

A detached Task 5 version of the local relay stopped earlier at predecessor
linked value-scheme saturation. That product-level RED proves that the complete
Task 6 path was absent, but it does not isolate predecessor generalization's
hard-coded `Type` binder. Direct generated-`DELTA` and exact generalization
witnesses own that narrower evidence.

The unchanged wide elaboration fixture could not afford both a separate
solution-authentication scan and final zonking. Fusing authentication into the
single iterative zonk retains reachability-local work: 4,096 unrelated
`OMEGA` entries do not change the cost of solving one variable. The unchanged
width witness consumes 325,616 of 327,680 type-work units.

Linked value-scheme saturation was not a Task 7 evidence-selection concern.
It was an earlier structural admission rule that rejected the Task 6 public
witness before inference or Core. Replacing only that rule with canonical
kinding is therefore a Task 6 prerequisite; matching, selection, prerequisites,
goals, routes, hidden closure, and exhaustive linked authentication do not move.

The full workspace gate, rather than the focused Task 6 suites, exposed the
imported abstract-nominal gap. Fixed-kind solution authentication correctly
rejected an unknown nominal Kind, but the checker view had retained only the
hidden or opaque identity's display name. The authenticated imported fact
already owned its ordered parameter kinds. Freezing only the derived Kind in a
checker-only sidecar supplies that evidence without making the nominal or its
constructors structurally visible. Task 8 still owns exhaustive summary,
hidden-closure, route, and linked-fact authentication.

Task 7's first deep public linked witness exceeded the production default by
four units in the private Kind judgment and by much more when repeated public
passes were counted. A continuation machine now reuses the current result and
one continuation per composite node. Fusing checked-value structural admission
with exact resolved-value comparison removes a duplicate traversal without
skipping scope, identity, nominal, inference, scheme, tuple, or application
checks. The resulting private `6D + 3` formula fit at depth 32,768. Later
origin and resolved-global authentication produce the current public
`9D + 63 + O + 2` formula, which fits the same production limit at type and
kind depth 32,768 and origin depth 16,384.

Kind-aware matching does not reauthenticate complete heads that the resolved
kind gate already admitted. Its semantic responsibility begins at a new
candidate binding or overlap solution: synthesize the argument Kind, compare it
with the defining binder Kind, then retain the type. This avoids repeated deep
passes while keeping goals rigid and substitutions authenticated.

## Deviations

Task 3 refines the predecessor Rust API so `Observation` can dismantle a
canonical result type on drop without recursion or unsafe code. Borrowing moves
to `value()` and `ty()`; direct field moves, overwrites, and by-value
destructuring are replaced by borrowing and consuming accessors. CP-0009
records this source-compatibility exception and its heap-owning return types.
Checked requirements, constrained schemes, interface method facts, and
implementation facts likewise expose their automatically dropped structural
fields through borrowing accessors. `TypeContext::insert` now disposes
a displaced binding fact iteratively and returns nothing; repository callers
already ignored its previous raw `Option<Type>` result. Ash semantics, library
and CLI rendering, and evaluator behavior do not change.

Task 5 extends the planned carrier scope into `src/types.rs`, `src/interface.rs`,
`src/evidence.rs`, and `tests/interfaces.rs`. The first three own the canonical
kinded scheme and the private selected-interface kind needed to construct it;
the fourth proves that retention. This boundary does not implement linked
evidence authentication or inference integration assigned to later tasks.

Task 6 extends its planned implementation scope into `src/resolved.rs`,
`src/evidence_validation.rs`, `src/driver.rs`, and `tests/architecture.rs` for
the private checker-view nominal Kind sidecar, the narrow linked value-scheme
prerequisite, its independent resource ledger, and the closed multi-context
Kind inventory. The sidecar consumes already-authenticated direct import facts;
it does not advance Task 8's exhaustive authentication scope. The execution
plan records those files and added boundaries. Task 6 does not change `spec/`:
Task 12 remains the planned point where implemented behavior and retained
evidence update normative language truth.

Task 7 extends its original file scope into `src/kind.rs`, `src/resolved.rs`,
`src/evidence_validation.rs`, `tests/architecture.rs`, and `tests/kinds.rs`.
These files own the shared stack-safe Kind worklist, canonical checker-view
authority, the direct linked selected/declaration seams, and their closed
carrier inventory. The task does not modify `spec/`. It does not advance Task
8's body-free or hidden closure, non-direct route coverage, exhaustive imported
summary and evidence-carrier tampering, or remaining linked fields. It does not
advance Task 9's linked Core boundary.

Task 12 extends its specification-only file scope into `src/resolve.rs`,
`tests/resolution.rs`, and `tests/architecture.rs`. A new executable
specification witness found that interleaving an explicit implementation with
a later polymorphic global assigned resolved type-binder identities out of
module source order. The correction restores the existing identity contract
across all declaration families and records its two new transient preparation
fields. It does not change the ordered resolved-global carrier, Core
validation, evaluator behavior, or a production limit.

Task 12's independent architecture-decision, normative-authority, and
evidence-lifecycle reviews pass without findings, each with `gpt-5.6-sol` at
`xhigh` reasoning. All 57 executable specification tests, `cargo xtask verify`,
Markdown lint, relative-link checks, formatting, and diff hygiene pass at this
checkpoint. Task 13 retains the final all-target inventory and lifecycle gate.

The malformed-Core resource fixture grows from width 700 to width 1,000 so its
expanded work remains above the accepted validator-local `3 * TYPE_WORK_LIMIT`
capacity. Its expected `Resource` result is unchanged. The predecessor-valid
depth-96, width-32,767, and depth-32,000 witnesses retain their dimensions.

No semantic deviation from CP-0009 is currently known. Any product evidence
that exposes missing or incorrect semantics returns to proposal or design work
instead of being decided in this task.
