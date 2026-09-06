# DN-0028: Effect Ash Milestone Plan

- ID: `DN-0028`
- Status: exploring
- Related: [DN-0027](DN-0027-effect-ash-program-design.md) and
  [DN-0026](DN-0026-effect-ash-resource-first-milestones.md)

> This design note is informative. It plans authority transitions and evidence;
> it does not define current Ash, accept an architecture, accept a change
> proposal, create an implementation task, or authorize product work.

## Question

How should the `effect-ash` program in
[DN-0027](DN-0027-effect-ash-program-design.md) be turned into proposal-gated,
test-driven product increments, beginning with the minimum module-`newtype`
slice?

## Planning boundary

Current Ash remains the behavior in [the specification](../../spec/README.md).
At this note's planning checkpoint, no effect or `newtype` proposal was
accepted and no implementation task was active. That statement records the
input to this informative plan, not current artifact state. The specification,
trajectory, accepted proposals, and active tasks own later state. This note
therefore cannot be a task-owned execution plan. It is exact through
preparation and acceptance of the first change proposal, then records
checkpoint gates and likely implementation pressure at decreasing detail.

After each proposal is accepted, create one active task and one temporary
task-owned execution plan with exact RED tests, production edits, verification
commands, review assignments, commit boundaries, and a bounded work budget.
Remove those transition artifacts after that product checkpoint closes; do not
remove this note while it still explains the live milestone program.

No experiment is required by default. Add a disposable prototype only when the
proposal cannot settle one named question from the current semantic model and
existing evidence. State the comparison corpus and disposal rule before writing
experimental code.

The module-`newtype`, local-`newtype`, and resume-required kernel product
checkpoints are combined on `integration/effect-ash-foundations`. The
[local-newtype evidence](effect-ash/local-newtype-evidence.md) records lexical
identity, escape, validation, and erasure. Scoped exact evidence is implemented
and locally integrated on the milestone branch, with
[implementation evidence](effect-ash/scoped-evidence-evidence.md) recording
authentication, resource bounds, reviews, and the full gate. The forecast below
retains its original relative weights; it is not an elapsed-work ledger.
Capture/usage and checked discard are complete in the retained checkpoint;
their [evidence](effect-ash/capture-discard-evidence.md) records inference,
runtime behavior, reviews, full verification and transition cleanup.
Safe resource scope also has a complete verified product checkpoint; its
[evidence](effect-ash/resource-scope-evidence.md) records the retained contract
and simplification review. Verified local integration follows.

## Completion condition

The program is complete only when all of these are true on an integrated
`main`:

- module and local `newtype`, scoped exact evidence, the one-shot effect
  kernel, checked discard, safe resource scope, synchronous hooks, reliable
  cleanup, and one narrow foreign provider are current in `spec/` and product
  code;
- the combined source, diagnostic, linked, Core, transformation, runtime,
  resource, migration, and tamper corpus passes;
- pure programs retain the pure dialect and acquire no effect, continuation,
  provider, hook, or resource runtime state;
- a simplification review at safe resource scope and another at closure have
  removed unjustified carriers, passes, state, and syntax;
- a bounded downstream-seam audit confirms the documented identity, authority,
  Core, capture, and runtime boundaries against named proof, existential,
  suspension, concurrency, and dynamic-loading pressure cases, records residual
  risk, and finds no demonstrated contradiction in current retained behavior;
- transition artifacts have been cleaned up without confusing cleanup with
  integration; and
- the trajectory, retained evidence, documentation links, and milestone claim
  agree with the integrated result.

## Program order

```text
CP module newtype -> CP local newtype -> CP scoped exact evidence ---+
                                                                    |
CP resume-required effect kernel                                    |
    -> CP capture/usage + checked discard ---------------------------+
                                                                    |
                                                                    v
                                                       CP safe resource scope
                                                                    |
                                                                    v
                                                       CP synchronous hooks
                                                                    |
                                                                    v
                                                       CP reliable cleanup
                                                                    |
                                                                    v
                                                  CP narrow foreign provider
                                                                    |
                                                                    v
                                                       effect-ash closure
```

The arrows are authorization dependencies. Work on the pure identity track and
the effect-kernel track may overlap only while they have separate product
state. Once they share source, type, Core, or runtime carriers, serialize
implementation agents and use parallel agents only for read-only audits.

## Forecast and approval boundaries

The following is a relative forecast over a notional 100-unit milestone, not a
work authorization or a promise of elapsed time:

| Checkpoint | Forecast units |
| --- | ---: |
| Module `newtype` | 8 |
| Local `newtype` | 8 |
| Scoped exact evidence | 7 |
| Resume-required effect kernel | 17 |
| Capture/usage and checked discard | 9 |
| Safe resource scope | 16 |
| Synchronous hooks | 9 |
| Reliable cleanup | 11 |
| Narrow foreign provider | 10 |
| Integrated closure | 5 |
| **Total** | **100** |

The weights include proposal closure, product implementation, specification,
evidence, reviews, corrections, and transition cleanup. Re-estimate only at a
proposal boundary or at the mandatory safe-resource reassessment. Do not spend
later capacity to hide an unresolved semantic gap in an earlier checkpoint.

## Operating protocol for every retained checkpoint

### Authority

1. Reconstruct current behavior from `spec/`, accepted decisions, product
   tests, and the precise compiler/runtime seam.
2. Draft the next unused `CP-NNNN` from
   [the proposal template](../proposals/template.md). Keep it `proposed` while
   any source, type, evaluation, diagnostic, limit, or erasure rule is open.
3. Obtain explicit acceptance of the complete semantic delta and evidence
   obligations. Do not interpret approval of this program note as acceptance of
   a later proposal.
4. Only then allocate the next unused `TASK-NNNN`, create its task-owned plan
   under `docs/plans/`, and activate product work.
5. If implementation exposes absent or contradictory semantics, stop the task
   and return to proposal or design work.

### Isolated execution

Follow [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md). Start each
authorized checkpoint from the verified milestone integration tip in the local
ignored `.worktree/` directory. Confirm the branch name and worktree path are
unused, record the base commit, and verify the baseline before editing. Keep
one active product checkout. After checkpoint closure and authorized local
integration, verify the combined result, require a clean feature checkout,
prove its tip is retained, and remove its worktree and local branch. A merge
into `main`, push, or tag still requires separate authorization.

Use sub-agents by risk:

- high reasoning for semantic closure, continuation/resource rules, and
  proposal compliance;
- high reasoning for compiler/Core/evaluator implementation and architecture
  review;
- high reasoning for independent resource, tamper, and Rust-quality review;
  and
- medium reasoning for mechanical Markdown, link, manifest, and migration
  audits.

The current user-authorized upper bound is high reasoning.

Use one implementation agent at a time when checkpoints share product state.
Parallelize independent read-only audits and report every agent's assignment,
model class, and reasoning level.

### Test-driven product transition

For every production checkpoint in the accepted proposal:

1. write the named behavioral or tamper test;
2. run it and preserve the expected RED witness;
3. make the smallest coherent implementation change;
4. run the focused GREEN command;
5. run an independent semantic/authority review;
6. run an independent implementation/resource review;
7. correct every actionable finding and repeat affected tests;
8. inspect `git status --short`, `git diff`, and `git diff --check`; and
9. create the named local unsigned commit.

Update normative `spec/` only in the product transition authorized by the
accepted proposal. The branch specification remains prospective until the
complete checkpoint integrates into `main`.

### Evidence ladder

Each task-owned plan must include, where applicable:

- source acceptance and rejection;
- stable diagnostics with phase, reason, precedence, primary span, and causal
  labels;
- linked-carrier and independently validated Core tampering;
- Core transformation followed by revalidation;
- runtime observations and exact static-erasure or retained-runtime-state
  boundaries;
- exact-budget success, one-unit-short atomic failure, retry, and deep
  stack-safe success/failure teardown for compiler-owned structural work;
- predecessor source, CLI, executable-specification, and resource migrations;
- pure-program non-regression and locality guards; and
- independent semantic, architecture, Rust/resource, documentation, and
  simplification reviews.

Runtime cleanup and foreign effects do not inherit compiler retry or atomicity
promises. Their proposals must define partial completion and failure ownership
on their own terms.

## First proposal: module `newtype`

The first proposal used `CP-0012` and closed with its product checkpoint.
The following matrix and implementation skeleton retain that planning input,
not instructions to recreate its removed transition artifacts. Later proposals
must allocate fresh IDs from current Git history.

### Goal

Propose the smallest module declaration that introduces a fresh nominal type
over one representation field, reuses current module visibility and identity
transport, exposes wrapping and matching only where the constructor is
accessible, and erases the wrapper without allocation after the typed boundary
has been authenticated.

The increment must not add effects, local type declarations, runtime-fresh
identity, implicit coercion, representation-derived interface evidence, local
implementations, existentials, or evaluator-visible module state.

### Step 1: Freeze the current boundary

Read and cite the exact current rules in:

- `spec/syntax.md` for module declarations, constructors, patterns, and
  visibility syntax;
- `spec/name-resolution.md` for nominal and constructor identity, scope,
  imports, re-exports, and opacity;
- `spec/static-semantics.md` for kinding, constructor schemes, representation
  recursion, pattern typing, coverage, interfaces, and failure ownership;
- `spec/elaboration.md` for linked nominal registries, constructor evidence,
  Core construction, validation, and erasure boundaries;
- `spec/dynamic-semantics.md` for constructor allocation and observations; and
- `docs/decisions/AD-0007-typed-core-dialects.md` for the closed pure-dialect
  boundary.

Confirm the corresponding product seams rather than inferring behavior from
them:

- `src/lexer/token.rs`, `src/lexer/mod.rs`, `src/parser/grammar.rs`, and
  `src/parser/project.rs`;
- `src/surface.rs`, `src/resolve.rs`, `src/resolved.rs`, `src/kind.rs`,
  `src/types.rs`, and `src/elaborate.rs`;
- `src/core/dialect.rs`, `src/core/validate.rs`, and
  `src/core/transform.rs`; and
- `src/eval/machine.rs`.

Record the current fact that an ordinary payload constructor allocates a
constructor cell. A zero-cost wrapper therefore needs a typed lowering and
validation boundary; changing only syntax or evaluator allocation is
insufficient.

### Step 2: Settle the proposal decision matrix

The proposal must answer every row before acceptance:

| Question | Leading direction | Rejected unless new evidence requires it |
| --- | --- | --- |
| Surface form | A distinct `newtype` declaration shaped like current `type`, with exactly one constructor and one representation field. | An attribute hidden inside ordinary `type`, multiple constructors, zero fields, or multiple representation fields. |
| Visibility | Reuse private, public opaque, and public transparent declaration modes and current import/re-export identity transport. | Constructor-specific visibility or a new module export channel. |
| Representation authority | Authenticate the representation through defining-module and linked compiler facts until its last checked use; specify visibility-dependent public summary content separately. | Exposing a private or opaque representation merely to validate erasure, or trusting unauthenticated lowering metadata. |
| Parameters and kinds | Reuse explicit declaration parameters and current kind checking; require the fully applied representation to have kind `Type`. | New kind inference or higher-rank representation types. |
| Identity | Allocate one module-owned nominal declaration identity in source order; imports and re-exports preserve it. | Runtime regeneration, path-based identity, or equality from representation shape. |
| Representation recursion | State exactly whether and where the representation may mention its owner, based on meaningful zero-cost construction and destruction. | Silently inheriting ordinary guarded-data recursion. |
| Wrapping | Type-check an explicit accessible constructor from representation to nominal type, then lower through an authenticated zero-cost boundary. | Implicit coercion or reuse of an allocating ordinary constructor. |
| Matching | Type-check one irrefutable accessible constructor pattern and expose its representation binder, then lower without runtime tag inspection. | General sum coverage machinery or matching through opacity. |
| Interfaces | Require explicit implementations and ordinary evidence selection. | Constraint lifting, representation inheritance, generalized coercions, or runtime lookup. |
| Core | Preserve nominal type identity and authenticate the representation conversion until its last checked use; choose the smallest validated lowering compatible with the closed pure dialect. | An unchecked type cast, a runtime wrapper cell, or an effect operation. |
| Runtime storage | The wrapped value uses the representation's storage without a wrapper allocation. | Runtime nominal registry, wrapper identity test, or module value. |
| Observation | Specify whether and where statically known nominal type information affects rendering despite representation storage. | Inferring rendering solely from zero-cost storage. |
| Allocation evidence | Use a structural post-erasure assertion and an internal evaluator unit observation in `src/eval/machine.rs`; add only test-scoped support in `src/eval/value.rs` if direct observation is otherwise unavailable. | A production heap-inspection API or an inference from trace events that do not record allocation. |

Compare the smallest viable Core directions in the proposal:

1. a dedicated typed zero-cost wrap/unwrap family validated in pure Core and
   erased before ordinary evaluation;
2. an authenticated conversion certificate attached to an existing Core
   family, retained through independent validation and both transforms, then
   erased only at the validated evaluator boundary; and
3. an ordinary constructor with an evaluator special case, retained only as a
   rejected comparison control because it adds evaluator-visible
   classification and a persistent branch.

Prefer the direction with the fewest retained nodes and no evaluator branch,
provided independent Core validation can still reject forged nominal-to-
representation conversions. Alternative 2 is not viable if it leaves an
existing Core node with disagreeing nominal and representation types or
consumes its certificate before validation. Alternative 3 would require an
explicit relaxation of this slice's no-evaluator-branch boundary and new
evidence; it is not a leading implementation direction. If the first two
cannot be distinguished by
static reasoning and a small hand-constructed tamper corpus, this note governs
one bounded Core-only experiment. Its question is whether existing pure Core
can authenticate and erase the conversion without a retained evaluator node.
Compare independent tamper rejection, both transforms followed by revalidation,
evaluator locality, allocation behavior, and retained carrier/resource cost.
Dispose of all prototype code and syntax after recording the evidence unless a
later accepted proposal and task adopt the representation. Do not experiment
with surface syntax merely to compare spellings.

Before acceptance, confirm that new representation-conversion authority stays
localized at the nominal-registry, lowering, Core-validation, and transform
boundary. Record the precise replacement or extension seam through which local
lexical identities can later authenticate conversions. Do not spread module
provenance into the evaluator or implement the local identity class early.

### Step 3: Define the pre-implementation corpus

Before proposing acceptance, name exact positive cases:

- two private module `newtype` declarations over `Int` remain unequal;
- parameterized wrapping and matching preserve the declared kind and
  representation;
- public transparent import and re-export preserve one defining identity and
  expose wrapping and matching;
- public opaque import and re-export preserve the nominal identity but reject
  constructor use;
- a hidden carrier can cross existing exported operations without exporting a
  name;
- explicit interfaces may be implemented for the new nominal identity; and
- wrapping, matching, linked Core transformation, evaluation, the proposal's
  chosen rendering rule, and teardown show no wrapper allocation.

Observe allocation structurally after lowering and with the named internal
evaluator unit test
`eval::machine::tests::module_newtype_wrapper_allocates_no_constructor_cell`.
Do not expose evaluator heap inspection as product API merely to support this
evidence.

Name exact negative and tamper cases:

- malformed declaration shape and recovery;
- duplicate type or constructor spelling;
- wrong representation kind and the chosen recursive-representation boundary;
- missing or opaque constructor access;
- nominal/representation mismatch without explicit wrapping;
- absent implicit interface evidence despite representation evidence;
- visibility-specific summary changes to identity, owner, access, parameter
  order, kind, or any representation fact that the accepted proposal permits
  that summary to carry;
- defining-module, linked, and Core changes to whichever owner,
  representation, conversion direction, binder, source, or erased-form facts
  the accepted proposal chooses to retain; and
- one-unit-short resource failures at every newly retained compiler carrier,
  with atomic retry and deep stack-safe disposal.

Preserve the ordinary nominal, module visibility, interface, constructor,
coverage, pure Core, and evaluator corpus as migration evidence.

### Step 4: Draft and review `CP-0012`

Create only after Steps 1–3 converge:

- `docs/proposals/CP-0012-module-newtype.md`; and
- the corresponding entry in `docs/proposals/README.md`.

Use every section in [the proposal template](../proposals/template.md). Link
each affected specification section. State exact resulting specification
truth, diagnostic ownership and precedence, resource policy, Core/runtime
boundary, migration, exclusions, and required evidence.

Run:

```text
markdownlint --disable MD013 -- docs/proposals/CP-0012-module-newtype.md docs/proposals/README.md
git diff --check
```

Check every changed relative link. Assign an extra-high semantic reviewer, a
high compiler/Core reviewer, and a high evidence/resource reviewer. Include an
explicit downstream-pressure audit of local and runtime generativity,
existential identity escape, and proof-authority separation; it preserves
extension options without importing those later semantics. Correct all
findings, repeat affected checks, and present the full proposal for explicit
acceptance. Do not create an implementation task while its status is
`proposed`.

## Module-`newtype` execution skeleton after acceptance

This section is not executable authorization. Once CP-0012 is accepted, recheck
the next task ID; at present it would be `TASK-0019`. Create:

- `docs/tasks/TASK-0019-implement-module-newtype.md`;
- `docs/plans/YYYY-MM-DD-module-newtype.md` owned by that task;
- entries in the proposal and task indexes; and
- a dedicated `.worktree/cp0012-module-newtype` product worktree from the
  then-current verified `main`.

The task-owned plan must turn the accepted semantics into these TDD
checkpoints. It must replace tentative file lists and test names with the exact
ones justified by the proposal.

### Product checkpoint A: syntax and projection

Likely files:

- `src/lexer/token.rs`
- `src/lexer/mod.rs`
- `src/parser/grammar.rs`
- `src/parser/project.rs`
- `src/surface.rs`
- `tests/newtypes_syntax.rs`
- `tests/lexer.rs`
- `tests/parser.rs`

First RED command shape:

```text
cargo test --locked --test newtypes_syntax module_newtype_projects_one_representation_field -- --exact
```

Cover keyword boundaries, all three visibility modes, parameters and kinds,
the accepted declaration shape, excluded shapes, token-complete recovery, span
retention, and exact syntax-resource formulas.

### Product checkpoint B: identity, resolution, and summaries

Likely files:

- `src/surface.rs`
- `src/resolve.rs`
- `src/resolved.rs`
- `src/kind.rs`
- `tests/module_newtypes.rs`
- `tests/module_resolution.rs`
- `tests/module_visibility.rs`
- `tests/library_imports.rs`

First RED command shape:

```text
cargo test --locked --test module_newtypes module_newtype_identity_survives_facade_reexport -- --exact
```

Cover source-order identity, distinct same-representation declarations,
private/opaque/transparent access, diamonds and aliases, kinded parameters,
body-free summary authentication, one-short publication, and summary tampering.

### Product checkpoint C: typing, explicit interfaces, and lowering

Likely files:

- `src/types.rs`
- `src/elaborate.rs`
- `src/evidence.rs`
- `src/evidence_validation.rs`
- `tests/module_newtypes.rs`
- `tests/interfaces.rs`
- `tests/interface_selection.rs`
- `tests/diagnostics.rs`

First RED command shape:

```text
cargo test --locked --test module_newtypes representation_does_not_supply_nominal_interface_evidence -- --exact
```

Cover constructor synthesis and pattern checking, the accepted recursion rule,
nominal mismatch, explicit implementation, absent inherited evidence, failure
precedence, complete diagnostic spans, and poisoned-state refusal to publish.

### Product checkpoint D: Core authentication and zero-cost execution

Likely files:

- `src/core/dialect.rs`
- `src/core/validate.rs`
- `src/core/transform.rs`
- `src/elaborate.rs`
- `src/eval/machine.rs` for the internal allocation test; production changes
  only if the accepted representation requires them
- `src/eval/value.rs` only for test-scoped allocation observation if needed
- `tests/core_validation.rs`
- `tests/semantics.rs`
- `tests/architecture.rs`

First RED command shape:

```text
cargo test --locked --test core_validation module_newtype_conversion_authenticates_representation -- --exact
```

Cover every accepted conversion direction, forged owner/representation/source,
both Core transforms followed by revalidation, runtime equivalence with the
representation, absence of constructor-cell allocation, deep execution, and a
locality guard that pure non-`newtype` programs remain unchanged.

Run the internal allocation observation explicitly:

```text
cargo test --locked eval::machine::tests::module_newtype_wrapper_allocates_no_constructor_cell -- --exact
```

### Product checkpoint E: resources, specification, and closure

Likely files:

- `tests/newtype_resources.rs`
- `tests/corpus.rs`
- `tests/spec_examples.rs`
- affected `spec/*.md`
- a retained evidence report under `docs/design/effect-ash/`
- `docs/trajectory.md`

Run the focused resource suite, every affected integration test, and finally:

```text
cargo xtask verify
markdownlint --disable MD013 -- docs spec
git diff --check
```

Audit all changed relative links and executable specification examples. Run
semantic/specification, Core/runtime, Rust/resource, and simplification
reviews. Confirm all CP-0012 evidence, remove the completed proposal, task, and
task-owned plan from the product branch, retain only current specification,
product code/tests, justified evidence, and trajectory state, and rerun full
verification. Cleanup is not integration, a tag, or a milestone claim.

Suggested local commits after each reviewed GREEN boundary are:

```text
docs: authorize module newtype implementation
feat: parse module newtype declarations
feat: retain module newtype identities
feat: check and lower module newtypes
test: retain module newtype evidence
docs: specify module newtypes
docs: close module newtype transition
```

The task-owned plan may combine or rename commits when the accepted proposal
shows a smaller coherent boundary. It must not combine semantic checkpoints to
hide a missing RED witness or review.

## Later proposal capsules

These capsules define prerequisites and evidence questions, not syntax or
implementation authorization.

Before any later proposal is accepted, expand its row in this compact evidence
forecast into named cases and exact ownership. The later task-owned plan adds
RED commands and implementation-level formulas; it does not invent the already
accepted evidence obligation.

| Checkpoint | Positive and runtime evidence | Rejection, diagnostic, and tamper evidence | Migration and resource evidence |
| --- | --- | --- | --- |
| Local `newtype` | Nested, sibling, and shadowed identities; every proposal-approved abstract flow; deterministic erasure. | Name/value/closure/abstract-return escape matrix; recursive/generalization failures with owned spans; forged lexical owner, scope, identity, and Core facts. | Local binding, recursion, polymorphism, nominal, and pure-runtime predecessors; exact local-identity retention and teardown. |
| Scoped exact evidence | Identity-equal complete goal selected at the declared lexical point, including every accepted improvement and prerequisite case; evidence validates and erases. | Wrong identity, stale scope, representation derivation, global hijack, local search, precedence disagreement, and linked/Core selection forgery with stable reasons. | Existing abstract, exact-current, concrete, fixed-snapshot, recursive-prerequisite, CLI, Core, and resource corpus; exact plan/source retention. |
| Resume-required effect kernel | Closed/open rows chosen by the proposal; ordered nested handlers, forwarding, discharge, one immediate resume, deep operation chains, validated Core transforms, and machine traces. | Unhandled or wrong-identity operation, row disagreement, handler-order conflation, continuation escape, zero or second resume, and forged Core operation/handler/control carriers with phase-owned diagnostics. | All pure syntax/type/Core/runtime witnesses; exact row/handler/control budgets, atomic compiler publication, and small-stack disposal. |
| Capture/usage and checked discard | One resume or one safe checked discard across the proposal's capture classes; closure and continuation capture observations. | Duplication, second completion, escape, discard with live obligation, inconsistent capture metadata, and forged Core usage facts with causal diagnostics. | Resume-required kernel and ordinary closure capture; exact capture-analysis work, retry, and deep teardown. |
| Safe resource scope | Separate acquisitions, identity-local operations, exact provider relation, and every explicitly admitted normal/rejected/nested exit; runtime state lasts exactly as chosen. | Cross-acquisition mix, value/closure/continuation escape, unsafe discard, missing or wrong provider authority, unsupported exit with live obligations, and static/Core/runtime carrier tampering. | Pure and effect predecessors; exact identity/evidence/capture/handle-or-witness retention, release, locality, and small-stack scope teardown. |
| Synchronous hooks | Registration, ordered inline publication, chosen chain-mutation observation, deregistration, and visible subscriber effects while dependencies live. | Wrong hook/payload, stale registration, captured-identity escape, ordering/failure masking, unsupported live-obligation failure, and forged registration/Core authority. | Resource/effect predecessors; exact chain update/publication work, capture retention, deregistration, and deep subscriber failure teardown. |
| Reliable cleanup | Exactly-once cleanup in the chosen order for every admitted return, discard, abort, unwind, subscriber failure, and partial acquisition case. | Double/missed/out-of-order cleanup, failure during cleanup, partial completion, masked primary failure, stale capture, and forged cleanup ownership. | Resource and hook predecessors; explicit runtime order/state measurements and stack-safe nested cleanup, without assuming retry or atomic external effects. |
| Narrow foreign provider | One provider success, typed native failure, exact identity/authority preservation, and cleanup across complete and partial acquisition. | Forged static evidence, handle substitution or leak, incorrect rollback, stale runtime state, invalid native result, and linked/Core/foreign-boundary tampering. | All cleanup/resource predecessors; exact static-evidence last use and runtime handle, optional witness, and cleanup-state lifetime with pure locality. |

### Local `newtype` — forecast 8 units

The product checkpoint implements sequential private declarations, stable
lexical identity, joint nominal/constructor shadowing, rigid generalization,
outward escape rejection, identity-free closure capture, and one erased Core
scope. It reuses the module-newtype conversion path. The
[retained evidence](effect-ash/local-newtype-evidence.md) covers nesting,
sibling distinctness, preceding representation scope, typed and runtime use,
Core authentication, exact resource boundaries, and teardown. Local `impl`
search, runtime-fresh identity, and existential packaging remain excluded.

### Scoped exact evidence — forecast 7 units

Prerequisite: integrated local `newtype`.

The implemented checkpoint supplies private sequential `with` declarations for one exact complete
application whose selection key contains an active local nominal. Abstract and
exact-current evidence precede the lexical source; concrete matching follows.
The existing fixed-snapshot forward improvement and complete-goal prerequisite
rules remain intact. The first pure `Read<Token, Int>` relation passes through
direct and constrained calls; fifty interaction cases retain the expanded
behavioral boundary.

The checkpoint authenticates every retained source, method, parameter, capture
use, and actual scope, including unused declarations. Exact resource and
predecessor checks, both independent reviews, and the full verification gate
pass. Local integration is separate from integration into `main`.
This grants no resource, provider, or proof authority and
adds no local implementation search, runtime lookup, or checked discard. The
original seven-unit forecast remains a relative planning weight, not measured
work or a fresh implementation budget.

### Resume-required effect kernel — forecast 17 units

Prerequisite: none from the identity track; integration waits for resource
scope.

The proposal must define operation/API identity, row syntax and shared semantic
type representation, kinding, equality, unification and inference boundary,
open and closed rows, duplicates, forwarding, ordered nested handlers,
discharge, immediate non-escaping continuation typing, exactly one resume,
diagnostics, small-step semantics, production effect Core, validation,
transforms, and explicit-machine entry and transitions.

Likely product pressure crosses the surface/resolved/type/elaboration path,
`src/core/dialect.rs`, `src/core/validate.rs`, `src/core/transform.rs`, and
`src/eval/machine.rs`. Preserve a separate closed pure dialect and its no-effect
locality guard. Do not turn evaluator frames into implicitly capturable control.

### Capture/usage and checked discard — forecast 9 units

Prerequisite: integrated resume-required effect kernel.

The accepted checkpoint implements explicit nullary discard, inferred
request-carried obligations, exactly-once completion, non-escape, independent
Core validation and moved-capture release. Known and imported functions retain
finite control summaries; unknown relevant obligations fail closed. The
[evidence](effect-ash/capture-discard-evidence.md) records tests and completed
inference/runtime reviews, full verification and transition cleanup.
The contract is one resume or one checked discard, never duplication, a second
completion, escape, or discard of unaccounted obligations.

This is not a complete ownership, borrowing, lifetime, multiplicity, or replay
system. Its corpus must nevertheless be strong enough that resource scope does
not need to replace the capture representation.

### Safe non-foreign resource scope — forecast 16 units

Prerequisites: integrated scoped exact evidence and checked-discard kernel.

The complete product checkpoint provides one sealed mutable-cell API and a
generative acquisition expression. The scope owns release; reusable handles
carry activation identity without owning the payload. Stored dependencies and
request-carried completion obligations separately prevent escape and unsafe
discard. Normal completion releases the cell; capture/resume preserves it.
Unsupported exits do not gain implicit cleanup.

The [evidence record](effect-ash/resource-scope-evidence.md) covers separate and
overlapping acquisitions, hidden captures, imported abstractions, provider/Core
authentication, exact resources, pure locality and full verification. Both
independent reviews and the simplification/downstream reassessment pass.
No additional proof, existential or hook machinery is justified by this slice.
The original 16-unit weight closes after verified local integration; it is not
measured expenditure. Hooks still require their own proposal and authorization.

### Synchronous typed hooks — forecast 9 units

Prerequisite: integrated safe resource scope and its reassessment.

The proposal must define hook identity and payload, registration resource,
subscriber effects, sequential order and priority, handler placement,
deregistration, captured identities, chain mutation observation, and the
restricted failure/capture boundary before reliable cleanup. Exclude
suspension, parallel fan-out, async completion, and a universal event bus.

The representation must permit later suspension without replacing the hook API
or adding a second effect runtime. Until reliable cleanup, reject any subscriber
failure or exit whose live obligations the hook slice cannot discharge.

### Reliable cleanup — forecast 11 units

Prerequisite: integrated synchronous hooks.

The proposal must enumerate all admitted exits, cleanup owners, LIFO or
dependency order, exactly-once behavior, destructor effects, handler unwind,
checked discard, subscriber failure, partial acquisition, partial cleanup, and
cleanup-failure ownership and combination. Runtime cleanup is not presumed
atomic or retryable.

Evidence needs an explicit exit matrix, order trace, nested obligations,
failure during cleanup, retained capture, deep stack-safe teardown, and proof
that unsupported exits remain rejected.

### Narrow checked foreign provider — forecast 10 units

Prerequisite: integrated reliable cleanup.

The proposal must select one statically named provider boundary and define
trusted static evidence, runtime handle introduction, whether any distinct
runtime identity witness is necessary and what purpose it serves, authority
preservation, partial acquisition rollback, native-to-typed failure
translation, lifetime, Core validation, and the last use of each static and
runtime carrier.

Static evidence may erase after authentication; the handle, cleanup state, and
any separately justified runtime identity witness remain through their declared
lifetime. Exclude general ABI design, dynamic libraries, package resolution,
runtime interface lookup, and a provider registry.

### Integrated closure — forecast 5 units

Prerequisite: every selected product increment integrated into `main`.

Run the combined effect/resource/hook/foreign corpus and all predecessor
migration tests. Audit specification truth, diagnostics, authority provenance,
Core dialect separation, transformed-Core revalidation, runtime state,
resources, deep teardown, and pure locality. Request independent effects,
proofs, existential/dynamic-composition, implementation/resource, and
documentation reviews. Remove unjustified state and transition artifacts,
update the trajectory and retained closure evidence, run `cargo xtask verify`,
Markdown lint, link checks, and diff hygiene, then request explicit approval for
integration and any milestone tag or push.

## Stop and replan conditions

Stop the current checkpoint rather than improvise if it requires:

- semantics absent from or inconsistent with its accepted proposal;
- an identity class, row algebra, continuation multiplicity, lifetime,
  cleanup, hook, or provider rule assigned to a later proposal;
- a second type checker, constraint solver, evidence-selection pipeline,
  effect runtime, evaluator, or runtime interface registry;
- a general capability, ownership, borrow, region, existential, proof,
  scheduler, replay, dynamic-loading, ABI, or package system;
- a persistent Core/runtime architecture choice without accepted authority;
- weakening independent linked/Core validation, static evidence provenance,
  pure-dialect closure, atomic compiler publication, or stack-safe disposal;
- broad production resource-limit increases instead of a bounded carrier and
  exact accounting; or
- work beyond the checkpoint's separately approved budget.

At a stop, preserve RED evidence and review findings, update the proposal's
open question or a governing design note, and ask for the semantic or budget
decision. Do not borrow future scope merely because downstream pressure is
known.

## Open questions

The module-`newtype` decision matrix and independently validated zero-cost
conversion were the immediate open questions when this plan was written.
The completed module-`newtype` checkpoint resolves them for module scope. The
completed resume-required effect-kernel checkpoint also resolves the initial
row, handler, and one-shot control questions. The local-newtype checkpoint
settles sequential lexical identity, escape, and erased scope validation.
Scoped exact evidence settles pure introduction, precedence, improvement,
authentication, and erasure. The branch results are not current on `main`.
The completed capture/discard checkpoint settles bounded continuation
abandonment. Resource-scope composition now has a verified product checkpoint;
local integration remains pending. This informative plan authorizes neither
expansion nor integration into `main`.
