# DN-0027: Effect Ash Program Design

- ID: `DN-0027`
- Status: exploring
- Related: [DN-0026](DN-0026-effect-ash-resource-first-milestones.md),
  [DN-0028](DN-0028-effect-ash-milestone-plan.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md), and
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This design note is informative. It does not define current Ash, accept an
> architecture, authorize a language change, or authorize product
> implementation.

## Question

What is the smallest causally ordered program that can close `effect-ash` at a
useful checked foreign-resource boundary while preserving clean extension seams
for later suspension, concurrency, proofs, and existentials?

## Current context

At this design note's original planning boundary, the
[specification](../../spec/README.md) defined pure, rank-1, passively linked
Ash. Module structure and interface selection erased before evaluation, and
Ash had no effect rows, handlers, source continuations, resource lifetimes,
runtime interface lookup, or dynamic module loading. The completed
module-`newtype`, local-`newtype`, and resume-required effect-kernel checkpoints
supersede the first parts of that historical inventory on `main`.

[DN-0026](DN-0026-effect-ash-resource-first-milestones.md) supplies the
resource-first decomposition. It remains exploratory evidence. This note
records the current program-level planning direction under the repository's
[artifact authority](../project/artifacts.md); it does not promote DN-0026's
candidate semantics into current Ash.

[AD-0007](../decisions/AD-0007-typed-core-dialects.md) requires closed typed
Core dialects and an operation-family boundary. The effect-kernel checkpoint
uses that boundary while retaining the closed Pure dialect.
[AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md) provides the
explicit stack-safe evaluator machine used by the kernel; its frames remain
implementation state rather than source-language continuations.

The retained nominal carrier distinguishes module and lexical declarations.
The local checkpoint uses one erased Core scope and permits identity-free
closure escape. It adds no runtime-fresh identity class. The kernel adds the
bounded effect-row form. The scoped-exact-evidence checkpoint is implemented
and verified; its [implementation evidence](effect-ash/scoped-evidence-evidence.md)
records the behavioral cases, independent authentication, resource bounds,
and reviews. Pure supplied methods
establish neither provider nor proof authority. The locally integrated
[safe-resource checkpoint](effect-ash/resource-scope-evidence.md) now supplies
acquisition-local activation, stored-dependency checks and scope-owned release.
The selected slices are integrated into `main`; final verification is recorded
in the [closure evidence](effect-ash/milestone-closure-evidence.md).

## Closure boundary

The selected `effect-ash` closure boundary comprises these retained
capabilities:

1. allocation-free module `newtype` declarations;
2. lexically scoped local `newtype` declarations;
3. trusted scoped evidence for one exact complete interface goal;
4. identity-bearing effect rows, ordered handlers, and a resume-required
   one-shot kernel;
5. the minimum capture and usage rules needed to add checked discard and thus
   affine one-shot completion;
6. a safe, non-foreign resource scope;
7. synchronous typed hooks;
8. reliable cleanup; and
9. one narrow, checked foreign provider.

The following remain later work: suspension and async hooks, concurrency,
multi-shot or replayable control, general foreign ABI design, dynamic loading,
existential packaging, and proof language features.

## Causal program

```text
Module newtype -> Local newtype -> Scoped exact evidence -----------+
                                                                   |
Resume-required effect rows + ordered handlers                      |
    -> Minimal capture/usage rules + checked discard ---------------+
                                                                   |
                                                                   v
                                                      Safe resource scope
                                                                   |
                                                                   v
                                                      Synchronous hooks
                                                                   |
                                                                   v
                                                      Reliable cleanup
                                                                   |
                                                                   v
                                                 Narrow foreign provider
                                                                   |
                                                                   v
                                                     effect-ash closure
```

The identity track and the effect-kernel track can progress independently.
They first need to compose at safe resource scope. Checked discard follows the
resume-required kernel because captured obligations must be known before the
checker can permit a continuation not to resume. Before checked discard, a
handled continuation must remain within the immediate handler call and resume
exactly once. Afterward, affine one-shot completion means either one resume or
one checked discard; escape, duplication, a second resume, and an unaccounted
discard remain invalid.

The program orders synchronous hooks before reliable cleanup so the first
general cleanup matrix can include subscriber failure and deregistration. This
is a chosen closure order, not a claim that hooks and cleanup have an inherent
semantic dependency in every possible Ash design. Before reliable cleanup, the
resource and hook proposals must enumerate their admitted exits and statically
reject any exit whose live obligations they cannot discharge.

Cleanup precedes a foreign provider because native acquisition must not be
admitted before partial and abnormal exits have an owned cleanup rule. Safe
resource scope is an explicit reassessment point. Its evidence may simplify
later hook, cleanup, or provider work, but it cannot silently broaden or weaken
an accepted earlier proposal.

## Authority and lifecycle

Each retained semantic checkpoint follows one transition:

```text
design evidence -> proposed CP -> accepted CP -> active task
    -> test-driven product and specification change
    -> independent reviews -> cleanup -> approved integration
```

The proposal owns the semantic delta. The task owns execution. An updated
`spec/` becomes current Ash only when the complete product checkpoint
integrates into `main`. A persistent, separately converged non-language choice
requires an architectural decision. A task or implementation detail must not
resolve missing semantics.

An experiment is not a default checkpoint. It is warranted only when a named
semantic or representation question cannot be settled from the current model
and existing evidence. Any experiment must state its comparison criteria and
retention or disposal rule under a design note. Experimental syntax and code
do not become product behavior without an accepted proposal and active task.

Transition proposals, tasks, and task-owned execution plans leave the product
branch after their retained checkpoint closes; Git preserves their history.
That cleanup does not close or tag `effect-ash`. Only the integrated combined
corpus, simplification audit, documentation review, and trajectory update can
support a milestone-completion claim or tag.

[AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md) governs the
local worktree lifecycle. The milestone integration branch is the continuation
anchor between checkpoints; completed feature checkouts and branches are
removed only after clean-state and retained-ancestry checks.

## Checkpoint gates

| Checkpoint | Purpose | Questions an accepted proposal must settle | Retained exit evidence |
| --- | --- | --- | --- |
| Module `newtype` | Add a pure generative nominal abstraction whose wrapper and pattern erase without allocation. | Grammar, visibility, representation admission, identity, constructor access, kinding, summaries, lowering, and Core authentication. | Same representation but distinct nominal identity; module visibility/import/re-export corpus; no runtime wrapper or effect machinery. |
| Local `newtype` | Add lexical nominal identity without local implementation search or existential packaging. | Scope, identity allocation, shadowing, recursive-group placement, generalization, lowering, Core identity scope, and a matrix for name escape, inferred hidden-value flow, closure capture, abstract return, and excluded existential escape. | Nested and sibling distinctness; legal and rejected escape cases chosen by the proposal; deterministic erasure and forgery rejection. |
| Scoped exact evidence | Admit trusted evidence for one identity-equal complete interface goal within a lexical scope. | Introduction authority, behaviorally distinct authenticated lexical evidence, selection precedence, improvement participation, lifetime, authentication, and erasure. | Pure relation corpus; no representation-derived evidence, local `impl` search, global hijack, or runtime lookup. |
| Resume-required effect kernel | Establish identity-bearing rows, ordered forwarding handlers, and immediate non-escaping control that resumes exactly once. | Shared row type/equality/kinding/unification boundary; row algebra and inference; operation/handler identities and types; forwarding, order, and discharge; continuation non-escape; failure ownership; production effect Core dialect, validator, transforms, evaluator entry, and machine transitions. | Small calculus and source/Core/runtime corpus; pure executable dialect remains closed and unchanged; evaluator frames are not implicitly capturable. |
| Capture/usage and checked discard | Add affine one-shot completion when captured obligations make discard safe. | Minimum capture classification, usage rule, discard rule, non-escape, diagnostics, Core metadata, and independent validation. | Exactly one resume or one checked discard; escape, duplication, second resume, unsafe discard, and forged capture facts rejected before runtime. |
| Safe resource scope | Compose generative identity, exact provider evidence, effects, and usage into a non-foreign scoped resource. | Acquisition freshness, shared identity carrier, handle ownership, provider evidence, identity-local discharge, value/closure/continuation escape, and the complete set of exits admitted before reliable cleanup. | Separate acquisitions cannot mix; lifetime and obligation accounting holds for each explicitly admitted normal, rejected, and nested path; unsupported exits with live obligations are rejected; pure programs gain no runtime state. |
| Synchronous hooks | Add typed named sequential publication while resource dependencies remain live. | Hook identity and payload, subscriber effects, order, registration lifetime, chain mutation observation, and the restricted pre-cleanup failure/capture boundary. | Registration/publication/deregistration and ordering corpus; no suspension, parallel publication, or universal event bus; unsupported live-obligation failures are rejected. |
| Reliable cleanup | Extend cleanup to every admitted return, discard, abort, unwind, subscriber failure, and partial acquisition path. | Cleanup ownership, order, exactly-once behavior, destructor effects, partial completion, and cleanup-failure ownership. | Exit matrix, exact-order trace, cleanup-failure and partial-completion observations, retained-capture, and small-stack disposal evidence. |
| Narrow foreign provider | Cross one checked native boundary without a runtime interface registry or general ABI. | Trusted static evidence and runtime handle introduction, authority preservation, partial rollback, typed native failure, lifetime, Core validation, and last-use boundaries. | One provider's success/failure/tamper corpus; static evidence erases after its last checked use, while runtime identity, handle, and cleanup state remain until their declared lifetime ends; no dynamic loader or package format. |
| Milestone closure | Demonstrate that the retained slices compose and remain simpler than their alternatives. | Every predecessor is integrated and current in `spec/`; no unresolved transition artifact is treated as authority. | Combined source/Core/runtime corpus, migration and downstream-pressure review, full verification, documentation/link review, simplification audit, and explicit trajectory update. |

Each proposal must make its evidence ladder concrete. Where applicable, it
names:

- source acceptance and rejection cases;
- exact failing phase, reason, precedence, primary span, and causal labels;
- retained, linked, and Core carrier tampering before runtime;
- runtime observation and the precise static erasure or retained-runtime-state
  boundary;
- predecessor source, CLI, executable-specification, and resource migration;
- the implementation owner and policy for bounded work, atomic publication,
  exact-boundary failure and retry, and deep stack-safe teardown; and
- independent semantic, authority, implementation-quality, and resource
  reviews.

The proposal chooses semantic limits and the task identifies concrete retained
carriers. Exact implementation dimensions and formulas are set only after
those carriers exist. Compiler resource invariants do not become source
semantics merely because a proposal requires evidence for them.

## Technical boundaries

### Identity and types

Module `newtype` can begin from existing module-owned nominal identity, but
local identity cannot fit the current module-plus-declaration carrier without a
generalized identity boundary. Each identity proposal must identify the shared
type equality, kinding, unification, substitution, summary, lowering, and Core
validation seams. Resource acquisition may later require a runtime-established
fresh witness; that choice belongs to the resource proposal and must not be
smuggled into pure local `newtype` semantics.

The effect proposal likewise must place row structure in the shared semantic
type boundary rather than treating rows as only Core or evaluator state.
Identity alone prevents accidental mixing. It does not establish ownership,
non-escape, continuation safety, or cleanup; those belong to capture, usage,
and lifetime rules.

### Evidence and authority

Scoped exact evidence may reuse the current occurrence-owned slots, linked
authentication, Core authentication, and erasure path. It cannot masquerade as
today's abstract requirement or global implementation source. Its proposal
must add an explicit authenticated lexical source and define its placement in
selection and improvement.

Interface evidence, handler authority, provider authority, foreign-handle
authority, and future proof evidence can share validation patterns, but they
must not collapse into one interchangeable carrier. Each authority kind needs
an authenticated origin, scope, allowed uses, and erasure or runtime boundary.

### Core and evaluation

AD-0007 provides the architectural seam, not a production effect
implementation. The effect checkpoint must materialize a production effect
dialect, independent validator and transform boundary, and evaluator entry
while preserving the closed pure executable dialect. The accepted effect
proposal or a separate architectural decision must choose the representation.

AD-0008 provides the explicit execution substrate. Its evaluator frames remain
implementation state. Effect semantics must define which typed control is
capturable and how validated effect Core enters the machine.

All generated or transformed Core is independently revalidated. Linked
validation authenticates recorded semantic choices and never re-runs evidence
selection. Runtime begins only after validation has made malformed static Core
and forged static authority unreachable. Validated execution may still report
the runtime failures explicitly admitted by resource, cleanup, and foreign
provider semantics.

### Failure and resource ownership

The earliest stage with sufficient information owns a failure. Parsing owns
malformed syntax; resolution owns names and lexical identity scope; kind and
type checking own invalid semantic use; linked validation owns forged retained
facts; Core validation owns malformed lowered programs; runtime owns only
failures possible for already validated execution.

Each accepted proposal names resource-limit policy and ownership for its new
work. Its implementation task then derives concrete budgets and exact probes
from the chosen carriers. Fallible compiler work retains the existing
charge-before-retention, atomic-publication, retry, and iterative-disposal
invariants wherever their accepted architectural scope applies.

## Downstream pressure without premature features

Future effects, proofs, and existentials influence boundaries but do not enter
this milestone:

- proofs need authority provenance and validation that cannot be forged by
  reusing interface or handler evidence;
- existential packaging needs explicit identity and authority escape rules, so
  local identity scope must not assume every hidden value can never cross its
  block;
- suspension and concurrency need owned capture and transfer rules, so the
  first capture/usage model should distinguish duplicable data from restricted
  authority without defining a scheduler;
- multi-shot control needs both duplicable captures and a replayable handler
  interpretation, so one-shot control must not encode an accidental
  concurrency dependency; and
- dynamic loading needs a separate identity and compatibility model, so the
  foreign-provider checkpoint remains statically named and narrow.

These pressures favor explicit identity classes, authority-specific evidence,
closed Core dialects, and typed capture metadata. They do not justify a general
capability calculus, existential packages, a universal effect runtime, or a
dynamic registry now.

## Intentional simplifications

The current direction deliberately chooses:

- one exact scoped evidence goal, not general local implementation search;
- ordered one-shot handlers, not commutative reordering or replay;
- a resume-required kernel before affine checked discard, not a complete
  multiplicity algebra;
- the minimum qualitative capture and usage distinctions required for safe
  discard and resource scope, not complete substructural typing;
- one safe non-foreign resource before hook and cleanup generalization;
- sequential synchronous hooks before suspension or parallel publication; and
- one statically checked foreign provider, not a general FFI or loader.

At safe resource scope and again at milestone closure, review whether any
carrier, validator pass, runtime state, or syntax can be removed or unified
without weakening authority separation or downstream extension seams.

## Open questions

At this design note's original planning boundary, the programme had not chosen
`newtype` grammar or escape, row algebra or inference, handler syntax or
forwarding rules, capture classification, resource acquisition syntax,
hook-chain mutation observation, cleanup order or failure combination, or the
foreign representation. The completed module-`newtype`, local-`newtype`, and
resume-required effect-kernel product checkpoints now resolve the bounded
identity, lexical escape, row, and handler questions. Their implemented
contracts are now current in the specification on `main`.

The verified scoped-evidence checkpoint settles the bounded pure-evidence
choices. The completed
[capture/discard checkpoint](effect-ash/capture-discard-evidence.md)
implements inferred request obligations and consuming abandonment, with its
reviews and full verification retained. The locally integrated safe-resource
checkpoint adds stored resource dependencies and normal scope-owned release;
reliable cleanup now extends the admitted completion and abandonment paths.
The narrow native-buffer provider supplies one checked foreign boundary.
The complete synchronous transforming-hook
checkpoint `ad2b0d4` retains implementation, specification, tests, reviews and
full verification. Its [evidence](effect-ash/synchronous-hooks-evidence.md)
records scoped registration, ordered callbacks and bounded normal release.
Unsigned local merge `7dacce7` and its full merged-checkout verification close
the checkpoint lifecycle. The final milestone merge retains these slices on
`main`; its verification is recorded separately in the closure evidence.

## Supporting evidence

- [DN-0026: Effect Ash Resource-First Milestones](DN-0026-effect-ash-resource-first-milestones.md)
- [DN-0009: Effects, Handlers, and Continuations](DN-0009-effects-handlers-and-continuations.md)
- [DN-0010: Identities and Resource Lifetimes](DN-0010-identities-and-resource-lifetimes.md)
- [DN-0011: Modules, Providers, and Resolution](DN-0011-modules-providers-and-resolution.md)
- [DN-0012: Coeffects and Hooks](DN-0012-coeffects-and-hooks.md)
- [DN-0013: Session and Resource Protocol Stress Tests](DN-0013-session-and-resource-protocol-stress-tests.md)
- [DN-0017: Resource Management and Storage Policy](DN-0017-resource-management-and-storage-policy.md)
- [DN-0018: Runtime-Established Static Evidence](DN-0018-runtime-established-static-evidence.md)
- [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md)
- [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md)
- [Documentation policy](../project/documentation.md)
- [Writing guide](../project/writing.md)
