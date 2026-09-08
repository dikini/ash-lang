# CP-0019: Reliable Cleanup

- ID: `CP-0019`
- Status: proposed
- Related: [DN-0026](../design/DN-0026-effect-ash-resource-first-milestones.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [DN-0010](../design/DN-0010-identities-and-resource-lifetimes.md),
  [DN-0013](../design/DN-0013-session-and-resource-protocol-stress-tests.md),
  [capture/discard evidence](../design/effect-ash/capture-discard-evidence.md),
  [resource evidence](../design/effect-ash/resource-scope-evidence.md),
  [hook evidence](../design/effect-ash/synchronous-hooks-evidence.md)

> This proposal is not current Ash and does not authorize implementation. The
> user agreed to build cleanup on ordinary effects and checked `discard`, with
> no separate exception mechanism. The detailed rules below are proposed for
> acceptance. No specification or product code is changed by this document.

## Current behavior

The baseline is the verified milestone integration tip `8741d7f`, not `main`.
Its [branch specification](../../spec/README.md) includes one-shot handlers,
checked discard, scope-owned cells and synchronous registrations. These changes
are not yet current on `main`.

Normal return releases cells and registrations. Capture/resume moves their
owners without release or duplication. `discard` returns `Unit` with an empty
effect row; it may abandon only control whose unfinished obligations are
proved absent, and may not skip required completion outside its capture.
Internal failure disposes host-owned state iteratively but invokes no source
cleanup. There is no source abort, exception, cancellation or unwind result.

Ordinary handlers preserve their body's result type `A`. Their clause's
`resume` returns `A`, not just the operation result. Ordinary closures retain
values and lexical instantiation, not the handler stack where they were made.
These facts constrain cleanup of captured control.

## Proposed behavior

### Scope and alternatives

Add one scoped cleanup action and extend checked abandonment to close the
owners it actually owns. Use ordinary typed reporting effects to represent
recoverable cleanup failures. Retain the existing evaluator and effect system.

Normal-return-only cleanup would leave the milestone's abandonment and
subscriber-failure cases unresolved. A separate exception calculus would add
another failure mechanism. A special cleanup-result type returned by `discard`
would require error-type agreement across captured scopes. None is selected.

The selected design keeps failure data in source programs. It adds no universal
error type, hidden failure queue, provider registry or implicit retry.

### Source form and acquisition

The following primary expression evaluates `action` once in the preceding
environment, acquires an invocation obligation, and then evaluates `body`:

```ebnf
cleanup_expression ::= "cleanup" expression block ;
```

This production is an additional primary-expression alternative, like `register`.
The action expression stops before the following block; ordinary grouping
disambiguates an action with a trailing block. `cleanup` becomes reserved.
The form adds no user binder or namespace. It does not give an action access
to an enclosing resume capability; the existing function barriers still apply.

`action` checks as `Unit -> Unit ! epsilon_cleanup`. An anonymous function
receives that domain/result context while its latent effects are inferred.
Ordinary callback values, imported factories, generics and inferred captures
remain usable. There is no pure-only callback exemption or restriction.

If initialization abandons control before acquisition, no cleanup action has
been acquired. Capacity and fallible preparation precede publication of the
new owner. Initialization failure cannot cause a partially acquired action to
run. An acquired action is retained even if its body is unused or pure.

Normal completion saves the body's value, invokes the action with `()`, and
returns the saved value after the action completes. The action's `Unit` result
does not replace that value. The scope owns this invocation, not ownership of
every value captured by the action. Copies of the callable own no extra
cleanup obligation. There is no manual deregistration or release handle.

The scope's result type is the body's type. Its outward effects conservatively
include initializer, body and callback effects. Handlers installed only inside
the body do not discharge the later callback's effects. The action may access
enclosing cells while they remain live; it may not export their dependencies.

### Exit matrix

An admitted exit means a source transition proved safe by both source checking
and independent Effect Core validation. The following is the complete boundary:

| Event | Required behavior |
| --- | --- |
| Normal body return, including an ordinary typed failure value | Invoke the action, then preserve the body value. Release cells and registrations at their enclosing boundaries. |
| Capture followed by resume | Transfer owners unchanged. Do not run cleanup at capture or resume; finish later in restored control order. |
| Checked `discard` | Consume the selected capability, close its owned abandoned control, then return `Unit` and continue the discarding clause. |
| Handler implements application failure using `discard` and a typed result | Complete the same close operation before the handler produces its failure value. No new abort primitive is involved. |
| Subscriber uses that admitted failure path | Close reachable pending control and registrations once; do not invoke the remaining abandoned publication callbacks. |
| Recoverable cleanup failure reported by the protocol below | Preserve the report, complete the action and continue remaining cleanup. Do not retry or roll back prior effects. |
| Failure or abandonment before a particular acquisition | Do not invoke its action. Close only already-acquired owners actually abandoned by the selected capability. |
| Discard skips an owner outside the owned abandoned control | Reject; do not extend the exit to an enclosing owner implicitly. |
| Discard abandons an executing cleanup action or its unfinished close operation | Reject. Finalizer-local discard remains possible when action and close operation still complete. |
| Divergence, internal work/capacity/allocation failure, malformed Core, process termination | No successful source-cleanup guarantee. Internal teardown remains iterative; no failure handler, retry, source callback or fabricated success is implied. |

An ordinary `Failure` constructor does not itself change control flow. Failure
and early termination remain expressible through ordinary data, operations and
handlers. The evaluator does not identify constructors by spelling.

### Ownership closure and ordering

The abandoned control starts with exactly the selected capability's owned
capture. A live clause boundary inside it owns another capture: include that
capture recursively at the clause's position. Consume each such capability
once, without executing its `resume`, suspended expressions or clause suffix.
Consumed clause boundaries carry no further live capture.

This is ownership reachability, not a search through every associated runtime
key. A non-owning registration or handle association never authorizes taking
an enclosing owner. A required completion outside the resulting closed set
must remain reachable in untouched surrounding control, or discard rejects.
In particular, retain the existing negative case where a local discard skips
an outer clause's scheduled resume and leaves its registration uncompleted.

Close in structural innermost-to-outermost order, expanding owned nested
captures at their boundaries. For uninterrupted lexical acquisition this is
LIFO. It is not reverse acquisition timestamp order: if scope A is captured,
its handler clause acquires B, and that clause resumes A, restored A completes
before B even though B was acquired later. Normal and abandoned completion
must respect that same structural nesting.

Closing a cell releases its owned payload. Closing a registration removes its
entry and releases its capacity; it never calls its transformer as a destructor.
Closing a cleanup scope invokes its action before advancing outward. A cleanup
scope inside a cell therefore runs while that cell is available. Inner owners
already closed are unavailable to later actions. Existing dependency checks
must prove this ordering sufficient; this slice admits no dependency graph,
ownership transfer, sharing of release responsibility or cyclic lifetime.

Every runtime owner moves through `armed`, `running` where applicable, and
`closed` at most once. These are conceptual states, not a mandated enum or
registry. Starting an action consumes its eligibility for another invocation,
but retains an unfinished completion obligation until its call returns.
Exactly once means one invocation attempt on an admitted, completing exit;
it does not prove termination or turn failed native release into success.

### Handler context during cleanup

Normal cleanup uses the actual surrounding handler context after the body
returns. Abandoned cleanup uses the surviving context at `discard`, plus still
live builtin cell interpreters in the structural owner nesting. Actions retain
their ordinary term, type and row environments. They may install ordinary
handlers inside their own execution.

Do not reinstate arbitrary captured source handlers, ordinary continuations
or generated hook handlers to run cleanup. A captured handler with answer
type `Int` and clause `(resume ()) + 1` needs the abandoned body's `Int` result.
Neither a dummy value nor treating that handler as answer-polymorphic is valid.

Instead, check each action at its structural closing position. Conceptual
interpreter lookup includes its own currently executing handlers, the still
enclosing captured boundaries at that position, and the surviving exit context,
with their lexical instantiation and precedence. It excludes body-local
handlers already passed on the way out to that action's owner. This is a proof
of context compatibility, not execution of the removed handlers.

Abandonment rejects when the nearest matching candidate for an actual
transitive action request is a source or generated handler that would have to
be removed. A nearer matching captured handler must not be silently replaced
by an outer handler or builtin cell interpreter for the same exact instance.
A handler installed inside the action can handle its requests normally. Source
checking and Core validation must track these requirements through actual callbacks,
imports and generic instantiation; uncertainty about a necessary captured
interpreter rejects that abandonment, not every use of the callback.

This restriction includes captured hook roots and registrations when an action
would publish through their interpretation. It does not prevent deregistration,
pure actions, access to still-live unshadowed builtin cells, or requests whose
handlers survive outside the exit. It is an explicit boundary of this slice;
general captured-handler cleanup would require a separate answer/control design.

The close operation itself is a required completion owner. Outward operations
from an action may capture and resume its state, but an abortive handler may
not skip that action or the remaining close operation. The same rule applies
to requests made by a reporting adapter. It prevents a cleanup failure handler
from silently abandoning the rest of cleanup. Callbacks may acquire and close
nested scopes using these rules; there is still one evaluator.

### Typed cleanup failures and their collector

Specify and test an ordinary source-level reporting protocol, not a privileged
runtime failure channel. The following names are explicit declarations in the
example or an explicitly imported source module; they are not builtin names:

- `CloseResult<E> = Closed | CloseFailed(E)` describes an action's fallible step.
- `CleanupFailure<E>` has one operation `report : E -> Unit`.
- `reportClose` maps `Closed` to `()` and `CloseFailed(e)` to a report request
  followed by `Unit` completion. It invokes no retry.
- `Failures<E> = NoFailures | FailureItem(E, Failures<E>)` retains ordered data.
- `Report<A,E> = Report(A, Failures<E>)` preserves the body's value separately
  from cleanup failures. Its collector handles reports by resuming with `()`,
  then prepending the current error to the returned failure sequence.

The collector must surround the relevant body, application-failure handlers
and cleanup scopes so it survives the selected abandonment. A report request
resumes the current computation; it is not a request to abort cleanup. The
standard protocol's clause does only pure report construction after resume.
The reports are in emission order: prepend after resume, not append.

`A` may be an application-defined `Outcome<T,P>`. A failed body retains its
primary `P` unchanged, with every cleanup `E` recorded separately. A successful
body retains its value too; report inspection treats the first cleanup error
as the primary cleanup failure and the remaining errors as subsequent failures.
An empty list leaves the body outcome unchanged. Distinct cleanup error types
can use an explicitly chosen sum, or distinct independently collected effects.
There is no implicit boxing, common error superclass or inferred error domain.

An arbitrary ordinary `CloseFailed` value that a program ignores is not an
automatically reported failure. The retention guarantee is the contract of
this explicit adapter and collector. Applications can deliberately choose a
different ordinary handler, but that does not change the standard protocol's
preserve-and-collect behavior. All handlers remain subject to the active close
operation's completion check.

The following complete proposed program reports inner failure `22` before
outer failure `11`, preserving the application failure `7`. It returns `72211`.
The failure operations and data types use existing Ash forms; only the cleanup
scopes and their abandonment behavior require this proposal:

```ash
type Outcome<T, P> = Success(T)
| Failed(P)
type CloseResult<E> = Closed
| CloseFailed(E)
type Failures<E> = NoFailures
| FailureItem(E, Failures<E>)
type Report<A, E> = Report(A, Failures<E>)

effect CleanupFailure<E> {
    report : E -> Unit
}
effect Stop {
    stop : Int -> Unit
}

reportClose<E> : CloseResult<E> -> Unit ! {CleanupFailure<E>}
reportClose result = match result {
    Closed => ()
    CloseFailed(error) => perform CleanupFailure<E>.report error
}

outer : Unit -> Unit ! {CleanupFailure<Int>}
outer ignored = reportClose (CloseFailed 11)
inner : Unit -> Unit ! {CleanupFailure<Int>}
inner ignored = reportClose (CloseFailed 22)

main : Unit -> Int
main () = {
    let observed : Report<Outcome<Int, Int>, Int> = handle {
        let outcome : Outcome<Int, Int> = handle (cleanup outer {
            cleanup inner {
                let ignored = perform Stop.stop 7
                Success 42
            }
        }) with Stop {
            stop primary => {
                let done = discard
                Failed primary
            }
        }
        Report(outcome, NoFailures)
    } with CleanupFailure<Int> {
        report error => match (resume ()) {
            Report(outcome, errors) => Report(outcome, FailureItem(error, errors))
        }
    }
    match observed {
        Report(Failed(primary), FailureItem(first, FailureItem(second, NoFailures))) =>
            primary * 10000 + first * 100 + second
        _ => 0
    }
}
```

The normal-return companion removes `Stop` and its handler and returns
`Success 42` from the same nested scopes. Its report is
`Report(Success 42, FailureItem(22, FailureItem(11, NoFailures)))`.
Both are required future executable examples, not tests already passed.

### Effect, dependency and completion checking

`discard` keeps its result type and structural capability consumption but is
no longer universally pure. Its least row includes the effects of actions
invoked by closing its owned capture, interpreted only by the handlers admitted
above. No report effect is silently discharged or assumed present.

Cleanup requirements must survive capture summaries even when an abandoned
handler removed an effect from the original computation's outward row. Carry
the action's effects, dependency and interpreter requirements through the
existing finite value/control relationships. Independent linked and Core
checks reconstruct the actual callback and exit relationships rather than
trusting a surface summary or a pure annotation.

Generic exact instances may coincide after substitution. Retain scopes and
possible interpreter conflicts until the corresponding identity facts justify
removal. Open rows require the same existing lexical row/lacks authority as
other effects; do not add guessed exclusions or demand closed rows universally.

The saved normal result, reported error values, cleanup closures and requests
remain subject to stored-dependency checks. In particular, reporting a closure
that retains a cell to a collector outside that cell still rejects. Cleanup
does not make operation payload escape safe or turn provider evidence into
release authority. In-flight cleanup and its remaining owners cannot escape,
duplicate or be abandoned, even if all ordinary result types look harmless.

Source failure precedence remains syntax, resolution, kind/type/row and
structural continuation checks before inferred cleanup/dependency checks.
Callback shape errors use ordinary type errors. Missing outward effects use
ordinary row diagnostics. Unsafe owner abandonment remains
`effect.discard-unsafe`; add `effect.cleanup-context` for a required captured
interpreter, with discard, action and handler labels. Resource-dependent error
escape remains `type.resource-escape`. Forged owner, callback, row or context
facts are internal validation failures, never alternative source authority.

### Failure preparation and partial completion

Prepare and validate ownership transfer before consuming a live capability.
An initial preflight failure leaves it and the owned scopes unchanged. Once
source cleanup begins, completed effects and closed owners are not rolled back.
Each next step has its own charged preparation. If internal exhaustion happens
after some actions ran, stop with the internal failure and perform iterative
host teardown; do not rerun completed actions or claim remaining source actions
ran. A fresh execution is not a promised retry of external cleanup.

Earlier successful acquisitions are protected by their published owners.
An interrupted later initializer owns only acquisitions already published
inside its actual control. This is scoped rollback of owned acquisitions, not
universal reversal of effects. A future foreign provider must separately define
native partial acquisition before publication and what a failed release means
for its handle. This proposal supplies neither a native rollback guarantee nor
permission to silently drop an unresolved native obligation.

## Semantic delta

- Add scoped acquisition and exactly-once attempted invocation of cleanup actions.
- Make cell, registration and cleanup owners closable by a proved owned
  abandonment; consume contained live captures recursively.
- Preserve rejection of skipped outside owners and introduce non-skippable
  active cleanup completion.
- Replace `discard`'s unconditional empty effect row with inferred cleanup
  effects while preserving its `Unit` value and one-shot capability use.
- Define structural cleanup order, the surviving-handler restriction, typed
  reporting protocol and partial-completion limits.

## Affected specification areas

- [Lexical structure](../../spec/lexical-structure.md): reserve `cleanup`.
- [Syntax](../../spec/syntax.md): the primary scope form and grouping.
- [Name resolution](../../spec/name-resolution.md): action/body scopes and
  existing resume-capability barriers.
- [Static semantics](../../spec/static-semantics.md): callback typing, discard
  effects, owned-capture closure, interpreter requirements, dependencies and
  diagnostics.
- [Elaboration](../../spec/elaboration.md): independently authenticated cleanup
  relationships and transformed-Core validation.
- [Dynamic semantics](../../spec/dynamic-semantics.md): normal invocation,
  abandonment order, running-close completion, reporting and partial failure.
- [Specification boundary](../../spec/README.md): precise new admission and
  retained foreign, exception, suspension and ownership exclusions.
- [`ash` tool guide](../tools/ash.md): exact examples, source diagnostics and
  distinction between reported failures and internal execution failure.

## Resulting specification truth

Only after complete implementation and integration into `main`, Ash has scoped
cleanup on normal completion and supported checked abandonment. Every acquired
owner is closed or retained according to structural control ownership, without
replaying abandoned code. Active cleanup cannot be silently abandoned. Typed
failure reporting preserves body results and ordered additional failures using
ordinary source effects and data. Internal termination and unsupported handler
contexts remain outside the successful cleanup guarantee.

## Interactions

The implementation route is the existing typed Effect family, finite capture
analysis and explicit evaluator. Cleanup needs an authenticated owner and a
bounded close continuation; ordinary function application invokes actions.
Choose concrete carriers during the authorized implementation plan. Do not
create a general registry, separate interpreter, permanent owner graph or
second capture analysis. Pure dialect admission and hook-free Pure execution
gain no cleanup state, reporting state or proportional cleanup scans.

The downstream reassessment must check these named pressures:

- **Foreign providers:** one future authenticated provider owner can use the
  same close sequencing, while retaining provider-specific release/rollback
  authority and unresolved native-failure responsibility.
- **Proofs:** the closed transition set and ordered observations distinguish
  attempted invocation, completion and successful release. No termination or
  physical-release theorem is inferred from structural completion.
- **Existentials:** no hidden package or universal error domain is introduced.
  Runtime owners and static authority have separate last uses; packaging a
  live owner later would require explicit transfer rules.
- **Suspension:** owned captures retain cleanup state and lexical instantiation;
  they do not currently escape. Later suspension must own the same state, not
  recover it from a global registry.
- **Handler generalization:** arbitrary captured-handler cleanup is deliberately
  excluded. Record the non-tail answer-type counterexample as residual pressure,
  not an unsupported claim that future handler work needs no changes.

## Non-goals

No `throw`/`catch`, exception hierarchy, implicit failure propagation, async or
cancellation guarantee, escaping/multi-shot continuation, resource transfer,
general destructor declaration, reference counting, tracing cleanup, dynamic
loader, native provider implementation, ABI, proof calculus or existential
package. No automatic recognition of arbitrary typed failure constructors.
No source cleanup after process kill or internal exhaustion guarantee. No
main merge, push, milestone tag or implementation authorization.

## Required evidence

These observations are required before any product checkpoint can close. They
are acceptance obligations, not experimental results or optional extensions.

| Case | Required observations |
| --- | --- |
| CLEAN-01: Surface and typing | Primary positions, grouping, keyword collisions, spans and malformed forms; contextual anonymous actions; wrong domain/result; initializer, body and latent callback rows; imported/generic callbacks and open-row authority. |
| CLEAN-02: Normal ownership | Initializer exactly once, action exactly once, saved result unchanged, repeated same-site activation, nested cell/action/registration order, live outer dependencies and forbidden escape. |
| CLEAN-03: Owned abandonment | Close cells, registrations and actions in the selected capture; recursively close contained live captures; consumed clauses add no work; no suspended expression, clause suffix or pending publication callback executes; the discarding clause continues. |
| CLEAN-04: Outside and running owners | Retain the outside-owner negative, reject taking ownership through non-owning associations, reject abandoning a running action or drain, admit safe action-local discard and capture/resume. |
| CLEAN-05: Structural order | Distinguish ordinary lexical LIFO from acquire-A/capture/acquire-B/resume order; nested owned captures; all callback and release traces agree with actual control nesting rather than activation timestamps. |
| CLEAN-06: Handler context | Live outer and action-local handlers work; retained builtin cells work; required captured non-tail source handler rejects, including same-instance outer fallback, captured hook interpreter and cell-handler override; a body-local same-instance handler already passed before closing admits, paired with the enclosing-handler rejection; position-sensitive lookup survives imported callbacks and generic coincidence; unused/handled-local effects do not create false conflicts. |
| CLEAN-07: Failure reporting | Exact `72211` program and successful-body companion; no-error case; two ordered cleanup failures; preserved differently typed primary error; explicit error sum and independent report effects; no implicit classification, retry, reversal or masking; abortive report handler and a reported error retaining a cell outside its owner both reject. |
| CLEAN-08: Partial acquisition/completion | No action before acquisition; prior owners close when a later initializer is abandoned; failure after visible cleanup effects retains exact partial trace; no repeated invocation; no fabricated successful release or source-cleanup promise on internal failure. |
| CLEAN-09: Independent authority | Same-typed linked callback substitution changes cleanup effects, dependency, completion or interpreter needs and is independently rejected where unsafe; forged/duplicate/stale owner/context/order facts; both Core transforms revalidate positive and negative generic-coincidence cases. |
| CLEAN-10: Resources and disposal | Separate charges for closure traversal, owner retention, action work and reports; exact/one-short/fresh compiler retries; atomic initial runtime preparation; charged post-start failure with no replay; live plus captured capacity and reuse; deep iterative success and partial-failure teardown. |
| CLEAN-11: Predecessors and tools | Full Pure, newtype, evidence, effect, cell and hook corpus; migrate only specifically newly admitted abandonment cases, preserving unrelated negatives; exact source/CLI examples; full `cargo xtask verify`, strict Clippy, docs/notation/link review and architecture inventory. |

Use retained predecessor small-stack bounds, real failed traces and unchanged
corrections. Do not loosen resource limits or bypass public Core validation to
make an example pass. Separate compiler retry evidence from runtime partial
completion; do not claim an exact work formula until the owning implementation
measures its actual scans and retained fields.

Before implementation, independent semantic and ownership/resource reviews
must close this complete contract. Return a missing rule to this proposal;
do not silently broaden captured-handler support or narrow a required positive
case in product code. After acceptance, create one task and its temporary plan.
The original 11-unit forecast remains a relative scope estimate, not an
authorization or measured budget. No implementation plan is started here.

## Design review status

Independent high-reasoning failure-protocol and control/ownership reviews pass
for this draft. The control review required position-sensitive interpreter
lookup and the paired body-local/enclosing-handler evidence; both are included.
The medium documentation review checked authority, unused proposal identity,
links, notation and example syntax. Its constructor-pattern and resume-grouping
corrections are included. Markdown lint with the project's MD013 exemption and
diff checks pass.

These are design and documentation reviews, not execution evidence. The
proposed example and CLEAN-01 through CLEAN-11 remain implementation obligations.
The full proposal still needs user acceptance before an implementation task.
