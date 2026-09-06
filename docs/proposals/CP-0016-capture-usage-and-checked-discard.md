# CP-0016: Capture Usage and Checked Discard

- ID: `CP-0016`
- Status: accepted
- Related: [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [DN-0027](../design/DN-0027-effect-ash-program-design.md)

> This proposal is not current Ash. The user accepted explicit `discard` with
> inferred capture summaries and conservative higher-order/open-row checks in
> the task conversation on 2026-09-06.

## Current behavior

The milestone integration branch implements the resume-required kernel. Each
operation clause owns a hidden, nonescaping continuation capability; every
normally completing path resumes exactly once. Requests move the continuation
segment through the nearest exact handler. A segment may contain another
clause's live capability. These milestone semantics are not yet on `main`.

## Proposed behavior

### Explicit completion

`discard` is a reserved, nullary expression of type `Unit`, with no immediate
effect requirement. It resolves to the enclosing operation clause's hidden
capability, subject to the same function, recursive-member, supplied-method,
and nested-clause capture barriers as `resume`.

Each normally completing path must consume its capability exactly once,
through either `resume value` or `discard`. Mixed completion choices in match
arms are valid when their outgoing usage states agree. Neither operation may
consume an already consumed capability. Divergence is not implicit discard.

`discard` abandons the captured segment through the selected handler and
continues the clause with `Unit`. It does not evaluate that segment, resume
with a dummy value, terminate an enclosing handler, or perform resource cleanup.

### Capture and request summaries

Duplication permission and discard permission are separate qualitative facts.
Ordinary values and their stored captures are unrestricted in this checkpoint.
The hidden continuation capability remains nonduplicable and nonescaping.
A live capability inside a captured segment is an unfinished obligation: that
segment cannot be discarded. A consumed capability no longer contributes that
obligation. Explicit discard consumes its own owner, not other captured owners.

Inference distinguishes stored closure captures from latent operation requests.
An ordinary helper or closure can store only unrestricted data yet perform an
operation while its caller, or a clause created inside that helper, has a live
owner. Summary composition must preserve that fact across calls.

Compute conservative request summaries separately for exact effect instances;
join possible paths and include the caller's live owners up to the selected
handler boundary. Do not contaminate an unrelated effect with another effect's
request obligations. A matching handler removes requests from its body;
requests made by its clauses reach outer handlers under the existing bypass
rule. A handler installed inside a live clause does not capture that outer
owner when it handles a request confined to its own body.

Known functions, local aliases, ordinary closures, recursive groups and imported
functions retain inferred summaries. Recursive summaries converge
conservatively; an unfinished inference is never assumed safe. For an unknown
higher-order callee or an open row, reject discard when the relevant request's
capture obligations cannot be proved absent. This uncertainty alone does not
reject resume-only code. No source capture annotations or capture-polymorphic
function types are introduced.

### Checked boundary and failure ownership

Resolve outside-clause use before typing. Structural capability errors retain
the existing resume-use reason family, with wording covering both completion
forms. An unsafe or unproved discard has type-phase reason
`effect.discard-unsafe`, a primary label on `discard`, and causal labels for
the relevant request/call and live owner where known. Existing syntax,
resolution and ordinary type errors retain their precedence.

Core has an explicit discard operation carrying its handler/owner identity.
Validation independently checks owner scope, `Unit`, empty immediate row,
exact-once use and discard safety. Any retained summary or usage fact is
checked against Core structure and authenticated function identity, not trusted
because elaboration supplied it. Transformations preserve these obligations
and their results must revalidate.

Inference and validation use existing structural work limits and iterative
walks. Exhaustion does not publish a partial successful result; retry with a
sufficient budget produces the same result as a fresh run. The evaluator
consumes the existing captured continuation without copying it, releases its
retained capture accounting, and disposes of deeply nested captured segments
without recursive stack growth. Existing evaluator failure ownership remains;
discard adds no failure recovery or cleanup semantics.

## Semantic delta

Replace resume-required normal completion with one resume or one checked
discard. Add inferred capture permission checks without allowing source
continuation values, duplication, implicit abandonment or escape.

## Affected specification areas

- [Syntax](../../spec/syntax.md): keyword and nullary expression.
- [Name resolution](../../spec/name-resolution.md): hidden owner and barriers.
- [Static semantics](../../spec/static-semantics.md): usage and capture inference.
- [Elaboration](../../spec/elaboration.md): summaries, Core and validation.
- [Dynamic semantics](../../spec/dynamic-semantics.md): consuming abandonment.
- [Lexical structure](../../spec/lexical-structure.md): reserved keyword.
  Diagnostic rules remain with the affected resolution and static judgments.

## Resulting specification truth

After the complete milestone is integrated into `main`, a clause may explicitly
abandon only a continuation proven free of other unfinished obligations.
Ordinary abstraction cannot conceal those obligations. The implementation and
specification in this product branch remain prospective until that integration.

## Interactions

Exact handler identities, lexical ordering, row typing, local nominal escape,
scoped evidence authentication and erasure remain unchanged. Ordinary closures
do not become resource values. Keep the summary distinction between stored
captures and request-carried obligations so resource scope can add actual
obligation classes later without replacing the analysis boundary.

## Non-goals

No ownership/borrow/lifetime calculus, capture polymorphism, explicit operation
modes, resources, automatic cleanup, foreign effects, replay, continuation
escape or duplication. No change to pure-program runtime state. No merge into
`main`, remote push or milestone tag.

## Required evidence

- Accept direct discard, mixed resume/discard branches, ordinary value/closure
  captures, known safe helpers and imported/recursive helper summaries.
- Observe that discarded suspended work does not run, clause work does run,
  and surrounding handler control remains intact.
- Reject missing/double completion, stored or escaping completion capability,
  wrong owner and outside-clause discard.
- Reject direct and helper-hidden B requests crossing a live A owner; reject
  same-effect outward delegation with a live owner. Accept a handler inside A
  that discards its own segment before A resumes, and outward requests after
  A's owner has been consumed when no other obligation remains.
- Keep unrelated request summaries separate. Cover unknown higher-order and
  open-row rejection alongside resume-only non-regression.
- Reject forged Core owners, usage, rows, types and safety summaries. Revalidate
  transformed programs and verify linked/imported summary authentication.
- Cover exact work limits, one-unit-short failure, retry, capture-accounting
  release and deep success/failure teardown; retain pure-dialect locality.
- Run the full verification gate and independent semantic, resource/Rust and
  documentation reviews. Retain measured evidence before transition cleanup.
