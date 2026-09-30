# CP-0021: Local effects in resume operands

- ID: `CP-0021`
- Status: accepted
- Related: [TASK-0032](../tasks/TASK-0032-core-one-shot-alignment.md), [DN-0033](../design/DN-0033-direct-effects-and-continuation-capabilities.md)

> This proposal is not current Ash.

## Current behavior

[T-Resume](../../spec/static-semantics.md#effects) requires the operand row to
be a subset of the selected continuation's output row. The independent Core
validator requires that subset and assigns the resume node exactly the output
row. Core row replay replaces the entire resume row when solving its owner's
handler contract.

The evaluator instead evaluates the operand under the surrounding clause
control before consuming the continuation, as specified by
[E-Resume-Operand](../../spec/dynamic-semantics.md#effect-handlers-and-completion).
Binding an effectful operand before resume permits a clause-local handler to
discharge its effects. The recorded direct form reaches Core construction and
fails internally when row replay removes those operand effects.

## Proposed behavior

Check the operand against the selected operation result type. The resume
expression's least row is `operand_effects union epsilon_out`, where
`epsilon_out` is the selected continuation's output contract. A surrounding
clause-local handler may discharge operand effects in the ordinary way. The
least output row of the enclosing selected handler is still solved from its
body remainder and complete clause computations.

This preserves the existing sequence: evaluate the operand, consume the live
capability once, restore the full captured segment above remaining clause work.
Operand evaluation may capture the pending resume frame; abandoning an outside
completion remains invalid.

## Semantic delta

Replace T-Resume's `operand_effects subset-of epsilon_out` premise with an
explicit union result row. This admits direct locally handled operands already
expressible by binding before resume. Do not erase operand requirements, inflate
unrelated node rows or turn least-row validation into a subset check.

Retaining the old rule with a source diagnostic would remove the internal
failure but preserve a syntax-sensitive restriction unsupported by the runtime
evaluation order. Rewriting every resume to a bind would hide the Core row
contract problem. The union rule states that contract directly and supports the
calculus comparison without introducing another control operation.

## Affected specification areas

- [Static effect rules](../../spec/static-semantics.md#effects): T-Resume.
- [Effect Core lowering](../../spec/elaboration.md#effect-core-lowering): the
  resume node's exact row equation.

## Resulting specification truth

The resume expression includes both operand and continuation effects. Locally
handled operand effects need not escape the surrounding local handler. Dynamic
evaluation order, result type, exact handler selection and one-shot ownership
remain as currently specified.

## Interactions

Row replay and independent validation must compute the same least union using
existing kind, exact-identity, open-row authority and resource-budget rules.
The least-handler-output calculation must retain operand requirements while
removing only the owner's recursive output contribution. Generated hook resumes
with pure operands remain valid. Capture analysis must still reject discarded
pending uses of an outside owner.

## Non-goals

No change to discard cleanup interpretation, continuation escape, multiplicity,
hook behavior, native buffers, suspension or asynchronous execution.

## Required evidence

- Reproduce the direct-form internal construction failure, the bound-form result
  `17` and the unsafe-discard rejection before the change.
- Direct and bound operands validate and return `17` after the change.
- Independent malformed-Core tests reject omitted operand effects, omitted
  continuation effects and inflated nonleast rows.
- Existing handler-row, one-shot-use, resource, hook and cleanup regressions pass.
- Check fallible row operations and replay rollback; retain bounded work.
- Update specification and comparison evidence; review semantics and code
  independently before checkpoint closure.

Acceptance follows the user's explicit authorization for necessary alignment
changes. TASK-0032 implements this bounded delta; it does not broaden C1–C5.
