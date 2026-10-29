# CP-0029: Exact base-256 integer split

- ID: `CP-0029`
- Status: accepted
- Related: [CP-0030](CP-0030-checked-network-codec.md), [TASK-0058](../tasks/TASK-0058-pinned-worker-network.md), [issue #79](https://github.com/dikini/ash-lang/issues/79)

> This accepted transition is not current Ash. Acceptance does not establish
> product implementation or evidence.

## Current behavior

Ash integers are mathematical integers. Current arithmetic supplies addition,
multiplication and equality, but no integer division or remainder. The
[compiler-owned module list](../../spec/name-resolution.md#compiler-owned-cell-module)
does not include `@builtin.integer`. Persistent construction and potentially
large arithmetic carry the existing [allocation requirement](../../spec/static-semantics.md),
and [dynamic semantics](../../spec/dynamic-semantics.md) governs selected
allocation, evaluation and failure.

## Proposed behavior

Add the passive canonical compiler-owned module `@builtin.integer`. It exports
exactly the transparent nominal type `SplitResult`, its constructors `Parts` and
`Negative`, and `split_base256 : Int -> SplitResult`. `Parts` has one ordered
`(Int, Int)` tuple payload, quotient first and remainder second; `Negative` is
nullary. Complete and targeted imports, aliases and public reexports preserve
the defining module, type, constructor and function identities. An ordinary
same-spelled declaration does not select this builtin. Transparent construction
of a same-shaped value is allowed, but does not establish an intrinsic return.
The implementation assigns identities through the normal compiler mechanism;
the contract does not depend on numeric identity values.

For every mathematical input `n`:

- If `n < 0`, a normal return is exactly `Negative` and contains no quotient or
  remainder. This negative case is a semantic rule for the operation, not a
  new source integer-ordering operator.
- If `n ≥ 0`, a normal return is exactly `Parts((q, r))` for the unique
  mathematical integers satisfying `n = 256*q + r`, `q ≥ 0` and `0 ≤ r < 256`.
  `n = 0` produces `Parts((0, 0))`. For positive `n`, `q < n`.
- Every mathematical integer has the appropriate result with sufficient
  computation and storage; there is no machine-word representability cutoff.
  This is conditional on the operation actually completing. Input evaluation is
  strict and occurs once under existing evaluation order.

The proposed builtin function has the same empty outward function row as the
canonical byte functions. Its *call* still carries the canonical allocation
requirement for potentially large arithmetic and persistent construction under
the existing row-lifting and provider-discharge rules. An empty outward row
does not erase the actual allocation operations or establish provider safety.

Use one definite M2 construction sequence. Ordinary application evaluates the
function and strict `Int` argument once in the existing call-by-value order.
On entry to the canonical builtin, it queries and saves the actual
caller-selected live allocation context. It then reads the evaluated argument
under its existing live owner, charges work and size before proportional
traversal or allocation, and computes the exact sign and quotient/remainder.
For a nonnegative input, it constructs any needed persistent quotient digit
backing, the ordered `(q, r)` payload tuple and the `Parts` constructor in that saved selected context; the
bounded remainder `r` is an immediate byte-valued `Int`. The quotient retains
the conservative selected residency required for potentially large arithmetic
even when its runtime representation is immediate. The result constructor
retains the payload and actual field dependencies. For a negative input it
constructs the nullary `Negative` result in the same selected context. Neither
case mutates or relocates the input.

Each construction follows the existing request, fresh compatible storage,
complete initialization and publication sequence. The tuple and constructor
are not published before all of their actual fields are initialized. Their
normal use and escape require live backing and the existing dependency and
region-close rules; a call or projection does not confer independence. The
preceding allocation selection is restored by the existing control rules.
Declared allocation refusal follows the ordinary effect/discard rules and does
not produce an intrinsic normal result. Internal work, control or storage
exhaustion is terminal, and yields no normal `Negative` or `Parts` value and no
partially published codec fact. A surrounding source handler constructing a
same-shaped result does not establish intrinsic success. Runtime work and the
validator's cumulative work are each charged under their existing budgets;
neither gains a fresh hidden allowance. No reentry, intercepted provider,
local handler or opaque callback is assumed away. A dependent codec check must
authenticate the actual selected provider and control or reject.

## Semantic delta

The new operation supplies exact nonnegative division by 256 with an ordinary
negative result. It adds one canonical module and its nominal result and
intrinsic identities. It does not add division or ordering operators or alter
`Int` representation. The declared empty outward row and the call-site
allocation requirement above are both part of this proposal.

The call-order revision replaces the original requirement to query the context
before evaluating the actual argument. Argument effects now occur before that
query; if argument evaluation does not return normally, the builtin does not
query the context or construct a result. The query still precedes reading the
evaluated integer, computation and result allocation. This ordering is
observable for an effectful argument. It preserves ordinary callable, alias,
import, provider, failure and dependency rules.

## Affected specification areas

Update [name resolution](../../spec/name-resolution.md) for the module,
exports and identities; [static semantics](../../spec/static-semantics.md) for
intrinsic typing, row lifting and dependency residency;
[dynamic semantics](../../spec/dynamic-semantics.md) for strict evaluation,
construction, work and failure; and [elaboration](../../spec/elaboration.md)
for authenticated intrinsic lowering and linked validation.

## Resulting specification truth

Only after the complete product branch is integrated into Main, the specified
canonical operation has exactly the returns and allocation behavior above for
all mathematical `Int` inputs. Resource exhaustion or refusal produces no
intrinsic normal result. Adoption alone makes none of these rules current.

## Interactions

[CP-0030](CP-0030-checked-network-codec.md) depends on this separately
accepted, implemented and verified operation. It relies on actual selected
provider and control evidence, not merely the function's empty outward row.
No ledger representation changes. CP-0030 applies the split to an already
bound scalar; the call-order revision does not change its framing or contextual
codec law. If this dependency cannot meet its resource or semantic requirements,
return to proposal review.

## Non-goals

No general division or modulo API, integer comparison, fixed-width conversion,
new parser primitive, automatic protocol trust or change to ledger state.

## Required evidence

Implement the actual canonical module, intrinsic and normal-return mapping;
check identity, imports, reexports, supported transformations, strictness,
selected context, provider control, lifetime, work and failure, including
argument effects before the query and argument failure before builtin entry.
At frozen linked inputs cover zero, 1, 255, 256, 257, negative values and values
beyond host word size, alias/import and same-typed replacement, allocation refusal,
terminal work/storage failure and budget boundaries. Independently review the
runtime-to-model mapping and applicable focused and integrated checks; update
the affected specification with the retained implementation. None of this
evidence is claimed by this accepted artifact.
