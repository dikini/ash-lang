# Linked Core Resolved Binder Authority Design

- Status: approved implementation design
- Date: 2026-08-27
- Related: [CP-0009: Explicit Kinds and Higher-Kinded Parameters](../proposals/CP-0009-explicit-kinds-and-higher-kinded-parameters.md), [TASK-0016: Implement Explicit Kinds and Higher-Kinded Parameters](../tasks/TASK-0016-implement-explicit-kinds-and-higher-kinded-parameters.md), and the [explicit-kinds execution plan](2026-08-26-explicit-kinds-and-higher-kinded-parameters.md)

> This document records an approved Task 9 implementation design. CP-0009
> defines the proposed semantic transition, TASK-0016 authorizes the work, and
> the current specification remains normative until the product checkpoint is
> complete.

## Problem

Task 5 independently validates locally assembled kinded Core. Task 8 supplies
an authenticated combined registry after body-free linking and evidence
validation. The combined registry retains every canonical resolved type
variable but flattens the checked global scheme that owned it.

That flattening loses two linked facts before Core validation:

- the stable term `BinderId` that owns each resolved outer-scheme binder; and
- the source order of those binders within the owning global scheme.

The current validator therefore accepts any non-nominal resolved type-variable
identity present in the canonical map when its Kind agrees. It cannot reject a
same-Kind swap between two global owners, a coherent reorder within one global,
or an interface-only binder forged into a Core abstraction. The positive linked
higher-kinded program already passes, so these authority mutations provide the
necessary Task 9 RED evidence.

CP-0009 draws a different boundary for generated Core binders. A generated
binder is owned by its local `TypeAbstractionNode` and its matching outer
`Forall`. A consistent fresh identity substitution across that abstraction,
scheme, body, and applications is valid alpha-renaming. Task 9 must not retain
the elaborator's original generated identity as external authority.

## Decision

Extend the combined `ResolvedRegistry` with ordered rows for non-empty resolved
global schemes:

```text
ResolvedGlobalParameterRow {
    owner: BinderId,
    parameters: Box<[TypeVariableId]>,
}
```

Retain the rows in deterministic module and declaration order and retain a
`BinderId`-to-row-position index for lookup. Each parameter identity remains a
resolved, non-nominal identity. The existing canonical `ResolvedTypeVariable`
record remains the only retained authority for Kind, spelling, and definition
origin. The row does not copy a Kind, spelling, `Origin`, scheme body, evidence
fact, implementation route, or module group.

The row represents a fact already authenticated while checked registries are
combined. Storing it in the existing registry has four consequences:

- final Core construction receives the fact only through
  `ValidatedInterfaceProgram`;
- `CoreBuilder`, unchecked Core, validated Core, and both retained transforms
  already preserve the same immutable registry `Arc`;
- no second carrier can disagree with the canonical variable registry; and
- evaluator behavior remains unchanged because evaluation does not inspect the
  rows.

Only resolved global parameters enter these rows. Nominal parameters keep
their existing ordered nominal rows. Interface parameters erase before Core.
Final implementation-method parameters and locally generalized parameters use
generated Core identities and retain local abstraction ownership.

## Construction and authentication

`combine_checked_registries` already visits every checked global scheme in
dependency and declaration order and authenticates its ordered parameter list
against canonical registry records. During that charged pass it will retain a
row for each non-empty scheme and reject duplicate owners, duplicate parameter
identities, non-resolved identities, missing canonical records, and parameters
owned by a nominal row before publication.

Linked evidence validation will compare the completed rows with the checked
module groups before it publishes `ValidatedInterfaceProgram`. This preserves
the existing boundary: unchecked combined data cannot create Core authority by
merely populating a private registry field.

All row and index capacity is reserved and charged before retention. Failure
publishes no partial row or index entry. Rows contain only scalar identities,
so their disposal does not add recursive payload ownership.

## Independent Core validation

Module-aware Core validation derives the stable term owner of an abstraction
from a `Bind` or `RecursiveBind` member whose initializer is that exact
`TypeAbstractionNode`. Node identities may change across transforms; the
owning `BinderId` does not.

For an abstraction containing resolved parameters, validation requires:

1. exactly one immediate term-binder owner;
2. exactly one registry row for that `BinderId`;
3. exact identity and source-order equality between the row and the
   abstraction parameters;
4. exact identity and order equality with the matching outer `Forall`;
5. each retained Kind to equal the canonical variable record;
6. source/module provenance to agree with the existing module relation; and
7. every retained row to be consumed exactly once.

A missing, extra, duplicate, reordered, wrong-owner, nominal, or interface-only
identity fails with `ValidationReason::Registry` before later node or scope
failures. The validator removes the existing fallback that treats canonical
map membership as sufficient resolved-binder authority.

Generated abstractions do not consult these rows. Their existing structural
rules continue to require one local abstraction owner, positional agreement
with the outer `Forall`, equal Kinds, graph-wide uniqueness, and lexical scope
without capture, shadowing, or escape. Tests will reject inconsistent generated
mutations and accept a complete capture-free alpha-renaming.

## Transform and runtime boundary

Identity traversal and literal folding share the immutable registry while they
rebuild expression nodes. Each transformed program must pass fresh module-aware
validation against the same rows. The two transforms will be built
independently from the original validated program so one transform does not
hide another transform's ownership error.

Kinds, schemes, abstractions, applications, and resolved-owner rows remain
compile-time data. Evaluation gains no value, lookup, interface object, frame,
or state transition.

## Resources

Let `S` be the number of retained non-empty global rows, `R` the number of
parameter identities in those rows, and `K_R` the number of canonical Kind
nodes compared for those identities.

The combined-registry retention delta is `2S + R`: one row slot, one position-
index slot, and one ordered identity slot. The existing combined-registry pass
already visits the `R` checked parameters and their canonical Kinds, so
capturing the authenticated identities does not add a duplicate Kind traversal
or clone.

Independent registry validation charges row visits, identity visits,
uniqueness storage, and canonical Kind comparisons. Core abstraction
authentication fuses row identity checks with the existing canonical Kind
checks and charges any initializer-owner index it retains. Implementation tests
will publish the complete additive formulas after measuring the integrated
passes.

Exact success, one-short atomic failure, deterministic precedence, retry, and
accepted and rejected teardown are required. Core construction and transform
rebuilding retain `TYPE_WORK_LIMIT`; independent Core validation retains its one
cumulative `3 * TYPE_WORK_LIMIT` ledger. Task 9 does not raise or reset a limit.

## Evidence

The focused mutation matrix includes:

- two same-Kind global owners whose abstraction, `Forall`, and occurrences are
  coherently swapped;
- one global whose same-Kind parameters are coherently reordered throughout
  Core;
- a resolved interface or nominal parameter forged into an abstraction;
- missing, extra, duplicate, wrong-owner, and unconsumed registry rows;
- canonical identity, Kind, and source/module provenance mutations;
- inconsistent generated identity, Kind, duplication, capture, shadowing, and
  escape mutations;
- a complete capture-free generated alpha-renaming that remains valid;
- independent identity and folding transforms followed by fresh validation;
  and
- exact and one-short construction, validation, transform, and teardown probes
  on the retained small-stack witnesses.

The existing positive linked higher-kinded program remains the end-to-end
construction, transform, revalidation, erasure, and evaluation witness.

## Rejected alternatives

A flat `TypeVariableId -> BinderId` map loses within-owner order. Adding an
ordinal recreates the ordered row with a less direct completeness check.

A separate Core sidecar duplicates transfer, capacity, transform, and teardown
paths while providing no fact absent from the combined registry.

Embedding owner metadata in `TypeAbstractionNode` changes Core expression shape
and makes unchecked syntax claim its own authority.

Pruning interface-only variables from the Core registry blocks one forgery but
does not authenticate cross-owner swaps or within-owner order.

Retaining generated identities externally rejects valid alpha-renaming and
conflicts with CP-0009's local generated-binder ownership rule.
