# AD-0009: Ordered Resolved-Global Binder Authority

- ID: `AD-0009`
- Status: accepted
- Related: [AD-0006: Front-End Semantic Boundaries](AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](AD-0007-typed-core-dialects.md), [DN-0025: Library and Package Milestones](../design/DN-0025-library-and-package-milestones.md), and the [explicit-kind evidence](../design/lib-ash/kinds-evidence.md)

## Decision

The combined resolved registry retains one private ordered owner fact for each
non-empty resolved global scheme. Each fact contains the stable term
`BinderId` and the global scheme's resolved `TypeVariableId` values in source
order. The registry retains the facts in deterministic module and declaration
order and provides private lookup by the owning term binder.

The canonical resolved type-variable record remains the only authority for a
parameter's kind, spelling, and source origin. An owner fact does not copy that
metadata, a scheme body, evidence, an implementation route, or a module group.
Checked-registry combination authenticates the facts before retention, and
linked-evidence validation authenticates the completed registry before it can
authorize Core construction.

Module-aware Core validation derives a resolved abstraction's owner only when
the abstraction is the immediate initializer of a `RecursiveBind` member. It
requires the abstraction parameters, matching outer `Forall`, canonical
records, and retained owner fact to agree exactly in identity and order. Every
retained fact must be consumed exactly once. A sequential Core `Bind` cannot
claim this authority.

Generated Core type binders remain local to their abstraction, matching outer
`Forall`, body, and applications. Complete capture-free substitution with
fresh identities is valid alpha-renaming; the elaborator's original generated
identity, source span, and allocation ordinal are not external authority.

Core transformations share the immutable combined registry and revalidate
their rebuilt programs. Evaluation does not inspect resolved-global owner
facts. This decision changes compiler authentication, not Ash syntax, static
semantics, or runtime behavior.

## Context

The canonical resolved-variable registry authenticated each identity and kind
but flattened the checked global scheme that owned the identity. Independent
Core validation could therefore accept a coherent same-kind swap between two
global owners, a coherent reorder within one global, or an interface-only
identity forged into a global abstraction. Checking canonical membership alone
could not recover owner or source order.

Global linking already preserves a stable term binder and lowers final globals
through recursive module groups. The combined resolved registry already
crosses the validated linking boundary, Core construction, independent
validation, and retained transformations through one immutable shared value.
Retaining the missing owner-and-order fact there avoids a second authority
carrier.

The rejected alternatives were:

- a flat type-variable-to-owner map, which loses within-owner order;
- an owner map plus ordinals, which recreates ordered rows less directly;
- a separate Core sidecar, which duplicates transfer, resource, transform, and
  teardown paths;
- owner metadata embedded in unchecked Core nodes, which lets syntax assert
  its own authority;
- pruning interface-only variables, which does not prevent cross-owner swaps
  or within-owner reordering; and
- external authority for generated identities, which rejects valid
  alpha-renaming.

## Consequences

- The compiler can reject missing, extra, duplicate, reordered, wrong-owner,
  nominal, interface-only, and unconsumed resolved-global facts before
  evaluation.
- Only resolved global parameters use this authority. Nominal parameters keep
  their separate ordered ownership; interface parameters erase before Core;
  implementation-method and locally generalized parameters use generated Core
  identities.
- The registry carries no redundant linked constructor scheme or generated
  binder provenance.
- Identity traversal and literal folding must preserve the exact shared
  registry and pass fresh module-aware validation.
- Retaining `S` non-empty owner facts containing `R` identities costs `2S + R`
  type-work units, plus the separately charged owner-uniqueness index.
- The concrete row and lookup types remain private compiler representation.
  The specification states only the observable authentication relationship.

## Verification

The implementation must retain:

- positive linked higher-kinded construction, both retained transformations,
  fresh validation, erasure, and evaluation;
- coherent cross-owner swap and within-owner reorder rejection;
- missing, extra, duplicate, wrong-owner, wrong-position, nominal,
  interface-only, and unconsumed fact rejection;
- sequential-`Bind` rejection and exact immediate-`RecursiveBind` ownership;
- complete generated-binder mutation rejection together with one accepted
  capture-free alpha-renaming;
- exact and one-short construction, validation, transformation, and teardown
  resource probes without a production limit change; and
- deterministic failure precedence, retry, and accepted and rejected teardown
  on the retained small-stack witnesses.
