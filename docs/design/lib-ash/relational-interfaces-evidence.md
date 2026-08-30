# Multi-Parameter Relational-Interface Evidence

This report retains implementation evidence for the fourth bounded `lib-ash`
increment: complete ordered multi-parameter interface applications and one
optional total forward determination edge. It is informative, not normative.
The [Ash specification](../../../spec/README.md) alone defines the current
language. Git history retains the accepted proposal, implementation task, and
execution plan after those transition-only artifacts leave the current tree.

The revised `lib-ash` product goal consists of this increment and the three
earlier retained increments. Integration, transition-artifact cleanup, and any
milestone tag are lifecycle actions. Associated-output syntax, general
determination graphs, defaults, effects, proofs, existentials, packages, and
persistent artifacts remain separate work.

## Scope and checkpoints

The branch starts from the integrated method-parameter checkpoint `a823094`.
Its principal unsigned product checkpoints are:

- `cf549f9`, which accepts CP-0011, creates TASK-0018 and its execution plan,
  and reserves the 65-unit implementation slice;
- `ade65e6`, which retains vector and determination syntax, recovery, resolved
  identities, and predecessor unary migration;
- `aeb7b82`, which carries complete ordered applications through checking,
  summaries, evidence, linking, and Core authentication;
- `f9868ba`, which admits one total partition and makes method determinacy,
  implementation coverage, coherence, orphan ownership, and prerequisite
  decrease use its selection key;
- `5b6acd2`, which retains the fixed one-pass improvement snapshot, determined
  requirements, full-goal selection, and the approved prerequisite-pair order;
  and
- `e660c17`, which retains the compositional linked product, adversarial
  authentication matrix, downstream-pressure inventory, exact resource
  formulas, independent reviews, and full implementation gate; and
- `87e6bcb`, which retains normative reconciliation, executable specification
  and predecessor guards, this durable report, the simplified milestone
  boundary, independent approvals, and the full documentation/product gate.

Commit identities are evidence boundaries, not language authority.

## Implemented boundary

An interface declares a nonempty ordered vector of fixed-kinded parameters.
Every requirement and implementation supplies one complete ordered application
with exact arity and positional kinds. An interface may also declare exactly
one total edge:

```ash
interface Relation<F : Type -> Type, Key, Dep> where (F, Key) -> Dep {
    relate<X> : (F<Key>, X) -> F<Dep>
}
```

Both edge sides are nonempty, disjoint, declaration-ordered, and together name
every parameter exactly once. The left positions are the selection key; the
right positions are the dependent complement. With no edge, the complete
application is the selection key. Unary no-edge interfaces remain the width-one
predecessor case.

Every method must mention every selection-key parameter. A dependent may occur
in a method domain, codomain, nested type, or nowhere. Free variables outside
the interface set are exactly the explicit method parameters. One occurrence
freshens the whole interface vector and then the method parameters, applies one
simultaneous substitution, and creates one complete-application obligation.
Method-local arguments never participate in improvement or evidence choice.

## Requirements, implementations, and coherence

A no-edge global requirement requires every application variable to occur in
the value type. A determined requirement requires every key variable there and
may retain dependent-only binders in its scheme and Core abstraction. No rule
propagates information between requirements. For the same `InterfaceId`,
complete duplicates are `constraint.duplicate-requirement`; an equal determined
key with a different dependent tuple is `constraint.determination-conflict`.

Implementation binders cover free variables across the complete head. An
omitted list follows first occurrence across all arguments. Dependent-head
variables must be covered by key variables. The all-bare-variable rejection,
orphan ownership, and generic prerequisite decrease use the selection key;
prerequisite variable containment and ground cycle identity use the complete
application. Decrease compares equal-width key tuples pointwise, with identity
or strict subterm at every position and at least one strict position.

Prerequisite pairs are classified deterministically after application arity and
kinds. Each current prerequisite is compared with earlier prerequisites in
their source order; complete identity is considered before key identity. The
first classified pair owns the failure. Detached summary admission
authenticates arity and kinds before replaying the same order.

Effective environments deduplicate stable implementation identities. Distinct
heads with non-unifying keys are coherent. If keys and complete heads unify,
the result is `impl.overlap`; if keys unify but complete heads cannot, it is
`impl.determination-conflict`. No source, dependency, import, or candidate order
chooses a winner.

## Improvement and selection

Ordinary kind-aware unification runs first. Before any improvement mutation,
the checker snapshots the determined obligations whose complete keys are
inference-free. It visits only that fixed set, once, in source order, and uses
the first applicable source:

1. an identity-equal abstract key;
2. the exact current implementation key; or
3. the unique visible independently freshened key match.

The source supplies the complete dependent tuple. Improvement is mandatory,
even when ordinary typing already fixed the dependent, and transactionally
unifies the whole tuple. A conflict publishes no partial inference solution.
Improvement does not guess or refine keys, reverse the edge, inspect
prerequisites, construct evidence, record a selection, repeat to saturation, or
unlock another obligation.

Full-application evidence selection follows improvement and retains the same
abstract, exact-current, and concrete priority. A pending determined occurrence
root must have belonged to the snapshot and must be complete and inference-free.
An unresolved key, a no-source unresolved dependent, or an outside-snapshot
pending root is `constraint.ambiguous`; an eligible complete root without a
matching source is `constraint.unsatisfied`. Recursively instantiated
prerequisites are already complete applications, use ordinary selection and
full-application active-cycle detection, and require no snapshot membership.
No-edge roots take the predecessor path and perform no snapshot work.

## Summaries, linking, and Core

Checked interfaces and every body-free mirror retain ordered parameter records
and optional determinant positions. Requirements, implementation heads,
prerequisites, and evidence roots retain complete applications. Summary
admission and linked validation authenticate arity, declaration order,
identities, kinds, origins, determinant positions, complete arguments,
substitutions, routes, and prerequisite trees.

`EvidenceSelection` remains opaque and occurrence-owned. Its only producers are
abstract requirements, exact current implementations, and concrete
implementations. Linked validation checks the recorded selection and never
chooses another candidate.

Elaboration simultaneously substitutes every interface argument in declaration
order before method-local arguments and evidence applications. Generated
adapters preserve implementation-head parameters before method parameters.
Determination adds no type binder, evidence method, Core node, validator
dialect, evaluator value, runtime dictionary, registry, lookup, frame,
transition, or failure mode. Determinant positions erase before Core; complete
applications may survive only in inert static authentication relationships
through transforms and independent validation. Complete substituted types and
those existing relationships remain sufficient; the evaluator does not inspect
them or make them control or state.

Identity and literal-folding transforms preserve or rebuild the complete
relationships. Original and transformed programs pass fresh validation and
evaluate equally.

## Linked product and adversarial evidence

The retained fixture in
[`tests/fixtures/relational-interfaces/linked-composite`](../../../tests/fixtures/relational-interfaces/linked-composite)
contains a higher-kinded three-parameter relation, a composite key, a
polymorphic method, a generic public implementation, an abstract constrained
helper, direct and unequal-length facade routes, and a concrete entry
selection. Body-free summaries retain one stable implementation identity and
the shortest authorization route. The library, CLI, identity transform, and
literal-folding transform all observe `42 : Int`.

The negative matrices independently reject:

- missing, extra, reordered, wrong-identity, or wrong-kind parameter records;
- invalid determinant positions and missing, extra, or reordered application
  arguments;
- key-only, dependent-only, abstract-root, implementation-root, prerequisite,
  route, and substitution disagreement;
- substitution of a same-shaped but identity-distinct hidden nominal;
- head-versus-method type-argument swaps and stale transformed authority; and
- partial publication after source, summary, linking, or Core validation
  failure.

Separate hidden, same-shaped private-twin, and public-opaque dependent nominals
cross summaries without making a hidden spelling nameable or an opaque
constructor accessible.

## Diagnostics and migration

The structured failure families retain exact causal ownership for argument
count and positional kinds, determination partitions, method seeds,
requirement pairs, implementation coverage, coherence, improvement conflict,
ambiguity, cycles, and unsatisfied evidence. The specification records the
ten-stage precedence from parsing through independent Core validation.

Every predecessor unary interface fixture remains valid as a one-parameter,
no-edge declaration. The executable specification corpus separately retains a
dependent-absent positive case, an ordinary no-edge omission rejection as
`interface.method-parameter`, an invalid partition rejection as
`interface.determination-parameter`, and the linked relational program.

## Exact resources

No production limit changes. The final retained exact boundaries are:

- `3P/2P` constraint/type work for method-free interface ingress;
- `7P+5/2P` for a leaf complete application;
- `17/2` imported and `18/2` local generic unary implementation ingress;
- `12L+11I/2(L+I)` for mixed zero-parameter implementation closures;
- `6W+11/6` for a wide improvement candidate scan;
- 11 type units for one constrained relational lowering owner;
- 6,516 constraint units for the fixed cross-stage graph, with an atomic
  one-short rejection at 6,515 before Core or evaluation; and
- determination snapshot boundaries `17/6` and `3W+14/6`.

The wide driver coefficients are 37, 53, 64, 67, and 116. At `W = 4890`,
linked work is 327,655, the unchanged constraint limit is 327,680, and
validation work is 567,320:

```text
327655 < 327680 < 567320
```

The retained `7P+5` formula charges the header, mirror comparison, candidate
carrier, interface authentication, scope, and structural traversal. An
additional per-parameter charge would count an existing visit twice. Generic
implementation-candidate ingress is different: its simultaneous vector and
owner index are separately retained and therefore each receive their own `P`
charge before allocation. Interface ingress retains only one vector and proves
module qualification, uniqueness, and declaration order in constant state.

All vector allocation, cloning, traversal, rejection, retry, and disposal
tests preserve charge-before-allocation, atomic publication, exact retry from
unchanged inputs, bounded explicit work stacks, and small-stack disposal.

## Reviews, verification, and exclusions

Checkpoint 6 semantic and security review approved the implemented semantics
without findings. Rust and resource review identified a missing second owner
for implementation candidates, a missing exact lowering probe, capability-free
goal validation, and an avoidable interface index. The corrections were
re-reviewed without remaining findings.

The `e660c17` product gate passed 801 library tests, 57 evidence tests, 46
interface-matching tests, 28 architecture tests, 64 Core-validation tests, 24
interface-module tests, and four method-parameter resource tests, plus
formatting, all-target checking, strict Clippy, and diff hygiene. Checkpoint 7
adds executable normative and predecessor-corpus guards. Its focused
specification and corpus suites pass 64/64 and 11/11. Independent semantic and
documentation/resource/lifecycle reviews approve without findings after
correcting the pending-root snapshot boundary, same-`InterfaceId` pair
premises, stale milestone prose, and suite counts. The retained tree passes
`cargo xtask verify`, including all integration suites, the xtask self-test,
doctests, and Rustdoc; Markdown lint, relative-link, and diff checks also pass.

Closed inventory checks confirm that no effect row or handler, proof term or
proof authority, existential binder or pack/unpack node, common universal
evidence family, associated declaration or projection, general edge graph,
default member, new Core form, or evaluator mechanism entered. Effects may
reuse identities but require separate dynamic authority. Proofs require a
separate authenticated evidence family. Existentials may encapsulate complete
applications and evidence without changing interface-head representation, but
still require separate scope, generativity, Core, and authority rules.

## Lifecycle state

This report is the durable replacement for the transition proposal, task, and
plan. During the retained Checkpoint 7 review those artifacts and their indexes
remain present so reviewers can compare accepted intent, execution evidence,
and normative truth. After the checkpoint is committed and independently
approved, a separate cleanup first records the result in those artifacts, then
removes the proposal, task, plan, and their index entries. Integration, repeated
root verification, and any tag follow their owning lifecycle; none changes the
language boundary recorded here.
