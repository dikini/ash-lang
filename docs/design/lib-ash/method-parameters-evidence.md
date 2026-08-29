# Method-Local Type-Parameter Evidence

This report records implementation evidence for the third bounded `lib-ash`
increment: explicit fixed-kinded method-local type parameters and authenticated
polymorphic method evidence. It is informative, not normative. The
[Ash specification](../../../spec/README.md) alone defines the current
language. Git history retains the accepted proposal, implementation task, and
execution plan after those transition-only artifacts leave the current tree.

This report does not close the complete `lib-ash` milestone. Multi-parameter
interfaces, determination, associated outputs, defaults, the combined library
corpus, and the final library simplification audit remain separate work. This
increment receives no `lib-ash` tag.

## Scope and checkpoints

The transition starts from integrated explicit-kind checkpoint `e4fbc54`. Its
principal unsigned boundaries are:

- `ebe4c5d`, `9f90176`, and `d415111`, which accept the semantic transition,
  create its task and plan, and record the fixed 70-unit authorization;
- `faeb689` through `2ae306f`, which retain syntax, projection, recovery,
  canonical resolved method binders, and exact front-end resources;
- `a9d5812` through `23f35bd`, which retain method schemes, occurrence
  instantiation, rigid implementation checking, pending inference closure, and
  selection isolation;
- `652f74c` through `61e3d77`, which retain body-free method schemes, import
  admission, atomic occurrence publication, linked authentication, and bounded
  validation;
- `cf93de7` through `851c26c`, which retain authenticated Core evidence
  domains and adapters, exact source relationships, transformations, resource
  formulas, and independent validation;
- `dab6e93` and `a6174ec`, which retain the complete product, diagnostics,
  migration, runtime trace, carrier inventory, small-stack lifecycle evidence,
  independent reviews, and the 1,531-test product boundary; and
- `685b019`, which reserves the final specification, evidence, review, and
  transition-cleanup checkpoint at cumulative use 70/70;
- `09e9dd8`, which reconciles the normative specification and creates the
  initial retained method-parameter evidence report;
- `9304a04`, which corrects the specification boundaries for atomic module
  publication, inert retained runtime authority, and method-list lexical
  syntax;
- `9ade2df`, which corrects the runtime-boundary wording for selected evidence
  flowing through existing function values and applications;
- `33ce4b4`, which records ten added authorized units and reserves eight for
  the concrete-source prerequisite correction at cumulative use 78/80, with
  two units unreserved;
- `8930564`, which corrects concrete-source prerequisite provenance and
  remeasures the directly affected validation resources; and
- `72a91e3`, which retains the semantic/specification and
  implementation/Core/resource approval records for that correction; and
- `689f64a`, which completes the principal checkpoint ledger and records the
  conditional transition-cleanup boundary.

The third evidence, migration, lifecycle, and authority review found that the
checkpoint ledger stopped at the reservation boundary and omitted these later
commits. The third-review re-review approves the correction after `689f64a`
resolved that sole Important finding. Fresh root and documentation verification
now pass. The next boundary is the retained-evidence commit; the approved
transition cleanup follows it. Commit identities are evidence boundaries, not
independent language authority.

## Implemented boundary

An interface method may bind one explicit, complete, ordered list of
fixed-kinded local parameters:

```ash
interface Functor<F : Type -> Type> {
    map<A, B> : (A -> B, F<A>) -> F<B>
}
```

The interface parameter and method parameters scope over that signature. An
omitted kind is `Type`; an absent list binds no method parameter. Source code
does not acquire implicit method binders, method requirements, `forall`, or
expression type arguments.

Each occurrence instantiates the interface parameter followed by the method
parameters. Only the interface argument creates an evidence obligation.
Selection neither observes nor refines method arguments. A selection may be
fixed before module inference closes, but its occurrence remains private
pending state until all interface and method arguments are inference-free and
the checked module publishes every occurrence atomically.

An implementation substitutes its head argument for the interface parameter
and checks each method once under two rigid sequences: implementation-head
parameters followed by method parameters. It retains the partition as well as
the combined order. A direct recursive occurrence reuses the method's rigid
arguments and cannot gain polymorphic recursion. Method-local arguments do not
enter an implementation head or prerequisite goal and cannot change candidate
choice.

## Canonical schemes and occurrence authority

The defining resolved method-binder record is the authority for identity,
spelling, kind, source origin, owner, and order. Allocation follows module
declaration order, interface parameter order, method declaration order, and
written method-binder order. The checked registry retains:

```text
MethodScheme = forall method_parameters. method_value_type
```

The interface parameter remains owned by the surrounding interface. The method
scheme does not enter the ordinary term environment and is not a source value.
Every occurrence retains its exact `MethodId`, interface argument, ordered
method arguments, checked occurrence type, and selected evidence. Import
aliases, targeted renames, facades, and dependency diamonds preserve the
defining identities.

The positive checking matrix covers optional and higher kinds, written order,
completeness, two unrelated instantiations, inference closure, exact-current
evidence, concrete evidence, generic heads and prerequisites, direct recursion,
qualified and targeted imports, facades, diamonds, hidden and opaque carriers,
and stable defining identity. The negative matrix keeps interface-goal
ambiguity at `constraint.ambiguous`, method-argument ambiguity at
`type.ambiguous`, and changed recursive instantiation at
`type.polymorphic-recursion`.

## Summaries and linked authentication

A public checked interface fact and every body-free mirror retain ordered
method-binder records and the method monotype separately. Summary construction
retains hidden kind and identity closure. Import admission authenticates the
complete binder set, order, owner, kinds, body scope, method identity, spelling,
annotation span, and provenance before the dependent checks from that summary.

After module inference closure, linked validation authenticates every frozen
occurrence argument against its defining method scheme and fixed kind. It also
checks the occurrence type, selected `MethodId`, selected `ImplMethodId`,
implementation head substitution, prerequisite producers, combined
head-versus-method binder partition, availability route, and source origin.
Core synthesis receives only the capability produced by that complete check
and does not select evidence again.

One body-free checked method fact must retain the exact annotation subspan in
addition to the complete declaration origin. Without it, an importer cannot
reconstruct the source relation authenticated by an implementation method. The
linked product retains this exact implementation provenance:

- primary `carrier.ash` range `81..130`;
- related carrier declaration `57..132` and method `81..130`;
- related `api.ash` method `42..76` and annotation `54..76`; and
- related carrier body `110..130`.

Linked validation authenticates that complete cross-source relation. Core's
accepted source-local provenance invariant receives the already-authenticated
primary span at final implementation-method lowering; the full linked relation
does not become an unauthenticated Core side table.

## Authenticated Core evidence

The existing Core type abstraction, type application, function, and
application forms express the increment. A polymorphic method requirement
becomes one generated evidence domain:

```text
forall definition_parameters.
    (forall method_parameters. substituted_method_value_type) ->
    ... ->
    source_value_type
```

A monomorphic method keeps its ordinary function evidence domain. At an
abstract occurrence, Core type-applies the evidence binder to the retained
method arguments before applying source arguments. Exact forwarding may pass
that binder uninstantiated only to the same authenticated evidence domain.

A concrete or exact-current polymorphic selection uses one unspecialized
adapter:

```text
type-abstract method_parameters.
    type-apply implementation_method
      <implementation_head_arguments, method_parameters>
      prerequisite_evidence...
```

The adapter exposes exactly the selected method scheme. It does not copy or
specialize the implementation body. Head arguments precede method arguments;
prerequisites retain prerequisite and interface-method order. Repeated
selections of one implementation at different evidence nodes or substitutions
remain distinct adapters.

Minimal immutable authentication facts relate every evidence position to its
definition owner, requirement and method order, `MethodId`, interface argument,
method scheme, and selected implementation source. Independent Core validation
derives the expected scheme, validates every occurrence, forwarding use and
adapter, and consumes every fact exactly once. Canonical method binders compare
exactly. Only a generated adapter may use one bounded capture-free, order- and
kind-preserving alpha-renaming. Monotype equality and unification remain exact.

For a retained concrete implementation source, validation also compares its
prerequisite rows lockstep with the selected implementation node's direct
prerequisites, flattened in prerequisite declaration order and then each
child's interface-method order. Both the selection node and `MethodId` must
match, and both sequences must end together. Existing per-row producer,
binder, Core application-chain, and recursive-source checks then validate the
matched rows.

Identity and literal-folding transformations preserve or rebuild the complete
relationship, then pass fresh independent validation. Method schemes and
authentication facts may remain as inert authority in the validated program,
but the evaluator does not inspect them or derive runtime state from them. Core
type operations erase through the existing dynamic rules before observation.
No new Core node or evaluator state is present.

## Tampering matrix

The retained private mutation suites reject each relationship independently:

| Boundary | Rejected mutations |
| --- | --- |
| resolved and checked method facts | missing, duplicate, reordered, wrong-kind, wrong-owner, wrong-origin, wrong-spelling, or interface-parameter-colliding binders; unlisted, unused, free, or escaped binder bodies |
| summaries and import admission | missing, extra, duplicated, reordered, wrong-kind, wrong-owner, wrong-origin, or wrong-spelling body-free binders; forged annotation spans; a nested scheme in an ordinary global, constructor, implementation head, prerequisite, or source method body |
| linked occurrences and implementations | mismatched interface or method arguments, wrong checked occurrence type, wrong `MethodId` or `ImplMethodId`, wrong selection, wrong head substitution, reordered head and method binders, wrong prerequisite producer or order, and unavailable or forged route provenance |
| Core authentication | missing, duplicate, unconsumed, wrong-owner, wrong-position, wrong-order, wrong-kind, wrong-method, forged, or shared facts; nested schemes in ordinary value positions |
| adapters and transforms | capture, escape, shadowing, partial or reordered type application, wrong implementation binder, wrong head or method arguments, wrong prerequisites including a reachable sibling-node substitution or same-node method-order swap, mismatched scheme, malformed transformed relation, or renamed canonical method facts |

Positive evidence accepts one complete capture-free generated adapter-binder
renaming. Original, identity-transformed, and literal-folded product programs
all pass fresh independent validation and evaluate equally.

## Linked product and runtime observation

The retained fixture in
[`tests/fixtures/method-parameters/linked-product`](../../../tests/fixtures/method-parameters/linked-product)
contains:

- a higher-kinded `Functor<F>` with `map<A, B>`;
- one separately checked `map_pair` constrained global using `Int` to `Bool`
  and `Bool` to `Int` instantiations;
- one public generic `Box<A>` implementation; and
- one entry that imports `map_pair`, `Box`, and `impl Functor` explicitly.

The library and CLI both observe:

```text
(Box(true), Box(42)) : (Box<Bool>, Box<Int>)
```

The retained files are named `interface.ash`, `implementation.ash`, and
`entry.ash`. Executable trees stage the first two contents as `api.ash` and
`carrier.ash` because `interface` is reserved in a module path.

The exact product trace has maximum continuation depth three and these nine
entry classes in order:

```text
type-abstraction-erasure
type-application-erasure
variable-lookup
apply
type-application-erasure
variable-lookup
apply
type-application-erasure
variable-lookup
```

Polymorphic method evidence flows as ordinary function values and applications,
but adds no new evaluator value class, environment-entry class, frame kind,
lookup class, transition class, failure reason, runtime interface state,
dictionary, registry, registration, or dispatch. The trace contains additional
instances of existing erasure, lookup, and strict-application transitions, not
a new transition rule.

## Diagnostics, migration, and unavailable routes

The diagnostic matrix retains exact typed reasons, primary and related spans,
causal labels, and deterministic precedence through the library and CLI.
Malformed binder syntax is parser-owned. Resolution owns duplicates, an
interface-parameter collision, unused binders, and unlisted names in a present
complete list. Kind checking owns invalid binder and method-type kinds.
Interface checking retains `interface.method-parameter` for another free
variable under an absent list or an omitted interface parameter, before
`interface.method-not-function` after successful kind checking.

The predecessor migration is explicit. This declaration remains invalid:

```ash
interface Project<I> {
    project : (I, A) -> A
}
```

Adding `project<A>` makes the previously rejected method valid. There is no
compatibility grammar, implicit binder, inferred binder kind, or second compiler
path.

Direct negative evidence keeps all twelve unavailable higher-rank routes out
of the language:

- source `forall` and explicit expression type application;
- polymorphic parameter and result annotations;
- polymorphic tuple and constructor fields;
- scheme storage, return, and passing to an ordinary parameter;
- implicit method binders and method-level requirements;
- and polymorphic recursive self-use.

## Exact resources and lifecycle

All proportional work charges before allocation, traversal, or publication.
Syntax work uses its syntax ledger. Binder records, method schemes, occurrence
arguments, substitutions, adapters, and Core types use the owning type-work
ledger. Summary, occurrence, selection, route, and linked-authentication work
uses the graph-wide constraint ledger. Core construction and Core validation
retain separate cumulative ledgers. No production limit changed.

The syntax token-plus-event formula is exactly `66 + 14P` for `P` method
parameters, retained at `P = 1, 2, 3, 512`. The source-derived owner manifest in
[`tests/method_parameter_resources.rs`](../../../tests/method_parameter_resources.rs)
contains 39 formulas attached to 27 unique probes. Its principal exact
boundaries are:

| Owner | Exact constraint / type work |
| --- | --- |
| resolution binder validation | `13` |
| imported method-binder kind authentication | `4` |
| hidden interface import | `19 / 19` |
| summary private binder authority | `1 / 4` |
| selector scheme ingress | `20`; wide `7W + 11 / 3W + 5` |
| occurrence publication | `8 / 2` |
| selected rigidity | `25 / 3`; shifted removal `27 / 3` |
| conditional rigidity | `12 / 1`; wide `4W + 8 / 1` |
| method occurrence kind copies | `7 + 2K` type work |
| Core evidence-scope carrier | `6` type work |
| selected rigidity traversal | `3` type work |
| general linked catalog | `107 / 74` |
| widened abstract-producer catalog | `89 / 32` |
| concrete adapter-source catalog | `141 / 36` |
| Core Builder constructor | `2E`, hence `4` for `E = 2` |
| one-anchor authentication and finish | `14` |
| concrete monomorphic validator | `633` |
| concrete source with two abstract-prerequisite methods | `1,092` |
| monomorphic adapter-edge validator | `746` |
| independent polymorphic validator | `2,339` |
| checked lowering worklist | `10` |
| identity or literal-fold transform | `686`, including a `4`-unit second Builder carrier |
| rejected pending-zonk teardown | depth `32,768` |

Every exact boundary retains success, one-short atomic failure, and two fresh
exact retries where the owner supports retry. Catalog formulas separately
charge selected method width, domains, adapters, producer lookups,
prerequisites, and checked traversal capacity. A generic implementation probe
also proves that a discarded six-unit head-scope buffer is not charged.

The wide concrete-source boundary is exactly
`1,084 + Q*W + R + D*W = 1,084 + 2*2 + 2 + 1*2 = 1,092`. The final two terms
charge one visit to each of the `R = 2` retained rows and one visit to each of
the `W = 2` methods under the `D = 1` direct selected prerequisite. The
zero-prerequisite 633-unit validator, 2,339-unit independent polymorphic
validator, and 686-unit identity and literal-fold transform boundaries do not
change.

Deep accepted and rejected method types at depth 96 and wide accepted and
rejected methods at width 128 traverse the public pipeline and dispose on a
256 KiB thread stack. A width-64 adapter program, both transformed programs,
and a prebuilt rejected adapter-bearing Core program freshly validate or reject
and dispose on the same stack. A depth-32,768 pending zonk failure disposes
iteratively there. Public width 1,024 succeeds; width 5,000 fails twice at the
unchanged typing constraint budget, and a fresh width-1,024 retry succeeds.

The complete public adapter pipeline cannot be constructed on a 256 KiB stack
even at width two because of a width-independent construction frame. The
small-stack lifecycle claim therefore consumes prebuilt accepted and rejected
adapter states. It covers teardown, not construction on that stack, and does
not justify a production-limit change.

## Production and maintenance sites

| Boundary | Principal production owners |
| --- | --- |
| syntax, events, projection, and recovery | `src/parser/grammar.rs`, `src/parser/project.rs`, `src/parser/mod.rs`, `src/surface.rs` |
| binder identity, scope, summaries, and import admission | `src/resolve.rs`, `src/resolved.rs` |
| kinding, schemes, inference, rigidity, selection, and occurrence publication | `src/kind.rs`, `src/elaborate.rs`, `src/evidence.rs`, `src/interface.rs`, `src/types.rs` |
| linking and complete authentication | `src/evidence_validation.rs`, `src/driver.rs` |
| Core evidence facts, construction, validation, and transforms | `src/core/dialect.rs`, `src/core/type_ops.rs`, `src/core/validate.rs`, `src/core/transform.rs`, `src/elaborate.rs` |

Primary maintenance targets are `interfaces_syntax`, `parser`, `resolution`,
`kinds`, `polymorphism`, `interfaces`, `implementations`, `interface_modules`,
`interface_validation`, `evidence_validation`, `core_validation`,
`architecture`, `diagnostics`, `source_diagnostics`, `corpus`,
`interface_resources`, `method_parameter_resources`, `module_cli`, and
`spec_examples`.

The increment changes no evaluator source, adds no Core node, and changes no
production resource limit.

## Review and verification status

Checkpoint 6 received two independent reviews. Semantic review approved binder
authority, linked provenance authentication, adapters, product behavior,
transforms, diagnostics, exclusions, and runtime erasure with no findings.
Quality and resource review first rejected an incomplete formula manifest, a
one-way carrier inventory, and insufficient rejected-lifecycle evidence. The
same implementation pass added complete formulas, bidirectional inventories,
prebuilt rejected-Core disposal, pending-zonk disposal, and the two omitted
hidden-import and discarded-buffer probes. Re-review approved the corrected
boundary with no findings.

Fresh Checkpoint 6 verification passes 711 library tests, 62 Core-validation
tests, 34 interface tests, 41 polymorphism tests, 23 architecture tests, and a
combined 240-test focus. The locked workspace/all-target/all-feature inventory
contains 1,531 passing tests. Formatting, locked checking, strict Clippy with
warnings denied, `cargo xtask verify` including warning-denied rustdoc,
Markdown lint, all relative-link targets in 84 Markdown files, and diff hygiene
pass at `a6174ec`.

Checkpoint 7 begins with 57 predecessor executable specification tests. Its
four documentation REDs prove the missing normative manifest, complete linked
overview, exact CLI observation, and predecessor-to-explicit migration while
all product execution succeeds. The reconciled specification passes all 61
examples. Its first semantic/specification review found three local
reconciliation defects: the formal module result was not connected to frozen
occurrence definitions, dynamic prose overstated physical erasure instead of
evaluator non-inspection, and the lexical angle-bracket inventory omitted
method lists. The correction connects atomic checked-module and summary
publication, states the inert retained-authority boundary, and updates the
lexical inventory and executable manifest. Final semantic re-review,
implementation/Core/resource review, evidence/migration/lifecycle/authority
review, and the complete inventory are recorded here before transition cleanup.

A later corrective review found one independent-Core implementation defect.
The concrete-source catalog already retained prerequisite selection nodes and
methods in the exact order fixed by linked selection, but validation checked
only reachable-node membership for each copied row. Before production changed,
the focused wide-`Leaf` RED coordinated the catalog rows and same-typed Core
applications. The exact command, under its temporary first test name, was
`cargo test --locked --lib
core::validate::tests::concrete_source_prerequisite_method_order_is_authenticated_after_every_rebuild
-- --exact --nocapture`; it failed at rebuild zero because validation admitted
the mutation, with zero passed, one failed, and 711 filtered tests.

The correction adds an allocation-free lockstep comparison against the direct
selected prerequisite and method sequence. The retained method-order test and
a distinct same-typed sibling-selection-node test reject in original,
identity-rebuilt, and literal-folded Core. Removing only the selection-node
comparison makes the sibling test fail at rebuild zero, proving that the test
does not rely on the method comparison. Fresh corrective verification passes
713 library tests, 62 Core-validation tests, 23 architecture tests, four
method-parameter resource tests, and the focused 633, 1,092, 2,339, and 686
one-short and fresh-retry probes. Workspace/all-target/all-feature checking,
strict Clippy with warnings denied, formatting, Markdown lint, and diff hygiene
also pass. No specification, selection rule, persistent Core carrier,
evaluator behavior, or production resource limit changes. The correction uses
its reserved eight units at cumulative use 78/80; two units remain unreserved.
Checkpoint 7 reviews and complete root verification remain open after this
implementation handoff.

The focused GREEN commands are `cargo test --locked --lib
core::validate::tests::concrete_source_prerequisites_match_direct_selection_nodes_after_every_rebuild
-- --exact --nocapture` and `cargo test --locked --lib
core::validate::tests::concrete_source_prerequisites_match_selected_method_order_after_every_rebuild
-- --exact --nocapture`. The 713/62/23/4 counts come from `cargo test --locked
--lib`, `cargo test --locked --test core_validation`, `cargo test --locked
--test architecture`, and `cargo test --locked --test
method_parameter_resources` respectively.

Independent semantic and specification compliance review approves
`33ce4b4..8930564` with no findings. Existing specification and accepted
CP-0010 authority fully determine this local validator correction, so it adds
no language rule. Fresh review verification passes both concrete-source
prerequisite regressions, 713 library tests, 62 Core-validation tests, and four
method-parameter resource tests. Formatting and diff hygiene also pass.

The original stop-condition reviewer approves the implementation, Core, and
resource re-review of `33ce4b4..8930564` with no Critical, Important, or Minor
findings. Exact selection-node and method lockstep comparison with cardinality
exhaustion closes the gap while preserving every downstream producer, binder,
Core application-chain, and recursive-source check. The same-typed sibling-node
substitution and same-node method-order swap remain meaningful in original,
identity-rebuilt, and literal-folded Core. The exact 633, 1,092, 2,339, and 686
boundaries retain one-short rejection and fresh retries. Fresh review
verification passes 713 library, 62 Core-validation, 23 architecture, and four
method-parameter resource tests, plus workspace/all-target/all-feature
checking, strict Clippy, formatting, changed-document Markdown lint, diff
hygiene, and clean status. The reviewer finds no semantic,
Core-representation, or production-limit stop condition.

The third evidence, migration, lifecycle, and authority review reports one
Important local evidence/lifecycle finding and no Critical or Minor finding:
the principal checkpoint ledger omitted the specification, wording,
correction, resource, and review commits after `685b019`. It finds no semantic,
Core-representation, production-limit, migration, or stack-lifecycle stop
condition. Its checks pass both concrete-source prerequisite regressions, 713
library tests, 62 Core-validation tests, four method-parameter resource tests,
all 61 specification examples, predecessor migration and all twelve excluded
higher-rank routes, Markdown lint, every relative link in 85 Markdown files,
and the budget and integration audit.

The third lifecycle re-review approves the corrected ledger at `689f64a` with
no remaining finding. The sole Important finding from the first review is
resolved; the re-review finds no semantic, Core-representation,
production-limit, migration, or stack-lifecycle stop condition.

Fresh root verification passes `cargo fmt --all -- --check`, `cargo check
--locked --workspace --all-targets --all-features`, and `cargo clippy --locked
--workspace --all-targets --all-features -- -D warnings`, each with exit status
zero. `cargo test --locked --workspace --all-targets --all-features` passes all
1,537 listed tests with exit status zero. `cargo xtask verify` also exits zero,
including its documentation checks. `git diff --check` passes, the reviewed
tree is clean, and `git diff --exit-code 9ade2df..HEAD -- src/eval spec` is
empty. The increment therefore changes neither the evaluator nor the normative
specification after the accepted specification boundary.

An independent documentation gate at `689f64a` checks 85 Markdown files: lint
passes and all 731 current relative links resolve. Simulated transition cleanup
checks 82 retained Markdown files and all 696 retained links, with no retained
link to a removed artifact.

The review approves transition cleanup after this ledger correction,
third-review re-review, full root verification, retained-evidence commit, and
clean-tree gate. The first three gates and the pre-retention clean-tree check
are complete. The next boundary is this retained-evidence commit; cleanup
follows it. The approved cleanup set is
`docs/proposals/CP-0010-method-local-type-parameters.md`,
`docs/tasks/TASK-0017-implement-method-local-type-parameters.md`, and
`docs/plans/2026-08-28-method-local-type-parameters.md`. Cleanup replaces the
CP-0010 entry in `docs/proposals/README.md` with the no-accepted-change state
and the TASK-0017 entry in `docs/tasks/README.md` with the no-active-task state,
then removes any stale current-tree links. This report records that conditional
approval without taking over task authority.

Cumulative reserved use remains 78/80, with two units unreserved. This retained
evidence does not claim integration or completion of the full `lib-ash`
milestone.

## Intentional exclusions and remaining pressure

This increment does not add implicit method binders, method-local kind
inference, kind polymorphism, type lambdas, higher-order unification,
impredicative instantiation, source `forall`, expression type arguments,
polymorphic annotations or ordinary values, method requirements, polymorphic
recursion, multi-parameter interfaces, determination, associated outputs,
defaults, overrides, specialization, negative implementations, fallback
selection, new implementation import forms, packages, persistent artifacts,
separate object linking, dynamic loading, runtime registries, or a public
authentication representation.

Later work may consume canonical method schemes, authenticated summaries,
occurrence arguments, and generated adapter evidence. It requires separate
semantic authority and cannot reinterpret this report as language truth. The
complete `lib-ash` milestone remains open and untagged.
