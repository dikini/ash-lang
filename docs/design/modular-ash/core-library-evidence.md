# Core and Library Equality Evidence

This report records the initial core-versus-library audit for Modular Ash. It
is informative, not normative. The [Ash specification](../../../spec/README.md)
alone defines the current language and runtime behavior. The active
[closure task](../../tasks/TASK-0014-finish-modular-ash.md) authorizes this
bounded audit but does not define semantics.

## Scope and representative

The paired representative is integer equality. This choice keeps one admitted
operation fixed while comparing two existing paths:

- source `41 == 41`, governed by the specification's
  [integer-only primitive rule](../../../spec/static-semantics.md#primitive-operations);
- explicit calls through a sibling `equality.ash` module that exports
  `Equal<A>`, `pub impl Equal<Int>`, its public `equal` method, and a
  constrained public `same` function.

The library path uses current method-only interface evidence. It does not
replace the operator, add an implicit import or prelude, or propose that
equality become a library-defined language feature. Existing
[constraint selection](../../../spec/static-semantics.md#constraint-satisfaction-and-checked-evidence),
[linked evidence validation and lowering](../../../spec/elaboration.md#interface-evidence-lowering),
and [generated-evidence execution](../../../spec/dynamic-semantics.md#generated-interface-evidence)
govern the observed path.

The retained target is
[`tests/modular_closure.rs`](../../../tests/modular_closure.rs). Before this
increment, that file was absent, was not tracked by Git, and no matching test
target or case existed under `tests/`.

## Source admission and typing

The direct path is fixed language syntax. The lexer and parser admit `==` as a
non-associative expression operator without a declaration or import. Resolution
retains a dedicated equality expression, and the primitive typing judgment
requires both operands to check as `Int` and synthesizes `Bool`. No interface
selection can change that domain.

The explicit library path is ordinary current Modular Ash source. The witness
loads a sibling module through an explicit import. Resolution authenticates its
public `Equal` interface, `equal` method, `Equal<Int>` implementation, and
constrained `same` global. Checking validates the method shape, implementation
ownership and membership, constrained scheme, and available implementation;
each occurrence retains its selected evidence for linked authentication. The
method call at `Int` and the `same` instantiation both synthesize `Bool` through
those existing judgments.

The comparison does not identify a shipped Ash library. The witness declares
its `Equal<A>` capability in test source. Its `Equal<Int>` method body uses
`left == right`, so integer equality remains implemented by the fixed intrinsic
and `Primitive::Equal`; the interface supplies an explicit reusable capability
boundary above that operation.

## Positive witness

The shared `positive_witness` helper creates a temporary two-module tree with
RAII cleanup. It manually loads the source graph, resolves and checks each
dependency in order, links the checked modules, validates the linked interface
evidence, synthesizes Core, and independently validates the whole Core program.
That manual assembly retains the intermediate Core needed by the structural
audit below.

`integer_equality_paths_complete_the_pipeline_with_one_observation` separately
invokes the public [`run_path`](../../../src/driver.rs) pipeline on the same
temporary entry path while the tree remains alive. This path owns entry-contract
validation, graph-wide resource orchestration, Core validation, and evaluation;
the manual assembly is not used as a substitute for that driver boundary.

The entry module returns this structural tuple:

```ash
(
    41 == 41,
    Equality.equal(41, 41),
    Equality.same((41, 41))
)
```

The public driver reports the exact structural type `(Bool, Bool, Bool)`, the
same exact source-facing type display, and the exact value
`(true, true, true)`. The separately assembled Core also passes independent
whole-program validation before inspection. This is one shared result, not a
claim that the three source paths have identical typing, diagnostic, or Core
structure.

## Core facts

`direct_and_library_equality_retain_distinct_core_paths` inspects the manually
assembled, independently validated Core. It locates definitions by their
resolved binder identities and module recursive-group membership. It uses
source origins to distinguish the direct expression from the implementation
method body. It does not depend on arena-wide node counts.

The retained facts are:

- the direct entry expression `41 == 41` is a Core `Primitive::Equal` with that
  source expression as its primary origin;
- the `Equal<Int>` implementation method belongs to the dependency's ordinary
  recursive group, and its body contains the retained `Primitive::Equal` whose
  primary origin is `left == right`;
- `Equality.equal(41, 41)` is an ordinary Core value application whose function
  is the selected implementation-method binder and whose argument is the
  source tuple;
- `Equality.same((41, 41))` is an ordinary type application of the `same`
  binder at `Int`, followed by an evidence application of the same
  implementation-method binder and then the source tuple application; and
- neither explicit library call introduces an interface or dictionary Core
  node. The existing [Core lowering rules](../../../spec/elaboration.md#interface-evidence-lowering)
  erase interface identities after linked evidence validation.

These assertions describe the stable audited boundary: binder identity, group
ownership, source origin, and the ordinary type/evidence/value application
nesting required by the specification. They intentionally omit unrelated
global node totals and incidental arena ordering.

## Evaluation and order consequences

The direct primitive evaluates its left operand and then its right operand
before comparing the two integer values. The explicit `equal` call instead
evaluates an ordinary implementation-method function and its tuple argument,
enters the method's pattern match, and then reaches the same left-to-right
integer primitive in the method body.

The constrained `same` call has more static and dynamic structure. Its Core
type application erases without a runtime value. Strict ordinary application
then supplies the selected implementation method as evidence before it
evaluates and supplies the source tuple. The method call inside `same` uses the
ordinary evidence binder, recursive-group lookup, function application, pattern
match, and finally the method body's `Primitive::Equal`.

The three fixed calls produce the same Boolean result, but the report does not
claim equal traces or equal cost. The library paths add ordinary lookup,
closure, type-erasure, application, tuple, and match transitions. They add no
runtime interface lookup, interface value, dictionary value, registry, Core
node, or evaluator rule.

## Paired negative diagnostics

The negative witnesses preserve a deliberate difference. They do not claim
diagnostic equivalence.

| Source | Owning boundary | Stable reason and cause |
| --- | --- | --- |
| `true == false` | Primitive operand typing | `type.operator-operand`; primary label on `true`, related label on `==`, expected `Int`, found `Bool` |
| `Equality.equal(true, false)` with only `Equal<Int>` available | Interface selection | `constraint.unsatisfied`; primary label on `Equality.equal`, then exact public method declaration, direct import, and interface-declaration causes |

`direct_boolean_equality_keeps_the_operator_operand_diagnostic` checks the
exact source spans and label messages for the operator-owned failure.
`imported_boolean_method_keeps_the_unsatisfied_interface_diagnostic` checks the
exact method occurrence, public declaration, import, and interface causes. It
also proves that no related label overlaps the unrelated `pub impl Equal<Int>`
declaration or body. The dependency contains no `Equal<Bool>` implementation,
so the importer has no available candidate. This agrees with the
specification's distinct
[failure ownership](../../../spec/static-semantics.md#failure-ownership-and-constraint-resources)
rather than forcing the interface call to imitate the operator diagnostic.

## Maintenance sites

This exact current search follows the direct equality representation from
source admission through resolved traversal, Core, transformation, and
evaluation:

```text
rg -l '\b(EqualEqual|EqualityExpression|RepeatedEquality)\b|SurfaceExprKind::Equal|ResolvedExprKind::Equal|BinaryKind::Equal|^\s+Equal\((BinaryExpr|ResolvedBinaryExpr)\),|Primitive::Equal|Self::Equal =>' src
```

Sorted, it returns these 15 production files:

```text
src/core/primitive.rs
src/core/transform.rs
src/elaborate.rs
src/eval/machine.rs
src/evidence_audit.rs
src/evidence_validation.rs
src/lexer/mod.rs
src/lexer/token.rs
src/parser/expression.rs
src/parser/grammar.rs
src/parser/mod.rs
src/parser/project.rs
src/resolve.rs
src/resolved.rs
src/surface.rs
```

Some files carry the equality expression through an exhaustive traversal rather
than define its behavior. The narrower closed-stage search

```text
rg -l 'Primitive::Equal|Self::Equal =>' src/core src/elaborate.rs src/eval
```

returns exactly `src/core/primitive.rs`, `src/core/transform.rs`,
`src/elaborate.rs`, and `src/eval/machine.rs`. These are the equality-specific
Core joins: variant and signature, construction and result typing, the explicit
decision not to constant-fold equality, and evaluation. Generic primitive Core
construction, validation, and traversal remain closed sites but require no
equality-specific branch.

The stable interface maintenance search remains:

```text
rg -l '\b(InterfaceId|MethodId|ImplId|ImplMethodId|RequirementId|EvidenceSelection|ConstrainedScheme|validate_interface_evidence)\b' src
```

It returns exactly `src/driver.rs`, `src/elaborate.rs`, `src/evidence.rs`,
`src/evidence_audit.rs`, `src/evidence_validation.rs`, `src/interface.rs`,
`src/resolve.rs`, and `src/resolved.rs`. The witness's `Equal<A>` declaration,
constrained function, and `Equal<Int>` implementation use those generic module
and interface paths. Adding another implementation to an admitted Ash source
graph requires no new Rust production site. This is a locality result for
current source mechanisms, not a claim that Ash ships a prelude, packaged
library, or reusable `equality.ash` artifact.

## Resources, ownership, and lifetimes

Both paths pay the existing source, type, Core-construction, Core-validation,
and evaluation bounds. Direct equality contributes one fixed expression and
one primitive Core node after its operands. The explicit library witness also
pays for a second source and import edge, interface and implementation facts,
constraint selection, checked occurrence evidence, linked authentication,
ordinary evidence Core applications, recursive-group method ownership, and
their evaluation transitions. The interface constraint-work budget spans
summary admission, checking, linking, and validation; Core synthesis and
independent validation keep their existing separate budgets. This comparison
does not infer a general cost ratio from the fixed witness.

The linked-interface registry is local to linked evidence validation. Successful
validation returns the `ValidatedInterfaceProgram` capability with its checked
source program, but does not retain the registry used by
`validate_occurrences`. Core synthesis borrows the capability. After synthesis
finish succeeds, the public driver explicitly drops it before independent Core
validation, releasing checked bodies, structural evidence, implementation
routes, and remaining checked interface metadata. The linked validator's
registry and indexes are already local to validation and have ended before this
drop. The resolved registry used to display the closed result type and the
computed type display remain available without keeping the validated interface
program alive. The focused architecture guard enforces both lifetime
boundaries.

The manual structural witness intentionally keeps its independently validated
Core for inspection. A returned `Value::Data(ObservedValue)` already owns an
`Arc` to the heap needed to render its structural or cyclic value. The public
driver's [`Observation`](../../../src/driver.rs) separately retains the
evaluation heap because a returned closure can capture an environment that
contains raw heap locations. The direct
`driver::tests::returned_closure_observation_retains_its_captured_structural_heap`
test returns such a closure and checks that its observation retains the
captured tuple's heap cell. `Observation._heap` is therefore not an unused
cleanup candidate.

## Simplification decisions and exclusions

The audit accepts three bounded conclusions:

- retain direct integer equality and `Primitive::Equal`; the explicit
  `Equal<Int>` method needs that implementation;
- use existing passive modules and method-only interfaces when source chooses
  an explicit equality capability; adding the tested implementation needs no
  new compiler representation or production dispatch site; and
- release the validator-local linked registry after authentication and the
  validated interface program after successful Core synthesis finish.

The audit rejects operator rewriting, an implicit import or prelude, an
interface-specific Core or runtime node, runtime lookup or registration,
dictionary values, and specialization. It does not introduce `lib-ash` or
`pack-ash` mechanisms, package or cache behavior, module signatures, reexports,
or a shipped library.

The stale-state review also rejects three proposed cleanups.
`ResolvedModuleProgram.entry` and each `ResolvedModuleGroup` module identity now
have interface-era readers for entry-closure and group-ownership
authentication. `Observation` must separately retain the heap for raw locations
captured by returned closures; returned structural `Value::Data` already owns
its own heap. A lean consuming synthesis payload remains deferred: the explicit
post-finish drop closes the proven long lifetime without adding another
representation or API.

## Evidence and verification

The target was first run while absent. Cargo rejected the command with
`no test target named modular_closure`, which establishes the pre-edit baseline.
After the target was added, its four tests passed.

The completed comparison retains the four paired tests and the architecture
boundary test. This increment uses these focused verification commands:

```text
cargo test --locked --test architecture authenticated_interface_state_ends_at_the_core_synthesis_boundary -- --exact
cargo fmt --check
cargo test --locked --test modular_closure
cargo test --locked --test architecture --test interfaces --test interface_modules --test interface_validation
cargo test --locked --test interface_corpus --test module_elaboration
cargo test --locked --lib
cargo clippy --locked --all-targets -- -D warnings
markdownlint --disable MD013 -- docs/design/modular-ash/core-library-evidence.md docs/design/modular-ash/evidence.md docs/design/modular-ash/interfaces-evidence.md docs/tasks/TASK-0014-finish-modular-ash.md
git diff --check
```

Before the production cleanup, the exact architecture test failed with
`retains registry: true, releases at boundary: false`. After the cleanup, the
same command passed one test. Fresh post-change runs passed 4 paired audit
tests; 53 architecture and interface tests; 19 interface-corpus and module-
elaboration tests; and all 298 library tests. Formatting, denied-warning
all-target Clippy, changed-document Markdown lint, and whitespace checks
reported no findings. The three documented maintenance command/result sets
returned the exact 15-file direct path, four equality-specific Core joins, and
stable eight-file interface path recorded above.

Manual review also checks every relative link in this report and confirms that
semantic claims remain grounded in `spec/`.

## Result and remaining boundary

The comparison is complete across admission, typing, diagnostics, Core,
evaluation order, maintenance, resources, ownership, lifetimes, and bounded
simplification. The production reconciliation changes only retention after the
last consumer. It does not change source behavior, diagnostic ownership, Core
shape or validity, evaluation, or observation rendering.

The existing [passive-module evidence](evidence.md) and
[interface evidence](interfaces-evidence.md) retain the broader module and
interface boundaries. Modular Ash closure review, complete verification,
lifecycle cleanup, and tagging remain outside this increment.
