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

## Verification retained by this increment

The target was first run while absent. Cargo rejected the command with
`no test target named modular_closure`, which establishes the pre-edit baseline.
After the target was added, its four tests passed.

The increment retains these verification commands:

```text
cargo fmt --check
cargo test --locked --test modular_closure
cargo test --locked --test architecture --test interfaces --test interface_modules --test interface_validation
markdownlint --disable MD013 -- docs/design/modular-ash/core-library-evidence.md
git diff --check
```

All five commands exited `0` for this increment. The focused target passed four
tests. The architecture and interface command passed 51 tests: 6 architecture,
24 interface, 20 interface-module, and 1 interface-validation test. Formatting,
Markdown lint, and whitespace checks reported no findings.

Manual review also checks every relative link in this report and confirms that
semantic claims remain grounded in `spec/`.

## Current conclusion and deferred work

The paired witness required no production Rust change and no semantic change.
Current equality admission, diagnostic ownership, Core validation and shape,
and evaluation already support the audit.

This initial report does not conclude the full maintenance-site, resource,
ownership, or simplification comparison. The next authorized increment will
measure those questions against this retained witness and the existing
[passive-module evidence](evidence.md) and
[interface evidence](interfaces-evidence.md). It may remove only state proven
unused or stale without changing the facts recorded here.
