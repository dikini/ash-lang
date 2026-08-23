# Rank-1 Polymorphism Integration Evidence

This report records implementation evidence for Mini-Ash's rank-1 increment.
It does not define Ash semantics. The [normative specification](../../../../spec/README.md)
owns the language after the increment merges.

## Scope

The work starts from `main` at `9e7a5e0` and is isolated on
`feature/rank-1-polymorphism`. The implementation checkpoints are:

- `279da15`, which admits parameterized declarations and saturated type
  applications;
- `423baa3`, which resolves type parameters and implements first-order rank-1
  inference;
- `959533b`, which retains explicit Core type abstractions and applications;
  and
- `8195e6f`, which bounds cumulative type work across the pipeline.

The specification, executable documentation, and closure audit follow those
checkpoints on the same branch. Intermediate commits are unsigned. Integration
still requires review and explicit approval.

## Causal semantic model

Resolution first allocates nominal declarations and their ordered type
parameters. Constructor payloads then resolve in the owning parameter scope.
Free uppercase type names in each global interface receive separate stable
identities in first-occurrence order. This preserves forward nominal visibility
while preventing one declaration's parameters from leaking into another.

Elaboration turns resolved annotation variables into rigid variables and uses
private inference variables for implicit instantiation and eligible local
functions. Structural unification includes an occurs check. Local
generalization admits only a single binder initialized syntactically by an
anonymous function and excludes variables free in the incoming environment.
Application-shaped bindings and local recursive groups remain monomorphic.

Every generalized definition becomes an explicit Core type abstraction. Every
polymorphic global or constructor occurrence becomes an explicit Core type
application. The independent validator rechecks scope, outer scheme shape,
arity, substitution, types, provenance, handles, and reachability. The evaluator
then removes either type operation in one transition. It creates no runtime type
objects and does not change value, heap, or evaluation-order semantics.

## Changed composition points

- The closed lexer token family adds `<` and `>`.
- The closed parser grammar and projection add declaration parameter lists and
  saturated nominal type arguments. Expression grammar remains unchanged.
- Resolution adds declaration-scoped and interface-scoped type identities,
  constructor schemes, applied nominal types, and type-arity and kind
  diagnostics.
- `Type` adds rigid variables, private inference variables, applied nominals,
  and outer universal schemes. Semantic equality still has one owner.
- Elaboration owns instantiation, unification, occurs checking, local
  generalization, zonking, recursive rigidity, and explicit Core type
  operations.
- Pattern checking and coverage substitute the expected applied nominal
  arguments into constructor payloads. The usefulness algorithm itself does
  not change.
- The closed Core computation family adds `TypeAbstraction` and
  `TypeApplication`. Builders, validation, both retained transforms, child
  traversal, and evaluation exhaustively consume them.
- Resolution, elaboration, Core construction, and Core validation charge one
  cumulative type-work policy before retaining proportional type structure.

The stable maintenance search is:

```text
rg -n 'Type::(Variable|Inference|AppliedNominal|Forall)|TypeAbstraction|TypeApplication' src
```

At the implementation checkpoint it finds 152 declarations and consumers. The
count locates the closed sites; it is not an edit count or complexity metric.

## Correctness evidence

| Obligation | Retained evidence |
| --- | --- |
| Parameterized declarations and constructors | `tests/parser.rs`, `tests/polymorphism.rs::parameterized_constructors_are_ordinary_polymorphic_values` |
| Global instantiation | `implicitly_quantified_global_instantiates_at_unrelated_types`, `polymorphic_global_instantiates_freshly_inside_another_global` |
| Conservative local generalization | `anonymous_function_local_bindings_generalize`, `application_shaped_local_bindings_remain_monomorphic`, `function_generalization_excludes_inference_shared_with_the_environment` |
| Constructor patterns and coverage | `constructor_patterns_instantiate_the_expected_nominal_arguments`, `coverage_substitutes_parameterized_constructor_payloads` |
| Occurs check and ambiguity | `infinite_inferred_types_are_rejected_by_the_occurs_check`, `unresolved_local_function_inference_is_a_source_ambiguity` |
| Monomorphic recursion | `inferred_polymorphic_recursion_is_rejected`, `recursive_global_self_uses_apply_the_same_rigid_parameters` |
| Explicit Core facts | `source_instantiation_is_explicit_in_validated_core`, `rejects_constructor_payload_variables_outside_the_owner_parameters`, `rejects_polymorphic_constructor_payloads_in_the_registry`, and malformed type-operation cases in `tests/core_validation.rs` |
| Transform preservation and erasure | `explicit_type_operations_survive_both_core_transforms_and_erasure` |
| Parameterized cyclic data | `parameterized_guarded_recursive_data_keeps_runtime_types_erased` |
| Source-facing output | `static_semantics_rank_one_polymorphism_is_executable` and `tool_rank_one_example_has_exact_cli_observation` |

The existing monomorphic parser, resolution, typing, Core, transform,
evaluation, diagnostics, recursion, data, coverage, resource, and CLI suites
remain in the complete verification boundary. Rank-1 support does not select a
second driver path or evaluator.

The earlier `function-needs-context` fixture now has two explicit outcomes. A
direct anonymous-function initializer is retained as a positive locally
generalized corpus case. A nested block returning an anonymous function remains
rejected, proving that contextual diagnostic propagation does not widen the
syntactic eligibility rule. Existing returned-function tests also prove that
zonking retains inner annotation provenance whenever substitution leaves its
shape unchanged.

## Diagnostics and provenance

Resolution reports distinct stable reasons for duplicate declaration
parameters, unknown types, unsaturated or overapplied nominal constructors, and
application of a kind-`Type` parameter. Elaboration reports ordinary contextual
mismatches plus infinite types, ambiguous unsolved inference, and polymorphic
recursion. Source-facing type rendering consults the registry, so nominal
identities appear as declaration spellings with their structural arguments.

Type abstraction and application nodes retain causal origins. Validator tests
reject foreign type-variable identities, free type variables, nested schemes,
wrong argument counts, wrong substituted result types, and malformed origins as
internal Core failures rather than source-language diagnostics.

## Resource and stack evidence

`TYPE_WORK_LIMIT` is 327,680 cumulative units. Resolution, elaboration, Core
building, and validation charge type cells before proportional retained work.
The limit admits the pre-existing 10,000-member cyclic-data corpus while direct
oversized Core construction and unchecked-Core validation produce structured
resource errors. The latter test does not depend on the source syntax or parser
budget, so it proves malformed-Core error mapping at the target boundary.

Substitution and zonking first charge every cell in the expanded result through
constant-width work stacks and only then rebuild that result. The focused unit
tests reject expanded substitutions and zonks before rebuilding. The direct
`expanded_malformed_type_application_maps_to_validation_resource` case shows
that a compact malformed Core application whose substitution exceeds the
budget maps to `core.validation.resource`.
Core type admission, Core validation, and the adjusted match elaboration
traversal also use explicit work stacks at their admitted depth.
`deep_parameter_substitution_completes_on_a_small_stack` and the retained deep
pattern, recursive-group, heap, rendering, and destruction tests run on a 256
KiB host stack. Type work is cumulative within each stage; repeated
instantiation cannot reset the budget by moving to another expression.

The type budget complements rather than replaces the syntax and coverage
budgets retained by the data-and-pattern increment. A source can therefore stop
before large syntax retention, during coverage specialization, or during type
construction with a boundary-specific internal resource result.

## Transferable findings

- Declaration parameters and implicit value quantification need distinct
  scopes even though both use uppercase source spellings.
- Expected-type checking must reach match arms before local inference; otherwise
  checking-only anonymous functions fail in function-valued branches.
- Keeping inference variables private to elaboration makes the resolved tree a
  stable input and lets Core validation require fully zonked types.
- Explicit Core type operations make transforms and validation inspect the
  static facts that runtime erasure removes.
- Parameterized pattern coverage is a substitution at constructor-head
  expansion, not a second usefulness algorithm.
- Recursive polymorphic functions require their own rigid parameters while
  checking their bodies. Fresh ordinary instantiation is correct only outside
  that recursive self boundary.
- Cumulative accounting must charge traversed type cells, including rejected
  malformed Core, before materializing proportional replacement structure.

The architecture mutation harness in `tests/architecture.rs` was updated with
the two new closed computation cases. Its mock feature still changes only the
recorded payload, validation, and dispatch assembly points. The probe types do
not enter production APIs.

## Downstream pressure and exclusions

Future passive modules can consume immutable resolved and Core registries,
outer schemes, stable nominal identities, and independently validated Core.
They cannot assume that inference variables survive elaboration or that runtime
values carry type arguments. Separate interface checking will need to decide
which scheme identities are exported without reopening Mini-Ash's local
generalization rule by accident.

This increment intentionally excludes higher-rank types, higher-kinded
variables, partial type application, explicit expression type arguments, broad
Hindley–Milner generalization, polymorphic recursion, aliases, records, modules,
interfaces, effects, resources, type classes, overloading, type-level
computation, and runtime type reflection.

## Verification checkpoint

`cargo xtask verify` passes formatting, metadata, build, denied-warning Clippy,
all unit and integration tests, and denied-warning rustdoc. The complete run
includes the 10,000-member cyclic-data case, all small-stack boundaries, direct
Core resource mapping, both transforms, the monomorphic corpus, and 32
executable specification and tool examples.

Markdown lint passes for every changed document with `MD013` disabled because
the repository's artifact metadata, tables, and formal rules intentionally
contain long lines. Manual checks confirm new relative links, artifact
authority, `ebnf` and `sequent` fence syntax with matching prose, closed Core
consumer coverage, ownership release boundaries, and every CP-0004 evidence
item.
