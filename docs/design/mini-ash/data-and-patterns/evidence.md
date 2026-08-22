# Data and Pattern Integration Evidence

This report records implementation evidence for accepted CP-0003 and compares
it with the informative findings in [DN-0007](../../DN-0007-data-and-pattern-typing.md)
and [DN-0019](../../DN-0019-primitive-feature-composition.md). It does not
define Ash semantics. The normative specification owns the merged language.

## Scope and environment

The measurement covers `4d5ce64...a141d5c` in the
`feature/data-and-adts` worktree. Commit `8c1c6af` is the first checkpoint with
the candidate parallel pipeline removed. Commit `79af325` closes the review
findings around admitted depth, registry authentication and destruction,
coverage resources, transition ownership, trace behavior, and diagnostics;
commit `ca3ae75` records the clean lint checkpoint for that remediation.
Commit `77ca07b` charges nested pattern shaping against the cumulative coverage
budget and gives source-facing type errors registry-resolved nominal spellings.
Commit `46df1aa` propagates a surrounding expected type to every match arm;
commit `b157e14` aligns the normative pattern rules, recursive initialization
steps, and representative value-binding derivations with retained behavior.
Commit `d349b0c` retains the data binder-to-location map across recursive slot
allocation. Commit `a141d5c` directly exercises contextual diagnostic causes
and the source-ordered initializer-entry and alias-storage transitions.

| Property | Observation |
| --- | --- |
| Baseline | recursive-definition merge `4d5ce64` |
| Retained-pipeline checkpoint | unsigned commit `a141d5c` |
| Rust | `rustc 1.97.1 (8bab26f4f 2026-07-14)` |
| Cargo | `cargo 1.97.1 (c980f4866 2026-06-30)` |
| Host | Linux `x86_64` |

At the evidence checkpoint, the production diff under `src/` contains 6,068
added and 662 deleted lines in 23 files. These counts exclude integration tests
and do not measure semantic difficulty.

## Changed composition points

- The lexer adds uppercase identifiers, `_`, `type`, `match`, `|`, and `=>`.
  The token spelling table is the closed parser-facing join.
- The retained parser adds declaration, tuple, pattern, and match grammar at
  its closed assembly points. CST projection verifies each new node and emits
  ordinary Surface forms.
- Resolution performs file-wide identity allocation before resolving payload
  types, then resolves constructor occurrences, patterns, and binder scopes
  into one registry-bearing program.
- `Type` adds nominal and tuple variants. Type admission, provenance traversal,
  display, registry validation, and coverage are the exhaustive consumers.
- The retained elaborator, Core arena, independent validator, transforms, and
  evaluator machine add tuples, constructors, typed patterns, structured
  matches, and guarded recursive data without a driver-level syntax switch.
- `Evaluation` freezes and retains one completed heap. `Observation` takes the
  same shared heap, and a structural `Value::Data` shares it with its root.
  Scalar and closure results remain ordinary visible values while their result
  owner retains any locations reachable through a captured environment.

The exact audit below found 234 occurrences in production files at the
checkpoint. It locates declarations and consumers; it is not an edit count.

```text
rg -n \
  'TokenKind::(Type|Match|UpperIdentifier|Wildcard|Pipe|FatArrow)|'\
'Type::(Tuple|Nominal)|CorePattern|HeapCell' src
```

## What localized

Two-pass type and constructor allocation, expected-type pattern checking, the
shared usefulness relation, guarded-root analysis, heap cells, alias handling,
and active-path rendering have one implementation owner. Match arms,
equational clauses, and local irrefutability all call the same usefulness
function. Constructor expressions use ordinary unary application after one
registry lookup determines their type.

Match synthesis and checking remain two paths through the same elaboration
owner. Synthesis lets the first arm determine the result type. Checking carries
the surrounding expected type and its diagnostic cause to every arm, including
the first, so checking-only forms do not require a second match representation.

The explicit heap avoided Rust ownership cycles. Recursive data names denote
numeric slots; constructor cells and tuple cells contain numeric locations.
The 10,000-member cyclic group evaluates, renders, and drops on a 256 KiB host
stack. Iterative matching and rendering, rather than recursive Rust ownership,
make that boundary possible.

Review hardening aligned parser admission with every downstream pattern and
type wrapper. Full-pipeline tests exercise the admitted constructor-pattern,
nested-match, multi-pattern equation, tuple-domain header, and synthesized
type-wrapper boundaries on a 256 KiB stack. Unchecked Core patterns and
registry payloads have independent limits and stack-safe rejection paths.

Coverage uses both a memoized-state limit and one cumulative work budget shared
by all usefulness queries in a case group. A 512-constructor exhaustive match
is the retained practical-width regression; an 800-constructor group reaches
the default budget and reports compiler resource exhaustion rather than a
source-level coverage result. Pattern shaping charges each visited tuple and
constructor cell before scheduling its children, so repeated conversion of
earlier wide rows cannot run outside that budget. A direct 100-arm by 200-field
tuple reproduction reached the resource failure at the one-million-work limit
in 20.11 seconds with 77,924 KiB maximum resident memory on the environment
above. Registry lookup indexes keep identity lookup independent of declaration
width.

## What necessarily crossed stages

Nominal identity must survive resolution, type equality, constructor typing,
coverage, validation, evaluation, and source-facing type display. Tuple shape
likewise crosses parsing, typing, constructor payload metadata, pattern
checking, application, matching, and rendering. These are semantic facts, not
registration data.

The registry now owns source-facing type rendering. It resolves nominal
identities to declaration spellings while formatting tuples and arrows with an
explicit work stack. Structured argument, binding, definition-result, pattern,
operator, and application diagnostics use that rendering. General mismatch
values retain their identity-bearing `Type` members while their textual view
uses the same source spelling. `Type`'s registry-free display remains the
internal identity view.

The normative static account now exposes the same bidirectional boundary:
separate match synthesis and checking rules share pattern usefulness and
exhaustiveness, while function and local-binding rules extend their bodies with
all bindings returned by one typed irrefutable pattern. The dynamic account
enters each guarded data initializer under an explicit continuation and stores
its returned constructor location in a separate one-step transition. Derived
integer and closure examples bind values directly and introduce no heap
allocation beyond the location-bearing data forms.

Constructor-guarded recursion changes group initialization. Function templates
alone cannot represent it: all member slots must exist before initialization,
data initializers must run in source order, and completed slots alias their
constructed roots. Observation must retain the evaluation heap because a
cyclic value cannot be copied into an acyclic host enum. The retained
`returned_closure_retains_the_heap_for_captured_structural_values` and
`returned_closure_observation_retains_its_captured_structural_heap` regressions
also prove that a closure result cannot discard a heap referenced from its
captured environment.

## Maintenance mutations

Three deliberate uncommitted mutations tested discoverability in the first
candidate implementation. Each was reverted with a targeted patch. The
private file named below no longer exists; the results remain evidence about
the transferred registry and heap design, not about the retained composition
boundary.

### Constructor registry accessor

Renaming the candidate `Registry::constructor` produced four unique
missing-method errors: name lookup, payload coverage, witness display, and
value rendering. Rust exposed all candidate consumers in one check. In the
retained implementation, registry lookups now cross elaboration, usefulness,
Core validation, evaluation, and observation rendering; those crossings are
named directly in the changed-composition audit instead of treated as a
feature-private boundary.

### Observed heap contract

Adding one required field to `ObservedHeap` produced one missing-field error at
the sole heap-freezing boundary. This confirms that evaluation-to-observation
ownership has one constructor.

### Type family

Adding a temporary `Type::Probe` variant produced six unique non-exhaustive
match errors in four files: Core payload admission, elaboration provenance,
the shared type display/equality owner, and three data-pipeline consumers. The
compiler located the closed semantic joins without a search. The wildcard in
the equality decision remained an intentional review point because a new type
must not compare equal accidentally.

After reverting all probes, `cargo check --all-targets` passed. The later
shared-pipeline remediation removed the candidate parser, Core wrapper,
recursive evaluator, source-text routing, and their public API variants.

## Transfer from earlier evidence

DN-0007's central split transferred: tuples are structural, nominal sums use
declaration identity, constructors are ordinary values, patterns check against
expected types, local bindings require irrefutability, and matches and equations
share coverage. Records, polymorphic constructors, and access control did not
transfer because CP-0003 excludes them.

DN-0019's simplification rule also transferred. Ordinary application carries
payload constructors and higher-order construction. One typed pattern and
coverage representation serves three surface contexts. The new facts that
could not lower away—nominal registries, structured patterns, and heap
locations—remain explicit at validation and observation boundaries.

The recursive-definition evidence correctly predicted the runtime difference:
allocate-all-then-check scope transferred, while cyclic constructor data needed
preallocation and initialization rather than function templates alone.

## Requirement audit

The retained tests assign each CP-0003 evidence family to a named owner. This
table records the primary owners; the complete suites also retain the earlier
first-stratum invariants.

| Evidence family | Primary retained tests |
| --- | --- |
| Grammar, recovery, token coverage, spans, projection refusal, and admitted depth | `data_and_pattern_forms_build_one_token_complete_concrete_tree`, `data_and_pattern_recovery_stays_balanced_and_synchronizes_at_the_arm_line`, `projects_data_declarations_tuples_matches_and_pattern_vectors`, `structural_depth_budget_bounds_nested_constructor_patterns`, `structural_depth_budget_bounds_nested_matches`, `admitted_nested_patterns_complete_the_full_pipeline_on_a_small_stack`, and `admitted_type_depth_survives_synthesized_tuple_and_function_wrappers` |
| File-wide identities, namespaces, recursive references, pattern scope, shadowing, and restoration | `data_and_pattern_resolution_allocates_file_wide_identities_and_pattern_binders`, `data_namespaces_report_stable_resolution_reasons`, `match_arm_pattern_scope_does_not_leak_to_later_arms`, `nominal_declarations_are_file_wide_recursive_and_distinct`, and `failed_nested_and_recursive_resolution_restore_the_scope_stack` |
| Nominal and tuple typing, constructor values, function domains, pattern typing, coverage, irrefutability, clause arity, guarded recursion, contextual matches, and bounded usefulness | `nominal_identity_and_tuple_structure_share_one_type_equality_rule`, `contextually_typed_matches_check_every_anonymous_function_arm`, `a_wide_constructor_set_has_practical_exhaustive_coverage`, `an_over_budget_case_group_reports_an_internal_resource_failure`, `usefulness_charges_every_pattern_cell_while_shaping`, and the typing and coverage cases in `data_and_adts` |
| Registry, identity, source order, constructor, pattern, scope, coverage, provenance, handle, reachability, resource, ownership-cycle, and safe-destruction validation | `rejects_malformed_data_registries_and_constructor_annotations`, `rejects_registry_identity_order_spelling_and_source_forgery`, `rejects_and_destroys_overdeep_registry_payloads_on_a_small_stack`, `rejects_missing_and_redundant_structured_match_arms`, `validates_a_deep_guarded_initializer_on_a_small_stack`, and the existing malformed-Core cases in `core_validation` |
| Strict order, capture, mixed groups, finite and cyclic data, rendering, result-heap ownership, transition ownership, match selection, runtime failures, explicit stacks, and destruction | `constructor_tuple_payloads_enter_elements_strictly_left_to_right`, `returned_closure_retains_the_heap_for_captured_structural_values`, `returned_closure_observation_retains_its_captured_structural_heap`, `match_trace_enters_the_scrutinee_once_and_only_the_selected_body`, `recursive_data_initializers_store_each_slot_before_entering_the_next`, `every_core_feature_has_one_named_entry_owner_and_explicit_return_owners`, `mixed_recursive_groups_support_functions_and_guarded_data`, `rendering_repeats_shared_values_and_marks_only_active_cycles`, `defensive_transition_failures_remain_structured`, and `ten_thousand_member_cycle_evaluates_renders_and_drops_on_a_small_stack` |
| Transform validation and differential evaluation | `shared_pipeline_elaborates_and_validates_finite_data_core`, which independently validates and evaluates identity and literal-folding results, plus the existing transform suite in `semantics` |
| Executable specification, tool behavior, structured diagnostics, and provenance | the CP-0003 cases in `spec_examples`, including `static_semantics_contextual_match_checks_function_arms`, `static_semantics_operational_tuple_pattern_is_executable`, `checked_match_arms_retain_the_definition_result_cause`, `data_resolution_diagnostics_retain_names_and_binder_sites`, `coverage_diagnostics_retain_arm_spans_and_concrete_witnesses`, `nominal_mismatches_render_source_declaration_spellings`, `unguarded_recursive_use_retains_the_transporting_expression_span`, and `provenance` |

The parser rejection corpus covers integer, record, guarded, or-pattern, and
other excluded pattern syntax. The type grammar and registry tests admit no
parameters, aliases, records, modules, empty declarations, or unary tuples.
Core retains structured matches rather than pattern-compilation or decision
forms. The heap is private to one evaluation and exposes neither mutation nor
stable source-level identity.

Fresh post-review runs of `cargo test --all-targets` and `cargo xtask verify`
pass at the retained checkpoint. The latter includes formatting, build,
warning-free Clippy, all targets, and rustdoc. Changed Markdown passes with the
project-approved line-length and repeated-heading exceptions; changed relative
links and anchors resolve.

## External notation tooling

The repository continues to use readable `ebnf` and `sequent` fences with
matching prose. The previously recorded lack of an external railroad or
sequent renderer remains outside this repository. This increment adds no
renderer dependency or conformance claim.
