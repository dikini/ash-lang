# Data and Pattern Integration Evidence

This report records implementation evidence for accepted CP-0003 and compares
it with the informative findings in [DN-0007](../../DN-0007-data-and-pattern-typing.md)
and [DN-0019](../../DN-0019-primitive-feature-composition.md). It does not
define Ash semantics. The normative specification owns the merged language.

## Scope and environment

The measurement covers `4d5ce64...ac840eb` in the
`feature/data-and-adts` worktree. Commit `8c1c6af` is the first checkpoint with
the candidate parallel pipeline removed. Commit `ac840eb` adds the final
strict-order and transform evidence, converts usefulness to an explicit
memoized work stack, and closes project lint findings.

| Property | Observation |
| --- | --- |
| Baseline | recursive-definition merge `4d5ce64` |
| Retained-pipeline checkpoint | unsigned commit `ac840eb` |
| Rust | `rustc 1.97.1 (8bab26f4f 2026-07-14)` |
| Cargo | `cargo 1.97.1 (c980f4866 2026-06-30)` |
| Host | Linux `x86_64` |

At the evidence checkpoint, the production diff under `src/` contains 4,927
added and 615 deleted lines in 23 files. These counts exclude integration tests
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
- `Observation` and `Value` add one heap-backed result boundary. Scalar and
  closure observations retain their representations.

The exact audit below found 176 occurrences in 17 production files at the
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

The explicit heap avoided Rust ownership cycles. Recursive data names denote
numeric slots; constructor cells and tuple cells contain numeric locations.
The 10,000-member cyclic group evaluates, renders, and drops on a 256 KiB host
stack. Iterative matching and rendering, rather than recursive Rust ownership,
make that boundary possible.

## What necessarily crossed stages

Nominal identity must survive resolution, type equality, constructor typing,
coverage, validation, evaluation, and source-facing type display. Tuple shape
likewise crosses parsing, typing, constructor payload metadata, pattern
checking, application, matching, and rendering. These are semantic facts, not
registration data.

Constructor-guarded recursion changes group initialization. Function templates
alone cannot represent it: all member slots must exist before initialization,
data initializers must run in source order, and completed slots alias their
constructed roots. Observation must retain the evaluation heap because a
cyclic value cannot be copied into an acyclic host enum.

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
| Grammar, recovery, token coverage, spans, and projection refusal | `data_and_pattern_forms_build_one_token_complete_concrete_tree`, `data_and_pattern_recovery_stays_balanced_and_synchronizes_at_the_arm_line`, `projects_data_declarations_tuples_matches_and_pattern_vectors`, and `retained_data_syntax_failures_keep_the_exact_current_token_span` |
| File-wide identities, namespaces, recursive references, pattern scope, shadowing, and restoration | `data_and_pattern_resolution_allocates_file_wide_identities_and_pattern_binders`, `data_namespaces_report_stable_resolution_reasons`, `match_arm_pattern_scope_does_not_leak_to_later_arms`, `nominal_declarations_are_file_wide_recursive_and_distinct`, and `failed_nested_and_recursive_resolution_restore_the_scope_stack` |
| Nominal and tuple typing, constructor values, function domains, pattern typing, coverage, irrefutability, clause arity, and guarded recursion | `nominal_identity_and_tuple_structure_share_one_type_equality_rule` and the typing and coverage cases in `data_and_adts` |
| Registry, identity, constructor, pattern, scope, coverage, provenance, handle, reachability, and ownership-cycle validation | `rejects_malformed_data_registries_and_constructor_annotations`, `rejects_missing_and_redundant_structured_match_arms`, and the existing malformed-Core cases in `core_validation` |
| Strict order, capture, mixed groups, finite and cyclic data, rendering, runtime failures, explicit stacks, and destruction | `constructor_tuple_payloads_enter_elements_strictly_left_to_right`, `mixed_recursive_groups_support_functions_and_guarded_data`, `rendering_repeats_shared_values_and_marks_only_active_cycles`, `defensive_transition_failures_remain_structured`, and `ten_thousand_member_cycle_evaluates_renders_and_drops_on_a_small_stack` |
| Transform validation and differential evaluation | `shared_pipeline_elaborates_and_validates_finite_data_core`, which independently validates and evaluates identity and literal-folding results, plus the existing transform suite in `semantics` |
| Executable specification, tool behavior, diagnostics, and provenance | the CP-0003 cases in `spec_examples`, `diagnostics`, and `provenance` |

The parser rejection corpus covers integer, record, guarded, or-pattern, and
other excluded pattern syntax. The type grammar and registry tests admit no
parameters, aliases, records, modules, empty declarations, or unary tuples.
Core retains structured matches rather than pattern-compilation or decision
forms. The heap is private to one evaluation and exposes neither mutation nor
stable source-level identity.

## External notation tooling

The repository continues to use readable `ebnf` and `sequent` fences with
matching prose. The previously recorded lack of an external railroad or
sequent renderer remains outside this repository. This increment adds no
renderer dependency or conformance claim.
