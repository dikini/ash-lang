# Explicit Implementation Import and Re-export Evidence

This report records implementation evidence for the first `lib-ash` increment:
explicit implementation imports and targeted name and implementation
re-exports. It is informative, not normative. The
[Ash specification](../../../spec/README.md) alone defines the current
language. Git history retains the accepted semantic transition, implementation
task, and execution plan; those temporary artifacts no longer occupy the
current tree after the reviewed product checkpoint.

This report's linked reproof and lowering order describes those checkpoints.
Under [AD-0006](../../decisions/AD-0006-front-end-semantic-boundaries.md) and
[AD-0007](../../decisions/AD-0007-typed-core-dialects.md), completed modules
publish their lowering and metadata; imports and linking reuse them and check
new connections. The assembled Core then receives independent validation once.

This report alone did not close the complete `lib-ash` milestone. At the first-
increment checkpoint, the retained
[milestone note](../DN-0025-library-and-package-milestones.md) kept later type,
interface, library, package, and artifact pressure separate. Later integrated
increments close the revised milestone without changing this report's evidence
scope.

## Scope and checkpoints

The implementation work starts from unsigned authorization checkpoint
`4f0541d`. Its principal unsigned checkpoints through the reviewed product
boundary are:

- `850de5a`, which parses the independent targeted name and implementation
  channels and targeted public imports;
- `0f0b74d`, which removes automatic direct-import implementation availability
  and selects implementations explicitly;
- `cd81938`, which publishes selected name spellings without creating facade
  declarations;
- `c099f03`, which publishes transitive implementation authorization routes;
- `b8e7ba4`, which retains and authenticates lightweight linked authorization
  tables before Core synthesis; and
- `768e0ed`, `4a4783e`, `2acc601`, and `534404a`, which close the deep-resource,
  diagnostic, route-retention, and source-relationship evidence; and
- `76e8104`, which reconciles the normative specification, executable examples,
  tool guide, trajectory, design state, and this retained evidence report; and
- `95e17c0`, which retains the independent reviews, exact final gate, review
  corrections, and completed first-increment status.

The implementation, specification, evidence, independent reviews, and final
verification are complete. The current tree contains the product evidence and
omits the transition-only artifacts. These checkpoints are evidence boundaries,
not independent semantic authority.

## Implemented boundary

A targeted import can select names and public implementations independently:

```ash
pub import equality (Equal, equal, impl Equal)
```

The name selectors make their selected spellings available and, with `pub`,
publish those spellings. `impl Equal` makes every public implementation for the
dependency's public `Equal` interface available and, with `pub`, authorizes
dependents to select them. An implementation selector does not bind a source
name. A targeted or complete name import does not select implementations, and a
qualified import remains a name-only module alias.

Public name re-exports preserve the defining binder, nominal, constructor,
interface, and method identities. Public implementation re-exports preserve
the defining `ImplId`, implementation-method identity, method identity, and
defining method binder. A facade adds a route to an existing fact; it does not
copy a declaration, body, or implementation.

## Selector and facade corpus

[`tests/library_imports.rs`](../../../tests/library_imports.rs) retains the
primary matrix. It proves that:

- a name-only import resolves its names but leaves the method occurrence with
  `constraint.unsatisfied`;
- an implementation-only selector supplies evidence without binding the
  interface or method names;
- missing and private interface selectors fail during resolution, and selecting
  a nominal instead of an interface reports `resolve.interface-kind`;
- one public targeted import re-exports global, nominal, constructor,
  interface, method, and implementation channels under the selected spellings;
- a base, facade, and entry module complete the public pipeline through two
  explicit implementation selectors.

Shortest implementation routes win deterministically. The separate rank and
hop-key probes in [`src/resolved.rs`](../../../src/resolved.rs) prove that
equal-length choices follow dependency, import, selector, and stable graph-local
hop ordering without consulting process-global source allocation.

The transitive and diamond cases in
[`tests/interface_modules.rs`](../../../tests/interface_modules.rs) and
[`tests/library_imports.rs`](../../../tests/library_imports.rs) reach one
defining implementation through several paths without changing or duplicating
its identity. Effective local availability and public re-export authorization
choose independent routes, so a private shortest local path cannot displace
the route that a public dependent is authorized to follow.

## Identity, summaries, and retained linked state

A checked module publishes a body-free summary only after resolution and
checking succeed. Selected names enter that summary under facade spellings but
retain defining identities. Selected public implementation facts retain their
complete checked shape and a flat authorization route while the dependent is
being checked. Alternate routes for the same `ImplId` deduplicate before
coherence checking.

Linking drains each summary's public implementation entries into a lightweight
table. Each table entry contains the implementation identity and its flat
authorization route. It does not retain a dependency source body, imported
implementation body, method body, method fact, facade declaration, or complete
export summary. The complete summaries are discarded before the linked program
is exposed.

[`tests/interface_validation.rs`](../../../tests/interface_validation.rs)
proves this boundary for the base, facade, and entry groups. Their public table
routes have zero, one, and two hops respectively. The facade and entry retain
no implementation bodies or complete implementation facts. The exact linked
retention probe in [`src/elaborate.rs`](../../../src/elaborate.rs) generalizes
the result to eight public implementations per layer and checks that every
layer retains the same defining identities.

## Coherence, privacy, opacity, and diagnostics

The effective environment checks the deduplicated union of local and explicitly
selected implementations. Distinct overlapping facts fail at the first module
whose closure combines them. The retained orphan rule and acyclic module graph
make a valid sibling-source overlap fixture unreachable, so
`distinct_reexported_implementations_conflict_at_the_first_combined_closure` in
[`src/elaborate.rs`](../../../src/elaborate.rs) assembles the checked structural
boundary directly. It proves the exact primary route label, both defining
locations, and every earlier and later authorization hop.

Name re-export tests preserve private declarations, opaque constructor
withholding, complete transparent constructor families, hidden nominal and
interface closure, and owner-distinct opaque identities. An alias changes only
the public spelling. It neither changes identity nor creates a facade body.
Unavailable private or transitive implementation data remains absent from
source diagnostics.

[`tests/interface_diagnostics.rs`](../../../tests/interface_diagnostics.rs)
retains exact labels for unavailable selections, selected prerequisite chains,
and concrete cycles. The structural overlap witness cited above owns the
overlap-route labels. A selected facade prerequisite failure
relates the source occurrence and declaration, the name import used by the
occurrence, the interface declarations, every selected implementation route
hop, the implementation declaration, and the supplying method. The CLI witness
in [`tests/module_cli.rs`](../../../tests/module_cli.rs) renders that same
structured diagnostic without reclassification and preserves whether labels
refer to the same or different source files.

## Exact resources and small-stack disposal

All new selector, route, summary, linking, and validation work uses the existing
graph-wide interface-and-constraint budget. The retained exact-limit probes
include:

- `wide_implementation_selector_expansion_has_an_exact_constraint_limit` in
  [`src/resolve.rs`](../../../src/resolve.rs), which expands one selector over
  16 distinct nominal heads, admits the measured exact budget, and rejects one
  unit less at the selector-owned failure;
- `implementation_authorization_prepend_has_an_exact_limit` in
  [`src/resolved.rs`](../../../src/resolved.rs), which charges one new hop plus
  the complete suffix atomically before allocation;
- `linked_public_authorization_move_charges_two_records_plus_every_hop` in the
  same file, which proves the exact extraction formula
  `2 * entries + total_hops` for varying route lengths and leaves the complete
  summary undrained when one unit is missing;
- `link_retains_public_authorization_tables_at_an_exact_limit` in
  [`src/elaborate.rs`](../../../src/elaborate.rs), which admits the measured
  exact linked-table budget and rejects one unit less without retaining facade
  bodies or implementation facts; and
- `deep_authorization_suffix_comparison_has_an_exact_limit` in
  [`src/evidence_validation.rs`](../../../src/evidence_validation.rs), which
  compares a 20,000-hop suffix iteratively at its exact limit.

The public-driver resource witness uses 48 facade layers and four
implementations per layer. `deep_wide_public_routes_admit_and_reject_on_a_small_stack`
in [`src/driver.rs`](../../../src/driver.rs) admits the measured exact budget,
rejects one unit less at linked evidence validation, and disposes both outcomes
on a 256 KiB thread stack. The independent public integration witness in
[`tests/interface_resources.rs`](../../../tests/interface_resources.rs)
admits and drops the same deep, wide shape on a 256 KiB stack.

## Linked authentication and tampering

Linked evidence validation authenticates every local public inventory, then
each dependency-ordered public authorization table, then every module's
effective availability, before it inspects selected occurrences or constructs
Core. Each imported route must start with the exact direct dependency edge and
must match an already authenticated dependency suffix through to the defining
owner.

The mutation probes in
[`src/evidence_validation.rs`](../../../src/evidence_validation.rs) reject:

- a missing exact direct edge or a route that skips its immediate publisher;
- a forged intermediate suffix, first-hop span, or final owner;
- disconnected or repeated route hops;
- a changed available implementation identity; and
- an unused forged public table entry before any occurrence could select it.

Every case fails as `evidence.validation.*` before Core synthesis. These private
crate tests expose no public mutation hook. Integration tests exercise only
source-reachable linked programs.

## Core and runtime boundary

[`tests/interfaces.rs`](../../../tests/interfaces.rs) proves that a facade
selection completes the public pipeline, independently validates the resulting
Core program, and lowers to the original defining implementation-method binder.
The facade contributes no Core group or forwarding body. Type arguments,
evidence, and value arguments remain ordinary type and term applications.

[`tests/architecture.rs`](../../../tests/architecture.rs) scans the closed Core
and evaluator sources and rejects route, authorization, interface-evidence, or
implementation-registry state there. The increment adds no Core node, runtime
dictionary, implementation registry, registration, lookup, dispatch, or
runtime failure. All route identities are discarded after linked validation
authorizes existing Core synthesis.

## Migration

Every positive cross-module fixture that consumes implementation evidence now
uses an explicit `impl Interface` selector. The migration covers unit,
integration, CLI, resource, specification-example, and Modular Ash comparison
fixtures. `name_only_import_does_not_select_implementation` remains as the
negative compatibility witness: importing the interface and method names alone
leaves the implementation unavailable and reports the source-level unsatisfied
constraint.

No compatibility grammar, implicit selector, or second compiler path remains.

## Production and maintenance sites

The implementation increment changes these production sites:

| Boundary | Production owners |
| --- | --- |
| Syntax and projection | `src/parser/grammar.rs`, `src/parser/project.rs`, `src/surface.rs` |
| Selection, identity, summary closure, and route accounting | `src/resolve.rs`, `src/resolved.rs` |
| Linked retention and validation | `src/elaborate.rs`, `src/evidence.rs`, `src/evidence_validation.rs`, `src/driver.rs` |

The transition changes no production Core or evaluator file. Its principal
maintenance targets are
[`tests/library_imports.rs`](../../../tests/library_imports.rs),
[`tests/interface_modules.rs`](../../../tests/interface_modules.rs),
[`tests/interface_validation.rs`](../../../tests/interface_validation.rs),
[`tests/interface_resources.rs`](../../../tests/interface_resources.rs),
[`tests/interface_diagnostics.rs`](../../../tests/interface_diagnostics.rs),
[`tests/module_cli.rs`](../../../tests/module_cli.rs),
[`tests/interfaces.rs`](../../../tests/interfaces.rs), and
[`tests/architecture.rs`](../../../tests/architecture.rs). Parser, migration,
and normative-example coverage also lives in
[`tests/interfaces_syntax.rs`](../../../tests/interfaces_syntax.rs),
[`tests/modules_syntax.rs`](../../../tests/modules_syntax.rs),
[`tests/parser.rs`](../../../tests/parser.rs), and
[`tests/spec_examples.rs`](../../../tests/spec_examples.rs).

## Verification status

The final pre-cleanup gate passes formatting, all-target and all-feature
checking, the complete workspace test suite, clippy with warnings denied, the
test inventory, `cargo xtask verify`, full-tree Markdown lint, and whitespace
checking. The inventory contains 330 library tests, 10 `ash` binary tests, 648
integration tests, and one `xtask` test: 989 tests.

Three independent product reviews cover transition and specification
agreement; parser, resolver, summary, route, validation, resource, and Core
quality; and evidence, migration, links, authority boundaries, and exclusions.
Review corrected the normative distinction between transient route ranks and
the final `ModuleId`-bearing hop key, stale current-dialect wording, and two
evidence-report attributions. The exact corrected state passed repeat review
with no Critical, Important, or Minor findings. Retained Modular Ash reports
remain unchanged, and the transition changes no production Core or evaluator
file.

## Intentional exclusions and remaining pressure

This increment does not add higher kinds, kind inference, method-local type
parameters, multi-parameter interfaces, determinations, associated outputs,
defaults, named implementation selectors, head-pattern selectors,
specialization, wildcard or qualified-module re-exports, or module signatures.
It does not add packages, manifests, caches, persistent summaries or artifacts,
separate compilation or linking, runtime implementation lookup, or new Core and
evaluator forms.

Later `lib-ash` increments consumed the effective/public closure distinction,
stable identities, body-free summaries, and authenticated route model under
separate semantic authority and evidence. At this checkpoint, the complete
milestone still required its later comparison corpus, combined identity and
summary audit, Core-versus-library simplification analysis, retained linked
program, and closure review. The later integrated relational increment supplies
those closure facts. The retained first-increment checkpoint received no
`lib-ash` tag. Git retains the removed transition artifacts and their history.
