# Modular Ash Closure Report

This report records the final Modular Ash implementation and simplification
checkpoint described by
[DN-0020](../DN-0020-ash-dialect-milestones.md) and
[DN-0025](../DN-0025-library-and-package-milestones.md). It is informative and
does not define the language. The
[specification](../../../spec/README.md) remains authoritative.

## Retained dialect

Current Ash is one pure, rank-1 Modular Ash dialect. It contains:

- passive acyclic source modules with public and private declarations, opaque
  and transparent exports, qualified imports, and targeted direct imports;
- one stable compilation-local identity for each canonical module source,
  independent of aliases, roots, and alternate routes;
- dependency-ordered checking against immutable body-free summaries, so a
  dependent does not retain or recheck its dependency's body;
- one local, monomorphic, unconstrained entry `main : Unit -> R`, where `R` is
  closed;
- method-only interfaces with one type parameter, anonymous `impl`, explicit
  constraints and prerequisites, and implementation availability through the
  defining module or an authenticated direct dependency;
- checked structural evidence that survives occurrence checking, is
  authenticated once after linking, and erases during Core synthesis; and
- one linked pure Core program containing every dependency-ordered definition
  group around the generated call `main ()`.

The [current specification](../../../spec/README.md#current-ash) owns these
facts. This report records why the implementation retains their boundaries; it
does not add features to that inventory.

## Stage boundaries

| Boundary | Facts retained by the next stage | Facts released |
| --- | --- | --- |
| Loading to resolution | canonical module and source identities, acyclic dependency order, projected source modules, owning roots, and import provenance | filesystem traversal state, inactive pending work, and unused path spellings |
| Resolution to checking | stable declaration and evidence identities, resolved bodies and schemes, direct-dependency routes, defining registries, and body-free imported facts | aliases as identity, unavailable private names, and mutable namespace search state |
| Checking to summaries and linking | closed public schemes, public and hidden summary closure, complete checked definition groups, structural evidence, module ownership, and dependency order | dependency bodies from dependent checking, private dependency scopes, selection search state, and inference substitutions after obligation closure |
| Linking to evidence validation | exact entry closure, group ownership, combined registries, retained selections, availability routes, types, and provenance | module-local assembly state and already-authenticated import syntax |
| Evidence validation to Core synthesis | authenticated checked definitions and one capability to synthesize their selected evidence | the validator-local linked-interface registry and its indexes |
| Core synthesis to Core validation | ordinary typed Core, combined nominal and constructor registry, source provenance, and the registry used to display the result type | checked bodies, structural evidence, implementation routes, and remaining interface metadata after the explicit post-synthesis wrapper drop |
| Core validation to evaluation | one authenticated pure Core program | validator indexes and remaining static module and evidence policy |
| Evaluation to observation | result value, closed result type, and completed shared heap | control, continuations, and transient environments not reachable from the result |

`ResolvedModuleProgram.entry` and each definition group's module identity remain
live through linked evidence validation. They authenticate the exact entry
closure, group ownership, binders, declarations, and implementation routes;
their earlier passive-module status as unread fields is historical rather than
a current cleanup opportunity.

## Simplification audit

### Constructs and lowering

Module structure lowers to dependency-ordered ordinary recursive groups around
the generated application of the entry binder to unit. Imports, paths, aliases,
summaries, visibility, and opacity leave no Core or runtime module node.

Interface evidence lowers only after linked validation authenticates the
selected goal, route, identity, substitution, prerequisite tree, method order,
scope, type, and provenance. Requirements become ordinary function parameters;
constrained occurrences become ordinary type and function applications; and
implementation methods become hidden ordinary globals in their defining
module's recursive group. Interface, implementation, method, and requirement
identities then erase. There is no interface Core family, dictionary value,
runtime registry, lookup, or dispatch rule.

The resulting program uses the retained pure Core value and computation
families and the existing evaluator. Modules and interfaces therefore extend
the authenticated source-to-Core path without extending the runtime inventory.

### Core versus library

The paired [core-and-library audit](core-library-evidence.md) retains direct
integer `==` and Core `Primitive::Equal`. It also demonstrates an explicit
source-library capability declared as `Equal<A>` with `Equal<Int>` and a
constrained `same` function. The source library method ultimately uses the
same retained integer primitive; it does not replace the operator.

The two paths remain deliberately distinct. The operator is admitted without
an import, checks only `Int` operands, reports primitive-operand diagnostics,
and lowers directly to `Primitive::Equal`. The explicit capability requires a
module and implementation route, selects and authenticates interface evidence,
reports constraint diagnostics when no implementation is available, and
lowers to ordinary type, evidence, and value applications before it reaches
the method body's primitive. Their successful results agree, but their Core
shape and evaluation traces do not. Ash ships no prelude, package, or reusable
equality module at this checkpoint.

### Budgets and resources

- One syntax-work budget spans every admitted source. Module loading separately
  bounds sources, edges, path segments, retained owner facts, and active pending
  work before retaining proportional graph state.
- Resolution and checking use graph-wide type and coverage budgets. One
  interface-and-constraint budget spans summary admission, module checking,
  linking, and linked evidence validation rather than resetting per module.
- Core construction and independent Core validation retain separate cumulative
  bounds for the complete linked program. Evaluation, observation, and
  destruction use explicit work stacks at admitted deep boundaries.
- Syntax work is bounded at 1,500,000 units; type and interface-constraint work
  are each bounded at 327,680 units. Coverage separately bounds work and
  memoized states. Core payload and pattern depth remain explicit admission
  limits.

Resource exhaustion is a structured internal result. It does not substitute
for module admission, typing, constraint selection, coverage, or Core-validity
judgments.

### Ownership, lifetimes, and identity

Canonical source, module, declaration, Core arena, and heap identity domains
remain distinct. Alternate import routes do not create semantic duplicates.
Core handles, binder identities, and heap locations are numeric identities
rather than Rust ownership edges, so recursive Core scope and cyclic data do
not create host ownership cycles.

Linked evidence validation builds its interface registry locally and does not
retain it in `ValidatedInterfaceProgram`. Core synthesis borrows that validated
wrapper. After synthesis finish succeeds, the driver explicitly drops the
wrapper before independent Core validation, releasing checked bodies,
structural evidence, routes, and remaining interface facts after their last
consumer.

An observed structural or cyclic data value owns the heap needed to render its
locations. The public observation separately keeps the completed evaluation
heap because a returned closure can capture an environment containing raw heap
locations. Removing that heap would make an admitted returned closure's
captured data invalid even though ordinary data observations already retain
their own heap.

### Maintenance and locality

The module path is concentrated in loading, resolution, checking, summaries,
the graph driver, and linked synthesis. Interface-specific semantic machinery
is concentrated in eight production files: the driver, elaborator, evidence
selection and audit, evidence validation, interface model, resolver, and
resolved data. The direct equality path crosses 15 production files, while its
equality-specific Core joins remain the primitive definition, transformation,
elaboration, and evaluator.

The closure audit removed actual stale retention rather than adding a parallel
representation. `ValidatedInterfaceProgram` no longer stores the linked
validator registry, and the driver now performs an explicit post-synthesis
drop. It retained the entry identity, group module identities, and observation
heap after proving their interface-era or closure-observation readers. Earlier
released alternatives remain absent: a Mini-Ash compiler path, source
dictionaries, span-keyed evidence maps, lowering-time reselection, summary
bodies and private scopes, route-specific implementation identities, runtime
registries, and module or interface Core nodes.

The architecture guard checks the single current Modular source pipeline, the
post-synthesis interface-state lifetime, and the closed Core and evaluator
inventories. These are maintenance witnesses, not language authority.

## Retained evidence

- [Passive-module evidence](evidence.md) records canonical module identity,
  body-free summaries, visibility and opacity, graph-wide resources, linked
  Core construction, and historical Mini-Ash comparison.
- [Interface and implementation evidence](interfaces-evidence.md) records
  method-only checking, direct availability, authenticated structural evidence,
  ordinary Core lowering, diagnostics, resources, and the bounded
  unspecialized evaluation trace.
- [Core and library equality evidence](core-library-evidence.md) records the
  paired admission, typing, diagnostic, Core, evaluation, maintenance, and
  lifetime comparison.
- The [Mini-Ash closure report](../mini-ash/closure.md) retains the predecessor
  dialect without requiring a second current compiler path.

Together these reports retain the implementation evidence for this final
checkpoint. The specification remains the source of current language truth.

## Verification checkpoint

A fresh pre-cleanup `cargo xtask verify` passed at this closure checkpoint. It
ran formatting, locked metadata and build checks, denied-warning Clippy, every
workspace unit and integration test, and denied-warning rustdoc. The exact test
inventory was 298 library tests, 10 `ash` binary tests, 625 integration tests,
and one `xtask` test: 934 tests with no failures.

The focused architecture target passed all eight tests. The stable equality
maintenance search returned the recorded 15 production files; the interface
maintenance search returned the recorded eight production files; and the
interface-identifier search over `src/core` and `src/eval` returned no matches.
Markdown lint, relative-link review, authority review, and `git diff --check`
complete this documentation checkpoint. The final lifecycle increment will
repeat root verification and independent reviews after removing the completed
task and temporary execution plan.

## Intentional exclusions and later pressure

This checkpoint does not contain any `lib-ash` or `pack-ash` mechanism. It adds
no higher-kinded or multi-parameter interfaces, associated outputs,
determination rules, method-local type parameters, method defaults,
implementation imports or re-exports, name re-exports, package manifests,
exact dependency resolution, caches, compiled-module or distributable artifact
formats, or a separate object linker.

It also excludes module signatures; dynamic providers, loading, registration,
or runtime lookup; parent traversal, module cycles, and cross-module recursive
groups; an operator rewrite or implicit prelude; specialization and dead-code
elimination; effects and handlers; and a selectable current-tree Mini-Ash
compiler path. Associated types and specialization remain later design
pressure, not unresolved Modular Ash semantics.

The final annotated unsigned `modular-ash` tag will retain this final dialect
checkpoint after lifecycle cleanup and repeated verification. Creating that
marker is task mechanics; it does not supply missing language semantics or
change the final state recorded here.
