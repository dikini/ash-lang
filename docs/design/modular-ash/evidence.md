# Passive Static Modules Integration Evidence

This report records implementation and comparison evidence for Modular Ash's
passive-static-module increment. It does not define Ash semantics. The
[normative specification](../../../spec/README.md) owns the current language.
The retained [module design note](../DN-0022-passive-static-modules.md) and
[dialect-milestone note](../DN-0020-ash-dialect-milestones.md) explain the
design pressure and future direction.

## Scope and environment

The historical comparison baseline is the peeled `mini-ash` tag at
`d62d3baeb2ae56dcac28fb5dbc3f9810ba5ec436`. The implemented and specified
Modular Ash comparison checkpoint is unsigned commit `3b66040`. The principal
retained checkpoints between them are:

- `0bc17bd`, which replaces the file-result root with module syntax;
- `a9f923d`, which loads canonical acyclic module graphs;
- `d00fd10`, which introduces module-qualified identity and export-boundary
  resolution;
- `be610c8`, which enforces private, opaque, transparent, and hidden-type
  access during checking;
- `8b9e19f`, which links dependency-ordered groups into pure Core;
- `1906c6a`, which enforces the entry contract and evaluates generated
  `main ()`;
- `270adb6`, which migrates the retained corpus to declarations-only modules;
- `b2e69bf`, which closes diagnostics and graph-wide resource evidence; and
- `3b66040`, which replaces the normative specification and tool guide.

The measurements used:

| Property | Observation |
| --- | --- |
| Historical tag commit | `d62d3baeb2ae56dcac28fb5dbc3f9810ba5ec436` |
| Modular comparison checkpoint | `3b66040009b056ac577f3ad548297f78cf01c9a8` |
| Rust | `rustc 1.97.1 (8bab26f4f 2026-07-14)` |
| Cargo | `cargo 1.97.1 (c980f4866 2026-06-30)` |
| Host | Linux `x86_64` |

Intermediate commit signatures are mixed. The work remains isolated on
`feature/modular-ash`; this report does not record a merge.

## Causal semantic model

The loader starts from one entry source and configured named roots. It resolves
relative and absolute imports, canonicalizes every admitted source, assigns one
compilation-local `ModuleId` to that source, and retains all roots that own it.
Every relative descendant must remain within every retained owner. The loader
admits one canonical source once, rejects cycles, and orders every dependency
before its dependents.

Resolution allocates term, nominal, constructor, and type-variable identities
under the defining module identity. Complete imports bind public namespaces
under an alias. Targeted imports bind selected public identities without
changing them. Private declarations do not enter an importer scope. A public
opaque nominal exports its name but not constructors. A public transparent
nominal exports its complete constructor family. A private nominal identity may
occur in public schemes without acquiring an exported source name.

Each dependency publishes an immutable body-free export summary only after its
complete body checks. A dependent resolves and checks from that summary rather
than the dependency's private scope or body. Imported rank-1 schemes instantiate
without re-inference or re-generalization. Hidden identities remain equal
wherever compatible public schemes carry the same module-qualified identity.

After all modules check, linking combines their defining registries and lowers
each nonempty module's globals to one existing Core recursive group. Dependency
groups surround dependent groups. The innermost body applies the entry module's
local monomorphic `main : Unit -> R` to unit, where `R` is closed. Independent
validation authenticates the whole linked program and its module-to-source
provenance relation before the existing evaluator runs it. Paths, imports,
aliases, summaries, visibility, and opacity have no Core node or runtime value.

## Historical milestone comparison

The historical compiler was built outside the current source tree in a
temporary detached worktree:

```text
git worktree add --detach <temporary-path> mini-ash
git -C <temporary-path> rev-parse HEAD
cargo xtask verify
```

The resolved commit was
`d62d3baeb2ae56dcac28fb5dbc3f9810ba5ec436`. Its documented `cargo xtask
verify` boundary ran formatting, locked metadata and build checks, denied-warning
Clippy, every unit and integration test, and denied-warning rustdoc. The command
exited `0`: 514 tests passed across 22 binaries with zero failures, ignores,
measured cases, or filters. The detached worktree remained clean.

Six cases compare behavior intentionally unchanged by modules. Each Mini-Ash
source uses its file result. Its Modular Ash counterpart retains the same
declarations and expression under a local `main`. Every direct executable run
exited `0`, wrote the displayed line to standard output, and wrote nothing to
standard error.

| Case | Historical source | Modular source | Exact output in both |
| --- | --- | --- | --- |
| Integer precedence | `tests/fixtures/first-stratum/valid/v001-precedence.ash` at the tag | current fixture of the same name | `7 : Int\n` |
| Function application | tagged `v002-operational.ash` | current `v002-operational.ash` with local `main` | `42 : Int\n` |
| Global recursion | tagged `recursion/valid/global-mutual.ash` | current fixture with local `main` | `42 : Int\n` |
| Nominal data and higher-order construction | tagged `HIGHER_ORDER_CONSTRUCTOR` executable-documentation source | current `HIGHER_ORDER_CONSTRUCTOR_MODULE` source | `42 : Int\n` |
| Transparent tree patterns | tagged `TREE_PRESENTATIONS` executable-documentation source | current `TREE_PRESENTATIONS_MODULE` source | `4 : Int\n` |
| Rank-1 instantiation and local generalization | tagged `RANK_ONE_POLYMORPHISM` executable-documentation source | current `RANK_ONE_POLYMORPHISM_MODULE` source | `(Some(42), false) : (Option<Int>, Bool)\n` |

The three historical generated sources were byte-for-byte copies of constants
retained in the tagged `tests/spec_examples.rs`. Their SHA-256 values were
`8d93f2660f39349d60ece25a3023d1f65dd597e9af89e477e01a772ad5a9be7a`,
`53bb1d834344d1ec6b54066cfef7ba6777a8e622205f388062010c4a9f36b636`,
and `20321342522a7b55b5fc87711f4fddb0516607367401ff298c7618ec6292c36b`
in table order. The three tagged fixtures had SHA-256 values
`3553c468c86fade22a00dab4c3970537a6d2e1588fa7514a01b860de9a151ba1`,
`00d6c2e3a0eab46ab136994f7ab98be799f619b1d9af86f1a78bd9b3079ca0d4`,
and `ccdd86ab54a12934a3f770d42dd9e720bd3eacbb0d29b84c424100f80850f881`.

This comparison is bounded. It does not require current verification to build
the tag, compare behavior changed by modules, preserve Mini-Ash source
admission, or claim equivalence for every historical diagnostic or internal
trace. Git retains the historical compiler; no historical source was copied
into the current implementation.

## Changed composition points

The diff from the peeled tag through `3b66040` contains 110 files, 15,445
insertions, and 2,938 deletions. File-level classification gives:

| Class | Files | Insertions | Deletions |
| --- | ---: | ---: | ---: |
| Production | 26 | 6,873 | 964 |
| Tests | 65 | 6,067 | 1,521 |
| Documentation and specification | 19 | 2,505 | 453 |

`src/resolve/module_tests.rs` is classified as a test file because it is
compiled only under `cfg(test)`. Inline unit tests in production files remain
inside their production file's count. These counts locate the change and its
evidence; they do not measure semantic or implementation complexity.

The production change decomposes as follows:

| Boundary | Files | Insertions | Deletions |
| --- | ---: | ---: | ---: |
| Lexer, parser, Surface, syntax budget | 9 | 791 | 239 |
| Resolution and resolved types | 3 | 2,660 | 216 |
| Elaboration and coverage | 2 | 675 | 241 |
| Loader, driver, CLI, and diagnostics | 5 | 1,969 | 178 |
| Core construction and validation | 4 | 637 | 47 |
| Evaluator | 2 | 135 | 37 |
| Library assembly | 1 | 6 | 6 |

Most module-specific work remains at the source, resolution, and graph-driver
boundaries. Core changes qualify semantic identities and authenticate
module-to-source provenance. Evaluator changes consume linked identities and
resource results but add no module dispatch.

A stable maintenance search is:

```text
rg -l '\b(SurfaceModule|SurfaceImport|SurfaceQualifiedName|SurfaceTypeVisibility|DependencyExports|ExportSummary|ImportedFacts|ResolvedModule|CheckedModule|ResolvedModuleProgram|ModuleId|link_modules|synthesize_module_program|validate_modules)\b' src
```

The individual symbols occur in two to eight production files. In particular,
`DependencyExports` occurs at the driver, resolver, and resolver-test boundary;
`ExportSummary` occurs at resolution, checking, and resolved-data boundaries;
and linking and synthesis each have one driver caller and one elaboration owner.

## Core inventory and erasure

The retained pure Core families are:

- `PureExprKind`: `Value`, `Variable`, and `Computation`;
- `PureValue`: `Integer`, `Boolean`, `Unit`, `Function`, and `Constructor`;
- `PureComputation`: `Bind`, `RecursiveBind`, `Apply`, `Primitive`, `Tuple`,
  `Match`, `TypeAbstraction`, and `TypeApplication`.

The inventory extracted from `src/core/dialect.rs` is byte-identical at the
Mini-Ash tag and `3b66040`. The runtime `Value` inventory is also byte-identical:
integer, Boolean, unit, function, constructor function, location, and data.
The comparison used:

```text
diff -u \
  <(git show d62d3bae:src/core/dialect.rs | sed -n \
    -e '/pub enum PureExprKind {/,/^}/p' \
    -e '/pub enum PureValue {/,/^}/p' \
    -e '/pub enum PureComputation {/,/^}/p') \
  <(sed -n \
    -e '/pub enum PureExprKind {/,/^}/p' \
    -e '/pub enum PureValue {/,/^}/p' \
    -e '/pub enum PureComputation {/,/^}/p' src/core/dialect.rs)
```

The command produced no diff. Searches found zero module node variants in the
Core dialect and zero module-surface or access-policy terms in evaluator
dispatch. The evaluator's public entry remains
`evaluate(&ValidatedProgram) -> Result<Evaluation, RuntimeFailure>`.

Module linking therefore reuses `RecursiveBind` and `Apply`. The new Core-facing
fact is the static relation from each `ModuleId` to its admitted `SourceId`,
which validation checks together with qualified binder, nominal, constructor,
and type-variable identities. That relation is provenance, not runtime module
behavior.

## Requirement evidence

| Obligation | Retained evidence |
| --- | --- |
| Module tokens, import grammar, modifiers, qualification, projection, and recovery | `tests/lexer.rs`, `tests/modules_syntax.rs`, parser unit tests, and `tests/parser.rs` |
| Sibling, nested, named-root, qualified, targeted, and renamed imports | module-loading and resolver module tests plus executable examples in `tests/spec_examples.rs` |
| Canonical duplicate admission and one diamond identity | diamond, overlapping-root, alternate-route, and resolver-identity tests in `tests/module_loading.rs` and `src/resolve/module_tests.rs` |
| Unknown roots, missing files, path escape, direct and indirect cycles, malformed roots, aliases, unavailable exports, and binding conflicts | `tests/module_loading.rs`, `tests/module_cli.rs`, `tests/module_resolution.rs`, and resolver module tests |
| Private, opaque, transparent, smart-constructor, hidden-carrier, mismatch, and coverage behavior | `tests/module_visibility.rs`, resolver module tests, `tests/module_elaboration_nominals.rs`, and executable specification examples |
| Cross-module rank-1 instantiation without inference escape or re-generalization | `tests/module_elaboration.rs::imported_polymorphic_scheme_instantiates_at_unrelated_types_without_re_generalizing` |
| Body-free immutable dependency summaries | synthetic dependency-summary resolver tests, `failed_module_body_never_publishes_an_export_summary`, and the resolved-data API boundary |
| Exact entry contract and observation | `tests/module_entry.rs`, `tests/module_cli.rs`, and `tests/spec_examples.rs` |
| Qualified binders, combined registries, multi-source provenance, transforms, validation, and evaluation | module resolution/elaboration tests, modular Core validator tests, cross-source diagnostics, and linked transform/revalidation cases |
| Graph-wide source, edge, path, owner-fact, syntax, coverage, type, Core, and validation resources | exact graph-budget units, public path/deep-chain tests, shared syntax/type/coverage and repeated summary-metadata tests, and direct Core/validation boundary suites |
| Explicit worklists and small-stack destruction | deep dependency chain, parser projection, type traversal, Core disposal, validation, cyclic data, and evaluator tests |
| Specification, tools, reasons, links, and authority | the normative replacement at `3b66040`, executable document manifest, diagnostic tests, Markdown lint, and manual review |

The `entry.main-open-result` reason is a defensive driver boundary. A
successfully checked source scheme is closed: every source type parameter is
bound by its outer `forall`, and a polymorphic `main` fails before its domain or
result is admitted. A source-level open-result fixture would contradict that
checker invariant. The direct
`driver::tests::entry_result_closure_walks_every_nested_type` test retains the
closure predicate without manufacturing invalid checked source evidence.

Expensive source and edge maxima are not duplicated as end-to-end fixtures.
Exact unit-accounting tests prove those two graph boundaries, while public
loader tests cover path budgets, repeated canonical edges, deterministic
failure selection, and deep graph stack safety. Syntax, type, coverage, Core,
and validation limits additionally have graph-wide witnesses.

## Facts retained and released

| Boundary | Facts retained | Facts released |
| --- | --- | --- |
| Loading to resolution | canonical module and source identities, projected module, dependency identities and order, import provenance | filesystem traversal state and unused path spellings |
| Resolution to checking | module-qualified declarations, local bodies, imported body-free facts, defining registry, export candidate | aliases as semantic identity, unavailable private scopes, mutable resolution state |
| Checking to dependents | closed public schemes, public nominal and constructor facts, hidden identities, access facts, provenance | dependency bodies and private name environments |
| Checked graph to linking | full defining registries and bodies, summaries, module/source relation, dependency order | import selection syntax and access checks already authenticated |
| Linking to Core validation | qualified semantic identities, combined registry, source provenance, dependency-ordered recursive groups, generated entry application | module paths, aliases, summaries, visibility, and opacity |
| Validation to evaluation | one authenticated pure program | validator indexes and all remaining module-policy facts |

Two linked-intermediate fields have no current-tree reader after construction:
`ResolvedModuleProgram.entry` and the `module` field of each
`ResolvedModuleGroup`. They are possible later cleanup targets, subject to a
bounded API review and interface-era pressure. This report does not remove them
because cleanup is not needed to establish passive-module semantics.

## Diagnostics, resources, and ownership

Module loading retains stable reason families for unknown roots, missing files,
path escape, import cycles, and graph resources. Resolution distinguishes
duplicate aliases, unavailable exports, import conflicts, and opaque
constructors. Entry checking distinguishes missing, polymorphic, wrong-domain,
and defensive open-result failures. Cross-module diagnostics retain the
importing occurrence as their primary cause. Cross-module type diagnostics
also retain the exported declaration that supplied the imported type.
Diagnostic-only nominal spellings preserve declaration visibility separately
from importer nameability, so an unselected public type is not described as a
private declaration.

One cumulative syntax budget spans every admitted source. Loading charges
source, edge, path-segment, and retained owner-fact limits before keeping their
proportional graph state. Resolution charges imported namespace and nominal
metadata to its graph-wide type budget. Checking retains a separate graph-wide
type budget and one graph-wide coverage budget, including irrefutability
checks. Core construction and independent validation apply their cumulative
limits to the whole linked program. Pending loader work counts only active
traversal ownership, not every edge ever visited. Deep loading, validation,
evaluation, rendering, and destruction use explicit work stacks at their
admitted boundaries.

Canonical sources, module graphs, Core arenas, and heaps own identity domains.
Alternate paths do not create semantic duplicates. Core handles and runtime
locations remain numeric rather than Rust ownership cycles. Linking all loaded
definitions preserves one ordinary lexical environment chain; it does not add
module initialization or dynamic lifetime management.

## Transferable findings

- A module needs one stable identity for its canonical source, independent of
  alias, root, and route. Overlapping roots add access constraints rather than
  route-specific identities.
- Export summaries must carry hidden nominal identity without carrying private
  source nameability. This lets public APIs compose smart-constructor-style
  carriers without exposing representation.
- Opaque and hidden are distinct access states. Opaque types support new
  downstream global interfaces; hidden carriers support only inferred local
  composition through compatible public schemes.
- A body-free summary is a checked dependency boundary, not a source module
  signature. Interfaces and `impl` can build on it only through a separate
  semantic proposal.
- Module structure can erase after resolution and checking authenticate every
  reference. Byte-identical Core and runtime value inventories demonstrate that
  static modularity does not require a module Core node.
- Resource accounting must span the whole admitted graph. Resetting syntax,
  type, or coverage work at each module, or retaining owner relations without
  a cumulative charge, would make the bound route- and partition-dependent.
- Entry-result closure is guaranteed by the checked rank-1 scheme invariant;
  the driver guard is defensive rather than a source-reachable rejection.
- Retained design notes need explicit retrospective status after their proposal
  lands. A historical note that keeps saying current Ash is Mini-Ash would
  cross the repository's authority boundary even when its original analysis is
  useful.

## Downstream pressure and exclusions

At this passive-module checkpoint, the next planned increment was [interface
and `impl` design](../DN-0023-interfaces-and-implementations.md) against real
module boundaries. Ash interfaces are Rust-trait- or Haskell-type-class-like
typed relationships, not module signatures. DN-0023 later selected method-only
interfaces, scoped coherence, implicit source evidence, and explicit flattened
Core evidence. That increment is now implemented and specified; associated
types and specialization remain later pressure. It did not reinterpret
compiler-generated export summaries as source declarations.

The passive-module increment documented here intentionally excludes individual
constructor exports, import re-exports, parent traversal, module cycles,
cross-module recursive groups,
package manifests or acquisition, persistent compiled modules, separate object
linking, initialization, runtime module values, dynamic loading, providers,
registration, effects, dead-code elimination, a core-versus-library migration,
interfaces, `impl`, and a selectable current-tree Mini-Ash dialect.

The historical comparison excludes changed source-root admission and does not
constrain later core-versus-library refactoring to keep Mini-Ash syntax runnable
in the evolving compiler.

## Verification checkpoint

The historical `cargo xtask verify` passed at the peeled `mini-ash` tag. The
Modular Ash comparison checkpoint also passed `cargo xtask verify`, including
formatting, metadata, build, denied-warning Clippy, every unit and integration
test, and denied-warning rustdoc. After this report and its exact syntax cases
were added, `cargo fmt --check`, `cargo check --locked --all-targets`,
`cargo test --locked --all-targets`, and `cargo xtask verify` all passed again.
Artifact completion additionally checks Markdown, relative links, authority
boundaries, the complete accepted evidence inventory, and the absence of
interfaces, module signatures, parent traversal, runtime modules, and a
current-tree Mini-Ash compatibility path.
