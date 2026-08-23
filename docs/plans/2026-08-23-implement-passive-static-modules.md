# Passive Static Modules Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Replace the Mini-Ash file program with an acyclic graph of passive modules whose accepted exports link through entry-local `main : Unit -> R` into one validated pure Core program.

**Architecture:** Extend the existing lossless lexer/parser/projector with a declarations-only `SurfaceModule`. A new module loader admits canonical sources and produces a deterministic dependency order; each module resolves and type-checks against immutable dependency export summaries before its own fully zonked summary is published. Final graph assembly consumes those checked module records, nests dependency groups around dependents, and generates `main ()` in the only retained Core program; imports, visibility, and opacity have no Core representation.

**Tech Stack:** Rust 2024, existing Ash concrete-tree parser, resolver, rank-1 elaborator, pure Core validator and evaluator, Cargo integration tests, Markdown specification.

---

Implementation follows `superpowers:test-driven-development`, `rust-skills`,
`superpowers:systematic-debugging` for unexpected failures, and
`superpowers:verification-before-completion`. Each behavioral checkpoint begins
with the named focused test and a witnessed expected failure.

## Task 1: Authorize and baseline the implementation

### Task 1 — Files

- Create: `docs/tasks/TASK-0011-implement-passive-static-modules.md`
- Create: `docs/plans/2026-08-23-implement-passive-static-modules.md`
- Modify: `docs/tasks/README.md`

### Task 1 — Step 1: Record the accepted authority and bounded work

Link CP-0005, DN-0022, AD-0005, AD-0006, AD-0007, and this execution plan from
TASK-0011. Record the historical-tag boundary and required verification.

### Task 1 — Step 2: Verify the clean implementation baseline

Run: `cargo build --locked && cargo test --locked --all-targets`

Expected: PASS with 565 tests and no failure.

### Task 1 — Step 3: Validate and commit the task artifacts

Run:

```text
markdownlint --disable MD013 -- docs/tasks docs/plans
git diff --check
git add docs/tasks docs/plans
git commit -m "docs: authorize passive module implementation"
```

Expected: both checks pass and the commit contains only planning artifacts.

## Task 2: Replace the syntax root and add module spellings

### Task 2 — Files

- Modify: `src/lexer/token.rs`
- Modify: `src/lexer/mod.rs`
- Modify: `src/parser/mod.rs`
- Modify: `src/parser/grammar.rs`
- Modify: `src/parser/project.rs`
- Modify: `src/surface.rs`
- Modify: `tests/lexer.rs`
- Modify: `tests/parser.rs`
- Create: `tests/modules_syntax.rs`

### Task 2 — Step 1: Write the failing lexical and projection tests

Add cases that require tokens for `import`, `as`, `pub`, `opaque`, `@`, and
`.`. Add a projection case equivalent to:

```ash
import @std.collections.list as List
import helpers.math (sum, Number as ImportedNumber)

pub opaque type Number = Number(Int)

pub main : Unit -> Int
main () = List.length (sum ())
```

Assert ordered `SurfaceImport` values, exact path segments and spans, explicit
visibility, two declarations, and no file result.

### Task 2 — Step 2: Run the focused tests and witness RED

Run: `cargo test --test modules_syntax --test lexer --test parser`

Expected: FAIL because the tokens, CST nodes, and `SurfaceModule` do not exist.

### Task 2 — Step 3: Implement the minimal closed syntax family

Add the following source-level shapes, using boxed slices after projection when
ownership is fixed:

```rust
pub struct SurfaceModule {
    pub imports: Vec<SurfaceImport>,
    pub type_declarations: Vec<SurfaceTypeDeclaration>,
    pub definitions: Vec<SurfaceDefinition>,
    pub span: Span,
}

pub enum SurfaceModulePath {
    Relative(Vec<SurfaceName>),
    Absolute {
        root: SurfaceName,
        segments: Vec<SurfaceName>,
    },
}

pub enum SurfaceImportSelection {
    Qualified { alias: SurfaceName },
    Targeted(Vec<SurfaceImportItem>),
}

pub enum SurfaceTypeVisibility {
    Private,
    PublicOpaque,
    PublicTransparent,
}
```

Represent function visibility with a `public: bool` field on both global
presentations. Add exact CST nodes for imports, paths, selectors, qualified
names, and modifiers. Replace the selected parser dialect and Mini-Ash comments
with the sole Modular Ash grammar; do not retain the result-expression branch.

### Task 2 — Step 4: Migrate parser-local fixtures to declarations-only roots

Wrap expression-focused parser cases in a local `main : Unit -> T` definition
where whole-module parsing is required. Keep direct expression-parser unit
tests direct. Delete expectations for `parse.expected-result` and add rejection
of a trailing file expression.

### Task 2 — Step 5: Run focused tests and witness GREEN

Run: `cargo test --test modules_syntax --test lexer --test parser`

Expected: PASS with exact token coverage and no recovery-bearing projection.

### Task 2 — Step 6: Commit

```text
git add src/lexer src/parser src/surface.rs tests/lexer.rs tests/parser.rs tests/modules_syntax.rs
git commit -m "feat: parse passive module sources"
```

## Task 3: Admit canonical module graphs

### Task 3 — Files

- Create: `src/module.rs`
- Modify: `src/lib.rs`
- Modify: `src/source.rs`
- Modify: `src/driver.rs`
- Create: `tests/module_loading.rs`
- Create: `tests/support/modules.rs`

### Task 3 — Step 1: Write failing graph-loader tests

Use an RAII temporary tree to cover sibling and nested relative imports, a
named `std` root, one canonical dependency reached through a diamond, duplicate
canonical paths, unknown roots, missing files, root escape through a symlink,
direct cycles, indirect cycles, and graph resource limits.

### Task 3 — Step 2: Run the loader tests and witness RED

Run: `cargo test --test module_loading`

Expected: FAIL because `ModuleRoots`, `ModuleGraph`, and `load_module_graph` do
not exist.

### Task 3 — Step 3: Implement typed loader inputs and failures

Create APIs with these ownership boundaries:

```rust
pub struct ModuleRootName(String);

pub struct ModuleRoots {
    named: HashMap<ModuleRootName, PathBuf>,
}

pub struct ModuleId(u32);

pub struct LoadedModule {
    pub id: ModuleId,
    pub source: SourceFile,
    pub surface: SurfaceModule,
    pub dependencies: Box<[ModuleDependency]>,
}

pub struct ModuleGraph {
    pub modules: Box<[LoadedModule]>,
    pub entry: ModuleId,
}

pub fn load_module_graph(
    entry: &Path,
    roots: &ModuleRoots,
) -> Result<ModuleGraph, ModuleFailure>;
```

Canonicalize roots and targets before admission. Carry an owning canonical root
with every pending source. Resolve relative segments from the importing
directory, reject targets outside the owning root, intern canonical paths once,
and use an explicit DFS worklist with source-ordered edges. When several routes
reach one canonical source, reuse its identity, retain every owning root, and
revalidate earlier relative edges against newly discovered owners. Return
dependency order and retain the import occurrence on every edge. Add explicit
source, edge, path-segment, and pending-work budgets.

### Task 3 — Step 4: Run loader tests and witness GREEN

Run: `cargo test --test module_loading`

Expected: PASS; diagnostic assertions distinguish source rejections from root
configuration failures.

### Task 3 — Step 5: Commit

```text
git add src/module.rs src/lib.rs src/source.rs src/driver.rs tests/module_loading.rs tests/support
git commit -m "feat: load canonical module graphs"
```

## Task 4: Resolve imports and generate immutable export summaries

### Task 4 — Files

- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify: `src/module.rs`
- Modify: `src/types.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/transform.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/eval/machine.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/pattern.rs`
- Modify: `tests/core_validation.rs`
- Create: `tests/module_resolution.rs`

### Task 4 — Step 1: Write failing import-scope and identity tests

Cover qualified imports, targeted imports, renames, term/type/constructor
namespaces, a same-spelled public type and constructor selected together,
duplicate aliases, duplicate targets, local/import conflicts, inaccessible
private declarations, and a diamond that shares binder and nominal identities.
Assert that the importer-facing resolver input exposes summaries but no
dependency definitions.

### Task 4 — Step 2: Run focused resolution tests and witness RED

Run:

```text
cargo test --test module_resolution
cargo test --lib resolve::module_tests
```

Expected: FAIL because module-qualified identities and export summaries are
absent. The Mini-Ash file-result fixtures in `tests/resolution.rs` remain a
corpus-migration boundary for Task 8; they do not define the modular resolver
root.

### Task 4 — Step 3: Add module-qualified binder identity and summary data

Use typed identities rather than encoded strings:

```rust
pub struct BinderId {
    namespace: BinderNamespace,
    local: u32,
}

pub enum BinderNamespace {
    Module(ModuleId),
    Generated,
}

pub struct ExportSummary {
    pub module: ModuleId,
    terms: HashMap<String, ExportedGlobal>,
    types: HashMap<String, ExportedType>,
    constructors: HashMap<String, ExportedConstructor>,
}

pub enum ExportedTypeAccess {
    Opaque,
    Transparent,
}
```

Keep hidden nominal identities in exported global schemes but omit their name
map entry. Include transparent constructors only. Summaries own fully resolved
and closed schemes plus causal declaration origins; dependency bodies are not
reachable through the summary API.

Use the same disjoint ownership rule for type-variable identities: source type
variables are qualified by their defining module, while elaborator-generated
type variables occupy a generated namespace. Core transforms preserve both
binder namespaces exactly.

### Task 4 — Step 4: Resolve one module from dependency summaries

Split the current resolver entry into a `ModuleResolver` created with its
`ModuleId` and selected dependency summaries. Populate qualified and targeted
scopes before local declarations, reject all silent shadowing, and retain
file-wide local mutual visibility. Resolution produces a private export
candidate; it must not publish an `ExportSummary` until Task 6 has checked the
complete defining module. Preserve explicit type-work accounting while cloning
dependency summary types and origins.

### Task 4 — Step 5: Run focused tests and witness GREEN

Run:

```text
cargo test --test module_resolution
cargo test --lib resolve::module_tests
```

Expected: PASS, including proof that two hidden identities with the same source
spelling do not compare equal and that an unchecked export candidate cannot be
supplied as a dependency summary.

### Task 4 — Step 6: Commit

```text
git add src/resolved.rs src/resolve.rs src/resolve/module_tests.rs src/module.rs src/types.rs src/surface.rs src/parser/project.rs src/core/dialect.rs src/core/validate.rs src/elaborate.rs src/eval/machine.rs tests/core_validation.rs tests/module_loading.rs tests/modules_syntax.rs tests/parser.rs tests/primitive_vertical.rs tests/module_resolution.rs
git commit -m "feat: resolve module export boundaries"
```

## Task 5: Enforce private, opaque, and transparent nominal access

### Task 5 — Files

- Modify: `src/resolve.rs`
- Modify: `src/resolved.rs`
- Modify: `src/pattern.rs`
- Modify: `src/render.rs`
- Create: `tests/module_visibility.rs`

### Task 5 — Step 1: Write failing visibility tests

Add positive cases for a private carrier passed between imported functions, a
public opaque type named by a downstream global, smart construction and public
observation, and exhaustive matching on a public transparent type. Add negative
cases for naming a private type, constructing or matching an opaque type,
mixing two hidden identities, importing a private spelling, and targeting a
withheld constructor.

### Task 5 — Step 2: Run visibility tests and witness RED

Run: `cargo test --test module_visibility`

Expected: FAIL at unavailable access or because the module pipeline is not yet
connected.

### Task 5 — Step 3: Implement source access at resolution boundaries

Allow the defining module to resolve every constructor. Importers receive
opaque nominal identity and kind metadata without constructors; private names
receive no binding. Preserve hidden identity inside `ExportedGlobal` schemes.
Render hidden diagnostic types through a display-only module label such as
`Math.<private T>` without inserting that spelling into any name map.

At this checkpoint, retain the hidden display spelling, stable defining module
identity, and causal declaration span. Task 6 connects that display-only data
to modular type diagnostics when the module checker first exists; Task 5 has no
cross-module type-diagnostic path to render yet.

### Task 5 — Step 4: Run visibility tests and witness GREEN

Run: `cargo test --test module_visibility`

Expected: PASS with stable `resolve.unavailable-export` and
`resolve.opaque-constructor` categories.

### Task 5 — Step 5: Commit

```text
git add src/resolve.rs src/resolved.rs src/pattern.rs src/render.rs tests/module_visibility.rs
git commit -m "feat: enforce module type visibility"
```

## Task 6: Type modules from summaries and link dependency groups

### Task 6 — Files

- Modify: `src/resolved.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/driver.rs`
- Create: `tests/module_elaboration.rs`
- Modify: `tests/core_validation.rs`
- Modify: `tests/provenance.rs`

### Task 6 — Step 1: Write failing typing and Core-shape tests

Cover cross-module polymorphic instantiation at unrelated types, no exported
inference variables, no re-generalization, module-local recursion, dependency
visibility, a dependency-order Core nesting assertion, combined nominal
registry identity, multi-source provenance, transform preservation, independent
validation, and evaluation.

### Task 6 — Step 2: Run focused tests and witness RED

Run:

```text
cargo test --test module_elaboration --test core_validation --test provenance
```

Expected: FAIL because `ResolvedProgram` has one file-wide definition group and
one source.

### Task 6 — Step 3: Check each module before freezing its summary

Add a module-checking entry that receives only the resolved defining module and
its selected dependency summaries. Check all local definitions against their
declared schemes, fully zonk public schemes, reject escaped inference, and then
freeze the export candidate as an immutable `ExportSummary`. The existing
elaborator may emit temporary builder nodes during this check, but the checker
must discard them: they are neither validated programs, compiled fragments,
cache artifacts, nor linker inputs.

Process modules in dependency order. A dependent resolver and checker can
observe only summaries already frozen by successful dependency checks, never a
dependency body or unchecked candidate.

### Task 6 — Step 4: Represent linked groups without a module Core node

Change the resolved program root to retain dependency-ordered groups:

```rust
pub struct ResolvedModuleGroup {
    pub module: ModuleId,
    pub definitions: Vec<ResolvedDefinition>,
    pub schemes: Box<[CheckedGlobalScheme]>,
    pub span: Span,
}

pub struct ResolvedProgram {
    pub registry: Arc<ResolvedRegistry>,
    pub groups: Vec<ResolvedModuleGroup>,
    pub entry: ModuleId,
    pub result: ResolvedExpr,
}
```

Merge registries by authenticated identity. Populate each group's schemes from
its checked record and do not recompute exported schemes from dependency bodies
or re-generalize them during final lowering.

### Task 6 — Step 5: Nest ordinary Core recursive groups in dependency order

Refactor `elaborate_program` so it admits each checked module scheme into the
typing context, lowers that module's bodies, and records an ordinary recursive
Core group. Fold groups in reverse dependency order around the generated entry
application. Do not add import, export, module, opacity, or loader variants to
the Core dialect. Only this final builder is finished and passed to independent
Core validation.

### Task 6 — Step 6: Validate with every admitted source

Pass the complete stable source slice to `validate`. Assert related provenance
never crosses sources unless represented by separate related labels and that
every Core origin belongs to one admitted source.

### Task 6 — Step 7: Run focused tests and witness GREEN

Run:

```text
cargo test --test module_elaboration --test core_validation --test provenance --test semantics
```

Expected: PASS; the closed Core feature inventory remains unchanged.

### Task 6 — Step 8: Commit

```text
git add src/resolved.rs src/elaborate.rs src/core src/driver.rs tests/module_elaboration.rs tests/core_validation.rs tests/provenance.rs tests/semantics.rs
git commit -m "feat: link module groups into pure Core"
```

## Task 7: Enforce entry `main` and expose the modular driver API

### Task 7 — Files

- Modify: `src/driver.rs`
- Modify: `src/render.rs`
- Modify: `src/main.rs`
- Modify: `tests/cli.rs`
- Create: `tests/module_entry.rs`

### Task 7 — Step 1: Write failing entry and invocation tests

Test missing local `main`, imported-only `main`, polymorphic `main`, a non-Unit
domain, an open result, a valid private `main`, exact `main ()` observation,
repeatable `--root name=path`, duplicate root names, malformed root arguments,
and multiple positional paths.

### Task 7 — Step 2: Run entry and CLI tests and witness RED

Run: `cargo test --test module_entry --test cli`

Expected: FAIL because the driver still runs one `SourceFile` result and the CLI
accepts exactly one unparsed argument.

### Task 7 — Step 3: Add modular driver inputs and entry checking

Expose one tool-facing configuration:

```rust
pub struct RunConfiguration {
    pub entry: PathBuf,
    pub roots: ModuleRoots,
}

pub fn run_path(configuration: RunConfiguration)
    -> Result<Observation, FileFailure>;
```

After resolution, select exactly one entry-local binder spelled `main`. Require
a monomorphic `Unit -> R` scheme and a closed zonked `R`. Generate a resolved
unit application with causal entry provenance and retain structured
`entry.*` failures.

### Task 7 — Step 4: Parse CLI roots without a search order

Accept `ash [--root name=path]... <entry-file>`. Reject malformed or duplicate
configuration at status 2. Preserve status 1 for import-caused source
rejections and exact stdout observation for success.

### Task 7 — Step 5: Run focused tests and witness GREEN

Run: `cargo test --test module_entry --test cli`

Expected: PASS with exact stdout, stderr reason prefix, and status.

### Task 7 — Step 6: Commit

```text
git add src/driver.rs src/render.rs src/main.rs tests/cli.rs tests/module_entry.rs
git commit -m "feat: run modular Ash entry points"
```

## Task 8: Migrate the retained current corpus to Modular Ash

### Task 8 — Files

- Modify: `tests/*.rs`
- Modify: `tests/fixtures/**/*.ash`
- Modify: `src/**/*.rs` test modules and Mini-Ash-facing documentation

### Task 8 — Step 1: Establish the current-tree compatibility exclusion

Add an architecture assertion that the selected parser and driver expose no
Mini-Ash dialect, selector, file-result root, or compatibility code path.

### Task 8 — Step 2: Run all targets and witness RED

Run: `cargo test --locked --all-targets`

Expected: FAIL only where retained tests still construct Mini-Ash file roots or
call superseded single-source helpers.

### Task 8 — Step 3: Convert tests without changing expression semantics

For every whole-program fixture, replace the final result expression with a
local entry definition whose declared closed result matches the old expected
type:

```ash
main : Unit -> Int
main () = old_result
```

Use inline operational `main` when the result needs a multi-line block. Update
helpers to build in-memory single-module graphs or RAII file trees through the
same public modular pipeline. Rename Mini-Ash-facing current comments to Ash or
Modular Ash. Do not add compatibility parsing.

### Task 8 — Step 4: Run all targets and witness GREEN

Run: `cargo test --locked --all-targets`

Expected: PASS with all retained expression, recursion, data, polymorphism,
Core, transform, evaluator, resource, and diagnostic obligations exercised
through module roots.

### Task 8 — Step 5: Commit

```text
git add src tests
git commit -m "test: migrate the Ash corpus to modules"
```

## Task 9: Close graph-wide failures and resource boundaries

### Task 9 — Files

- Modify: `src/module.rs`
- Modify: `src/diagnostic.rs`
- Modify: `src/render.rs`
- Modify: `src/driver.rs`
- Modify: `tests/module_loading.rs`
- Modify: `tests/module_resolution.rs`
- Modify: `tests/module_elaboration.rs`
- Modify: `tests/diagnostics.rs`
- Modify: `tests/source_diagnostics.rs`
- Modify: `tests/architecture.rs`

### Task 9 — Step 1: Add the missing negative and boundary tests from CP-0005

Inventory CP-0005's required evidence and add one focused failing test for every
uncovered reason family, deterministic ordering rule, source edge, work budget,
small-stack boundary, summary isolation invariant, or implementation-locality
claim.

### Task 9 — Step 2: Run the new tests and witness RED

Run:

```text
cargo test --test module_loading --test module_resolution --test module_elaboration --test diagnostics --test architecture
```

Expected: at least one deliberate boundary test fails before its accounting or
diagnostic path is complete.

### Task 9 — Step 3: Complete structured failures and accounting

Keep invocation, module loading, parsing, resolution, entry checking, typing,
validation, and runtime failures distinct. Charge retained graph structures
before allocation, use explicit worklists rather than host recursion, preserve
source-order causality, and render all public reason codes from typed enums.

### Task 9 — Step 4: Run focused and complete tests

Run:

```text
cargo test --locked --all-targets
cargo clippy --locked --all-targets -- -D warnings
```

Expected: PASS with no warning.

### Task 9 — Step 5: Commit

```text
git add src tests
git commit -m "test: close passive module evidence"
```

## Task 10: Replace the normative specification and tool documentation

### Task 10 — Files

- Modify: `spec/README.md`
- Modify: `spec/lexical-structure.md`
- Modify: `spec/syntax.md`
- Modify: `spec/name-resolution.md`
- Modify: `spec/static-semantics.md`
- Modify: `spec/elaboration.md`
- Modify: `spec/dynamic-semantics.md`
- Modify: `docs/tools/ash.md`
- Modify: `README.md`
- Modify: `tests/spec_examples.rs`

### Task 10 — Step 1: Add failing executable documentation examples

Add sibling, named-root, targeted import, opaque smart-constructor, hidden
carrier, transparent matching, and `main ()` examples to `tests/spec_examples.rs`
before changing normative prose.

### Task 10 — Step 2: Run the documentation examples and witness RED

Run: `cargo test --test spec_examples`

Expected: FAIL until examples and their extracted documents agree.

### Task 10 — Step 3: Replace current normative truth

Apply CP-0005's semantic delta to every affected specification area. Remove the
Mini-Ash single-file result root from current truth. State path ownership,
summary generation, namespace and access rules, dependency order, entry
checking, group linking, erasure, validation, and evaluation without importing
implementation details as semantics.

### Task 10 — Step 4: Update exact tool behavior

Document `ash [--root name=path]... <entry-file>`, exit categories, module
failure observations, and a complete executable module tree.

### Task 10 — Step 5: Run examples and documentation checks

Run:

```text
cargo test --test spec_examples
markdownlint --disable MD013 -- README.md spec docs
```

Expected: PASS.

### Task 10 — Step 6: Review links, authority, and notation

Check every changed relative link resolves. Confirm the accepted proposal is
the only prospective artifact used to justify the transition and that `spec/`
now states the implemented result.

### Task 10 — Step 7: Commit

```text
git add README.md spec docs/tools/ash.md tests/spec_examples.rs
git commit -m "docs: specify modular Ash"
```

## Task 11: Compare the historical milestone and complete the artifacts

### Task 11 — Files

- Create: `docs/design/modular-ash/evidence.md`
- Modify: `docs/design/DN-0020-ash-dialect-milestones.md`
- Modify: `docs/design/README.md`
- Modify: `docs/trajectory.md`
- Modify: `docs/tasks/TASK-0011-implement-passive-static-modules.md`

### Task 11 — Step 1: Build Mini-Ash outside the current source tree

Create a temporary detached worktree at tag `mini-ash`, run its documented
verification, and compare representative unchanged integer, function,
recursion, nominal-data, pattern, and rank-1 observations with equivalent
Modular Ash entry modules. Do not copy historical compiler code into the
current branch.

### Task 11 — Step 2: Record bounded evidence

Document commands, tag commit, cases, exact outcomes, implementation-locality
inspection, Core inventory result, exclusions, and any transferable discovery.
Update TASK-0011 progress, discoveries, deviations, and verification from
observed evidence only.

### Task 11 — Step 3: Run complete verification

Run:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --all-targets
cargo xtask verify
markdownlint --disable MD013 -- README.md spec docs
git diff --check
```

Expected: every command passes. Review all changed relative links and CP-0005
required evidence manually.

### Task 11 — Step 4: Commit the retained evidence checkpoint

```text
git add docs
git commit -m "docs: record modular Ash evidence"
```

### Task 11 — Step 5: Remove completed transition artifacts

After review confirms implementation, tests, specification, and evidence have
merged as one coherent change, remove CP-0005, TASK-0011, and this temporary
execution plan; update their indexes. Git retains their accepted and completed
history. Keep DN-0022 and the Modular Ash evidence because they explain the
design and retained milestone.

### Task 11 — Step 6: Re-run documentation and repository verification

Run:

```text
markdownlint --disable MD013 -- README.md spec docs
git diff --check
cargo xtask verify
```

Expected: PASS with no active proposal or task left for the completed change.

### Task 11 — Step 7: Commit completion

```text
git add -A docs
git commit -m "docs: complete passive static modules"
```

Use `superpowers:requesting-code-review` before integration and
`superpowers:finishing-a-development-branch` after every required check and
review finding is resolved.
