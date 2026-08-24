# TASK-0011: Implement Passive Static Modules

- ID: `TASK-0011`
- Status: active
- Related: [CP-0005: Passive Static Modules](../proposals/CP-0005-passive-static-modules.md), [DN-0022: Passive Static Modules](../design/DN-0022-passive-static-modules.md), [DN-0020: Ash Dialect Milestones](../design/DN-0020-ash-dialect-milestones.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), the [passive-module evidence](../design/modular-ash/evidence.md), and the [execution plan](../plans/2026-08-23-implement-passive-static-modules.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0005 is the accepted transition authority. Commit `3b66040` replaced the
  normative specification after the implementation and test checkpoints made
  those claims true. Current `spec/` now defines Modular Ash.
- Work runs on `feature/modular-ash` in `.worktrees/modular-ash`.
- The `mini-ash` tag retains the historical compiler and corpus. Current source
  receives no Mini-Ash dialect selector or compatibility grammar.
- Behavioral changes use witnessed red-green-refactor cycles. Production Rust
  follows the project lint configuration and the Rust ownership, error, API,
  type-safety, testing, and documentation guidance selected for this task.
- Intermediate commits may contain a deliberately incomplete transition but
  must state their bounded checkpoint and keep their focused tests green.

## Work

Execute the linked plan to:

- replace the file-result root with declarations-only module syntax;
- add qualified and targeted imports, named roots, canonical loading, graph
  identity, deterministic cycles, and graph-wide resource accounting;
- add private, public opaque, and public transparent declarations;
- resolve each module from immutable dependency export summaries;
- preserve hidden nominal identity across public schemes without exporting its
  source name or constructors;
- link dependency-ordered module groups and generated `main ()` into one pure
  Core program without a module Core node;
- update the CLI, diagnostics, corpus, normative specification, tool docs, and
  retained evidence; and
- compare representative unchanged behavior against a separately built
  `mini-ash` tag.

## Progress

- The user accepted CP-0005 and its required evidence.
- The isolated worktree starts from `main` at `f1cf6a1`.
- `cargo build --locked` and `cargo test --locked --all-targets` pass before
  implementation. The baseline contains 565 passing tests and no failure.
- The implementation plan records the intended red-green checkpoints.
- Commit `0bc17bd` implements declarations-only module syntax and import
  spellings with focused syntax evidence.
- Commit `a9f923d` implements canonical graph loading with focused loader
  evidence.
- Commit `d00fd10` makes import resolution preserve structured
  qualifier/member spans, use compilation- and module-qualified identities,
  consume body-free dependency summaries, and produce a declarations-only
  resolved module plus a distinct unchecked export candidate. Focused Task 4
  evidence is green.
- Commit `be610c8` enforces private, public opaque, and public transparent type
  visibility through checked export summaries. Hidden nominal identities can
  flow through public schemes without exporting their source names.
- Commit `8b9e19f` links dependency-ordered module groups and a generated entry
  application into the existing pure Core dialect. Core retains no module,
  import, export, alias, or opacity node.
- Commit `1906c6a` enforces the local `main : Unit -> R` entry contract and runs
  modular entry graphs. Commit `6506d00` records why open results remain a
  defensive checked-boundary case rather than a source-level negative fixture.
- Commit `270adb6` migrates the current corpus and architecture guards to the
  declarations-only modular grammar. The current tree retains no Mini-Ash
  parser selector, file-result driver, or compatibility lowering.
- Commit `b2e69bf` closes the passive-module diagnostic and graph-wide resource
  evidence, including exact syntax, type, coverage, Core, validation, path,
  source, and edge accounting with explicit-worklist and small-stack cases.
- Commit `3b66040` replaces the normative specification and tool documentation
  with implemented Modular Ash behavior and executable examples.
- The final evidence audit adds exact lexer, CST, projection, export, import,
  and execution coverage for `pub fn`; exact parser recovery for leading,
  trailing, and empty relative-path segments; and exact malformed term, type,
  and pattern qualification recovery.
- A detached worktree at `mini-ash^{commit}` resolved to `d62d3ba`. Its full
  documented verification passed 514 tests across 22 binaries with no failed,
  ignored, measured, or filtered tests.
- The bounded comparison produced the same six exact observations from both
  historical Mini-Ash and current Modular Ash, with exit status 0 and empty
  standard error in every run: integer `7 : Int\n`, function `42 : Int\n`,
  global recursion `42 : Int\n`, higher-order constructor `42 : Int\n`,
  transparent tree matching `4 : Int\n`, and rank-1 Option/local
  generalization `(Some(42), false) : (Option<Int>, Bool)\n`.

## Verification

Focused commands are recorded in the execution plan. Completion requires:

```text
cargo fmt --check
cargo check --locked --all-targets
cargo test --locked --all-targets
cargo xtask verify
```

Manual review covers CP-0005 required evidence, Markdown, relative links,
artifact authority, formal notation, reason codes, all changed Core consumers,
module-summary isolation, graph and type resource accounting, multi-source
provenance, historical-tag comparison, and the absence of interfaces, module
signatures, parent traversal, runtime modules, or a current-tree Mini-Ash
compatibility path.

The historical verification ran under Rust 1.97.1 and Cargo 1.97.1:

```text
rustc --version --verbose
cargo --version --verbose
cargo xtask verify
```

Formatting, metadata, build, Clippy, all 514 tests, and rustdoc passed. Current
`cargo xtask verify` also passed at commit `3b66040`. After recording the
retained evidence, every completion command above passed again. Markdown and
repository-diff checks also passed before artifact retirement.

## Discoveries

- One canonical source may be reached through several configured roots. It has
  one compilation-local module identity, retains every owning root, and checks
  relative descendants against every owner. This removes discovery-order
  dependence without creating route-specific module identities.
- Linking registries also requires module-qualified resolved type variables and
  a separate namespace for generated term and type binders. Qualifying only
  source term binders and nominal declarations would leave cross-module or
  generated-identity collisions.
- A successfully checked module publishes closed, inference-free rank-1
  schemes. Every source type parameter is already bound by an outer `forall`,
  so a monomorphic entry `main` cannot expose an open result. The driver retains
  the `entry.main-open-result` guard as a defensive boundary, but current source
  cannot supply the plan's proposed negative case without first failing the
  polymorphic-entry check.
- The six-case historical comparison shows that replacing the source root and
  adding module assembly did not change the selected integer, function,
  recursion, nominal-data, pattern, or rank-1 observations. This result is
  bounded to those cases; it does not make the Mini-Ash compiler part of
  current verification.
- A checked dependency summary needs schemes, authenticated identities,
  visibility metadata, constructor families, and provenance, but no dependency
  body. The complete implementation becomes visible again only when the graph
  assembles and independently validates one linked Core program.

## Deviations

- Task 4's identity migration crosses Core construction, transformation,
  validation, evaluation, and their tests in addition to the files named by the
  initial plan. Those consumers must change together to preserve exact
  identities. This expands the implementation boundary without changing
  CP-0005 semantics.
- Task 4 no longer runs the legacy `tests/resolution.rs` file-result corpus as
  modular evidence. Those sources are intentionally invalid under the selected
  declarations-only grammar and remain part of the Task 8 corpus migration.
- Task 7 replaces the planned source-level open-result case with direct closure
  traversal coverage. Constructing an open checked scheme would contradict the
  checker contract and would not be valid language evidence; the accepted
  entry contract and its defensive reason family remain unchanged.
- Task 11 also updates DN-0022, although the execution plan omitted it from the
  file list. Retaining a design note that still called Mini-Ash current and left
  implemented choices open would contradict the new normative specification;
  the update preserves the exploration while recording its result and evidence.
- Task 11 adds exact syntax cases in `tests/modules_syntax.rs` and an operational
  export case in `tests/module_resolution.rs`, although its listed checkpoint
  was documentation-only. Review of those cases also found that a qualified
  term ending after `.` bypassed qualified-name recovery and that lowercase
  qualification-shaped forms cascaded through later grammar owners. The parser
  now recognizes the valid qualified prefix before requiring its member and
  consumes a lowercase qualification-shaped form once at its term, type, or
  pattern owner.
