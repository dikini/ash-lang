# TASK-0066: Expression Macros

- ID: `TASK-0066`
- Status: active
- Related: [CP-0033](../proposals/CP-0033-hygienic-expression-syntax.md),
  [AD-0005](../decisions/AD-0005-parser-architecture.md),
  [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0010](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [DN-0062](../design/DN-0062-hygienic-surface-macros.md),
  [first-slice design](../design/macros/first-slice.md),
  [execution plan](../plans/2026-11-05-expression-macros.md).

> This task organizes delivery of accepted, unimplemented CP-0033. It does not
> define current Ash semantics or extend the proposal's scope.

## Dependencies

CP-0033 supplies the accepted semantic transition and Ash interface.
AD-0005 now accepts one data-defined imported expression-prefix mechanism while
retaining its lexer, precedence, recovery, and projection boundaries. Current
language behavior remains in [the specification](../../spec/README.md).

The milestone anchor is local `integration/expression-macros`; the active
checkpoint is local `codex/expression-macro-delivery` in
`.worktree/expression-macro-delivery`. Both start at
`80994bec968f5d0a79448ebf8117f5bd3c23498d`. Recheck exact refs at every handoff.
Preserve other worktrees and unrelated changes. Use this one product checkout
and its compatible target cache for sequential deliveries under AD-0011.

The public `TokenKind` constructor names and spelling mapping are a general
language-definition dependency of the syntax service. Define and document one
shared lexical/metaprogramming vocabulary during D0/D2, with conformance cases
for the same interface version. Do not expose Rust enum discriminants or invent
a second macro-only vocabulary. Selecting these names is not another
macro-design acceptance gate; it remains a required implementation/interface
deliverable under CP-0033.

There is no dependency on CP-0032 or effects redesign. Use the current effect,
allocation, resource, evidence, continuation, completion, and build contracts.
If those inputs move before retention, identify and verify the affected path;
do not silently adopt another branch's semantics.

## Work

Deliver public imported expression syntax with templates and checked Ash
transformers through the real compiler driver, interpreter, and supported
build/image path. The task owns the pending M01–M14 matrix below and its
temporary execution plan. Component tests support one production acceptance
path; they do not create separate completion ledgers.

### Current behavior and affected boundaries

The [current grammar](../../spec/syntax.md#grammar) has no syntax declarations
or imports. [Lexical rules](../../spec/lexical-structure.md#tokens) admit no `$`
token or public token-constructor vocabulary. The new contextual forms must
preserve existing valid no-syntax programs, including ordinary globals named
`syntax`; misplaced `$` deliberately changes to a syntax rejection.

`src/module.rs::load_module_graph` currently reads, lexes, parses, and projects
each complete module while discovering its dependency graph.
`src/driver.rs::compile_graph_with_report` later resolves and checks modules in
dependency order. The delivery must connect fixed-header graph discovery to
checked syntax publication and then importer body parsing. Adding a matcher
parameter to an unused parser entry would leave the public driver disconnected.

The [current scope rules](../../spec/name-resolution.md#local-scope) distinguish
sequential locals, simultaneous recursive groups, pattern scopes, local nominal
declarations, resource/region scopes, and hidden continuation capability.
`src/resolve.rs` uses spelling-based scope maps today. Expansion and final
resolution must share one implementation of those policies while adding the
accepted contextual lookup and per-occurrence generated identities. Protected
fragments preserve grouping without becoming lexical scopes.

The [checked-module boundary](../../spec/elaboration.md#module-linking-and-entry-generation)
already retains lowered fragments, selected evidence, and hidden declaration
facts. Those facts do not themselves authorize a syntax expansion to reference
private declarations. Add the proposal's authenticated syntax-specific grants,
retain their original routes and executable closure, and independently validate
each newly linked compile-time or final program. Do not add private names or
definition-site implementation imports to caller scope.

`Evaluation` retains an `ObservedHeap` whose final drop closes its root. A macro
host needs an explicit output/diagnostic decode, compiler-storage transfer, and
root-close boundary, including combined primary and teardown failures. Keeping
an Ash value or allocation alive after its evaluation root closes is not output
transfer. The current `Origin` primary chain and flat related spans likewise
need a checked representation of ordered expansion frames and multiple causal
inputs through diagnostics and build/image consumers.

Existing parser, module, scope, runtime, and validator tests establish useful
regression boundaries. They are not macro evidence. No prior macro experiment
or measured implementation result transfers. Reuse the existing ordinary
checker, linker, evaluator, and validation paths; do not add macro-specific
typing or effect rules. Typed hooks, additional output categories, persistent
caches, expansion UI, compiler-size reduction, self-hosting, and browser hosting
remain excluded by CP-0033.

### Ownership and handoffs

| Responsibility | Owner |
| --- | --- |
| Scope, dependency order, eligible launches, checkpoint triggers, and milestone integration | Orchestrator for `integration/expression-macros`. |
| Product source, fixtures, specification/tool updates, all heavy builds, repairs, and retained acceptance update | Assigned developer; sole product writer and Cargo operator. |
| D0 boundary challenge, each reviewable delivery, retained end-to-end result, and acceptance audit | The same assigned independent reviewer throughout the milestone. |
| Product checkpoint verification | Developer runs the pinned gate; reviewer checks its inputs and receipts; orchestrator checks retention and closure. |
| Main integration and signing | Human gate; neither action is authorized by this task or plan. |

The orchestrator assigns concrete developer/reviewer identities and exact pins
when initiating D0. The current planning handoff does not launch implementation.
Do not divide product implementation before the D0 boundary challenge. The
orchestrator may divide independent work only after producer/consumer contracts
compile; shared product writers and heavy builds remain serialized.

Handoffs name source and target refs/commits, changed scope, focused checks,
review result, retained commit, latest full-gate receipt and intervening changes,
next checkpoint, cleanup result, and next actor. If repeated repairs stall the
path, the same reviewer challenges the whole remaining plan; preserve confirmed
findings here before adding mechanisms.

## Progress

- Parser amendment, task and execution plan are recorded. D0 has a concrete
  producer/consumer proposal and a frozen fixture family. The checkpoint,
  header projection, source census and staged driver compile; syntax contexts,
  grants and the macro host do not. Macro execution and expansion are absent.
- Contextual syntax selectors and the `$` token now parse; misplaced `$` fails
  at the parser. The checked driver rejects a missing syntax export before
  parsing the importer body, and the syntax-free loader reports that such
  selectors require the driver. This is fail-closed: no syntax export can yet
  be published or used. Specification changes await the integrated feature.
- The frozen macro graph now reaches the unimplemented
  `@builtin.compiler.syntax` import and fails as unknown builtin. The
  independent handwritten graph executes to `Int` value `42`, and the proposed
  procedural transformer's ordinary Ash body parses and projects. These are
  baseline observations, not macro acceptance.
- The independent boundary challenge identified three required repairs: resume
  retained header parser state without duplicate event charges; look up generated
  syntax by each leading identifier's retained context; and independently
  validate a dedicated compile-time entry and authenticated input handoff.
  The plan now records those contracts and the source census and borrowed
  checked-fragment ownership they require. The staged driver now discovers
  canonical headers, pays one source census, and checks each dependency before
  parsing its importer body. The public syntax-free loader retains its original
  complete-body schedule. Syntax contexts, grants and the validated macro host
  are not yet connected or compiled. D1–D4 and every M01–M14 criterion remain
  pending. No retained macro implementation or fresh full gate is claimed.
- Re-review found that retained contexts cannot borrow exports from a checked
  module vector that continues to grow. The plan now uses compilation-owned,
  append-only immutable context/export records addressed by authenticated stable
  IDs; operation-local views may borrow them without outliving a lookup.
- Independent Core validation currently reparses original source without a
  syntax environment to authenticate declaration coordinates and resolved
  effect summaries. Binder ownership, order, and resource coordinates also
  assume source spans. Its evidence must account for copied and generated
  occurrences separately from diagnostic origins. The same
  reviewer is challenging this boundary. The earlier whole-chain estimate is at
  risk until this remaining validator work is sized.
- Next actor: developer verifies and pins this repair; the orchestrator sends
  that exact candidate to the same reviewer. The remaining interfaces must be
  completed before claiming the D0 gate or substantial feature work complete.

### D0 baseline receipt

- Source anchor: `80994bec968f5d0a79448ebf8117f5bd3c23498d`; the candidate
  commit also pins this task, the plan, test targets and fixture bytes.
- Rust: `rustc 1.97.1 (8bab26f4f 2026-07-14)`; delivery-owned `target/`;
  one Cargo job. The cold targeted build took approximately 65 seconds and
  used 2.3 GB of target storage, with 244 GB free after the build.
- `cargo test -j 1 -p ash --test surface_macros --test macro_host --no-fail-fast -- --nocapture`:
  expected exit 101. The handwritten and standalone transformer-parser cases
  pass; both graph cases reject their entry's syntax import before body parsing.
  This does not demonstrate a transformer invocation or macro expansion.
- `cargo fmt --all -- --check`, `python3 tools/ash_indent.py --check
  tests/fixtures/surface-macros/*.ash`, and `git diff --check` pass on the D0
  candidate. No full workspace gate has run for this candidate.
- The whole-chain estimate is revised to an uncalibrated 30–55 focused
  engineer-days, accounting for reviewed checkpoint, context, checked entry and
  borrowed-fragment work. One cold compile does not calibrate the unresolved
  host, validator, build-consumer, review, and integration work.

### D0 boundary-repair receipt

- Reviewed candidate: `f791b95c4345d591abe269c7e3969bd7f89ed7b5`.
  This repair candidate records the subsequent parser/census changes; its
  retaining commit pins the exact inputs.
- `cargo test -j 1 -p ash --lib parser::checkpoint_tests -- --nocapture`:
  two pass. Tests compare the original 52/104/70-unit costs, exact and
  one-below boundaries, tiny budgets, and interleaved header checkpoints with
  recovery under a single 174-unit budget.
- `cargo test -j 1 -p ash --lib
  compiler_work::tests::source_census_retains_the_paid_ledger_for_each_admitted_source
  -- --exact`: one passes. The source census keeps the paid unit per admitted
  source and checks empty and arithmetic-overflow refusal.
- `cargo test -j 1 -p ash --test parser --test modules_syntax --test
  module_loading --test compiler_work_reporting --no-fail-fast`: parser 50,
  module syntax 20, module loading 24 and work reporting 6 pass. The frame
  composition work-reporting case took 100.47 seconds. This run preceded the
  addition of tiny-budget assertions in the test-only checkpoint module; no
  production source changed between that run and this candidate.
- The two full macro graph tests still fail at unsupported targeted syntax
  imports; the handwritten execution and ordinary Ash transformer parser checks
  pass. The staged graph and macro behavior are not implemented.

### D0 header-projection repair receipt

- Reviewed candidate: `27d80b2859706cda1934dabf1ad305189fde7d31`.
  The retaining commit pins this repair and its evidence. The revised 30–55
  focused engineer-day estimate remains uncalibrated for the whole chain.
- `cargo test -j 1 -p ash --lib parser::checkpoint_tests -- --nocapture`:
  eight pass. They cover projection before an invalid body, import-form parity,
  header and body lexical errors, foreign sources, recovery and malformed
  events, and budget refusal. The actual loader parser adapter matches the
  original parser's tree and paid work at low, exact and one-below limits.
- `cargo test -j 1 -p ash --lib parser::cst::tests -- --nocapture`: four
  pass, covering the shared complete-event builder and malformed trees.
- `cargo test -j 1 -p ash --test parser --test modules_syntax --test
  module_loading --test compiler_work_reporting --no-fail-fast`: parser 50,
  module syntax 20, module loading 24 and work reporting 6 pass. The long
  work-reporting case took 99.41 seconds. The loader budget comparison was
  added to the test-only checkpoint module after this run; production source
  did not change between these runs.
- The frozen macro graph tests still fail at unsupported syntax imports; their
  handwritten execution and ordinary transformer-parser controls pass. The
  existing loader uses the projected header but does not yet stage the graph.

### D0 staged-graph receipt

- Reviewed candidate: `80beb33105ed3cc2aad2bed31899561a48845b43`.
  The staged source and tests were verified at
  `0274daf9e644e4fb47845c794f2ea4da8f475f60`; the subsequent receipt update
  changes this task only. The 30–55 focused engineer-day estimate remains
  uncalibrated for the remaining chain.
- `cargo test -j 1 -p ash --lib module::staged_tests -- --nocapture`: one
  passes. An alias and diamond graph includes the implicit builtins once and
  compares source census, edge order, spans and total syntax work with the
  syntax-free path. Exact work succeeds; header, first-body and one-below-final
  refusals retain deterministic source and import attribution.
- `cargo test -j 1 -p ash --lib parser::checkpoint_tests -- --nocapture`:
  nine pass, including whole-module span parity for empty, whitespace,
  import-only and ordinary LF/CRLF inputs.
- `cargo test -j 1 -p ash --test parser --test modules_syntax --test
  module_loading --test module_resolution --test compiler_work_reporting
  --no-fail-fast`: parser 50, module syntax 20, module loading 27, module
  resolution 11 and work reporting 6 pass. The long work case took 101.01
  seconds. A real driver case proves a dependency check precedes a malformed
  importer body; other cases retain source/import diagnostics and paid partial
  checking work after body failure.
- `cargo test -j 1 -p ash --features resource-calibration --test
  resource_calibration_observer -- --nocapture`: three pass. Observation on
  and off agree; complete surfaces produce one input record, early failures
  produce none, and incomplete compilation is not reported as complete.
- Macro graph tests still fail at unsupported targeted syntax imports, while
  their handwritten and ordinary transformer-parser controls pass.

### Contextual-selector progress

- The lexer retains `$` and preserves `syntax` as an identifier. Parser and
  header projection distinguish syntax selectors from ordinary imports named
  `syntax`; public syntax re-exports and names not beginning with lowercase are
  rejected. The ordinary `syntax` global still executes through the driver.
- The driver authenticates that the selected dependency has been checked and
  rejects its unavailable syntax export before importer-body parsing. This
  temporary refusal is not checked syntax publication, matcher selection or
  expansion; those paths and the acceptance matrix remain pending.

## Verification

### Acceptance evidence

This is the single delivery matrix transferred from the first-slice companion.
CP-0033 continues to own its semantic requirements. All rows remain unchecked
until their complete original scope has evidence on the intended retaining
branch, including the applicable checkpoint and integration verification.

| State | Case | Required positive and negative evidence |
| --- | --- | --- |
| Pending | M01: natural syntax | Imported template `if`, both accepted nestings, precedence, parentheses, LF/CRLF, missing capture/separator, and no ordinary-application fallback. |
| Pending | M02: grouping | Splice `a + b`, blocks, and nested DSL forms as arguments; inspect protected fragments and compare handwritten parenthesized behavior. Contrast protected splicing with explicit `expression_syntax` unwrapping while retaining the original fragment and nested context/origins. Reject trailing output and recovery-bearing fragments. |
| Pending | M03: procedural path | An Ash transformer reads captures, computes an output tree, and executes through the real host. A discarded nested rejection does not run. Compare a template result; reject wrong signature/row, malformed output, authored rejection, and evaluator failure. |
| Pending | M04: term hygiene | Caller/introduced temporary collision, reused and distinct fresh identifiers, supplied binder/body with preceding initializer, repeated splices, and nested expansion. Positively demonstrate deliberate `caller_identifier` capture; contrast definition/fresh contexts and ordinary hygienic non-capture. Assert exact binder/use relationships. |
| Pending | M05: non-term scope | Local `newtype` and constructor, parameters, annotation types, recursive groups, and resource/region type and value scopes. Duplicate a fragment containing local binders, local nominal/region identities, and nested syntax; assert distinct output declarations with connected internal uses and unchanged caller free references. Include invalid scope and duplicate cases. |
| Pending | M06: definition authority | Private helper and own opaque construction; targeted/qualified/facade imports with caller shadowing. Reject ordinary caller private access, another module's withheld constructor, forged/retargeted grants, and missing definition helpers. |
| Pending | M07: imports and staging | Renamed and duplicate syntax imports, term-name conflicts, no activation through complete import, missing exports, unsupported re-exports/local definitions, and canonical dependency cycles. Unused imports cannot run transformers. |
| Pending | M08: DSL composition | Two separately authored forms nest and embed Ash. A template invokes a syntax dependency absent from caller imports. A same-spelled caller syntax import cannot redirect a generated identifier. |
| Pending | M09: current checks | Generated method obligations require ordinary evidence; wrappers preserve current handler selection and observable effect count/order. Test valid/invalid `resume` and resource escape/use, including a nested function and required direct builtin import. |
| Pending | M10: bridge and origins | Identity transformer round-trips token/group/fragment structure, contexts, grants, and origins. Check total negative/out-of-range capture indices, empty origin combination, invalid identifier/token construction, and `parse_expression` without name resolution or expansion; returning `SyntaxDiagnostic` preserves parse causes/origins. Reject wrong nominal constructors, malformed data, stale/foreign handles, and authority gained from strings/origins/caller syntax. Assert multiple input origins and nested frames in human/JSON diagnostics. |
| Pending | M11: completion and limits | Successful output survives evaluation-root teardown; authored failure, malformed output, evaluator/transfer failure, and exhausted budgets publish no partial result and retain teardown information. Bound self-producing recursive expansion. |
| Pending | M12: reproducibility | Repeat equal compilations modulo fresh identity renaming; change caller binding, matcher, helper, imported syntax, and interface/semantic inputs and show updated output or rejection. No persistent cache is required. |
| Pending | M13: module/Core boundary | Reuse a completed dependency without repeating its source proof; validate new compile-time and final linked Core independently. Reject mutations of declaration grants, scope, type, and provenance at their owning boundaries. |
| Pending | M14: compatibility | Existing valid no-syntax programs keep their behavior; retain unaffected diagnostic regression cases and test the specified new syntax error for out-of-place `$`. Compile generated output through the current interpreted and supported program-image/build paths; generated runtime code needs no syntax-service interpretation. |

The required production graph has a helper dependency, a syntax module with a
template and a computed Ash transformer, a separately authored DSL dependency,
and a renamed-syntax entry module. Through `driver::compile_path` and execution,
observe the private definition helper after linking, caller binder preservation,
nested DSL expansion, and structured diagnostics from invalid variants. The
same supported output must build and execute through the real public build
consumer. Observe output after macro-root teardown and no publication after
failed expansion. The [plan](../plans/2026-11-05-expression-macros.md#production-acceptance)
assigns the inputs and observations before implementation.

Record partial acceptance using the shared workflow's `Delivered`, `Remaining`,
`Awaiting`, and `Owner` fields. Attach exact test names, fixture/configuration
pins, commands, receipts, and retained commits to the affected row when known.
The developer prepares and applies the retained update, the reviewer checks it,
and the orchestrator confirms its readback before advancing.

### Checkpoints and commands

The plan maps D0–D4 to focused targets. `surface_macros` and `macro_host` exist
with the expected failing graph cases and passing baseline cases recorded above;
neither target establishes macro support yet. Run one Cargo job and the pinned
toolchain. Reuse the delivery checkout's compatible cache.

```sh
cargo test -j 1 -p ash --test surface_macros
cargo test -j 1 -p ash --test macro_host
cargo test -j 1 -p ash --test diagnostic_json
cargo test -j 1 -p ash --test program_build_native
```

The first fresh full workspace gate is C1 after D2: both authoring forms run
through the actual file graph, their new Core program is validated, and success,
transfer, failure, and root teardown are connected. Developer owns the command
and frozen receipts; reviewer owns the audit. C1 includes a real checked Ash
transformer that recurses without syntax requests until its invocation-only
machine transition budget exhausts, closes its root, and publishes nothing.
The D1 template vertical path is
required earlier and does not wait for that gate.

C2 closes D4 only after all M01–M14 obligations, specification/tool updates,
diagnostic catalogs, independent review/repairs, and the complete production
graph/build evidence are ready on a pinned candidate:

```sh
cargo xtask verify
```

Milestone-wide regression verification remains pending between C1 and C2.
Recheck and verify the actual retained result under the
[verification guide](../project/verification.md). Transfer receipts only within
demonstrated input/configuration/tool/artifact equality; refresh affected checks
after movement. The orchestrator owns integration into the milestone anchor.
A future pre-Main gate may reuse C2 only at equal inputs; Main permission and
signing remain separate.

Documentation checks cover Markdown lint, relative links/anchors, IDs, status,
commands, and authority boundaries. Keep CP-0033 until one product checkpoint
retains implementation, positive/negative tests, specification, review, and
verification; then retire it on that product branch under the artifact guide.
Remove this execution plan when its owning task finishes. Neither cleanup makes
the feature current Ash before Main integration.

## Discoveries

- Full-body parsing currently precedes dependency checking; the loader and real
  driver must share a staged source/header carrier rather than two disconnected
  graph paths.
- Existing hidden declaration summaries are reusable checked facts, not syntax
  authorization. Grants and private executable dependencies need their own
  authenticated path through resolution, checking, linking, and validation.
- Existing spelling-keyed scope maps and structural continuation scopes require
  a single scope-policy account; a term-only expansion adapter is incomplete.
- Ordinary observation lifetime is not the macro host's transfer/close contract.
  Decode/transfer failures and teardown failure preservation need direct evidence.
- `Machine::run_loop` has no general transition limit. Request/service budgets
  alone cannot bound checked Ash recursion without syntax requests. The developer
  owns invocation-only transition charging and its root-closing failure path;
  C1 requires a real nonterminating transformer observation.
- Interface signatures alone do not establish operation-result semantics. D2
  must observe deliberate caller capture, fragment unwrapping, parse-without-
  expansion and parser-failure preservation, total capture lookup, empty origin
  combination, and denied authority through real Ash service calls under the
  existing M02/M04/M10 acceptance rows.
- Current origins do not by themselves supply the ordered, multi-input macro
  relationships required by CP-0033. Their serialization and render consumers
  belong in the delivery chain.

## Deviations

None. Open Rust representation, API placement, host-service adapter, budget,
and fixture details are D0 implementation planning. A missing semantic rule or
contradiction returns to CP-0033/design work before implementation chooses it.
