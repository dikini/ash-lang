# Expression Macros Implementation Plan

> The original plan and completed checkpoints below are preserved as history.
> The [2026-11-06 remaining-scope amendment](#2026-11-06-remaining-scope-amendment)
> supersedes conflicting outstanding requirements and forecasts.

> Execute task by task using `superpowers:executing-plans` and the Ash developer
> workflow. [TASK-0067](../tasks/TASK-0067-expression-macros.md) owns this
> temporary plan; remove it when that task finishes.

**Goal:** Deliver accepted CP-0033 through one real file graph, checked Ash
execution, ordinary checking/linking, and the interpreter and build consumers.

**Architecture:** Add one data-defined imported prefix mechanism under amended
AD-0005. Share protected syntax, contextual expansion, definition grants, and
provenance between templates and Ash procedures. Reuse checked dependencies and
independently validate new compile-time and runtime Core programs.

**Tech stack:** Existing Rust lexer/parser/front end, checked-module linker,
Effect Core evaluator and allocation/completion machinery, Ash-defined canonical
syntax data/services, generated program images, and current diagnostic catalogs.

This plan implements [CP-0033](../proposals/CP-0033-hygienic-expression-syntax.md)
and its [design companion](../design/macros/first-slice.md); it defines no new
semantics or architecture. The task holds scope, refs, role ownership, the only
M01–M14 acceptance matrix, and checkpoint status. The acceptance obligations
below remain pending. Main integration and signing remain outside authorization.

## Boundary agreements

Before substantial implementation, the developer records concrete Rust carrier
and function signatures for these agreements and the independent reviewer
challenges the complete path. Compile both producer and real consumer early;
do not substitute isolated helpers for the public driver. One developer owns
both sides unless the orchestrator explicitly divides work after D0.

### B1: source headers, checked syntax, and importer parsing

**Producer/consumer:** `src/module.rs` discovers fixed import headers and
canonical module edges; `src/driver.rs::compile_path` orchestrates dependency
checking and supplies selected checked syntax to the importer body parser in
`src/parser/`. Developer owns all three; orchestrator owns their integration.

**Data/lifetime:** Retain source bytes/IDs, lexed token coverage, import spans,
canonical IDs, graph order, root/path ownership, and unparsed body extent for
the compilation. Checked dependencies publish immutable syntax exports:
declaration identity, restricted matcher, local alias/import route, template or
transformer, definition environment/origins, and checked closure. Compilation-owned
stable IDs retain those records and their checked owners; each operation borrows
only for its duration. Generated parsing uses the identifier's retained syntax
environment, including definition-site imports.

**Failure/check:** Header discovery executes no transformer and publishes no
unchecked syntax. Reject graph cycles, selection conflicts, absent exports, and
unsupported imports at their owning boundaries. Keep source/import diagnostics
and existing graph ownership/work limits. Do not parse importer bodies before
the required exports are checked. D0 enumerates public `load_module_graph`
callers and their staged-body needs; a legacy convenience wrapper cannot remain
the production path if it parses before checked syntax is available.

M07/M08 and the graph acceptance must prove that `compile_path` consumes the
selected matcher and retained dependency once. Instrumented phase/call evidence
may support that observation; a hand-built environment is insufficient.

### B2: parsing, protected fragments, and lexical expansion

**Producer/consumer:** `src/lexer/`, `src/parser/{mod,grammar,expression,cst,event,project}.rs`
produce validated context-bearing syntax/captures; expansion and
`src/resolve.rs` consume them. The closed assembly adds one built-in prefix
mechanism with matcher data; existing application/infix parsing stays the sole
precedence owner. Developer owns the producer, expander, and resolver.

**Data/lifetime:** Retain the complete original invocation, capture ranges,
contexts, origins, balanced groups, and immutable protected unexpanded fragments.
The compiler owns these for the compilation; output occurrences get separate
internal binder/nominal/region/nested-expansion identities while input storage
may be shared immutably. Splicing is not text conversion or a new lexical scope.

**Failure/check:** No recovery-bearing capture or output crosses projection or
transformer admission. Commit to the selected identity; enforce stop literals,
nested consumption, logical lines, and loose-prefix boundaries without ordinary
application fallback. M01/M02 inspect concrete coverage and final grouping, then
run the same input through the public graph. A malformed discarded capture still
rejects before any transformer; a valid discarded nested invocation never runs.

The expander and final resolver share current binding-form policies across term,
type, constructor, alias, interface, and effect names. Establish enclosing scopes
before transformer input; resolve complete expanded output before typing.
Sequential initializers, recursive groups, patterns, local `newtype`, resources,
regions, and hidden `ResumeId` scopes require explicit regions from the current
specification. M04/M05/M09 assert exact identities and negative scope/capability
cases; do not implement a parallel term-only scope walk.

### B3: definition authority and retained private closure

**Producer/consumer:** Template definition checking and expansion issue retained
reference grants; `src/resolve.rs`, `src/resolved.rs`, `src/elaborate.rs`, module
linking, and independent validators consume them. Developer owns both sides.

**Data/lifetime:** An authenticated grant ties the original syntax export,
declaration, namespace/access, definition context, and original import route to
the surviving reference. Retain its checked declaration fact and completed
executable/helper dependencies for as long as the compiled caller needs them.
Nested syntax preserves the issuer chain; relocation preserves original identity
and source provenance. Existing hidden summary records can carry checked facts
but do not create this new syntax authorization channel automatically.

**Failure/check:** Template free helpers fail at definition time; computed
definition-context references resolve after generated binders are known.
Ordinary caller names, captured identifiers, caller-context construction, forged
origins, and same-spelled aliases cannot gain or retarget grants. The syntax
owner may delegate its own private/opaque access, not a dependency's withheld
access. Method identity retains ordinary caller evidence obligations; grants
cannot import chosen implementations or hidden continuation capability.

M06/M09/M13 execute a private helper through `compile_path` and the final
program, then reject grant/route/declaration/scope/type/provenance mutations at
their owning admission or validation boundary. Verify checked closure reuse
without dependency body rechecking, not merely successful source lookup.

### B4: public syntax vocabulary and compile-time entry

**Producer/consumer:** Compiler-owned module publication in `src/module.rs`,
ordinary resolution/checking in `src/resolve.rs`/`src/elaborate.rs`, and canonical
API recognition in `src/resolved.rs` supply checked declarations and callable
facts to the compile-time linker/evaluator. Developer owns the shared interface.

**Data/lifetime:** Define the canonical `@builtin.compiler.syntax` Ash data,
opaque types, canonical `Ops`, and wrappers exactly as accepted. Complete the
shared public `TokenKind` constructor names, kind/spelling mapping, logical-line
representation, and validation table as a language/tool vocabulary. Document
included non-identifier kinds and exclusions, including grouped delimiters and
non-output lexer sentinels; derive no public identity from Rust enum order.
Conformance cases cover every documented constructor, valid spelling, invalid
spelling, and round trip for one interface version. Preserve integer/string
source spellings rather than reconstructing them from decoded Rust values.

Keep checked transformer/helper fragments, canonical nominal/effect identities,
source/configuration/interface pins, and any validated compile-time program in
compiler storage for the compilation. The host admits the actual monomorphic,
unconstrained function type with closed row containing only implicit default
allocation and optionally canonical `Ops`; no arrow subtyping or source `main`
is required. An unchanged validated program can be reused; changed linked Core
must be independently validated before execution.

**Failure/check:** Reject copied/same-spelled builtin identities, wrong domains,
results, polymorphism, constraints, open rows, and other effects. M03/M10/M13
call a computed Ash transformer, observe its result, and verify that only fresh
input/output host admission repeats when the linked program is unchanged.
No Rust replacement transformer, native callback, ambient compiler mutation,
filesystem, network, clock, or target-query service is an admitted substitute.

**Service-result checks:** D2 runs these through actual Ash requests under the
existing M02/M04/M10 criteria, alongside nominal/handle authentication:

- Contrast `caller_identifier` deliberately selecting a caller binding with
  `definition_identifier` retaining the definition helper under the same-spelled
  caller shadow and `fresh_identifier` remaining private. Include deliberate
  caller-context binder/body capture and ordinary hygienic non-capture. The
  context is the invocation leading identifier's, not an arbitrary capture's.
- `expression_syntax` removes only the returned sequence's outer fragment
  boundary. The original fragment remains intact; nested fragments, contexts,
  grants, origins, and sequence order survive. Compare grouped splicing with
  explicit unwrapping and the corresponding handwritten expression.
- `parse_expression` parses one complete expression without resolving names,
  expanding nested invocations, or executing another transformer. Observe zero
  nested transformer calls until the returned fragment survives expansion.
  Return a rejected parse as `SyntaxDiagnostic` and assert that its structured
  parser cause and origins survive the final diagnostic.
- `capture` returns `MissingCapture` for negative and out-of-range `Int` indices,
  including values larger than a host index, and cannot expose another
  invocation's captures. `combine_origins` returns `MissingOrigins` for an empty
  list and preserves the nonempty list's ordered causes and expansion frame.
- Invalid identifier spellings return `InvalidIdentifier`; kind/spelling
  mismatches return `InvalidToken`. Display strings, supplied origins, captured
  or caller-context identifiers, and copied nominal declarations cannot mint
  context, grants, private access, evidence, or hidden continuation capability.

### B5: host values, output transfer, root close, and limits

**Producer/consumer:** `src/eval/{machine,value,region,failure,disposal}.rs` and
the syntax-service adapter produce `MacroResult`; decoder/admission and expansion
consume the complete compiler-owned syntax or diagnostic. Developer owns the
whole invocation lifecycle; reviewer audits success and failure consumers.

**Data/lifetime:** One invocation owns a fresh allocation root/service state and
authenticated `Input`. Opaque handles belong to the issuing compilation and
retain their lexical/syntax context, authority, and origin closure. Capture
lookup exposes only the issuing invocation. Decode and authenticate nominal
shape, tokens, groups, fragments, grants, and handles while the root is live;
transfer complete output or failure data to compiler-owned storage, then close
the root and publish only a complete admitted result. Do not retain `Value`,
`ObservedValue`, or its backing allocation beyond the closed owner.

Ordinary evaluator success currently retains root completion in `ObservedHeap`;
its eventual drop is not evidence of the required macro transfer/close ordering.
D0 chooses a bounded completion/decoding interface that preserves both primary
and teardown failures, rather than relying on unobservable drop behavior.

The ordinary `Machine::run_loop` has no general transition limit. The developer
adds an invocation-only evaluator budget at the compile-time entry: charge each
machine control transition, including calls and returns, before it proceeds.
Exhaustion returns a structured expansion resource failure through the same
invocation completion path. It must close the root and preserve teardown failure;
running out of transformer steps cannot skip cleanup. Ordinary runtime entries
retain their current behavior. Syntax-service work, output transfer, and recursive
expansion retain their separate bounded work/storage/depth accounting. Charging
syntax requests alone cannot bound a transformer that makes no such requests.

**Failure/check:** Authored rejection, evaluator/service error, malformed or
foreign/stale handles, transfer failure, and exhausted work/storage/depth budgets
close the invocation and publish nothing. Transfer rejection details before
teardown; if that transfer fails, use bounded host failure data. M10/M11 observe
successful output after root closure and every failure path, including combined
teardown failures. Label injected failure tests separately from actual evaluator
observations. Charge service, decode/output, and recursive expansion work; bound
self-producing syntax without changing source semantics or exposing identity
allocation order. Before C1, run a real checked Ash transformer that recurses
forever without syntax requests: observe transition-budget exhaustion, completed
root close, and no output publication through the public driver. A process
timeout or injected service failure does not supply that evidence. Numeric
budgets remain implementation policy.

### B6: causal origins and reporting

**Producer/consumer:** Parser/expander/service operations retain origins in
`src/source.rs`; resolution/checking/linking/validation preserve them; diagnostics,
`src/message.rs`, `locales/{en-US,bg}.ftl`, and human/JSON consumers report them.
Developer owns producers and consumers together.

**Data/lifetime:** Retain source and construction origins, all causal inputs,
and ordered invocation/definition frames through compiler storage and Core.
Current `Origin` chains/flat span relations are a starting point, not proof of
this contract. The representation must survive copying, relocation, diagnostics,
and image serialization without losing order, causes, or original sources.

**Failure/check:** Keep invalid definition/import/invocation, authored rejection,
host/service/resource/output failure, and ordinary generated-program rejection
as distinct structured causes. Preserve the ordinary reason and facts. M10 and
the invalid production graph assert primary and related locations, nested frame
order, and multi-input branch mismatch in human and locale-independent JSON.
The Boolean-condition example points to `42` with the ordinary Boolean
expectation; it need not infer a DSL-specific role description. Authored text
does not replace compiler-owned localization or semantic facts.

### B7: final compiler program and runtime/build consumers

**Producer/consumer:** Expanded caller → ordinary resolver/checker → linker →
independent Core validators → `driver::execute` and the public build preparation,
image, generated-host, and executable paths in `src/build/`. Developer owns the
connected path; orchestrator owns milestone retention.

**Data/lifetime:** Preserve the checked declaration/grant/private dependency and
source/origin closure as required until packaging; keep macro input/service
state out of the runtime image. The final program contains ordinary checked
runtime code and independently validated metadata. A generated executable
reconstructs the compiler-verified representation under the existing build
contract, without reopening source or repeating dependency body checking.

**Open validator boundary:** `core/validate/source_declarations.rs::syntax`
currently reparses retained original sources without a checked syntax
environment to authenticate declaration coordinates, including resolved effect
summaries. Binder ownership, order, and resource coordinates also depend on
source spans. Macro-bearing source can fail that parse, and copied or generated
binders need independently authenticated coordinates separate from diagnostic
origins. The same reviewer must challenge that validator input and coordinate
strategy before this boundary is claimed connected. It must not replace
independent validation with trusted generated coordinates or repeat dependency
body checking.

**Failure/check:** M09/M13/M14 reject invalid generated type/effect/evidence,
resource/continuation behavior and corrupted retained relations before runtime.
Run the same valid graph through interpretation and the supported real build;
generated runtime needs no syntax-service interpretation. Verify relevant
identity/origin/grant serialization and corruption checks where those facts are
retained. Do not serialize compile-time handles or make image reconstruction
repeat the compiler proof. Runtime completion and build cleanup remain required.

### D0 concrete carriers and calls

These crate-private Rust interfaces freeze the connected handoffs for review.
They are implementation contracts, not Ash semantics. A change to ownership,
admission, or failure behavior returns to the same reviewer. The checkpoint,
header projection, canonical-source census and staged driver compile. The
driver checks each dependency before resuming its importer. A restricted
single-expression-capture template runs through the driver. Syntax contexts,
grants, general matcher admission and the host interfaces remain planned.

```rust
fn parse_module_header(
    tokens: Vec<Token>,
    lexical_diagnostics: Vec<Diagnostic<LexReason>>,
    syntax_budget: SyntaxBudget,
) -> (ParserCheckpoint, SyntaxBudget);
fn project_module_header(
    source: &SourceFile,
    checkpoint: &ParserCheckpoint,
) -> Result<Vec<SurfaceImport>, ProjectionError>;
fn finish_module_from_checkpoint(
    checkpoint: ParserCheckpoint,
    syntax_budget: SyntaxBudget,
) -> (ConcreteTree, SyntaxBudget);
fn source_work_for_sources<'a>(
    sources: impl ExactSizeIterator<Item = &'a SourceFile>,
) -> Result<(TypeWorkBudget, usize), ()>;
```

```rust
struct StagedModule {
    id: ModuleId,
    canonical_path: PathBuf,
    source: SourceFile,
    surface: StagedSyntax,
    dependencies: Vec<ModuleDependency>,
    // Graph ownership, relative edges and traversal state are also retained.
}
struct StagedSyntax {
    imports: Vec<SurfaceImport>,
    span: Span,
    body: ModuleBody,
    import_span: Option<Span>,
}
enum ModuleBody {
    Parsed(SurfaceModule),
    Header(ParserCheckpoint),
}
struct ParserCheckpoint {
    tokens: Vec<Token>,
    lexical_diagnostics: Vec<Diagnostic<LexReason>>,
    position: usize,
    events: Vec<Event>,
    diagnostics: Vec<ParseDiagnostic>,
    pending_recoveries: Vec<usize>,
    recovered_expression_group_boundary: bool,
    nesting_depth: usize,
    resource_failure: Option<ResourceFailure>,
    syntax_work_exhausted: bool,
}
struct HeaderGraph {
    pending: VecDeque<StagedModule>, // dependencies first
    loaded: Vec<LoadedModule>,
    completed: Option<ModuleGraph>,
    entry: ModuleId,
    syntax_budget: SyntaxBudget,
}
fn discover_headers(entry: &Path, roots: &ModuleRoots)
    -> Result<HeaderGraph, GraphDiagnostic>;
impl HeaderGraph {
    fn next_module(&mut self) -> Result<Option<&LoadedModule>, GraphDiagnostic>;
}
```

The still-planned syntax admission extends that handoff without changing its
dependency order:

```rust
fn parse_staged_module(
    module: &mut StagedModule,
    syntax: SyntaxContextId,
    syntax_registry: &CheckedSyntaxRegistry,
    budget: &mut SyntaxBudget,
) -> Result<LoadedModule, LoadGraphError>;
```

`discover_headers` reads and lexes each source once, parses only its fixed
header, discovers canonical edges and owners, and retains the complete token
stream. It executes no transformer. The checkpoint owns the still-open module
event stream, token cursor, diagnostics and recovery state; it borrows no token
slice. Body parsing reconstructs that borrow and resumes the same stream after
checked imports are available. The checkpoint owns its tokens and lexical
diagnostics so it cannot be resumed against another module's token stream.
Header and body share one graph syntax budget; ordinary source and header events
are charged exactly once as before. The staged schedule attributes a refusal to
the source and import edge of the next retained unit. Its source order can differ
from the legacy complete-body schedule, so equal totals and deterministic
attribution do not imply identical first-failure sources. Each staged module's
whole-module span uses its first retained token through EOF, preserving the
implicit region edge's span and its position after explicit imports. The staged
driver parses/projects and checks each dependency before its importer. Matcher
selection, expansion and checked syntax publication remain to be connected.
Before checking, the completed header graph's canonical sources, including
implicit builtins, pay the same `compiler_work::source_work_for_sources` census once.
Carry that ledger and source-size allowance through checking; aliases and
diamonds do not mint source credit. Test overflow/low-budget refusal and
existing reporting/calibration. Body syntax failures retain their source and
import route along with the already-paid partial checking report. Calibration
emits one input record only after every source-authored surface is available;
loading timers measure discovery and body-parsing segments. The driver links the
checked modules without rechecking their bodies. It retains the parsed graph and
sources for diagnostics and builds. Lexical and
header errors remain structured; missing, duplicate, re-exported, or
inaccessible syntax selections fail before importer expansion. Recovery nodes
cannot cross projection.

The public `load_module_graph` remains a syntax-free parsing API for existing
low-level callers; it rejects currently unsupported macro forms and never
supplies unchecked matchers. Macro-enabled compilation will use `compile_path`.
The staged
driver does not call that wrapper. The complete in-tree caller inventory is
reproducible with `rg -l 'load_module_graph\s*\(' --glob '*.rs' src tests`.
The production call is `src/driver.rs::compile_path_with_consumers_internal`;
other `src/` occurrences are test code. `tests/module_loading.rs` inspects graph
edges, ownership, cycles, source and parse failures. The compiler-work and
calibration targets inspect source work. Other integration targets use parsed
modules in isolated resolver, checker, Core, runtime, diagnostic, and
architecture tests, including intentionally statically invalid programs. They
keep the syntax-free wrapper rather than acquiring implicit checking or a
`main` requirement. External low-level callers receive the same limitation.

```rust
struct SyntaxId { compilation: CompilationId, module: ModuleId, declaration: u32 }
struct SyntaxContextId { compilation: CompilationId, index: u32 }
struct SyntaxExport {
    id: SyntaxId,
    matcher: Matcher,
    definition_context: ContextId,
    definition_origin: Origin,
    implementation: SyntaxImplementation, // checked template or global BinderId
}
struct SyntaxSelection {
    export: SyntaxId,
    local_name: String,
    import_span: Span,
}
struct SyntaxContext {
    selections: Box<[SyntaxSelection]>,
}
struct CheckedSyntaxRegistry {
    compilation: CompilationId,
    exports: Vec<SyntaxExport>,
    contexts: Vec<SyntaxContext>,
}
struct SelectedSyntax<'registry> {
    export: &'registry SyntaxExport,
    local_name: &'registry str,
    import_span: Span,
}
fn select_syntax<'registry>(
    registry: &'registry CheckedSyntaxRegistry,
    checked: &CheckedModules,
    context: SyntaxContextId,
    local_name: &str,
) -> Result<Option<SelectedSyntax<'registry>>, ExpansionFailure>;
enum SyntaxNode {
    Token(ContextToken),
    Identifier(ContextName),
    Group(Delimiter, SyntaxSequence, Origin),
    Expression(FragmentId, Origin),
}
struct ContextName {
    spelling: String,
    lexical_scopes: ScopeSetId,
    syntax_context: SyntaxContextId,
    origin: Origin,
    grant: Option<SyntaxGrantId>,
}
fn parse_syntax_expression(
    input: &SyntaxSequence,
    syntax_registry: &CheckedSyntaxRegistry,
    checked: &CheckedModules,
    budget: &mut SyntaxBudget,
) -> Result<SurfaceExpr, ExpansionFailure>;
fn resolve_module_with_expansion(
    module: &LoadedModule,
    dependencies: &[DependencyExports<'_>],
    syntax: SyntaxContextId,
    syntax_registry: &CheckedSyntaxRegistry,
    expansion: &mut ExpansionState,
    budgets: &mut CompilationBudgets,
) -> Result<ResolvedModule, ExpansionFailure>;
```

The compilation-owned registry holds append-only immutable export and context
records addressed by private stable IDs; `CheckedModule` publishes only IDs to
exports checked with that owner. Records reference other records and owners by
ID, not by pointers into a growable checked-module vector. Each lookup
authenticates the compilation, checked owner, export and original import route
and returns only a short-lived borrowed view. Appending another checked module
cannot invalidate retained contexts, and the registry and checked owners live
until expansion and linking finish. The acyclic ID relations create no ownership
cycle. The compilation identity is privately allocated with checked exhaustion;
constructors for these IDs stay compiler-owned. No ID or context is accepted
from a different compilation.

Parsing mixed output consults the leading identifier's context, never a single
caller-wide spelling map. Empty and fresh-private contexts contain no syntax
binding and cannot fall back to the caller. `ContextToken` retains
lexical kind, exact spelling and origin;
it does not reconstruct literals from decoded values. The source parser stores
immutable fragment IDs only after recovery-free parsing. Generated parser input
is a structured token/group/fragment sequence, never text. A protected fragment
is one expression atom. Generated input has its own sequence order: source
spans can overlap or come from different files, so they cannot order that tree
or be joined as one source range. Each generated node has an invocation anchor
for existing structural-span consumers and separately retains its full causal
origin; captured nodes keep their own origins. Diagnostics use the origin, not
the anchor as a replacement for source attribution.

`resolve_module_with_expansion` extends the existing resolver's binding-form
walk instead of running a second scope policy. It establishes actual enclosing
scopes before an invocation. Each retained fragment occurrence gets its own
internal scopes and declaration identities while caller free contexts remain
unchanged. The same namespace-aware table provides scope introduction, unique
most-specific lookup, duplicate detection and final resolution for source and
output. Work remains iterative and bounded. The surface carrier attaches context
and origin to each applicable term, type, constructor, alias, interface and
effect occurrence, not just terms.

```rust
struct SyntaxGrant {
    issuer: SyntaxId,
    declaration: DeclarationId,
    namespace: Namespace,
    access: Access,
    original_route: ImportRoute,
    origin: Origin,
}
fn authenticate_syntax_grant(
    grant: SyntaxGrantId,
    occurrence: &ContextName,
    checked: &CheckedModules,
) -> Result<AuthenticatedReference, ExpansionFailure>;
fn link_syntax_closure(
    modules: &[CheckedModule],
    entry: MacroEntry,
    grants: &AuthenticatedSyntaxGrants,
    budget: &mut TypeWorkBudget,
) -> Result<ResolvedModuleProgram, TypeError>;
```

Grant IDs index a compiler-owned compilation table and cannot be issued from an
Ash value, spelling, origin or captured caller identifier. Authentication checks
the issuing checked syntax export, declaration, namespace/access and original
route before admitting a surviving reference. Linking retains the checked
private declaration and executable closure without importing its name or
definition-site implementation evidence into the caller. A compile-time link
borrows completed checked modules and constructs a separately owned entry and
closure using `SharedModuleLowering` and bounded `copy_checked_fragment`-style
relocation. It retains selected evidence, layouts, cleanup, provenance and
authenticated routes. The final link can still consume the original checked
modules; compile-time linking does not repeat their source checking. An
unchanged validated compile-time entry can serve repeated inputs. Compile-time
and final linked programs each cross independent validation.

```rust
struct InvocationFailure {
    primary: ExpansionFailure,
    teardown: Option<ResourceFailure>,
    cleanup: CleanupStatus,
}
struct ValidatedMacroEntry {
    program: ValidatedEffectProgram,
    transformer: BinderId,
    input_nominal: NominalTypeId,
    result_nominal: NominalTypeId,
    service_effect: EffectId,
}
fn validate_macro_entry(
    program: UnvalidatedEffectProgram,
    contract: MacroEntryContract,
    linked: &ValidatedInterfaceProgram,
    budget: &mut TypeWorkBudget,
) -> Result<ValidatedMacroEntry, MacroEntryFailure>;
fn invoke_checked_transformer(
    entry: &ValidatedMacroEntry,
    input: InvocationInput,
    service: &mut SyntaxService<'_>,
    budget: &mut MacroBudget,
) -> Result<TransferredMacroResult, InvocationFailure>;
```

The independent validator checks the selected monomorphic, unconstrained
`Input -> MacroResult` global, canonical nominal/effect identities, permitted
closed row, generated entry root and linked closure. It returns the private
entry capability only after the normal interface and Core validation. The
machine's dedicated host handoff authenticates one compiler-issued input and
applies it to that validated entry without synthesizing unvalidated Core or
revalidating an unchanged program. Ordinary runtime and image validation keep
their existing entry contract.

The compiler issues the input; service handles carry private compilation
identity, kind and table index, and capture lookup authenticates the invocation.
The compile-time evaluator interprets only canonical `Ops` and default
allocation. It charges a transition before every `Machine::run_loop` iteration
in this invocation only. The decoder authenticates nominal constructors,
handles, origins and grants while the root is live and copies the complete
output or authored diagnostic into bounded compiler-owned staging. It closes
the root inside a disposal-observation scope and returns the transferred result
only if close succeeded. A primary failure and first teardown failure survive
together; failure discards staged output. No `Value`, `ObservedValue`, heap
owner or compile-time handle enters the final runtime program or image.

Origins carry ordered causal inputs and invocation/definition frames, with
bounded clone, traversal and destruction. They reach human and JSON diagnostics
and any retained image representation; today's first flat related-span list is
insufficient. The build consumer remains `prepare_program` followed by
`build_prepared` on the independently validated runtime program.

The working shared lexical vocabulary maps `Wildcard` to `_`, `IntegerLiteral`
to an ordinary decimal literal, `StringLiteral` to an ordinary quoted string,
and `LineEnd` to LF or CRLF. For reserved words, the constructor names are
`True`, `False`, `Fn`, `Let`, `Rec`, `And`, `Type`, `Newtype`, `Effect`, `Match`,
`Perform`, `Handle`, `With`, `Resume`, `Resource`, `Region`, `Using`, `Hook`,
`Register`, `Cleanup`, `Discard`, `Retain`, `Import`, `As`, `Pub`, `Opaque`,
`Interface`, `Impl`, and `Where`; each maps to the corresponding lowercase
reserved spelling. `IntType`, `BytesType`, `StringType`, `BoolType`, and
`UnitType` map to `Int`, `Bytes`, `String`, `Bool`, and `Unit`.

| Constructor | Spelling | Constructor | Spelling |
| --- | --- | --- | --- |
| `At` | `@` | `Dot` | `.` |
| `Colon` | `:` | `Equal` | `=` |
| `EqualEqual` | `==` | `Plus` | `+` |
| `Star` | `*` | `Arrow` | `->` |
| `FatArrow` | `=>` | `Pipe` | `\|` |
| `Bang` | `!` | `Comma` | `,` |
| `Less` | `<` | `Greater` | `>` |

`make_token` requires one exact spelling without surrounding whitespace and
rejects a kind mismatch. Identifiers use opaque handles; parentheses and braces
use groups; EOF, semicolon and declaration-only `$` are excluded. The lexer,
canonical declarations and this table must agree; move the reviewed vocabulary
to the shared language and tool interface documentation at delivery. Rust enum
ordinals are not exposed.

The fixture files under `tests/fixtures/surface-macros/` freeze the D2 graph.
`bind` introduces `temp = 1`, binds caller-supplied `item = 5`, constructs and
matches its owner's opaque `Hidden`, then uses the imported `choose` and `bump`
syntax and its private helper. The caller's `temp = 10` remains the reference in
the captured body. The condition is `true` and the result is 18; the actual Ash
`twice` transformer reads and duplicates
that capture around a constructed `+`, and the caller adds 6, producing `Int`
value `42`. `handwritten.ash` independently computes the same value. For D1,
copy this graph to a temporary fixture, remove only the builtin syntax import
and the `twice` declaration/transformer from `macros.ash`, and use an entry
importing only renamed `bind` that adds 24 to its result. That same
`compile_path`/`execute` route must observe 42 before D2; the stored full graph
remains unchanged for later acceptance. The invalid-condition entry passes `42`
to `choose`; its ordinary Boolean-pattern mismatch must identify that caller
input and preserve the nested expansion frames.

## Production acceptance

Create one fixture family under `tests/fixtures/surface-macros/` and exercise it
from new `tests/surface_macros.rs` and `tests/macro_host.rs`, extending existing
diagnostic and build targets for their consumers. The first developer change
adds a failing driver test for unsupported syntax; do not ignore it or count
that expected initial failure as acceptance.

Freeze these roles and expected observations in D0 before implementation:

| Fixture role | Required observation |
| --- | --- |
| `helpers.ash` | Public helper dependency reached only by the syntax owner; original identity and checked closure retained. |
| `other_dsl.ash` | Separately authored public syntax with embedded ordinary Ash and a negative variant. |
| `macros.ash` | Template plus computed checked Ash transformer, a same-module private helper, own opaque construction case, and imported second DSL. No source `main`. |
| `entry.ash` | Renamed syntax import, caller collision/supplied binder, nested DSL whose dependency the caller does not import, and a simple `Int` observation compared with a handwritten program. |
| Invalid graph variants | Bad condition/branch inputs, missing separator, signature/row refusal, authored/host/output failure, denied private access, missing evidence, and invalid continuation/resource use retain their distinct causes. |

The developer chooses exact accepted Ash source and a fixed expected value
during D0; the reviewer checks the handwritten comparison. The computed path
must read captures and construct an output tree in Ash, not just call a Rust
identity function. A template-only subset must execute at D1. Add the computed
form at D2 to the same driver path, not a second manual compilation route.

Use `driver::compile_path(RunConfiguration { entry, roots })`, then
`driver::execute`, and compare value/type and binder/use evidence. Remove fixture
source files after successful compilation before public build preparation where
the current build tests establish source independence. Use `prepare_program`,
`build_prepared`, and a real generated executable with the shared native-host
cache. Compare its observation with interpretation. Run invalid variants through
the CLI/reporting consumer for human and JSON observations; do not manufacture
those diagnostics solely in a renderer fixture.

Internal parser/scope/grant/handle/validator mutation tests complement the real
graph. Test-only observations must prove selected producer results reach their
actual consumers: checked syntax selection, real Ash body invocation, distinct
Core validation events, publication after close, no publication on failure,
and completed dependency reuse. Keep observations bounded and local to their
owning boundary rather than adding a product tracing facility.

## Ordered delivery

Each step follows the Ash developer workflow: add a focused failing case, run
it to identify the intended missing behavior, implement the minimum connected
change, and rerun the case plus affected callers. Record exact new test names
and filters in TASK-0067 as they are created. Commit only a reviewable coherent
delivery under the authorized Git workflow; do not switch branches with active
readers or dirty work. Full gates occur at C1/C2, not after each local step.

### D0: make the contracts executable

Files: inspect `src/module.rs`, `src/driver.rs`, `src/parser/`, `src/surface.rs`,
`src/resolve.rs`, `src/resolved.rs`, `src/elaborate.rs`, `src/source.rs`,
`src/eval/`, `src/core/validate.rs`, `src/build/`, and current callers. Create the
two macro test targets and fixture family. Update only this task/plan with
confirmed boundary decisions; semantic gaps return to CP-0033.

1. Enumerate existing graph/parser/checker/evaluator/image entry callers and
   record the smallest B1–B7 carrier/signature agreements, owning lifetimes,
   admission boundaries, and failure types. Review the real `compile_path`
   control flow before choosing where to stage bodies.
2. Record the shared public token vocabulary/mapping work and conformance table
   owner. Compile producer/consumer interface changes early; no new macro API
   should depend on Rust discriminants or a guessed public constructor name.
3. Add the public file-graph test and handwritten comparison, then run
   `cargo test -j 1 -p ash --test surface_macros`. Confirm failure is specifically
   unsupported syntax at the real entry. Add focused host lifecycle/admission
   cases as interfaces emerge; no fake transformer can satisfy M03.
4. The same independent reviewer challenges B1–B7, ownership, validation and
   failure/cleanup consumers, fixture observations, and remaining estimate.
   Resolve concrete planning findings before substantial implementation.

Completion: reviewed concrete boundary map, compiling agreed interfaces, pinned
sources/expected observations, useful initial failure, and updated whole-chain
estimate. D0 is not a delivered expression-macro feature or full gate.

### D1: connect a real template path

Files: `src/lexer/{token,mod}.rs`, `src/parser/`, `src/surface.rs`,
`src/module.rs`, `src/driver.rs`, `src/resolve.rs`, `src/resolved.rs`,
`src/elaborate.rs`, `src/source.rs`, validators and focused tests as needed.
Keep exact placement from D0; do not create one Rust module per plan boundary.

1. Add contextual declaration/import and `$` cases, preserving ordinary
   `syntax` globals, token spans, LF/CRLF, and out-of-place rejection.
2. Add fixed-header discovery and checked syntax publication, then wire importer
   body parsing from `compile_path`. Verify cycles/conflicts/unused imports and
   ordinary complete import behavior before expansion.
3. Add restricted matcher recognition, nested stop boundaries, protected capture
   storage, and output admission with token-complete recovery/projection checks.
4. Connect outermost-first template expansion with shared scope policies,
   per-occurrence identities, retained syntax contexts, and definition grants.
   Carry surviving private references and checked executable closure through
   ordinary caller checking, linking, and independent validation.
5. Execute the template subset of the production graph, including private helper,
   caller binder, nested DSL absent from caller imports, and invalid variant.
   Run M01/M02/M04/M06/M07/M08 focused cases and affected existing targets.

Focused targets: `lexer`, `parser`, `modules_syntax`, `module_loading`,
`module_resolution`, `module_elaboration`, `resolution`, `module_visibility`,
and `surface_macros`, selecting targets/cases affected by each change. Expected:
the real template graph passes; invalid cases fail with their assigned structured
causes; unaffected no-syntax regressions pass. Review D1 as connected template
delivery, with procedural and remaining matrix obligations explicitly pending.

### D2: connect the checked Ash host and C1

Files: compiler-owned modules/API recognition in `src/{module,resolved,resolve,elaborate}.rs`,
compile-time entry/link/validation consumers in `src/driver.rs` and Core,
`src/eval/`, shared syntax interchange/expansion storage, `tests/macro_host.rs`,
the same production graph, and the corresponding vocabulary/interface docs.

1. Add canonical Ash data/opaque declarations and `Ops` request wrappers;
   complete the shared token constructor/spelling mapping and versioned
   conformance cases. Include B4's service-result semantics in M02/M04/M10;
   authenticate declarations by canonical origin.
2. Admit exact transformer function types, link already checked helper fragments
   into a compile-time entry without source `main`, and validate the new Core.
   Demonstrate unchanged-program reuse without source rechecking/revalidation.
3. Marshal authenticated input, interpret only the accepted syntax/default
   allocation services, and execute an actual computed Ash transformer. Run B4's
   service-result cases through Ash: deliberate caller capture versus hygienic
   definition/fresh contexts, explicit fragment unwrapping, parse without nested
   execution and preserved `SyntaxDiagnostic`, total indices, empty origins,
   invalid construction, and denied authority.
4. Decode/admit the entire output or rejection, transfer its closure/diagnostic
   data before root close, preserve paired failures, and connect output to the
   same parser/expander used by templates. Add invocation-only transition-budget
   charging in `Machine::run_loop`, with exhaustion using the root-closing failure
   path. Exercise malformed/stale output, and a real checked Ash transformer
   recursing without any syntax request until its budget exhausts. Observe root
   close and no partial publication; retain ordinary runtime evaluator behavior.
5. Run M03/M10/M11/M13 plus D1 regressions through the production graph; compare
   template and computed results. Independently review admission, grants,
   validation, execution, transfer, cleanup, and failure consumers.
6. Freeze C1 inputs and run fresh `cargo xtask verify` with one Cargo job. Record
   complete receipts and review; refresh affected checks after any repair.

C1 completion: both authoring forms actually execute through the graph, new
Core validation is observed, output survives root close, and failures publish
nothing. A nonterminating checked Ash transformer making no syntax requests
must exhaust its invocation transition budget, close its root, and publish no
expansion. The task remains open; C1 does not close M05/M09/M12/M14 or any other
incomplete original criterion. Developer owns the gate, reviewer its audit, and
orchestrator the decision to advance from the verified retaining state.

### D3: finish scopes, diagnostics, reproducibility, and build

Files: existing resolver/checker/evaluator scope consumers, source/origin and
diagnostic/rendering/message catalogs, `src/build/` image/host consumers,
macro tests, `tests/{diagnostic_json,diagnostic_presentation,diagnostic_catalogues,provenance,program_build,program_build_native}.rs`,
and affected current effect/resource/evidence targets.

1. Complete M05's non-term scopes and copied declaration occurrences, and M09's
   ordinary evidence, handler count/order, continuation, resource, and direct
   builtin-import checks. Compare relevant handwritten programs.
2. Complete M10's multi-input causes and ordered nested frames through later
   checking, relocation, human/JSON output, locale catalogs, and retained image
   structures. Keep authored and compiler-owned messages separate.
3. Complete M12 with repeated compilations modulo fresh identity renaming and
   changed matcher/helper/caller/import/interface/semantic inputs. Test actual
   new compilation; do not introduce a persistent cache to test invalidation.
4. Complete M14 through the current interpreted and supported image/build path;
   execute the generated program after source removal. Verify no syntax service
   or compile-time handles are required at runtime and no checked proof is
   repeated by image reconstruction.
5. Audit every M01–M14 row against the original positive/negative scope. Run the
   selected affected tests and native graph, then obtain independent review of
   the full connected path. Keep C2 regression verification pending.

Completion: all cases have reviewable evidence mapped to exact targets/pins;
runtime/build/diagnostic consumers pass their focused checks. Component evidence
awaits final checkpoint verification and retained acceptance.

### D4: specification, product checkpoint, and milestone retention

Files: affected `spec/{README,lexical-structure,syntax,name-resolution,static-semantics,elaboration,dynamic-semantics}.md`,
a syntax-expansion chapter only if needed, `docs/tools/ash.md`, accepted
decision/design implementation-status wording, executable spec examples,
task acceptance, and proposal/plan lifecycle cleanup.

1. Update specification and tool docs with the implemented semantic delta and
   canonical interface/vocabulary only. Keep broader DN-0062 alternatives
   informative. Verify source examples and positive/negative tests with their
   owning implementation delivery; do not postpone known spec drift to closure.
2. Resolve final reviewer findings. Run Markdown/link/anchor/status/authority
   checks, affected source examples, diagnostic catalogs, and the complete
   interpreter/build graph. Freeze source/configuration and artifacts.
3. Run fresh C2 `cargo xtask verify` on the pinned candidate and retain its
   receipt/logs. The same independent reviewer verifies full required evidence,
   including acceptance/failure/cleanup consumers and all M01–M14 obligations.
4. Complete the authorized product checkpoint and transition cleanup: remove
   CP-0033 only when implementation, tests, specification, review, and verification
   have been retained together; remove this plan when TASK-0067 finishes. Check
   links after cleanup and refresh evidence affected by changed verification
   inputs. Do not claim Main semantics from branch-local specification updates.
5. Orchestrator integrates the released clean checkpoint into
   `integration/expression-macros` with the workflow's explicit merge commit and
   verifies the combined retaining result using the same checkout/cache. Supply
   retained commit and verification receipts to the developer, who prepares,
   applies, and reads back acceptance; reviewer audits and orchestrator confirms
   it before closure/next work. No Main merge, signing, or unrelated cleanup.

Completion: retained product result and full M01–M14 acceptance, with reviewed
spec/tool docs, graph/native evidence, full gate and integration verification,
artifact cleanup, and next owner recorded. Main integration remains outstanding
until its separate authorization. If later inputs equal C2's frozen inputs, its
full gate may serve the pre-Main gate without a duplicate identical-input run.

## Estimate and re-planning

After the introduced resource and region graphs, the provisional forecast is
**about 7.9 additional Codex elapsed hours**, with a tentative **6–13 hour**
range. At 01:03 Sofia time on 6 November, 55.5 reviewed and 0.5 provisional
weighted points over about 10 elapsed hours, including setup, inform the
midpoint. Review can change the provisional credit. The range is
not a confidence interval. It is a whole-chain estimate, not a deadline or
a measured model-runtime total; independent review may revise it.

| Remaining connected work | Codex elapsed hours |
| --- | --- |
| Remaining Ops, vocabulary, output forms, transfer failures, and limits | 2–3 |
| Complete contexts, copied identities, grants, and Core coordinates | 2–5 |
| Diagnostics and actual image/build/native path | 1–3 |
| Remaining evidence, docs, gates, review, and retained acceptance | 2–3 |

The ranges include about 1–3 hours of command/gate time and 1–2 hours of
review/correction; they overlap in the chain and are not separate forecasts to
add again. External waiting and separately authorized Main integration are
excluded. Assumptions: one product writer/build operator, compatible warm cache,
current checker/linker/evaluator reuse, no effects redesign or extra output
category, and no new ownership/validator architecture contradiction. Such a
contradiction requires a new forecast and a recorded plan change.

Git commit spans provide the available calibration: boundary checkpoint
`f791b95c` at 15:42:37 to reviewed template repair `26b43869` at 18:57:59 is
3 hours 15 minutes. The preceding accepted-design-to-boundary span is about
38 minutes, giving about 3 hours 53 minutes including setup. Early retained
increments took 20–27 minutes, the connected template increment about 64
minutes, and its repair about 10 minutes. These are elapsed proxies containing
coding, tools, review and waiting, not exact model compute time; that is unavailable.

[TASK-0067's weighted ledger](../tasks/TASK-0067-expression-macros.md#weighted-delivery-progress)
sets fixed effort-weighted delivery credits, with an agreed 20-point reviewed
baseline supported by retained results and their review. That is a delivery
estimate, not a measured fraction of model effort; it is not derived from the
forecast and does not move when the ETA changes. The observed session pace is a
calibration check only. The additional 8 reviewed credits at `ad8ca9cc` record the canonical module,
checked entry, partial host/output and frozen combined graph; they do not claim
a complete procedural host or borrowed-owner acceptance. The ledger changes no M01–M14 acceptance requirement. Its remaining
weights favor unresolved contexts/grants and consumers; implementations and their
negative/transfer/mutation evidence receive disjoint credit.

Use that ledger's small observable increments for requested half-hour reports,
including honest zero-credit investigation and actual-versus-estimated elapsed.
The first real checked `twice 21` and frozen combined graph both produced 42
about 33 minutes after the reviewed template checkpoint, faster than the prior
1.5–4 hour hypothesis. Re-estimate after repeated repairs or changed interfaces. Keep confirmed findings in the task and use the same reviewer
to challenge a stalled path. Do not add tests, benchmarks, or gates solely to
produce progress points or timing data.


## 2026-11-06 remaining-scope amendment

This section updates only work still outstanding. Earlier checkpoint descriptions,
weights, evidence, sketches and estimates remain historical records; they do not
require the removed implementation to be restored. The amended
[CP-0033](../proposals/CP-0033-hygienic-expression-syntax.md) and
[first-slice design](../design/macros/first-slice.md) govern the remaining work.

- Definition-context references use compiler-issued contexts and ordinary
  resolution in the checked defining environment. Checked facts and executable
  dependencies survive linking. Separate post-resolution per-reference grant
  records, their link rechecks and their grant-specific mutation tests are removed
  from the outstanding work. Private and opaque access, original public import
  routes, caller isolation and ordinary independent Core checks remain required.
- Template bodies are parsed for syntactic validity at definition time. Their
  literal free names resolve in the defining environment when expanded; an
  unused unresolved name is not an error. The caller cannot supply or redirect
  that name. Captures and introduced binders retain their contexts. Transformer
  `using` targets and ordinary imports keep their existing admission checks.
- M06 and M10 exercise source access, contextual behavior, origins and handle
  isolation rather than a grant object. M13 retains checked-dependency reuse and
  independent new Core validation, including existing scope, type, coordinate
  and provenance refusals. The other M01–M14 and C1/C2 obligations remain open.
- Completed checkpoints, their evidence and original weights are not altered
  by this scope change. The historical estimates above are not a current ETA.
  The task records the remaining-only reconciliation and additional corrective
  work separately.

The remaining-only estimate preserves the original 38.5 uncredited points and
removes one point of grant-object and grant-only mutation work. It does not
remove privacy, route, closure or ordinary validation obligations.

| Remaining package | Original points | Current points |
| --- | ---: | ---: |
| Context, hygiene and definition access | 4.5 | 3.5 |
| Canonical API and checked entry | 3 | 3 |
| Services, transfer and lifecycle | 9 | 9 |
| Graph, Core and reproducibility evidence | 6 | 6 |
| Diagnostics | 2 | 2 |
| Supported image/build evidence | 3 | 3 |
| Specification and tool documentation | 4 | 4 |
| Review, gates and milestone retention | 7 | 7 |
| **Remaining** | **38.5** | **37.5** |

The task separately records about 30 points of additional performed corrective
work, estimated from disjoint session/receipt intervals and the previously
recorded checkpoint pace. The original 61.5 reviewed points are unchanged;
the resulting 91.5 of 129 is an effort-accounting index, not feature or
acceptance completion. Removed work is not counted as a finished requirement.

The current connected-work scenario totals **about 4 hours 51 minutes** of
session elapsed time:

| Remaining work | Estimate and basis |
| --- | --- |
| Pattern/scrutinee diagnostic repair | 60 minutes; the earlier match, application, and origin/stack changes took about 24, 10, and 57 minutes between their checkpoints. |
| Evidence reconciliation and uncovered cases | 90 minutes; inspect existing bridge/input/handle contrasts (M10), paired active-failure disposal (M11), changed-input and repeat cases (M12), and API/version/image evidence. Add only missing discriminating cases. The timing and negative-control changes took about 19 minutes. |
| Specification, API, `TokenKind`, and tool documentation | 75 minutes; a working estimate without a clean isolated documentation analogue. |
| Independent review and corrections | 30 minutes; earlier partial verdicts took about 1–8 minutes, while this review covers more. |
| Fresh C2 gate | 16 minutes, based on the 940.57-second full gate at `6b72d2de`. |
| Native refresh, retention and acceptance readback | 20 minutes. |

This is a scenario based on the current known work, not a deadline or measured
active runtime. If evidence exposes a new producer defect, re-estimate that
work. External waiting and separately authorized Main integration are outside
the scenario. The task's separate point-rate calculation gives **about 6.8
hours** for 37.5 points at 5.55 points/hour; it is a low-confidence mechanical
comparison, not an added buffer or a confidence interval.

## 2026-11-06 operational update, 20:34

This table supersedes the earlier remaining-time scenario. It records one
connected delivery path in elapsed session minutes, not new point credit or
measured active time. Completed evidence and the original weighted history
remain unchanged. Estimates are conditional on the listed investigation
finding no additional producer defect.

| Work | State and owner | Previous / remaining minutes | Actual event or remaining outcome |
| --- | --- | ---: | --- |
| O01 Pattern/value diagnostics | Reviewed; Dev and Rev | 60 / 0 | The 19:12:28–19:48:04 checkpoint produced `a3f6650b`; P30 and P31 each gained 0.25 as recorded in the task. |
| O02 Combined graph and copied uses | Reviewed; Dev and Rev | Not separately estimated / 0 | The 19:48:04–20:21:02 checkpoint produced `6216692f` and `cb9d8963`; P10 and P27 each gained 0.5. |
| O03 Finish specification, API and tool candidate | Active; Dev | 30 / 30 | Complete the current draft, verify its examples and links, and hand it off. Host-request totality is already included in O04, not charged here. |
| O04 Host input and output boundary evidence | Demonstrated; Dev, review pending | 25 / 0 | The real source fixture passed at 20:20:16; the private host identity test and 43-case host suite finished at 20:34:13. Review is included in O09. |
| O05 Active-machine disposal failure | Remaining; Dev and Rev | 25 / 25 | Investigate the existing disposal hook and distinguish an observed refusal from ordinary active-root destruction. Re-estimate if a producer repair is demonstrated. |
| O06 Repeat and changed-input evidence | Remaining; Dev | 30 / 30 | Compare repeated compilations and discriminating caller, matcher, helper, import and interface changes. |
| O07 Remaining acceptance evidence | Remaining; Dev and Rev | 25 / 25 | Reconcile M01–M14, Core and image assertions, adding only demonstrated missing controls. |
| O08 Status and documentation checks | Remaining; Dev | 15 / 15 | Reconcile implementation status, authority, links and executable documentation after the candidate is complete. |
| O09 Independent whole-path review and corrections | Remaining; Rev and Dev | 25 / 25 | Review the connected candidate and repair concrete findings; O04 does not add a separate review allowance. |
| O10 Fresh final gate | Remaining; Dev | 16 / 16 | Run one complete gate after prerequisites; the `6b72d2de` gate took 940.57 seconds but predates later source changes. |
| O11 Retained handoff and acceptance readback | Remaining; PM, Dev and Rev | 20 / 20 | Verify the retained input and evidence, apply acceptance updates, and complete any separately authorized milestone merge. |
| **Remaining scenario** | | **186** | **About 3 hours 6 minutes**, excluding external waiting and any newly demonstrated repair. |

The 19:12–19:48 and 19:48–20:21 windows include review and tool time; they do
not measure exclusive active work. O04's source receipt is
`/tmp/ash-acceptance-host-requests.log`. Its final identity and host-suite
receipts are `/tmp/ash-acceptance-host-identity-final.log` and
`/tmp/ash-acceptance-host-suite-final.log`. O04 is demonstrated but has no
reviewed-point increment yet. Update this table when a result, review, or
re-estimate changes the remaining path; do not infer a time forecast from the
historical point conversion.

### 20:42 active-disposal investigation update

O05's first investigation ran from approximately 20:37:00 to 20:42:18,
including tool time. The real transformer reached its post-construction
service request and dropped an active root after exhausting work, but made no
disposal-worklist growth attempt; the injected refusal remained armed. The
probe and receipt are retained in the task. This establishes no paired
failure and earns no reviewed credit. The intentionally failing probe was
removed from the candidate.

The remaining O05 work is a bounded 20-minute review of the existing common
disposal and failure handoff, replacing the 25-minute investigation allowance
above. The resulting scenario is **181 minutes**, conditional on that review
and other evidence finding no new repair. Four existing owning-boundary tests
have since passed; the task records their separate observations. A new
producer defect, if found, requires its own estimate rather than an assumed
completion here.

### 20:47 documentation and disposal handoff

O03's specification and tool candidate is complete for independent review:
its runnable example returns 42, the host suite and vocabulary checks pass,
and the local-link and Clippy checks pass. Its 30-minute implementation
allowance is now zero; status and authority cleanup remain in O08.

O05's owning-path investigation is also complete for review. The transformer
and ordinary evaluator use the same disposal-scope failure handoff; four
existing tests pass across active-root destruction, actual refusal, and
primary/teardown reporting. These are compositional observations, not one
injected refusal in an active transformer. Its remaining 20-minute
investigation allowance is now zero. Review of both handoffs remains in O09;
no reviewed points or M11 closure are inferred here.

The conditional remaining scenario is **131 minutes**: O06 30, O07 25, O08
15, O09 25, O10 16 and O11 20. This remains an elapsed-work estimate and must
be updated if review or an acceptance check identifies additional work.

At 20:49, review found that the first wrong-nominal host test also lacked the
required output payload. The corrected test first transfers a valid output,
then changes only its outer nominal owner and observes refusal. The focused
unit, 43-case host suite and refreshed Clippy pass. This correction
is part of the existing O09 review-and-findings allowance, not a new point
credit or an additional forecast item.

At 20:55:33, independent review cleared `7ae26e76`. O03 and O04 are reviewed;
O05's shared disposal handoff is reviewed as compositional evidence, without
claiming one injected refusal in an active transformer. The task records the
six disjoint point increments. The remaining 131-minute scenario still
includes the whole-path review in O09, the outstanding status work, and the
fresh gate; this partial review does not close M11 or C1/C2.

### 20:59 reproducibility handoff

O06 is demonstrated and awaits review. The two-compilation comparison checks
the existing copied graph's observed shape and binding relationships with fresh
identities; caller, matcher, helper, imported syntax and interface changes
produce the expected updated result or ordinary rejection. The three focused
tests and their scope are recorded in the task. Its 30-minute implementation
allowance is now zero; review remains in O09. The conditional remaining
scenario is **101 minutes** (O07 25, O08 15, O09 25, O10 16 and O11 20).
No new point credit or M12 closure is inferred before review.

At 21:02, review identified that the first repeat check unnecessarily
compared raw identity and Core node allocation order across compilations. The
revised check repeats the existing per-copy use assertions and compares
source-relative ranges and result type instead. All three focused tests pass;
this refinement remains within O09's review allowance.

### 21:06 remaining-work inventory

The 101-minute figure is a conditional known-work scenario, not a calibrated
completion forecast. O07 must inventory all 32 unearned original-scope points
and the still-open M01–M14/C1–C2 obligations against actual evidence; any
missing work needs a named estimate before the full remaining chain is known.
The 25 minutes in O09 are a fresh estimate for the remaining whole-path review
and known corrections, not a measurement of review time already spent. Actual
event windows above are kept separate from these remaining estimates.
Clippy also identified a complex tuple in the repeat test; flattening the
test observation to a fixed array resolved it, and the focused tests and
Clippy now pass. That correction is within O09's existing review allowance.

### 21:09 reviewed reproducibility and measured windows

Independent review cleared `787f5ef5` at 21:09:00 and accepted the two P29
increments recorded in the task. O06 changes from demonstrated to reviewed;
its implementation allowance was already removed, so the 101-minute
known-work scenario is not reduced again. O07 must inventory the remaining
obligations before that scenario can be treated as a complete forecast.

The observed session windows were O01, 19:12:28–19:48:04 (about 35 minutes
37 seconds); O02, 19:48:04–20:21:02 (about 32 minutes 57 seconds); the
combined O03/O04/O05 work, 20:21:02–20:55:33 (about 34 minutes 31 seconds);
and O06, 20:52:46–21:02:51 (about 10 minutes 4 seconds). O06 overlaps the
previous window. These elapsed windows include tool and review time and are
not added together as exclusive active work. Only the 16-minute O10 gate
estimate comes directly from a comparable complete gate; the other remaining
minutes are planning judgments.
