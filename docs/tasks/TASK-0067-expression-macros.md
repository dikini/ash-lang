# TASK-0067: Expression Macros

- ID: `TASK-0067`
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

### Shared syntax path checkpoint

The previously reviewed macro adapter enumerated supported language forms in
`validate_template` and `substitute`; the procedural projector also accepted
identifier fragments only under selected parent kinds. It rejected ordinary
valid expressions before the existing compiler could check them. In
`/tmp/ash-macro-common-path`, handwritten cleanup returns 42 while the equivalent
template fails; `/tmp/ash-procedural-region` shows a checked transformer whose
fresh-identifier region output fails before ordinary checking. These examples
are acceptance cases for the common path, not new cleanup or region rules.

The current candidate changes the handoff:

1. The module projector retains a balanced template as an immutable
   `MacroOutputNode` sequence from `capture_contents`. After dependency syntax
   selection, definition admission instantiates it with category-marked dummy
   captures and parses it through the ordinary output parser before resolving
   module bodies. The existing name-only resolver reuses that parsed value.
   The checked export retains the sequence and owner without re-lexing source
   or rerunning a dependency body.
2. One instantiator maps template `Splice` nodes to the selected immutable
   expression or identifier capture, adds the issued introduction to literal
   identifiers, and preserves token spelling, groups, contexts and origins.
   It produces the same structured node vocabulary as a checked transformer.
   Captured syntax is not retagged. Nested invocations remain outermost first;
   discarded nested captures must not execute.
3. `parse_macro_expression` consumes either producer. Its ordinary parser and
   projector recover each original `SurfaceName` through one token-index
   metadata lookup, including binder, pattern, type and effect positions.
   Expression fragments stay protected expression atoms and are rejected in
   identifier positions; a valid identifier is not rejected because its parent
   is a particular language form. The parent-kind whitelist and the form-by-form
   template substitution have been removed. Complete propagation of invocation,
   construction and captured-input causes through diagnostics remains pending.
4. Existing `Resolver::resolve_work` and its `ResolveTask` scope operations
   own lexical ordering and ordinary name resolution. The expansion handoff
   preserves the lexical context active at each invocation, including for
   `caller_identifier`. An owned replacement is resolved synchronously while
   the ordinary resolver's scopes are active. No borrowed reference to that
   replacement is stored in an outer task buffer. A structural-depth guard
   bounds nested expansion; it is restored on success and failure.
5. After lexical lookup, an introduced definition-context name may consult
   only its compiler-issued checked syntax owner and exact checked import route;
   fresh contexts have no owner fallback. It retains the existing original facts,
   private closure, opacity and caller-selected evidence. Origins describe
   causes and never grant access. The current resolver's name-only template
   admission rejects unused direct missing names and wrong splice kinds, defers
   nested syntax captures without running transformers, and admits unused valid
   cleanup and private owner references.

The candidate runs both invoked and unused cleanup templates, a checked
transformer's fresh-identifier region, an active caller-scope lookup and a
finite nested expansion to 42. A self-reproducing transformer fails with the
existing `internal.resource.structural-depth` reason. The driver regressions,
including protected/grouped captures, owner access, effects, resources and
unchanged 256 KiB stack controls, pass 113 cases:

```text
cargo test -j 1 -p ash --test surface_macros --test macro_host \
    --test local_newtypes --test cleanup_syntax --no-fail-fast -- --nocapture
```

Receipt: `/tmp/ash-common-shared-path-regressions.log` (SHA-256
`2c0b88e9688bdc363ae5068b69b6540fdd25b6663da7c652315695f3b13630c1`).
The independent Core mutation checks pass three cases with `cargo test -j 1 -p
ash --lib generated_local_ -- --nocapture`; receipt
`/tmp/ash-common-core-mutations.log` (SHA-256
`25fc90d83e4a94f99ceadd899e6271633f0188f5c73e9793cb5835f19571e0a9`).
The focused construction test rejects procedural or captured tokens as proof
of literal template construction (`/tmp/ash-common-proof-final.log`, SHA-256
`d2d2ead894a19818b9363d3650711e8ba17175e8af1bc670179c2d1269b4d26a`).
Existing source-origin and local-scope mutation checks also pass
(`/tmp/ash-common-source-origin-final.log`, `/tmp/ash-common-scope-final.log`).

Independent review of `df1cbeb5` found that the expansion-depth failure discarded
its invocation and definition locations. The repair uses the existing syntax
resource failure and retains both locations in human and JSON output. The real
self-reproducing transformer test failed before the repair with no labels
(`/tmp/ash-depth-location-before.log`, SHA-256
`354e28183847cc433a51bbef9ce83bcab69bc7e521a97f386231c16c48d5a75d`)
and passes after it (`/tmp/ash-depth-location-after.log`, SHA-256
`5eb287a3834eefa80b34ef237e690671b85ee7c7801ea4fef7201abc644e05d7`).
The affected driver suites pass 86 cases
(`/tmp/ash-depth-location-regressions.log`, SHA-256
`12edfa036a63cef0ad03abebbf29ed39d22e2932d94266466b6b735740539cea`).
Direct CLI receipts are `/tmp/ash-depth-location-human.log` (SHA-256
`c86c4d296605eb7e74bf14a8eba9f9b029e25c53021cce62bc71d75c466561d6`)
and `/tmp/ash-depth-location-json.log` (SHA-256
`b4ffd8515c6bd8ce5c2acc16a0d69fd1249a9bd37a21d489e59c8aff6cba767c`).
The repair was independently re-reviewed at `98ecab03`. The reviewed
`57ce1f1f` observations remain evidence for that pin, not automatic credit for
the changed path.

The next candidate gives generated type occurrences their actual invocation
extent when no literal-template construction extent exists. A real transformer
now constructs and matches a fresh local `Token(Int)` while its captured caller
expression uses a distinct caller `Token(Bool)`; a caller-supplied nominal name
also binds its captured body. Both graphs return 42, and the fresh constructor
does not escape to caller source. The revised projection check verifies the
occurrence extent and still rejects a captured identifier when literal-template
construction proof is requested (`/tmp/ash-procedural-newtype/projection-proof.log`,
SHA-256 `ab1acc0ea0c0cd7f419a638285780d32e10488e7731edbaff68f56b106c5565a`).
The four affected suites pass 114 cases
(`/tmp/ash-procedural-newtype/regressions-final.log`, SHA-256
`4b9680c8a8f57b6d3928f1a6b7781819d742d9d90f0f15dff26256f95876aeec`),
and the existing generated/local Core mutation checks pass
(`/tmp/ash-procedural-newtype/mutations.log`, `source-origin.log`, `scope.log`).
Independent review cleared this candidate at `e1780327`. At that pin, a real
procedural newtype with two type parameters still fails the ordering check
because both parameter causes are the same invocation span; parsed occurrence
order is still needed. A generated declaration whose name is captured carries a
`Source` invocation anchor rather than complete expansion provenance. At that
pin, template splices in local nominal and constructor name positions were still
rejected by the definition parser.

The next candidate retains balanced template contents and parses their
placeholder instantiation before any module body expansion. An identifier
capture can now name both a local newtype and its constructor: the real driver
graph executes to 42. Expression captures and lowercase actual identifiers are
still refused in those positions. Malformed unused templates, including one
with an imported nested matcher, fail before body expansion. The public
`parse(lexed)` API retains balanced template contents; context-free projection
checks their placeholder syntax, while the production driver uses selected
matchers. This does not claim parser-recovery parity or full validation of
imported syntax through the context-free API.

Literal-only declarations keep their definition construction extents. A
declaration containing captured syntax instead uses the invocation extent,
without treating captured origins as literal proof. Existing Core checks remain
unchanged. The original driver reproducer failed before this change
(`/tmp/ash-template-newtype-before.log`, SHA-256
`ec5d9da2affeee1eb1a953b761d9becf5bec29eb727fd4a6f41d344fb163c17d`).
The affected driver, host and module suites pass 115 cases
(`/tmp/ash-template-shared-pin-regressions.log`, SHA-256
`d7ef0739c52ac4feb322c3ac11d1f413529642fe7ab3fdb63e6d33f191742fcb`).
Focused generated-Core mutations, construction and admission checks, plus
local-newtype and cleanup suites pass 33 cases
(`/tmp/ash-template-shared-pin-core.log`, SHA-256
`3129ae8812b35dbad5064475a04c01a1d2f158b992df4a7a955f17c29bf8dbb7`).
Independent review cleared this candidate at `e9c42975`. At that pin, captured
names used only as type or effect references remained open.

The next candidate admits an issued identifier capture as a plain or applied
type name, an effect name, or an operation selector. Actual expansion uses the
ordinary caller or checked-owner lookup. Real driver graphs using a caller-local
`Token`, caller `Box<Int>`, caller effects, and a private owner effect under a
same-spelled caller effect all return 42. Definition admission still rejects
unresolved literal type arguments and operands. Actual output still rejects
wrong initializer types, missing operations, wrong handlers and direct caller
access to the private effect. Admission's temporary identifiers are cleared on
both success and failure.

The six affected driver, host, module, local-newtype and effect suites pass 198
cases (`/tmp/ash-template-captured-categories-pin.log`, SHA-256
`9ca1d7288aa33cd2543ab0f1383112d6d8b2aa2c839c2146c2a4364337253bf3`);
the admission-state isolation test also passes
(`/tmp/ash-template-captured-categories-pin-isolation.log`, SHA-256
`9db7242c45f341b4fe61785ccd7c4298a368d368b6251d5daaf301bef94cad14`).
Independent review cleared this candidate at `9f142555`. Qualified captured
names, other handler and row positions, generated multi-parameter ordering,
and complete expansion provenance remain open.

A lowercase identifier supplied for a template-generated newtype now retains
the ordinary parser's `parse.expected-form` rejection instead of reporting an
internal resolver error. The real CLI's human and JSON output identify the
captured identifier, invocation, and selected definition; the prior focused
run failed (`/tmp/ash-template-output-cause-before.log`, SHA-256
`bcfbb88acd0c542c6063f65013cc5c6238fe4e8482a0f5eb21bc9973c4393c5d`). The
surface macro, host, and JSON diagnostics suites pass 94 cases
(`/tmp/ash-template-output-cause-regressions.log`, SHA-256
`d91850bbd2f537a5306026fec930f378cae43237688a705aae82fedc8a0fabf9`).
After `cargo build -j 1 --bin ash`, running `target/debug/ash` on
`tests/fixtures/surface-macros/template-newtype-capture/lowercase.ash` with
and without `--message-format json` produced
`/tmp/ash-template-output-cause-pin-json.log` (SHA-256
`ae1b56eb532e08db2a2c4076a9c9111d52ac495c2489038fdeb4b80c0a5a571c`)
and `/tmp/ash-template-output-cause-pin-human.log` (SHA-256
`cc8d8649729763f8ba148e88a831e0bf9756f26d469e3b15e793795c8ab061ce`).
Projector-invalid output and complete causal expansion diagnostics remain
open. Independent review cleared this diagnostic change at `7f9abc16`; it adds
no ledger credit.

A caller-captured identifier can also select the effect handled by generated
syntax, or an operation clause of the syntax owner's private effect. Both real
driver programs execute to 42. The original admissions rejected their temporary
identifiers (`/tmp/ash-macro-captured-handler-before.log`, SHA-256
`b341e1b77fdc69b493ad46b9059cbfba4968672bbf13377adc12507d44398bb1`, and
`/tmp/ash-macro-captured-handler-operation-before.log`, SHA-256
`a3309929b0072dd240288ac61d122ef045dd7f2a854ce10b0db8d5a48503c455`).
Missing literal names in the handled expression, store, clause, type arguments,
and known-effect operations still fail; an unknown actual selector also fails.
The macro, effect, and cleanup suites pass 160 cases
(`/tmp/ash-macro-captured-handler-pin-regressions.log`, SHA-256
`ee8eae6e5b378c7faa3188835e8e7d76a211adf42a7f7e2f6e84594830bb4936`), and
the temporary resolver-state isolation test passes on success and failure,
including active and retained continuation state
(`/tmp/ash-macro-captured-handler-pin-isolation.log`, SHA-256
`4cd41b4e4644a4762063cc73ab2ab73abec0cfb989665159b8e3c8efaaae63c7`).
Independent review cleared this handler change at `1a6149d5`; it adds no ledger
credit.

A checked procedural transformer now emits and uses a two-parameter local
newtype. The real driver returns 42 for the generated declaration, for two
copies of the same captured invocation, and for two separately fresh
parameters both spelled `A`. Reusing one identifier for both parameters and a
handwritten `A, A` remain duplicate-parameter errors. The original generated
graph failed Core's source-span ordering check
(`/tmp/ash-procedural-pair-before.log`, SHA-256
`05f6bf121e75cd01d1f9742032e1a8d5f9b65d7ac327d58904063d29ac6fa009`).

The ordinary projector now retains the actual parameter occurrence order;
the existing resolver binds it to the generated owner and parameter IDs.
Independent Core compares that record with the original checked module group,
then retains the same immutable authority through identity and fold rebuilds.
The focused test checks the copied identities, donor and row mutations, a
fresh builder without authority, and a coordinated removal plus source-origin
downgrade at both initial linked and public unlinked validation. The previously
unprotected downgrade was accepted
(`/tmp/ash-procedural-pair-downgrade-actual.log`, SHA-256
`396c712f9af46a9a2ba6e4e231ed3eda94ada6db2bcdd77cf556bfe0ea91c0ac`).
It is now refused in
`/tmp/ash-procedural-pair-linked-final.log` (SHA-256
`0024adfdf2270e96bb40c379b326b92f12b15de4ac227767fe8bd930ebdd39ae`).
The four affected driver and language suites pass 122 cases
(`/tmp/ash-procedural-pair-regressions-final.log`, SHA-256
`4dcd5fa8914ff192cebb9b4a83bb4d7dde29001f617cf4ef829902087cdebeab`);
three existing generated-local checks also pass
(`/tmp/ash-procedural-pair-original-mutations.log`, SHA-256
`9664b0964f22ad1d858cd61a978b507f303d9010a1d3bb1122487c58b4b920c0`).
Independent review cleared this batch at `96fa725e`; it adds no ledger credit.
Captured-name expansion provenance and the native local-newtype image boundary
remain open.

An injected root-close refusal exposed a failure handoff bug: the real driver
replaced a transformer-authored rejection with `syntax.transformer-failed` and
lost the rejection (`/tmp/ash-transformer-teardown-paired-red.log`, SHA-256
`07d8736ff3c9c65f14ff96211fec6f1982d2d3b64b49683c89db0e7e8f2c5a3b`).
The first attempted injection used zero-sized work items and did not actually
trigger the failure; its passing result is not evidence. The corrected test
uses the existing disposal refusal path at root close. The repair retains an
authored or parser rejection together with the first teardown failure, and the
existing human, short and JSON diagnostics report both. A successful expansion
is withheld when close fails. A normal checked transformer is observed closing
its root before the compiled output executes to 42. The targeted driver and
presentation test passes in both locales with `cargo test -j 1 --lib
transformer_closes_root_and_preserves_rejection_on_teardown_failure --
--nocapture`
(`/tmp/ash-transformer-teardown-final.log`, SHA-256
`69eec7daac5be0f7f9cc4d7f76477ae5a24ebcb6f8f6c4580b67675ff0707d41`).
`cargo test -j 1 --test macro_host --test surface_macros --test diagnostic_json
--test diagnostic_catalogues --test diagnostic_rendering` passes 105 cases
(`/tmp/ash-transformer-teardown-regressions.log`, SHA-256
`64bb9436663ec09c68f16839081fddf6da036e07e585a5fec3730a9e517cf77a`);
`cargo test -j 1 --lib root_completion_ -- --nocapture` passes five existing
root-completion checks
(`/tmp/ash-transformer-teardown-root-regressions.log`, SHA-256
`2c8ff24eae37b8ebaf5722c3ba466ce60588dc92bc7cac8674ba62713a6e4866`).
Independent review cleared this batch at `93c0aa04`. The failure injection is
test-only; observing root closure for all other failure paths remains open.

A real transformer returning nested groups overflowed a normal test thread
during output transfer (`/tmp/ash-transformer-failure-roots-isolate.log`,
SHA-256 `84fb4a22b2dbd4e23372b18f5eddbdc992ba8cf74eba8a51f69d738d2e0ebbd2`).
Transfer now walks those groups with an explicit stack. A driver fixture
completes a depth-128 sibling, then refuses a deeper sibling, disposing the
partial output; another transfers nested groups and siblings through both
`parse_expression` and final output, then evaluates to 36. The existing
no-service divergence and an Ops failure leave active root records whose
machine-owned storage is dropped before the driver returns. A transfer failure
reaches the completed-root close; an injected refusal there retains both the
transfer cause and teardown failure. These observations pass with `cargo test
-j 1 --lib transformer_ -- --nocapture` (two tests,
`/tmp/ash-transformer-lifecycle-stack-final.log`, SHA-256
`87f5355cea627428e8b838406249161d018cd767035dcd9cc45f1ae80a1aa970`)
and `cargo test -j 1 --test macro_host --test surface_macros` (96 tests,
`/tmp/ash-transformer-transfer-regressions.log`, SHA-256
`c47b9abb7de7e2d9e2d87c349a46fe3bf8f5d93b435a258a0bf671f93aad4c97`).
This batch awaits review. An attempted completion-root injection on an active
failure did not reach that completion-only hook; a separate active-disposal
worklist injection did not encounter a worklist allocation. Neither establishes
paired active failure and teardown preservation, which remains open (respectively
`/tmp/ash-transformer-active-root-paired-red.log`, SHA-256
`73e41daa7e69fb469fe4b8b03151a1d1a4cc620915d413cf0797a218d8872c6f`, and
`/tmp/ash-transformer-active-closure-forest-probe2.log`, SHA-256
`e38972e47b54dbc7213cd50cbee35f5e67b9ad8b12ebad72fd91388ba11a32f6`).

The previously supported combined macro graph still builds with public
`ash build` after this rewrite and returns 42 after its four copied Ash sources
are removed (`/tmp/ash-macro-common-native/build.log`, SHA-256
`06da86579f973c802a59d0d8afd00f67902fa4272e92622eea098952f05fbab6`;
executable SHA-256
`9f5d0ca10c7736e7b187fb9e35ee3466ec7f6297f9c753508a4794d579fd762b`).
The procedural local-newtype graph and its handwritten control both hit the
existing unsupported `RegistryMetadata` native-image boundary. Full scope
hygiene, causal diagnostics, M01–M14, C1 and C2 remain open.

## Progress

The weighted ledger records **56.5/100 reviewed delivery points** and **0.5
demonstrated pending review**. The latest reviewed implementation pin is
`93c0aa04`. These are partial implementation observations, not acceptance of the
whole feature.
M01–M14 and C1/C2 remain pending.

### Weighted delivery progress

The cap is 100 estimated effort points for the complete milestone through
verified retention in `integration/expression-macros`; Main integration is
excluded. Weights reflect expected work, not an equal share per acceptance case
or feature. They are approximate: display about 56%, not a precise completion
probability. The current Codex elapsed forecast is in the
[plan](../plans/2026-11-05-expression-macros.md#estimate-and-re-planning).

`R` means independently reviewed at a named retained checkpoint; `D` means a
reported demonstrated result awaiting review. A zero has no earned credit.
Rows list bounded, separately creditable increments; numbers in parentheses are
point caps, not required test counts. The developer owns `Dev`, the independent
reviewer owns `Rev`, and the orchestrator owns `PM`.

| ID | Cap | Owner / credit | Observable increments and evidence |
| --- | --- | --- | --- |
| P01 | 3 | PM+Rev / R3 | Parser decision, owning task, reviewed boundaries and frozen graph/controls; `f791b95c`. |
| P02 | 2 | Dev / R2 | Parser checkpoint and recovery; `27d80b28` and its receipt below. |
| P03 | 2 | Dev / R2 | Fixed header projection before invalid bodies and source spans; `80beb331`. |
| P04 | 2.5 | Dev / R2.5 | Staged real driver, graph/source census and dependency-before-body checks; `0274daf9`/`60d79992`. |
| P05 | 2 | Dev / R2 | Contextual selectors and ordinary `syntax` compatibility; `9bb0c720`. |
| P06 | 2 | Dev / R2 | Imported/renamed protected-capture template executes to 35; `00d9f066`. |
| P07 | 5.5 | Dev / R5.5 | Restricted combined template graph to 42, supplied/introduced binders, private helper/opaque owner and nested DSL; `4a4c01b0`, reviewed through `26b43869`. |
| P08 | 1 | Dev+Rev / R1 | Operator-stop and annotation-admission review repair; `26b43869`. Full annotation support remains P10. |
| P09 | 4 | Dev / R3.5 | Procedural captured binder with preceding initializer scope (0.5), `/tmp/ash-syntax-captured-binder-driver.log`. An introduced function parameter avoids a same-spelled caller binding (0.5), and a captured parameter binds its captured body without escaping its scope (0.5); review cleared these function cases at `abd2e26f`. An introduced mutually recursive group retains a same-spelled caller binding (0.5), reviewed at `bc431118`. A captured recursive binder scopes over its initializer and body without escaping (0.5); template and procedural variants, fresh binders, and same-spelled distinct recursive members run to 42. A later sequential initializer sees the preceding captured binder (0.5), `/tmp/ash-syntax-recursive-capture-regressions.log` (SHA-256 `55937b612d95a37d110402814301820f0832c0113f5e1a6aed54337c0c541810`). Four ordinary recursive-resolution cases pass, `/tmp/ash-syntax-recursive-capture-ordinary.log` (SHA-256 `ea829a715c07691b22d1c07c85977e911398f57d0836ebf9685785edfd9974a0`). These cases and the R12 repair were reviewed at `a1135e26`. Captured `resume` expressions use the actual inner or outer clause selected by their expanded position (0.5, reviewed at `89b21a51`). Both execute to 42; duplicate/missing handler clauses and nested-function capture retain their ordinary refusals. A further graph captures caller `value = 40` inside a clause with its own `value = 2` and returns 42. Broader patterns and sequential scopes remain pending. |
| P10 | 5 | Dev / R4 | Duplicated captures retain distinct local binder IDs (0.5), local newtype and constructor IDs (0.5), and resource identity and handle IDs (0.5); the combined graph preserves nested syntax and a caller free reference and executes to 42. The independently validated Core is inspected in `/tmp/ash-syntax-copy-identities-batch.log` (SHA-256 `98dac1c11adf058b33a84ec3a6efb1fe95b3662a93796aacc8ea6163112b3afd`); review cleared these cases at `82d2f219`. A template-introduced local newtype and its constructor remain distinct from the caller’s same-spelled nominal and constructor; the captured caller annotation retains its own type and the real graph executes to 42 (0.5, reviewed at `9b1cb854`), `/tmp/ash-syntax-generated-newtype-origin.log` (SHA-256 `88b3373f0c8cfac57aa157f315748da7e55e56effa3d4cca981a7be1cdd131a4`). Independent Core rejects ten construction-origin and representation mutations and continues to reject wrapped source-only origins; five local-newtype checks pass in `/tmp/ash-syntax-newtype-lib-batch.log` (SHA-256 `2ae8d4a8ea3f5808eceed197f1515fcac1bd28ccde4fc357d0123a3b22afed7c`). An unqualified annotation selects the owner’s private nominal or an introduced local nominal instead of a same-spelled caller nominal or type parameter (0.5, reviewed at `47524835`). Both valid graphs return 42; distinct caller types, direct caller private access, and an unused unknown annotation are refused. A unique template-local nominal now resolves in its lexical scope even without a same-named owner nominal. Renamed targeted and qualified imported nominal annotations follow the checked owner route, including through a facade and under caller shadowing (0.5, reviewed at `d2d377bf`); wrong caller types, owner-only aliases, and an unused dependency-private qualified type are refused. Applied targeted and qualified types, including nested type arguments, use the defining context; one- and two-parameter template-local newtypes also execute to 42, while a parameter cannot escape its representation (0.5, reviewed at `ac1561e5`). Introduced cell and region scopes preserve caller bindings, initializer/provider order, generated type identities and ordinary escape checks; real graphs execute to 42 (0.5, reviewed at `57ce1f1f`). Other copied binder/use cases (0.5), and copied nominal/region cases, effect rows, and broader type scopes (0.5) remain pending. |
| P11 | 5 | Dev / R2 | A template's direct and facade-qualified public term retains the owner's route despite a conflicting caller alias; unused dependency-private references and ordinary caller use of the owner's alias are refused (0.5), `/tmp/ash-syntax-owner-qualified-regressions.log` (SHA-256 `c7c147b247ef8307a18adf5e65bfcbd719b14eade02b09ee2684f135cd6ebab9`), reviewed at `98613915`. A renamed targeted public import works in template and procedural output, through a facade and under caller shadowing; captured caller references retain caller access and ordinary caller access to the owner-only name is refused (0.5), `/tmp/ash-syntax-owner-targeted-regressions.log` (SHA-256 `625b357e3890ca7a2c59b11bd19c0266afd6e164e8fb83a51273c080c212f996`), reviewed at `1bd1a08e`. Owner-qualified public constructor expressions, match and function-parameter patterns work with caller shadowing; dependency opaque constructors remain refused and ordinary access/re-export coexists (0.5), `/tmp/ash-syntax-copy-constructor-final.log` (SHA-256 `6546d7ff826e169e5e32b31983fd3362e6381b8c07b6e50bdc86d56cb0bce5b2`), reviewed at `82d2f219`. A renamed targeted constructor works in template expressions and patterns, procedural output, a facade, and caller shadowing while ordinary caller access is refused (0.5, reviewed at `9b1cb854`), `/tmp/ash-syntax-targeted-constructor-current.log` (SHA-256 `90534ec49a44823be92f9f09f5bb6a36307558106c753fe98b0389959925b707`); the current batch is based on `0cd326dc`, with combined SHA-256 `7091e75c5d1b1e51aed543614a9be923f34bc38c1de1c69d92997fd6b011a1cb` for the six changed Rust files and generated-newtype and targeted-constructor fixtures. Remaining full authenticated grants/access (0.5), retained checked private closure and real Core-coordinate consumer (2), and route mutation refusals (0.5) remain pending, beyond P07. |
| P12 | 3 | Dev / R3 | A template or checked transformer selects a definition-site method, renamed targeted import, qualified import or public facade using caller-local evidence and executes to 42 under caller shadowing. Without caller evidence each fails `constraint.unsatisfied`; a syntax import does not introduce an ordinary caller method (1, reviewed at `b70c6bb3`), `/tmp/ash-macro-method-procedural.log` (SHA-256 `24cf1c1979cc1f0329109b71a2aca577b54e8c0cedf598f96e9ad6765830b84a`). Broader private-method cases remain pending. Six affected suites pass 167 cases in `/tmp/ash-macro-method-regressions.log` (SHA-256 `28baa45f8ca63a7b3b371c36f6398bcadb324b548fb3856af352ec6435e3363d`); the combined hash for the four changed Rust files and method fixtures is `0df274f24e1f2b92cb4f8d4f50abc2b71cb3273aced54ef728521b86c2af5a59`. Template-generated `resume`, `discard` and `retain`, plus a checked transformer producing `resume`, execute to 42 in their valid handler contexts; outside-clause, nested-function capture and outside-retained-root forms keep their ordinary refusals (1, reviewed at `d1e16df4`), `/tmp/ash-macro-continuations-procedural.log` (SHA-256 `160da5e3367be104cedfb308f77c13f4d588310569e9c6c0138c14091544f505`). Six affected suites pass 180 cases in `/tmp/ash-macro-continuations-regressions.log` (SHA-256 `243105483287c22e3ae8fe1d79b4b1c8acf79a708eef96ebf536a700ab4ec5a7`); the combined hash for the two changed Rust files and continuation fixtures is `46b508ae457b2574e94159fed18fc652744ce07499cc24f3bd338d0a92d53a42`. A copied effectful capture runs twice; two captured requests produce 42 in written order and 33 when reversed, with the handwritten control also producing 42. A captured resource read returns 42, and a captured closure escaping its resource is refused with the same `type.resource-escape` reason as handwritten source (1, reviewed at `47524835`), `/tmp/ash-macro-effects-resources.log` (SHA-256 `0fcd09a863e99691ed433f3061d2256c95dd8d527695f491ab2d0c5ba55eb31a`). The named-type and effect/resource batch passes 236 tests across seven affected suites in `/tmp/ash-macro-type-context-regressions.log` (SHA-256 `9fe3960da0c7118aa6c93713a91af245312d01f80f9c550fe91524c77027167c`); its combined Rust and fixture hash is `dfd5400b8d9f902dcf8072a259b6f6f6336d9b7b99029c853e0688286bd04483`. |
| P13 | 3 | Dev / R1.5 | Generated definition context selects its owner's imported syntax, caller context selects a different caller import, and fresh context selects neither caller syntax nor binding (1), `/tmp/ash-syntax-generated-context-driver.log` (SHA-256 `3f3815fdaedc6ee7a41ff6053c64a75aa832ef96d10d2a5ca36f09cef955833a`). An outer template's literal identifier retains its context as the binder and body of a separately imported nested syntax; its local 32 and the caller's same-spelled 10 produce 42 (0.5, reviewed at `c5bf51f3`), `/tmp/ash-macro-definition-admission-regressions.log`. Broader leading-context, import, reservation and conflict cases remain pending. |
| P14 | 3 | Dev / R2 | Reviewed canonical module load/check/link (0.5); complete vocabulary (1) and lexer/declaration conformance (0.5), `/tmp/ash-syntax-token-vocabulary.log`; API identity and interface-version conformance remain pending. |
| P15 | 2 | Dev / R1.5 | Entry-time exact checked transformer type admission (1); definition-time missing, wrong-type and disallowed-effect refusals (0.5), `/tmp/ash-transformer-review-repair-regressions.log`; polymorphism and constraint refusals (0.5) pending. The repair passed review at `ad8ca9cc`. |
| P16 | 3 | Dev / R2.5 | Mainless compile-time entry (1), independent entry validation (1), and real checked Ash body execution (0.5), `/tmp/ash-transformer-machine-step.log`; retained helper closure (0.5) pending. |
| P17 | 2 | Dev / 0 | Authenticated invocation Input (1), unchanged validated-program reuse (0.5), changed-program revalidation (0.5). |
| P18 | 2.5 | Dev / R0.5 | Actual identifier capture and origin round trip (0.5), `/tmp/ash-syntax-captured-ident-driver.log`; complete input encoding (0.5), handle ownership (0.5), and broader round trips and stale/foreign/forged refusal (1) pending. |
| P19 | 3 | Dev / R2 | Reviewed expression capture (0.5) and `Plus` construction (0.5); token kind/spelling round trip and mismatch refusal (0.5), `/tmp/ash-syntax-token-ops-driver.log`, and identifier spelling (0.5), `/tmp/ash-syntax-captured-ident-driver.log`; remaining total capture pending. |
| P20 | 4 | Dev / R3 | Structured parse rejects an incomplete expression, accepts an unresolved name without resolving it, and returns a protected fragment executing to 42 (0.5), `/tmp/ash-syntax-parse-service-driver.log` (SHA-256 `cb3b9e9e8f9376c505c8dd2c484a04940ba4b0d281e94b5ecb63b8b509024ee4`). Unwrapping `1 + 2` before `* 10` yields 21; protected, reparsed, and written-group forms yield 30, and template forwarding yields 21 (1), `/tmp/ash-syntax-unwrap-driver.log` (SHA-256 `5be6520598b42c1218239c23032279a0d5d682b009717f52b8c170cadbe005f2`). Parsing then discarding a nested rejecting transformer does not run it (0.5), `/tmp/ash-syntax-parse-no-expand-driver.log` (SHA-256 `4dd073d143a1f2da9658b8f22fc631d5a46fd488a57990f4332e16e3bd09b133`). Unwrapping a caller-qualified term retains its import and yields 30 (0.5), `/tmp/ash-syntax-qualified-after.log` (SHA-256 `dfbe5239cb5aa17305ed3648e85ed916bc030ca645b537f870b56a443b06db5e`). `SyntaxDiagnostic` retains a parser reason and construction location (0.5), `/tmp/ash-syntax-parser-diagnostic-driver.log` (SHA-256 `e8954105f99c7e0ff104fd5651ec14344b07bfda87310b58855e99ebd74d7472`); broader parse and unwrapping contexts remain pending. |
| P21 | 3.5 | Dev / R1.5 | Fresh binder avoids caller `temp` (0.5), definition identifier selects a private helper under caller shadowing (0.5), and caller identifier binds a caller body (0.5), `/tmp/ash-syntax-constructed-ident-driver.log` (SHA-256 `19f2462c862910b90739cfb207b2cdbf286bbe85ac0c1207714f5e5a287d29fa`); distinct fresh allocations and broader authority/context cases remain pending. |
| P22 | 1 | Dev / R1 | Empty origins return `MissingOrigins`; nonempty and nested combinations cross parse and unwrap before the graph executes to 42 (0.5), `/tmp/ash-syntax-combine-origins-driver.log` (SHA-256 `ca483c2b063c55e27a151adf79e1644a0b8e6f7f6e380c6fe11943688aa8dedd`). A transformer-authored rejection preserves its message and ordered caller/definition causes (0.5), `/tmp/ash-syntax-rejection-driver.log` (SHA-256 `dd3b9eea67d1ef9ac6191fdfa6b15df46fc270e969ab70018b23d6a0077ecccb`); final generated-program causal-origin propagation remains pending. |
| P23 | 4 | Dev / R2 | Reviewed expression/token decoding, transfer and protected-fragment parsing (1.5); parenthesis/brace group decoding and parsing (0.5), `/tmp/ash-syntax-vocabulary-groups-regressions.log`; complete output, failure and observed root-close behavior pending. |
| P24 | 2.5 | Dev / R1.5 + D0.5 | Malformed direct output reports `parse.expected-operand` (0.5), `/tmp/ash-syntax-invalid-output-driver.log` (SHA-256 `7d4df37046fea2bae1e0b14ac144bcd232809730f05ccd0df94be4edd455ef05`). Evaluator failure retains its underlying cause and invocation/definition locations (0.5), `/tmp/ash-syntax-diverge-after.log` (SHA-256 `4be2d989431d7da8b0844bb3af9dfe0a6e21afde7ba15f897f2dcda7ffbfd1a9`). A normal transformer closes its root before its output executes; an injected close failure retains authored or parser rejection plus teardown, and prevents successful output publication (0.5, reviewed at `93c0aa04`), `/tmp/ash-transformer-teardown-final.log` (SHA-256 `69eec7daac5be0f7f9cc4d7f76477ae5a24ebcb6f8f6c4580b67675ff0707d41`). Active-machine destruction on real evaluator and service failures, plus transfer failure and paired completed-root refusal, add 0.5 pending review (`/tmp/ash-transformer-lifecycle-stack-final.log`); paired active-disposal refusal and remaining failure paths are pending (0.5). |
| P25 | 1 | Dev / R1 | A real non-requesting recursive transformer terminates as an expansion failure under the existing execution limit, `/tmp/ash-syntax-diverge-after.log` (SHA-256 `4be2d989431d7da8b0844bb3af9dfe0a6e21afde7ba15f897f2dcda7ffbfd1a9`). |
| P26 | 0.5 | Dev / 0 | Required service, output, and expansion limits produce ordinary closed-invocation failures. |
| P27 | 2.5 | Dev / R1 | Frozen computed graph to 42 (1), `/tmp/ash-transformer-combined-driver.log`; template/procedure equivalence (0.5), discarded and repeated nested invocation behavior (1) pending. |
| P28 | 2.5 | Dev / 0 | Independent declaration-coordinate/grant/type/provenance mutation checks (1), distinct compile-time/final validation (1), completed dependency reuse (0.5). |
| P29 | 2 | Dev / 0 | Repeat compilation modulo fresh identities (1), changed semantic inputs update/reject output (1). |
| P30 | 2.5 | Dev / 0 | Ordered multi-input/frame representation (1), ordinary semantic causes/locations (1), bounded copying/relocation preservation (0.5). |
| P31 | 2.5 | Dev / R1 | Authored rejection (0.5) and retained parser failure (0.5) render their messages and caller/definition causes in human and JSON output, `/tmp/ash-syntax-rejection-driver.log` and `/tmp/ash-syntax-parser-diagnostic-driver.log`; remaining diagnostic variants, complete frame structure, and locale/catalog conformance are pending. |
| P32 | 2.5 | Dev / 0 | Required image records (1), reconstruction/round trip (1), corruption refusal (0.5). |
| P33 | 2.5 | Dev / R2 | The combined template and checked-transformer graph builds and links through public `ash build` (1); its generated executable returns 42, matching interpretation (1), `/tmp/ash-syntax-native-second.log` (SHA-256 `43fe9d4c89fe2a69791a8a835bf52e68e1af1e79292b98c70cbea5bfb68c3029`). Copied `.ash` inputs were removed before execution; the remaining cleanup and no-runtime-syntax-service assertions (0.5) are pending. |
| P34 | 2 | Dev / 0 | Implemented language delta in specification (1), executable positive/negative examples (1). |
| P35 | 2 | Dev / 0 | Public vocabulary/API and tool docs (1), status/link/authority and transition cleanup (1). |
| P36 | 1.5 | Rev+Dev / 0 | Connected C1 independent review (0.5), fresh pinned full gate (1). |
| P37 | 2.5 | Rev+QA / 0 | Final whole-path independent review (1), independent M01–M14/consumer evidence audit (1.5). |
| P38 | 1.5 | Dev+Rev / 0 | Fresh C2 full gate (1), retained-input/evidence equality and affected refresh (0.5). |
| P39 | 1.5 | PM+Dev+Rev / 0 | Milestone merge and retained verification (1), acceptance readback and owned cleanup (0.5). |

Weights total 100: reviewed foundation/template 20; remaining scope/grants 20;
API/entry 10; Ops/interchange 14; transfer/failure/limits 8; graph/Core/repeatability
7; diagnostics 5; image/build 5; spec/tool docs 4; review/QA/gates/integration 7.
The independent review assigns more weight to the unresolved contextual,
non-term, copied-identity, grant, and Core-coordinate consumers than the first
draft. The 20-point reviewed baseline is frozen; a changed ETA does not reweight it.
Reviewed effort is 56.5, demonstrated provisional effort is 0.5, and 43 points
have no credit. Review upgrades D to R without awarding implementation points
again. Explicit review/gate rows cover their own work, not a second implementation
credit. Record the exact commit or source hash, real consumer observation/test
receipt, and reviewer decision when changing a row. Withdraw credit if disproved.
One assertion has one primary credit owner. A shared graph/run may support
several rows only through distinct named assertions: exact type/row refusals,
service round trips, post-root-close transfer, graph composition, and independent
mutations are different observations. One positive graph does not earn all of
entry, bridge, transfer, full-graph, and mutation points.

When progress reports are requested about every 30 minutes, report: interval
actual elapsed versus estimate; R/D totals and changed IDs; concrete evidence;
current work/confirmed finding; next observable increment; and the whole remaining
Codex clock range. Pending rows split into 0.5–2-point increments; combine small
increments into a meaningful report. Half-hour reporting is not a requirement to
commit, freeze, review, or run a gate every half hour. Investigation can earn zero:
state what was learned and the next check. Time spent, commits, lines, test runs,
or adding another checkpoint do not themselves earn points. Keep the next
increment small when possible; do not invent work or extra tests for credit.

These are effort-weighted delivery credits, not measured model effort or time
remaining. M01–M14 and C1/C2 remain required. Review weights only when the work
decomposition or scope changes; preserve the old score and explain any agreed
rebasing. A forecast change alone does not change earned points.

Template-introduced cell and region scopes run through the driver with
same-spelled caller binders and type names. Captured initializers, region
providers, nested selection, and both operand orders execute to 42. An escaping
cell handle and a closure capturing a region are refused, caller access outside
the region is refused, and a cell still needs its direct builtin import. The equivalent
handwritten resource expressions revealed two existing continuation-snapshot
defects; the repaired producer keeps the active child and the actual completed
value. Nine affected suites pass 318 cases (`/tmp/ash-template-owned-scopes-regressions.log`,
SHA-256 `2f2face20c9b911541f8f7436747494a7453525c13f64da1aeea5bebb3a00a31`).
A focused value-analysis test preserves dependency atoms and refuses to create
a missing frozen value (`/tmp/ash-template-owned-scopes-value-guard.log`,
SHA-256 `3c578d0041f6a7dcec02ccd35e22cdd2eb5f8f722eb13c37d978ace73fddae26`).
The batch was reviewed at `57ce1f1f`; full resource/region acceptance remains open.

Applied imported types now retain the defining context in both the constructor
and nested arguments; direct and qualified graphs execute to 42 despite caller
shadowing, while wrong caller types and an unused unknown application are
refused. Generated local newtypes with one or two type parameters execute to 42;
their parameters do not escape the representation. Eight affected suites pass
194 cases (`/tmp/ash-template-generic-regressions.log`, SHA-256
`a51819eb7d03eb4e2e33604cd0fc7a65b88670b70a0398737bf818711ccfdaf6`).
Independent Core rejects ten parameter-origin mutations
(`/tmp/ash-template-local-generic-mutations.log`, SHA-256
`c5541389322c6c3a3baa2192da7a3a684733a80836f560b4c70931c66a77843f`);
five existing local-newtype checks pass (`/tmp/ash-template-local-generic-core.log`,
SHA-256 `0b21e3aaa96a1f2c8bdd5b30d7211ac11cbeb7f9063136b68941baa3982fa0cb`).
This batch was reviewed at `ac1561e5`.

A local newtype annotation, previously refused unless its name also appeared
as an owner-level type, now resolves through its actual lexical declaration.
Renamed targeted and qualified type imports retain their checked owner routes;
direct and facade graphs return 42 despite caller shadowing. Wrong caller types,
ordinary access to owner-only aliases, and an unused private dependency type
are refused. Eight affected suites pass 194 cases
(`/tmp/ash-template-type-routes-regressions.log`, SHA-256
`6d869227b43e686575533bcd04cbcd0490e3868c663a35653e99af2089227a5f`).
This batch was reviewed at `d2d377bf`.

An unused template with a direct missing helper, including inside a literal
function, is now refused at definition admission; the prior driver accepted it
(`/tmp/ash-macro-definition-admission-before.log`, SHA-256
`0da303995f01843038e7d6c57c9465f3e2887f1b4d96e3b289e66d674733766a`). The
existing resolver checks direct names with temporary capture placeholders, while
nested syntax remains deferred and is not executed during admission. A valid
private helper and captured identifier compile, a nested binder executes to 42,
and a surviving nested free name cannot use a caller helper. The resolver state
is restored on success and failure (`/tmp/ash-macro-definition-admission-isolation.log`,
SHA-256 `efea4d6cdef9cabf325626b7fa38752d4d97e9734ad756c4ef29d69accba5a8e`).
Seven affected driver and compatibility suites pass 183 cases
(`/tmp/ash-macro-definition-admission-regressions.log`, SHA-256
`87b0de1b6fd9ce970161fc16bbed6fe17919b9ca0653f6503bce34c02739c2ef`).
This batch was reviewed at `c5bf51f3`.

A template-authored `perform` and `handle` now use their owner’s checked effect
under a same-spelled caller effect. A private handler works when its operation
signature uses a private nominal, including a newtype wrapping another private
nominal; all three graphs return 42. Caller access to the private effect, types,
and constructors remains refused. Qualified/imported/parameterized effect
references and general private-closure and grant acceptance remain open. Six
affected suites pass 156 tests in `/tmp/ash-macro-private-effect-final.log`
(SHA-256 `8b9dc54b0d4c133e2d6eb908b43d24b5b0db48558c0e5cdf72e5a8323836cc49`);
the additional same-owner constructor-privacy check passes in
`/tmp/ash-macro-private-effect-privacy.log` (SHA-256
`2c81884b648f7f5de4ea75cc69a5c95ee4c6159e4342e3261a191b9f1ed684f7`). The
combined changed Rust and fixture hash is
`ee1d0d39dcdc32a0be70adb018bfece8601402339cb29ac37f6d8cab325df332`.

The unchanged 4,096-local-newtype program on a 256 KiB thread overflowed at
reviewed `82d2f219`, `/tmp/ash-expression-baseline-82d-small-stack.log`
(SHA-256 `6d1f647a6954a04c2c143d6fbe71e9f533942204e41b8c47f43134d1782957b0`).
Separating post-parse checking from staged projection restores its accept and
escape checks; 105 macro, newtype, module-loading, resolution, and visibility
cases pass in `/tmp/ash-syntax-targeted-newtype-stack-regressions.log`
(SHA-256 `4c7a7f6cffce56ff4e16ed4c26b123afdfca9f130eec2b471c1a0ff9f56d193e`).
Eight local-nominal scope checks and the copied-identity Core check also pass in
`/tmp/ash-syntax-nominal-lib-batch.log` (SHA-256
`9709ff1cc18172befde3c265cd3441dfae27886f75df9fe53aa3986c07930d06`) and
`/tmp/ash-syntax-copy-identities-recheck.log` (SHA-256
`2462cbc28eb5a9b13949443dac9a1a19154ec414c1b89e6263edce78e31ce265`).
These compatibility repairs add no separate progress credit.

A focused `cargo clippy -j 1 --lib -- -D warnings` is still failing with 17
existing warnings; the same command at reviewed `82d2f219` reports the same
17 sites. Current and baseline logs are `/tmp/ash-syntax-targeted-newtype-clippy.log`
(SHA-256 `90b0f1cad1268c54d1975c5f5ba985b50242aa157baaa4bf5d179e44fbb0c311`)
and `/tmp/ash-expression-baseline-82d-clippy.log` (SHA-256
`802fca986bc4b20e457a9bc9ac5d67022e72cad86843b2b0d0edf83baad33099`).
The all-target, all-feature lint and the complete C1 gate remain pending.

### Component observations

The following observations retain their evidence and limits. They are not six
equal progress units. The restricted template is reviewed at `26b43869`; the narrow procedural
vertical and its repairs are reviewed at `ad8ca9cc`.

At 20:35 Sofia time, the latest approximately 30-minute interval added 4.5
provisional points (constructed identifier contexts, unwrapping, and contextual
parsing); the ledger stands at R28 + D8.5. The
partial candidate `57f68ae1` passed 22 host, 25 module-syntax, and 18 template
driver cases (`/tmp/ash-syntax-retained-context-regressions.log`, SHA-256
`e32ace759c5cf11f1418cde8e782b00f865057f8e7a9e686c9a5ba056b94ea37`), the
vocabulary and cross-source-origin guards (`/tmp/ash-syntax-retained-vocabulary.log`,
`/tmp/ash-syntax-retained-origin.log`), and three calibration observer cases
(`/tmp/ash-syntax-retained-calibration.log`).

Review R10 found that template-written parentheses and a generated nested
protected fragment were each lost by whole-carrier substitution. Both real
programs produced 21 instead of 30 before the repair
(`/tmp/ash-syntax-r10-before.log`, SHA-256
`933d1af1614a4b83ad9fe5d90d3cb3f93c624b26b8e0b1d48cb4807944375572`).
Restricting that substitution to an actual bare splice retains both boundaries;
both programs now produce 30, and bare forwarding still produces 21
(`/tmp/ash-syntax-r10-after.log`, SHA-256
`40d14deff0c1a884317b05e86cc713ea086bb02636fcbb502c40a23d0d5d243f`).
The affected suite passes 23 host, 25 module-syntax, and 18 template cases
(`/tmp/ash-syntax-r10-regressions.log`, SHA-256
`1dee17cb3227324d7d686fb2224b3de4f6f8bd82fe30bcdc37851dbb01b30e4e`).
R10 re-review passed at `3a7fe9f4`; all M01–M14 remain pending. A caller's
qualified term now unwraps through its existing import, while definition-context
qualified names and identifiers in type and pattern positions remain incomplete.

At 21:07 Sofia time, the next 32-minute interval added 5 provisional points:
P20, P22, P24, P25, and P31 each gained one point for the distinct observations
listed above. The ledger stands at R36.5 + D5. The affected driver suites passed
29 host, 25 module-syntax, and 18 template cases
(`/tmp/ash-syntax-diagnostics-regressions.log`, SHA-256
`46ac0fb593923f73be3e9487dd1cf0ff6056677d4e2c549fbd30fa8cf4afddfa`),
the diagnostic presentation/catalogue suites passed 14 cases
(`/tmp/ash-syntax-diagnostics-presentation.log`, SHA-256
`9ffa74cdac9dc9d9dfab95b3924c880686fcd8ab8c18c4340a617aeeda798bd3`),
and the observer suite passed three cases
(`/tmp/ash-syntax-diagnostics-observer.log`, SHA-256
`0f48fba50539eca8700ba26f4cd1b0fd911672b11d4f19c3719b41af2f008750`).
These results were reviewed through `93bc3964`. The remaining forecast is in the plan.

Partial review of `94bd9467` found that repeated shared origin combinations
could expand without bound while reporting a rejection. The local repair limits
combined-origin size and depth and admits the complete rejection's causes
before reporting; ordinary cause order is retained. The affected host suite
passes 30 cases, including finite doubling, deep-chain, and repeated-cause
programs (`/tmp/ash-syntax-r11-host.log`, SHA-256
`d9bde04489051955c3169858869c4c1c4a99af9858c44d650b2c9e93ec679599`).

The first native build of the combined graph failed because the private image
refused the compiler-syntax module role (`/tmp/ash-syntax-native-first.log`,
SHA-256 `8bc692db34ee2dbcc1fa55cfab3749922e8b23cd507c400814d63694e1d20d74`).
The image role adapter now lets the real graph build and return 42 after its
copied sources are removed (`/tmp/ash-syntax-native-second.log`, SHA-256
`43fe9d4c89fe2a69791a8a835bf52e68e1af1e79292b98c70cbea5bfb68c3029`).
The focused image check reconstructs that graph and rejects changed canonical
syntax bytes and a duplicate syntax role (`/tmp/ash-syntax-image-mutations.log`,
SHA-256 `78fc15f63fad357d27313c36e71d86155ac3a1c93956cb19452e8455c3f6be61`).
Review cleared the repair and image adapter at `93bc3964`; broader image
corruption coverage and full causal origin preservation remain incomplete.

The native probe copied `entry.ash`, `macros.ash`, `helpers.ash`, and
`other_dsl.ash` from `tests/fixtures/surface-macros/` to
`/tmp/ash-macro-native-UOOOil/`. Their respective SHA-256 values are
`75b30fcb27a7a415c3abaf087289f54d8f0c2b0858d1c9455d2fa64adca09c3e`,
`1c7d5fc059b88b07ec76c0d11aa2a41becf99bd51f5f0ead3b4ff9bbbf59ae4a`,
`9190d577b45ef5ef953ee3dddd1a2122e7a9c3a2a11f962ecdfd01dda415e3ce`, and
`3caebbd20d0a03bda17159ab7199cc140e1eace82e53f479f0e276451b780c4e`.
After rebuilding the CLI with `cargo build -j 1 -p ash`, the probe ran:

```sh
probe_dir=/tmp/ash-macro-native-UOOOil
target/debug/ash "$probe_dir/entry.ash"
CARGO_BUILD_JOBS=1 target/debug/ash build --output "$probe_dir/program" \
    --cargo-target-dir "$PWD/target" "$probe_dir/entry.ash"
rm -- "$probe_dir"/*.ash
"$probe_dir/program"
```

The CLI SHA-256 was
`616379248e495f963c1a00c3d42fb5ce51b463cbf0dd94cd002cc3f1cbb44dd3`;
the generated executable SHA-256 was
`c348f13cbc894211553c2bfe99a0d4451308f375d49a7a65ff028b1e248a2008`.

At 21:36 Sofia time, the 29-minute interval since the preceding report added
three points: two reviewed for the native build/result and one provisional for
function parameters. The ledger stands at R43.5 + D1. The function cases pass
through the real driver and the existing independent Core validation; broader
pattern scopes and procedural contexts remain open. The remaining forecast is
in the plan. Two ordinary anonymous-function resolution cases also pass
(`/tmp/ash-syntax-function-ordinary.log`, SHA-256
`038764e1eee2faf4fa0187b1ce0e7c93acb74f4bafbdfe23d395ed9f8c7d1ecb`).

Review of `ef5a5d95` found that an expression fragment emitted in a recursive
binder position was accepted as a synthetic binder. The real transformer in
`entry_recursive_bad_binder.ash` reproduced that acceptance before the repair
(`/tmp/ash-syntax-r12-before.log`, SHA-256
`39cebbd3c38e5f15f470dea8e22746bc4250c846fadb3cab0c5aec20e5a770e0`).
The projection now refuses non-identifier fragments there. The negative and
the captured and fresh identifier programs pass in 135 host, template, parser,
and module tests (`/tmp/ash-syntax-r12-after.log`, SHA-256
`c10a3036d194f407d20303ee5ebf7aa91b60d05715df808606238c31c880e4cd`).
The same reviewer cleared the repair and prior one-point observation at
`a1135e26`.

At 22:08 Sofia time, the 32-minute interval since the previous estimate added
two points, including the qualified-import result above, later reviewed at
`98613915`. The
owner-qualified graph previously failed at template admission
(`/tmp/ash-syntax-owner-qualified-before.log`, SHA-256
`e50d73122e40cc146a4f4747f4a4f75773c2265e06a95ef5d5023c7626cb0334`).
The direct and facade graphs now return 42; the captured/fresh, ordinary import,
and visibility suites also pass, 77 tests in total. Qualified constructors,
methods, complete grants, and route mutation checks remain open.

The targeted renamed import graph initially failed with an unknown owner name
(`/tmp/ash-syntax-owner-targeted-before.log`, SHA-256
`a1ee1429a555b78f4eff3bf5eb44f79bec88f04c6cd1cff78a4f37ebcd80350a`).
The selected term now retains its checked dependency and selector route.
The template and a checked Ash transformer both return 42 with caller
shadowing, including captured caller expressions; the direct and facade cases
and the host, ordinary resolution and visibility suites pass 79 tests
(`/tmp/ash-syntax-owner-targeted-regressions.log`, SHA-256
`625b357e3890ca7a2c59b11bd19c0266afd6e164e8fb83a51273c080c212f996`).
The same reviewer cleared this half-point at `1bd1a08e`.

Duplicating a captured expression already preserves distinct binder, local
nominal, constructor, resource and handle identities through the existing
resolver and independent Core validator. The combined graph includes nested
syntax and a caller free reference. A separate graph exposed unsupported
owner-qualified public constructor expressions and patterns; those now use
the checked public export while withholding dependency-opaque constructors.
The focused host, template, module resolution, visibility and newtype suites
pass 108 tests (`/tmp/ash-syntax-copy-constructor-final.log`, SHA-256
`6546d7ff826e169e5e32b31983fd3362e6381b8c07b6e50bdc86d56cb0bce5b2`).
The same reviewer cleared these two points at `82d2f219`; this does not
establish complete copy, context, grant or M01–M14 coverage.

1. **Template grouping — demonstrated.** `cargo test -j 1 -p ash --test
   surface_macros template_macro_preserves_expression_capture_grouping --
   --exact` must compile and execute the imported template to `Int 35`.
2. **Combined template graph — reviewed restricted slice.** `cargo test -j 1
   -p ash --test surface_macros template_graph_preserves_bindings_and_private_helpers
   -- --exact` compiled the real graph and executed to `Int 42`. It exercises
   captured and introduced binders, an opaque constructor, a private helper and
   its dependency, and definition-site syntax imports. The helper and
   same-spelled caller binding also ran in isolation; direct caller access was
   rejected. The template driver suite also checks that an opaque re-export
   remains opaque and that an ordinary coverage diagnostic does not reveal its
   private constructor. The restricted review does not establish the complete syntax-specific
   authority, hygiene, or remaining acceptance cases. Operator
   matcher separators stop at the current expression level, including around
   grouped expressions. Named template annotations resolve supported local, owner, and imported
   types in their defining contexts. Effect-row annotations and other unsupported
   forms still fail closed. The driver suite
   passes 17 cases with the computed-transformer case filtered:
   `cargo test -j 1 -p ash --test surface_macros -- --skip
   imported_templates_and_ash_transformer_run_through_the_driver`.
3. **Computed Ash transformer — partial.** The actual Ash `twice` body executes
   through the checked entry and three syntax services, then its structured
   expression/token output crosses the ordinary parser and final pipeline.
   `checked_ash_transformer_constructs_expression_from_capture` runs `twice 21`
   to `Int 42` (`/tmp/ash-transformer-output-driver.log`). The frozen combined
   graph also runs to `Int 42`, matching its handwritten equivalent
   (`/tmp/ash-transformer-combined-driver.log`). A second graph constructs
   `Star` and an integer, round-trips token kind/spelling, and rejects a kind
   mismatch (`/tmp/ash-syntax-token-ops-driver.log`). The wider token mapping
   has a working constructor/spelling table and lexer/declaration check
   (`/tmp/ash-syntax-token-vocabulary.log`). Parenthesis and brace groups also
   execute through the driver (`/tmp/ash-syntax-vocabulary-groups-regressions.log`).
   Captured identifier inspection and caller-context reference/binder output
   also run through Ash (`/tmp/ash-syntax-captured-ident-driver.log`,
   `/tmp/ash-syntax-captured-binder-driver.log`). Fresh, caller and definition
   identifiers, contextual syntax selection, and restricted parse/unwrap now
   have the real-driver observations recorded above. Their broader contexts,
   remaining services, complete origins and diagnostics, public interface-version
   conformance, and image support remain pending.
4. **Diagnostics and refusal — partial.** Malformed selected syntax and direct
   private-helper access are rejected. Complete the proposal's negative cases
   and verify causal details in human and JSON diagnostics.
5. **Interpreter and build/image — partial.** The combined macro graph now runs
   through the interpreter and a native executable, both returning 42 after the
   executable's copied sources are removed. Broader image mutation, cleanup,
   and no-runtime-syntax-service evidence remain pending.
6. **Review and acceptance — pending.** Pin the completed implementation and
   evidence, obtain independent review and QA, run a fresh full gate, then
   integrate into `integration/expression-macros` and record acceptance. Main
   integration and signing remain separate human gates.

The current Codex elapsed forecast and measured commit-span limits are recorded
in the plan; historical engineer-day estimates below are superseded forecasts.

The independent reviewer has cleared staged parsing, syntax selectors, and the
restricted template through `26b43869`, and the narrow procedural vertical
through `ad8ca9cc`. Further procedural work remains open. Core declaration-coordinate handling, copied declarations, complete
contextual resolution, grants, the transformer host, diagnostics and build
remain open. Historical D0 receipts follow; they describe earlier candidates.

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
  rejects an unavailable syntax export before importer-body parsing. It can
  select a restricted checked template and expand a single expression capture.
  Its real file graph evaluates `times_five 6 + 1` to `35`, preserving capture
  grouping; a renamed selector also executes, and a missing capture rejects.
  Templates requiring name binding or definition authority are refused. The
  separate binding/private-helper graph currently fails on its multi-capture
  matcher. No acceptance criterion is closed by this partial path.

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
