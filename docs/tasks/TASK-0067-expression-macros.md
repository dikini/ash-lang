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

> Historical checkpoint and ledger text below remains unchanged. The
> [2026-11-06 amendment](#2026-11-06-approved-amendment) gives the
> current remaining scope where that text describes removed work.

## Current delivery status, 7 November

The latest reviewed product checkpoint is `1631b1b5`: **82.5/99 original-scope
points are reviewed and 16.5 remain**. The separately estimated 30.25 points of
additional performed work give an effort index of **112.75/129.25**, not an
acceptance percentage. M01–M14 and C1/C2 remain open.

The [operational plan](../plans/2026-11-05-expression-macros.md#2130-source-binder-reservation-finding)
records the reviewed source-binder reservation, copied-region and bounded
combined-origin resolution repairs and malformed discarded-capture control.
The preceding 141-minute scenario
is not a current complete forecast. Actual event windows and remaining
estimates are recorded separately. The historical
checkpoints below are preserved as written.

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
Independent review cleared this batch at `50ed262f`. An attempted
completion-root injection on an active failure did not reach that
completion-only hook; a separate active-disposal
worklist injection did not encounter a worklist allocation. Neither establishes
paired active failure and teardown preservation, which remains open (respectively
`/tmp/ash-transformer-active-root-paired-red.log`, SHA-256
`73e41daa7e69fb469fe4b8b03151a1d1a4cc620915d413cf0797a218d8872c6f`, and
`/tmp/ash-transformer-active-closure-forest-probe2.log`, SHA-256
`e38972e47b54dbc7213cd50cbee35f5e67b9ad8b12ebad72fd91388ba11a32f6`).
A later balanced-closure Ash graph also failed to trigger the active-disposal
worklist refusal (`/tmp/ash-transformer-active-forest-probe.log`, SHA-256
`68ea6d2207e83ac1e2cfbd18e97f7da4882d39540bd349272f15e8cbda05a426`).

A captured identifier now selects a caller effect in a generated function's
effect-row annotation. The real template and handwritten graphs both execute
to 42; a missing actual effect and an effect outside the declared row retain
ordinary failures. Unused templates still reject missing literal effects and
missing type arguments. Previously the valid template failed admission on the
temporary identifier (`/tmp/ash-template-row-capture-red.log`, SHA-256
`f249d04b50e567d0578b4646dec0781c819c72b5bb90ae4b52f1b1101dce7786`).
The existing name resolver defers only that issued placeholder after resolving
its arguments; actual expansion still resolves and checks the effect normally.

An unused valid template with local evidence also failed because admission
could not see its own module's original interface facts
(`/tmp/ash-template-local-evidence-red.json`, SHA-256
`23edcfe6694cc651d14af451c695a633d98a6be28e6e1eb6581e81d458afc150`).
Admission now temporarily places those original facts in the resolver and
returns them on either result. The existing isolation test confirms the
same interface allocation and resolver state after success and failure
(`/tmp/ash-template-row-admission-isolation-final.log`, SHA-256
`6cb6c3aa462560306c679dd5f66b9a9010f05424b0b5206215dd8e1aa585fbbd`).
Five affected suites pass 122 cases
(`/tmp/ash-template-row-capture-regressions.log`, SHA-256
`359ffbfb66faedaad3506f3cd88ccc89e293f9b49e06bc7a32b4dbb4f557dbdd`).
Independent review cleared this batch at `12e348ff`; it adds no ledger credit.
Other row positions remain open. At that checkpoint a generated local-evidence
graph exposed an owner-interface lookup failure and, when the caller imported
the interface and method, an independent Core `Registry` refusal
(`/tmp/ash-template-row-evidence-second.log`, SHA-256
`2ff509183d94a883fb4642dfded19737c00cee50de4f3c1e0591e32fb591d0be`, and
`/tmp/ash-template-row-capture-third.log`, SHA-256
`15c4dc0a013cfbe593137fd5fceabaff1735544672c495d22db44cbce733082e`).

The current candidate resolves the checked owner's private interface and
method without importing an implementation. A generated local-evidence graph,
its handwritten control, a private method-signature type, captured method
selection, and qualified and renamed owner imports execute to 42, including
caller-shadowing and same-interface method-alias collision controls. Direct
caller access to the private interface and method remains refused; a method
without evidence is unsatisfied. An unrelated resolved method is rejected in
both handwritten and generated declarations, including when its alias matches
a selected interface method. The focused driver receipt is
`/tmp/ash-template-private-evidence-alias-final.log` (SHA-256
`2259223e599963d7c25c266a79d3cab0d23a61b6acc6cc333cc611cf585d9f82`);
the candidate's earlier mistaken acceptance is retained in
`/tmp/ash-template-private-evidence-wrong-alias-red.log` (SHA-256
`0e38ae0a90da03b0a6f935609abb16e0a8421597e3eb445072f01da24cdd0cf0`).
Seven affected integration suites pass 194 cases in
`/tmp/ash-template-private-evidence-regressions-final.log` (SHA-256
`4ca697d0b0ec9f32e739abef43d26e1a940b6f49d7767ddb8be7ccf46b493b69`).
The existing lexical-method and admission-isolation checks also pass
(`/tmp/ash-template-private-evidence-method-unit-final.log`, SHA-256
`d8a30e51dcc444a2021306531ebdb415975e48215f850b6f2350c66b9a2fde4c`, and
`/tmp/ash-template-private-evidence-isolation-final.log`, SHA-256
`4aa7c68492571a9bfc28d4cab96fb8303f1c183198eb4b84e19743691fb64d12`).
The original private-interface and public-interface Core failures are retained
in `/tmp/ash-template-private-evidence-red.log` (SHA-256
`3511426481ec1db778d6beeebb31f8802f48c82285376e515ced04ed4bdb3b1b`)
and `/tmp/ash-template-local-evidence-public-red.log` (SHA-256
`becfbd71c9da82f054c03d169e6496523869c9b40a9237277e3ba35e81e6be68`).
Independent review cleared this observation at `4a79dcf9`; general private
closure, route mutations, other row positions, and complete acceptance remain
open.

The copied-invocation graph executed to 42 but prepared and validated the same
transformer entry twice. A debugger counted both calls through the real driver
(`/tmp/ash-entry-reuse-observe.log`, SHA-256
`b492ee4bbc3835c12ed1280adf4e58437535ec61953b63e1f76a4e438c789155`;
script `/tmp/ash-entry-reuse-observe.gdb`, SHA-256
`7977b11b8ca46cd2ef330727c474a822dac0dd954b3ca6d51f58fb73ed58c155`).
The current candidate retains a validated entry for its checked owner and
transformer binder for one compilation. Each invocation still creates its own
machine, input and root. The same graph now executes to 42 with one preparation
and one independent validation (`/tmp/ash-entry-reuse-observe-after.log`,
SHA-256 `5f9fcf8b747bda3f48e75dc06f7e1612ae0ca600e05585252ba2841c15ebd37d`).
A second real graph invokes the transformer from two importer modules; it
returns 42 with one preparation and validation. Changing a transitive helper in
a new compilation triggers a fresh validation and the changed transformer's
rejection (`/tmp/ash-transformer-entry-reuse-final.log`, SHA-256
`c0daaa4e2417a6e7ba0f68fc017281a6f2a16871b0287ad2329dfc97c4dd4e22`;
the prior two-preparation failure is `/tmp/ash-transformer-entry-reuse-red.log`,
SHA-256 `eb07eb623714bb91ee8ea71ac571c12ee64eae898364892c2c5fd5dee2657fbd`).
Four affected integration suites pass 139 cases in
`/tmp/ash-transformer-entry-reuse-regressions-final.log` (SHA-256
`bab129c19d1f634a9ac87fd8c3da7535eb32304026c32f7e04ccf4c19482eb4d`).
Independent review cleared reuse and changed-program revalidation at
`f19b1ab2`.

An ordinary type error in generated arithmetic previously labelled a zero-width
parser anchor. Projected generated tokens now use the actual invocation extent
while the parser retains its ordered grammar coordinates and the existing
literal-construction proof remains separate. The invalid template keeps its
`type.operator-operand` reason and `Int`/`Bool` facts, and its human and JSON
labels identify the invocation; valid generated arithmetic still executes to
42. The focused regression failed before this change
(`/tmp/ash-generated-token-location-red.log`, SHA-256
`bec841ce8d93654a0862279f87a63767e0c3c3e1b57ff266d63894f7c2f55781`)
and passes after it (`/tmp/ash-generated-token-location-final.log`, SHA-256
`435c338c3400f8e1abc3f6e8243882a737d78a9024c33d313180558c0a436795`).
Five affected integration suites pass 151 cases
(`/tmp/ash-generated-token-location-regressions.log`, SHA-256
`12e6dcc73e1091f3fae5a070d5f7853a3c82f8fb729a7de9436502d2549983e7`);
the existing literal-construction proof and five local-newtype checks pass
(`/tmp/ash-generated-token-location-proof.log`, SHA-256
`97fb32f9d2da260758df67d0e2627b43bd01a3e7980fae7a054c7997c125c228`, and
`/tmp/ash-generated-token-location-core.log`, SHA-256
`a653336fe52ee946c81d700967654037b4dd4e9cc5eaa1858d905639504d7fc5`).
Independent review cleared this partial repair at `b2367131`; exact definition
causes, combined inputs and nested expansion frames remain open and it earns no
additional ledger credit.

Qualified type, term and constructor expressions now select an alias in its
own context before selecting its public member. Six real graphs cover both
captured caller aliases and defining-module aliases, including conflicting
caller aliases, and return 42. Fresh aliases cannot borrow the caller's
import; private and opaque members, a lowercase alias, and missing literal
aliases, operands and type arguments are refused. The original captured-alias
case failed before this change (`/tmp/ash-qualified-capture-red.log`, SHA-256
`7ee850da792bbdbc5a497c513ff21f02df31c04d77e20616a6c0d783281513b9`);
five affected integration suites now pass 151 cases
(`/tmp/ash-qualified-context-suite.log`, SHA-256
`1d50658e0ae2c1dbd58b51400274779ba69ce00a0583422b4e7eb7cabae2e91f`).
Independent review cleared this partial result at `24bd8410`; it adds no ledger
credit. Other captured interface and pattern positions and broader scope hygiene
remain open.

An owner-qualified public effect previously produced an internal error even
though the handwritten equivalent ran to 42. The checked public-effect route
now retains the original identity for generated requests, handlers and effect
rows. Twelve real graphs, including the handwritten control, captured caller
and owner qualifiers, a facade, and a parameterized effect, return 42. Seven
negative cases refuse private effects, wrong kinds, lowercase names and missing
operations, aliases, operands or type arguments. The initial mixed-case failure
is retained in `/tmp/ash-qualified-effect-red.log` (SHA-256
`1e0fc8cf5bf6a9e0354c319003b7395089fe56c77ee5037e634b13dbe6690068`).
A first parser change broke the existing captured-operation case
(`/tmp/ash-qualified-effect-suite.log`, SHA-256
`9c5ac379f06e05058c1e85db3fec91630096842a317043e66cef4a551e6980d3`);
the corrected lookahead and seven affected suites pass 184 cases
(`/tmp/ash-qualified-effect-suite-pinned.log`, SHA-256
`537640c96a9bd6b2c66c7f3b0c58d38979fe8b0b8abf49b8499a1a1fdf2376f2`).
Independent review cleared this partial result at `2ad6e6be`; the named checked
effect-route observation is credited under P11.

Renamed targeted effect imports and owner-defined generic effects now retain
their original checked identities. Seven real graphs, including handwritten
controls, direct and facade imports, caller shadowing and an owner-private
generic effect, return 42. Five negative cases preserve caller privacy, reject
dependency-private imports and match handwritten wrong-arity failure. The
original targeted-import failure is `/tmp/ash-targeted-generic-effect-red.log`
(SHA-256 `54abc2e72e7bdb838d9b05aaef75a19aa153ff9a06c8636c77d52d7649e54120`);
six affected suites pass 180 cases in
`/tmp/ash-targeted-generic-effect-suite.log` (SHA-256
`7c7fa3b9683d53317e0784ae25d16c4335551174ce021027978a172be69d2900`).
Independent review cleared this partial result at `ee521864`; the named checked
effect-route observation is credited under P11.

A captured qualifier or member in a local-evidence interface application now
passes through the ordinary parser and resolver. Caller-context and owner-context
graphs each return 42, including a conflicting caller alias; the handwritten
control also returns 42. Wrong kind, missing literal alias, argument or method
body, and a method-pattern binding used outside its scope are refused. The
name-only admission path keeps no fabricated interface or evidence and restores
temporary resolver state on success and failure. The original failure is
`/tmp/ash-qualified-interface-red.log` (SHA-256
`e3dad1b56adac712b4a41d317eb820c21a10e99b1cb14b8cf16786f8aad89f7e`); seven
affected suites pass 215 cases in `/tmp/ash-qualified-interface-suite.log`
(SHA-256 `5a31d975c1d1a8fba852a7802e2605f25fa58deb196af93864ca8b3e415012eb`),
and the admission-isolation check passes in
`/tmp/ash-qualified-interface-isolation.log` (SHA-256
`48fbcc943750a091a493a5713c07e7e78e6017c38386ac4eb25469f7950f1ba2`). This
partial result was independently reviewed at `e9d873c5`; the named checked
interface-route observation is credited under P11.

A captured effect in a non-function row argument previously failed during
name-only admission. It now uses the existing deferred effect lookup after
resolving the row arguments, and transfers arguments only after an effect is
known. The original graph, a handwritten control and an owner-qualified graph
with a conflicting caller alias each return 42. Four negative cases refuse
missing row members in either order, a missing type argument and a wrong-kind
capture. The original failure is `/tmp/ash-captured-row-argument-red.log`
(SHA-256 `8e8ca4e44c9f41f769de52c876a72139ba070b178dde685942e8b10dbca692ca`);
seven affected suites pass 216 cases in `/tmp/ash-captured-row-argument-suite.log`
(SHA-256 `8af99e77eeb16373b36ea94331c6ac36ee0b03d88496512156a42a39594d0d72`).
Independent review cleared this partial result at `eeec9e7f`; the captured-row
observation is credited under P10.

Captured row tails now use the caller's contextual type parameter in function
annotations and interface row arguments. Five real graphs, including two
handwritten controls and a forwarded nested capture, return 42. A template's
introduced `R` does not capture the caller's same-spelled row parameter, and
missing literal or captured tails remain `resolve.unknown-type` failures. A captured
ordinary `Type` parameter used as a row tail has the same `kind.internal-state`
failure as handwritten Ash; an existing handwritten local newtype with an
effect-row parameter also reaches `kind.internal-state` (`owner-effect-row`).
The original capture failure is `/tmp/ash-captured-row-tail-red.log` (SHA-256
`537aba59399463b11e7e17ce9e06304d06d62ccef5262179e62f0dffa375fb68`); seven
affected suites pass 217 cases in `/tmp/ash-captured-row-tail-suite.log`
(SHA-256 `e2f0b01d88b3545dfe9e9e92e62cc82b046e595ba4b4e98c7d45466cfdd40198`).
Independent review cleared this partial result at `24c8d51c`; the captured-tail
observation is credited under P10. Broader row and scope hygiene remain open.

Captured constructor names in patterns now pass name admission without a
fabricated constructor identity; the ordinary resolver still visits the whole
payload and checks its binders. Six real graphs, including handwritten controls,
return 42 for owner-qualified, caller-qualified, unqualified and repeated
nullary captures. Seven negative cases retain ordinary opacity, name, duplicate,
scope and token-category failures, including an actual repeated lowercase
binder. Before the repair the captured qualifier failed to parse
(`/tmp/ash-captured-pattern-red.log`, SHA-256
`832b5d78eedd85d0ebed99a49ee543eeea7108573ab63b2848e1250473ed1f97`) and
the repeated nullary capture was mistaken for duplicate binders
(`/tmp/ash-captured-nullary-red.log`, SHA-256
`4ed1c596a097bca0586d58a74dc17064f83eee5c36667e34b668dfb699b5c3b9`).
The exact-placeholder deferral is shared by the existing type, effect,
interface and constructor admission paths. After that consolidation, eight
affected suites pass 244 cases in `/tmp/ash-captured-pattern-refactor-suite.log`
(SHA-256 `e24f5ffce0620b25e019971e4df3e2e213a0921b406dc2ea241576838eff0758`),
nine existing pattern cases pass in `/tmp/ash-captured-pattern-refactor-patterns.log`
(SHA-256 `f245ce550d53558ee54b5014a89e8c1ba2a301847e07b953576323eaa29e6b40`),
and admission-state isolation passes in `/tmp/ash-captured-pattern-refactor-isolation.log`
(SHA-256 `58e265a678db11ac1291900199784d336599eef78069de54245d62ddb0d8dcb8`).
Independent review cleared this partial result at `81eefcc9`; the named captured
pattern observations are credited under P09.

A real transformer unwrapping 100 nested groups now returns 70 on a 1 MiB
compiler thread stack, including its inner sibling tokens. The previous code
aborted with stack overflow (`/tmp/ash-syntax-unwrapping-small-stack-red.log`,
SHA-256 `d2fbab0d774e04d9bb648c5c4ea1e70a339c00aff82ef47c1806b110c24df1e3`);
the focused test now passes (`/tmp/ash-syntax-unwrapping-small-stack-green.log`,
SHA-256 `b290708384b51058c60b287b4b5dba31d76f3cf4f98f3eb6a80d70e0c657e09f`).
The existing conversion uses an explicit group traversal while keeping the
previous depth limit and node/origin order. Three affected suites pass 159 cases
in `/tmp/ash-syntax-unwrapping-stack-suite.log` (SHA-256
`0feee242981dd807748b511f52a1e89d47513a958ca6bf10d4b5df274ac4384b`).
Independent review cleared this repair at `f106bbe7`; it adds no ledger credit.

The next diagnostic slice retains an expression occurrence's causes and its
actual enclosing expansion frames through projection, resolution and checking.
For `add_boolean 40`, the real CLI now identifies the template's `true` and
`+`, and labels the caller invocation and syntax definition in human and JSON
output. A failing descendant of a protected caller capture retains its caller
location and enclosing frame. Nested expansions with equal invocation spans
retain separate frames; combined origins retain their ordered causes without
repeating one frame. The valid control returns 42. Before this change the
generated labels pointed at the invocation and the captured error lacked its
frame (`/tmp/ash-occurrence-origin-both-red.log`, SHA-256
`3db9b6d540a6c979f827949ee9ef290d789c427fd3b6ecf55866e9ddeb737efb`).
The captured expression's operator label now also identifies its written `+`;
the prior whole-capture label is reproduced by
`/tmp/ash-occurrence-origin-capture-operator-red.log` (SHA-256
`eb6ffe8c694ac0e3e14b53bbbdae51d9f2264c1f7a70766e55af2fa03ec912f7`).
The seven affected suites pass 255 cases in
`/tmp/ash-occurrence-origin-suite-final2.log` (SHA-256
`06c7c4e3c892cefe1c65add672dbe24a7e4fcae69a9ed7ff2adec2b8aa14eb01`).
The CLI human and JSON receipts are `/tmp/ash-occurrence-origin-final2-human.log`
(SHA-256 `ae594ee004246a4bdcf2a85a679ed6c0382621202c66d492e85d3d9a13362497`)
and `/tmp/ash-occurrence-origin-final2-json.log` (SHA-256
`0c801040ac15b1e77918a23cb196e9c84f9e59475ca987e7e944b9e0c03b0b5c`).
The captured operator CLI receipt is `/tmp/ash-occurrence-origin-final2-capture.json`
(SHA-256 `df570d149bbdd6e1b2fee57c8378cb86314211aaae4547f2e6f26e995c7a6d39`).
Independent review cleared this slice at `621f801c`; its occurrence and frame
representation is credited under P30. Broader causal coverage and complete origin
preservation remain open.
The private occurrence field also makes external Rust struct literals for
`SurfaceExpr` and `ResolvedExpr` unavailable; their parsed results still expose
their existing public kind and span fields.
The unchanged 256 KiB local-newtype accept/escape test passes after storing
optional locations and mismatch display strings compactly
(`/tmp/ash-occurrence-origin-stack-final2.log`, SHA-256
`b1e698e65f1fabd7142a56f22c648e6e58c956f151b366f821a4da9a13cfc068`).
The existing small-stack mismatch and context disposal test also passes
(`/tmp/ash-occurrence-origin-mismatch-final2.log`, SHA-256
`e75fe50bcc91481a47422f40dbafba593be4f3a61748354f1aaea8c9fc0f7f66`).

An inferred match now retains the first arm's occurrence when checking later
arms. Real graphs for `branches 1 else true` and its reverse identify both
caller inputs, retain the ordinary type reason and facts, and show one
invocation/definition frame; the valid graph returns 42. The earlier omission
is recorded in `/tmp/ash-origin-match-regression-red.log` (SHA-256
`8b42e2528027f33f9dc98813e068c4d8aa3e658a539c3acbf0a50bece306684f`).
The same expected cause survives a later function-context failure and a
function parameter pattern mismatch. A procedural expression's explicit
origin and an expected arm's combined origins also survive. Synthetic
template-forwarding origins no longer repeat the invocation as an extra cause;
the actual frame remains. The real human and JSON receipts are
`/tmp/ash-origin-match-human-final.log` (SHA-256
`9ea1c5c7b25e878ac4b2b16621575cf275ee8de1bebd506d61a487fa724b7e41`)
and `/tmp/ash-origin-match-json-final.log` (SHA-256
`d4ae1a926e0598d460f2f1da826e6d7fe069b9dcbb4eba0aa46dc29f4b9dafca`).
Seven affected suites pass 260 cases (`/tmp/ash-origin-match-suite-final.log`,
SHA-256 `ca15572ceb072895ebabcc65219f9a8a53319f916867a8aaa3a5e463a1c918da`),
and the unchanged 256 KiB accept/escape case passes
(`/tmp/ash-origin-match-stack-final.log`, SHA-256
`3285fc840093992e0705c588c040f4aa927aa77d7a1fcd7cd7660b4f3f9214b5`).
Independent review cleared this partial result at `79d3aad7`; broader causal
diagnostics and M/C acceptance remain open.

Application errors now retain the actual callee occurrence. A non-function
written in a template is identified at that token; a captured non-function is
identified in the caller. For an argument type mismatch, both the argument and
the generated or captured callee are retained alongside the existing function
domain relation. The valid callable graph returns 42. Earlier omissions are
recorded in `/tmp/ash-origin-application-regression-red.log` (SHA-256
`6d5e8e665ee32e0f9e537dd4bbfbef522b613d0f96e78911e893ba5f3caac7f7`)
and `/tmp/ash-origin-argument-regression-red.log` (SHA-256
`34776e9af02467d8df9223121b47eb661f17baac2c37564aec75dae2d6bbca28`).
The actual argument-error human and JSON receipts are
`/tmp/ash-origin-argument-human-final.log` (SHA-256
`50aaaa4df42c03eb821d40fe6031068bac22c464f025be7acc03103c17ee23df`)
and `/tmp/ash-origin-argument-final.json` (SHA-256
`ece397c395acf2c82197171052bbcbd1d83bad778c96f97a405fcd9582443d96`).
Seven affected suites pass 262 cases (`/tmp/ash-origin-application-suite.log`,
SHA-256 `e6335f355e37e86f66879486344e42be66372605a1a730d441e71d1173e8db60`),
and the unchanged 256 KiB accept/escape test passes
(`/tmp/ash-origin-application-stack.log`, SHA-256
`24145bf52b0dbea12f81a7e44ccb36f61d90ee46e6aa289eae3413df5d3320d9`).
Independent review cleared this partial result at `a1fec7d7`; broader
diagnostics and M/C acceptance remain open.

The previously supported combined macro graph still builds with public
`ash build` after this rewrite and returns 42 after its four copied Ash sources
are removed (`/tmp/ash-macro-common-native/build.log`, SHA-256
`06da86579f973c802a59d0d8afd00f67902fa4272e92622eea098952f05fbab6`;
executable SHA-256
`9f5d0ca10c7736e7b187fb9e35ee3466ec7f6297f9c753508a4794d579fd762b`).
The procedural local-newtype graph and its handwritten control both hit the
existing unsupported `RegistryMetadata` native-image boundary. Full scope
hygiene, causal diagnostics, M01–M14, C1 and C2 remain open.

The `core-authority/entry.ash` graph returns 42. An experimental mutation of
unchecked Core retargeted the caller's `ordinary` capture to a same-typed
private helper; ordinary Core validation accepted the changed program, which
returned 33 (`/tmp/ash-private-occurrence-authority-red-final.log`, SHA-256
`0a0760acc357d1ba914003e7b469cbf0e7a6e92a2e9d0a46717a837b89703e52`). This
does not demonstrate an Ash source or transformer access bypass: resolution
and linked-summary validation own source access and import routes. The
broader all-use Core correspondence prototype was parked at
`/tmp/ash-expression-authority-all-use-wip.patch` (SHA-256
`88e2be4b4044c21bca827f193bb9f60c7221e8d0988975704b1b64945f995b6c`).

The following grant-specific checkpoints are preserved exactly as evidence for
the earlier contract. The 2026-11-06 amendment below supersedes their
grant requirements; it does not erase the work or observations.

Definition-context global term selections now retain an occurrence-specific
grant through the existing checked-module and linked-summary boundary. The
linker checks the original syntax selection and import edge, checked owner,
target, access and route. Caller and fresh names receive no such grant. One real
private-helper occurrence retains the same grant into the linked group, passes
ordinary Core validation and returns 42. Separate linked-boundary controls
refuse mutations of a grant's target, issuer, export, route, access, occurrence
owner and selection, including a duplicate grant
(`/tmp/ash-syntax-term-grant-unit-final.log`,
SHA-256 `7a882ff5b90dc8cd6d36b978a6dc0470cf1af2c6b930f2317dd343a1d5f452b9`).
The 78-case driver suite passes with nested syntax, facade routes, privacy and
the combined-origin capture controls (`/tmp/ash-syntax-term-grant-driver-final.log`,
SHA-256 `7b990b3c47b373504d7a215fe855e33986d68b78fc66b14368b7ecaa5fac5e86`);
the unchanged 256 KiB stack case also passes
(`/tmp/ash-syntax-term-grant-small-stack.log`, SHA-256
`7c3a2a76a38b0c0f37039ecfbbd19ce199bca053a27998f9b5831d9602dd0dbd`).
Independent review passed at `ffe80802`; non-term grants and broader private
closure remain open.

The combined template and computed graph still interprets to 42 and its
native executable returns 42 after the four copied source files are removed
(`/tmp/ash-syntax-term-grant-native.log`, SHA-256
`7c34cb88866897f9b1b4537838734ea0acb92c12ea4a59122fd230514dd4e8c0`).
The executable is `/tmp/ash-grant-native-CYM561/program`, SHA-256
`261a04a3c9aaede0c63031b04bc8dc278180360a68bc2228ba9c1ded05050088`;
the exact probe is `/tmp/ash-grant-native-probe.sh`, SHA-256
`5c17b43f7744d1c39150958d1961961a2ca151e51557c75b32195f1ec61262b4`.

The same combined graph exposed a missing constructor handoff: its two copies
retained only two helper grants rather than the six helper and constructor
grants (`/tmp/ash-syntax-constructor-grant-red.log`, SHA-256
`58286c1f96cd7df030c8ad7c24ac79f7e973ce7448bfa3e046225c4fe7bc1fa7`).
The working-tree change retains the four constructor grants through the same
checked occurrence and linked boundary. A nested constructor graph retains four
distinct expression and pattern grants and returns 42; caller and generated
lexical constructors receive none. The focused checks also verify the public
facade route and refuse a withheld constructor or changed route
(`/tmp/ash-syntax-constructor-grants-final.log`, SHA-256
`417056a8ae800bf892b67f76c2b0039e037f7baac9dce66530dc9bcdb50b8d3a`).
Linked grant mutations cover both global and constructor targets
(`/tmp/ash-syntax-constructor-grants-mutations.log`, SHA-256
`34c290ea2f2235fa573dc37cc0999889b11947e827bb8f47c61545f1494d5029`).
All 78 driver cases pass (`/tmp/ash-syntax-constructor-grants-driver.log`,
SHA-256 `ad894790bb0bb98c342f99f25d6f42d809e30cdc23d92fa9a8a015f8a2a822ff`),
as does the unchanged 256 KiB case
(`/tmp/ash-syntax-constructor-grants-small-stack.log`, SHA-256
`8edf6fac405833a14c5b2687f3b25a18b3b1de45a4d1c90f379501a65160e2ee`).
The combined graph also interprets and builds to 42 after deleting its copied
sources (`/tmp/ash-syntax-constructor-grants-native.log`, SHA-256
`a749664380cb69e6191ed2dc963f5d8748bbff5057ab98ea12e1879d19495163`;
executable SHA-256
`7ac2ed2291ba5a1a642ab7338a9a88fdb3dcf6dea2dd7e364cfbec7c115470f9`).
Independent review passed at `7c50916c`; grants for the other namespaces
remain open.

A private owner type in a generated annotation resolved correctly but its
nominal occurrence was missing from the linked grant list: the real graph
retained two constructor grants instead of those two plus the type grant
(`/tmp/ash-syntax-nominal-grant-red.log`, SHA-256
`36bcde2adc433d5bbe16e0255882af7a8cc6b667b04ba21518e1afad90104d76`). The
current change retains each selected nominal grant with its resolved type
occurrence and passes the same grant to the checked module. The graph returns
42; two written occurrences have distinct grants, while views retain their
original grant. Public facade and private-access controls and 27 linked grant
mutations pass (`/tmp/ash-syntax-nominal-grants-final-check.log`, SHA-256
`49dfb8f879175386b9f297753f13afd2eb8a8c56491da72afa791c78f11c6266`). All 78
driver cases pass (`/tmp/ash-syntax-nominal-grants-driver-review.log`, SHA-256
`4a5fd040811b785aa323d54e29316f118dd059311f4c4a8ecc719761fb9b6688`), as does
the unchanged 256 KiB case (`/tmp/ash-syntax-nominal-grants-small-stack-review.log`,
SHA-256 `a2c34fae7bff64f65cc2aa9b0e3c4f0ddd3555a9ee69557ca9bc71d1fd828ee5`).
The existing combined graph still returns 42 in the interpreter and in a native
executable after its four copied sources are removed
(`/tmp/ash-syntax-nominal-grants-native-review.log`, SHA-256
`bc809630f2ed56b95a6780f4aac8b5b8375d8d741e1ab87a61da0b478624e715`;
executable SHA-256
`03e4080073a854f28fde2f0348951a023bbef28fdcbb94b4a2b5f96022598bfe`).
Independent review passed at `8af9a896`; other nominal lookup sites and other
grant namespaces remain open.

The private-interface example returned 42 but its definition-site `check`
method occurrence retained no grant (`/tmp/ash-syntax-method-grant-red.log`,
SHA-256 `da8ded84c07b8110672b8a7924b493efc8a9513edae65f88bd690f60988af000`).
The current change retains the selected method on the existing resolved
occurrence and checked link path. Private, renamed and qualified methods keep
the exact occurrence grant; a generated lexical shadow keeps none. The eight
focused grant checks, including 36 target and route mutations, pass
(`/tmp/ash-syntax-method-grant-final.log`, SHA-256
`b32029c84d95830c3f7451b4c4e511a33a0cf6975beceb8c7ba9002b78fbbc61`). All 78
driver cases pass (`/tmp/ash-syntax-method-grant-driver.log`, SHA-256
`ca7c8003bb7bb6d617cadee30bd7ee4972bfcb1da738f2741e4e816a22423d06`), as does
the unchanged 256 KiB case (`/tmp/ash-syntax-method-grant-small-stack.log`,
SHA-256 `2781e8f3ebe20213a3e992755d2800b751e4670f66653d26ae79751a93984926`).
A targeted public method with an explicitly imported implementation returns 42
both through the interpreter and from its native executable after the three
copied sources are removed (`/tmp/ash-syntax-method-grant-native-supported-final.log`,
SHA-256 `0963135b7408f22f04a1cf4286ba12ddab330bd30ca4b750ab122c0d822a18c1`;
probe `/tmp/ash-syntax-method-native-probe.sh`, SHA-256
`6d55d3eb19779442f274b666cc45809dffe7f4593ecbc2a02bd4ad563ad8056f`;
executable SHA-256
`9bf86fef87f0a9b5c9f2139fb8d87beb4d2cedb8034682f6a2de20284f3fb5dd`).
Independent review passed at `b19e160b`; interface/equation selector grants,
other namespaces and full acceptance remain open.

The same private-evidence graph retained its method grant but missed the
definition-site `Check` interface occurrence
(`/tmp/ash-syntax-interface-grant-red.log`, SHA-256
`e4db474b6e035de29557b606f517b55ec401a435b6ca6f007ea365ad016f1a1a`). The
current change retains the interface grant on its resolved occurrence and in
the existing checked link list. Private, renamed, qualified and owner-decoy
graphs return 42 and retain both exact interface and method grants; a captured
caller interface and generated lexical shadow retain none. Public-facade and
dependency-private controls and 45 grant mutations pass
(`/tmp/ash-syntax-interface-grant-review.log`, SHA-256
`6326e37c906fa626dd24df5ce8b9983d282cde8d26be23088492de393609a633`). The
name-only admission state check passes on success and errors
(`/tmp/ash-syntax-interface-grant-admission.log`, SHA-256
`e3cd1045ad59dd2a0cc6978774c4a86d52cbac0e20c08e8e2220ef0ffa187ef2`). All 78
driver cases pass (`/tmp/ash-syntax-interface-grant-driver.log`, SHA-256
`83c0e9113ba9d343474f363e53a1f2d1ff98ce266b860a657346306fd9d94652`), as does
the unchanged 256 KiB case (`/tmp/ash-syntax-interface-grant-small-stack.log`,
SHA-256 `ca92f5542cacb7f7f89310811cecb77faff161426ee3cc0fe050a10b7971e0fb`).
Independent review passed at `49575c1d`; other interface sites, other grant
namespaces and full acceptance remain open. The previously recorded
local-nominal image limitation still applies to the private-evidence graph.

The private-effect graph returned 42 but retained neither the generated
`perform` nor handler reference to its owner's `Ask`
(`/tmp/ash-syntax-effect-grant-red.log`, SHA-256
`557eee1bd5d900b5b84f1c1218004e3e809d2ca25c7416a40fc009b68a30b736`). The
current change retains separate grants on the two existing resolved effect
instances. Owner, caller-captured, renamed and facade graphs pass with their
expected grants, as do 54 linked grant mutations
(`/tmp/ash-syntax-effect-grant-focused.log`, SHA-256
`2009a4928b74d96fdf2ff5250aa8d263e48c2371f5e2bdb9251c4d7c6b07444d`). All 78
driver cases pass (`/tmp/ash-syntax-effect-grant-driver.log`, SHA-256
`d85a7ae6d802f6c65108fe1955b740c80e3bf523af6d397d4cccbdb9c8647495`), as do
the admission-state check (`/tmp/ash-syntax-effect-grant-admission.log`,
SHA-256 `b43ef2010bff46ed67b9d7b165a0787a3278c69ba5748c1fc10923bac6829dc5`)
and unchanged 256 KiB case (`/tmp/ash-syntax-effect-grant-small-stack.log`,
SHA-256 `43adc6236df94f74d7b0a3589365ada5ff8aeb60d1f6d5fd0323d861830f3839`).
A qualified handled-effect graph returns 42 in the interpreter and from its
native executable after its four copied sources are removed
(`/tmp/ash-syntax-effect-grant-native.log`, SHA-256
`428fa3f64cbd59d5b67671290132c9a5931fae4e85e26de47f9fdf3188c39483`;
probe `/tmp/ash-syntax-effect-native-probe.sh`, SHA-256
`0964b508190aeecc87933823a5960b4c242f2334c9225d1b59bef2aedf4abab8`;
executable SHA-256
`164a7151d6b27f368f23053807fcf13107d68d865312a15426df441ef4a93233`).
Independent review, effect-row occurrences, other grant sites and full
acceptance remain open.

## 2026-11-06 approved amendment

The earlier implementation added per-reference grant objects and link rechecks
for globals, constructors, nominals, methods, interfaces and effects. The user
approved an amendment to CP-0033 removing that extra representation: issued
contexts select a checked owner environment, ordinary resolution enforces its
access and import rules, and existing linking retains the checked closure. The
reviewer found no additional source-level protection from the grant objects.
The previous grant-count and grant-mutation receipts therefore describe a
superseded contract; they do not establish current acceptance. Preserve the
independent identifier-origin repair below and verify private/opaque access,
caller isolation, dependency visibility, handle authentication and ordinary
checking through the actual driver after removal. The pre-amendment uncommitted
work was saved at `/tmp/ash-grant-amendment-wip-20261106/tracked.patch`
(SHA-256 `6bc1331aa4115b9a5c56d1449fde9a69973bea8df8d4ed9dc58e3ea251439f17`),
including an unfinished, separate pattern-diagnostic attempt.

The user also clarified that template definitions receive syntax checks only:
free names resolve in the defining environment when an invocation expands.
Earlier receipts below for rejecting unknown names in unused templates document
the superseded timing, not current acceptance. Transformer `using` targets and
ordinary imports remain checked at definition as before.

### Remaining scope and additional work

The original ledger remains **61.5 reviewed points out of 100**, with its
completed observations and receipts unchanged. Of its 38.5 uncredited points,
one point of pending P11 grant-object and grant-only mutation work is removed;
ordinary source privacy, checked routes, private closure and Core checks remain.
The current original-scope remainder is **37.5 points**. The unused-template
name check had no separately weighted pending unit, so its removal does not
change the historical credit or subtract another point.

The following additional work was performed outside those credited outcomes.
Its points are an estimate of effort already spent, not new product-acceptance
credit. The measured endpoints are Sofia-time session and receipt timestamps;
they bound elapsed work, not exclusive active time or model runtime. The windows
do not overlap and do not add concurrent reviewer time.

Session line references use these retained JSONL files under
`~/.codex/sessions/2026/11/05/`:

- `ROOT`: `rollout-2026-11-05T15-10-00-01a1abd4-9e53-7792-adab-b49682c7ce1e.jsonl`.
- `REV`: `rollout-2026-11-05T15-12-15-01a1abd6-ae1e-7193-96b6-c5f400e351fd.jsonl`.
- `DEV`: `rollout-2026-11-05T15-32-02-01a1abe8-ca19-7363-ac59-5e49da626dca.jsonl`.

| ID | Elapsed window and evidence | Estimated extra points |
| --- | --- | ---: |
| X1 | Shared carrier/parser rework: 01:13:06–01:59:35 and 02:33:08–02:59:40 on 6 November (73.02 minutes), ROOT lines 12572, 13339 and 13966, commit `e9c42975`, and `/tmp/ash-common-shared-path-regressions.log`. Excludes the P09/P10/P30 feature observations. | 7 |
| X2 | Iterative syntax unwrapping stack correction: 12:22:27–12:28:31 (6.07 minutes), REV lines 8558 and 8617, `/tmp/ash-syntax-unwrapping-small-stack-red.log`, `/tmp/ash-syntax-unwrapping-small-stack-green.log` and `f106bbe7`. Excludes P24 lifecycle observations. | 0.5 |
| X3 | Diagnostic-payload layout and small-stack correction: 13:05:17–13:15:28 (10.18 minutes), DEV lines 44838 and 45468, `/tmp/ash-occurrence-origin-small-stack.log` through `/tmp/ash-occurrence-origin-mismatch-stack.log` and `621f801c`. Excludes credited P30/P31 diagnostic behavior. | 1 |
| X4 | Discarded all-use Core census: 14:09–14:56, with 24–43 minutes attributable after excluding overlapping identifier-origin work. ROOT lines 22255, 22489, 22571, 22936, 23109 and 23162 bound the investigation and interruption; DEV line 49730 records the parked patch. `/tmp/ash-private-occurrence-authority-red-final.log` and `/tmp/ash-expression-authority-all-use-wip.patch` retain its evidence. This prototype was abandoned, not accepted product work. | 3 |
| X5 | Per-reference grant implementation and incomplete row extension: 14:58:03–16:58:35 (120.53 minutes), ROOT lines 23188 and 25494, DEV line 55230, reviewed checkpoints `ffe80802` through `6a143845` and `/tmp/ash-syntax-effect-row-grant-focused.log`. These grant objects were subsequently removed; source-feature and native observations already credited elsewhere are excluded. | 11 |
| X6 | Grant removal, template timing change and failed-gate repairs together: 17:12:24–18:30:48 (78.4 minutes), ROOT lines 25735 and 27364 and the amendment receipts above and below, including `/tmp/ash-context-amendment-deep-abandonment-green.log` and `/tmp/ash-template-amendment-architecture-final.log`. The union avoids counting overlapping refactoring and gate repairs twice; the later successful full gate remains under P36. | 7.5 |
| **Total additional performed effort** | **312.20–331.20 elapsed minutes**, depending on X4. | **30** |

For X4, the lower bound counts the documented census intervals after the
identifier-origin repair and around the rollback. The upper bound uses the full
14:09–14:56 span less the 3-minute-37-second identifier-origin interval.

The conversion uses the earlier recorded checkpoint pace of 55.5 reviewed
points over about 10 elapsed hours, or **5.55 points/hour**, with each row
rounded to the nearest half point. That pace is an approximate historical
scale, not a measurement of active time. The X4 time range gives 28.9–30.6
unrounded additional points at that scale. For sensitivity, the 20-point
foundation from `80994bec` at 15:04:45 to `26b43869` at 18:57:59 gives about
5.14 points/hour; the 46-point first stint from ROOT session creation at
15:10:00 to its reviewed report at 22:01:14 (ROOT line 8761, REV line 2838)
gives about 6.7. Applying those elapsed rates gives roughly 27–37 additional
points. Other mixed or unrecorded work is not assumed to be zero. The
04:20–09:29 gap is excluded because activity there is not established.

For effort accounting only, the amended original scope is 99 points and the
30 additional estimated points bring the total to **129**. Historical 61.5
plus the 30 estimated performed points gives **91.5 accounted**, with the same
**37.5 original-scope points remaining**. This approximately 71% index is not
a feature-completion percentage or an M/C acceptance claim. No removed work is
counted as a completed requirement.

The current known-work scenario is about **4 hours 51 minutes**; its component
estimates and evidence are in the [remaining plan](../plans/2026-11-05-expression-macros.md#2026-11-06-remaining-scope-amendment).
As a separate low-confidence arithmetic benchmark, 37.5 points divided by the
5.55-point/hour historical pace is about 6.8 hours. Neither is a deadline or
an active-time measurement; they are not combined with an extra buffer.

The earlier implementation rejected the unused missing-helper control
(`/tmp/ash-template-deferred-names-red.log`, SHA-256
`b13661b3c818e86f08b4a12dc8e6ffe98ed47a7fe2679184d0bf8b576447001b`). With
syntax-only definition checks, it runs to 42; invoking that template still
rejects its unresolved definition-context helper, even when the caller defines
the same spelling. The shared driver, host, module and JSON suites pass 164
tests (`/tmp/ash-template-amendment-regressions.log`, SHA-256
`a881f0945442931b2c2898343c281982bdd302909bc1563f5ec377b30967963b`).

The amendment uses one connected checkpoint:

1. **Resolution and behavior — demonstrated.** Remove grant-only records and
   rechecks, retain checked syntax selection and dependency linking, and run the
   real private-helper, opaque-constructor, private-type, context and visibility
   controls. The surface, host, module resolution/visibility and JSON suites
   pass 137 tests in `/tmp/ash-context-amendment-regressions.log` (SHA-256
   `9d1cb2c0c626782e404da8ca421bc60d982f45175dcc8aebdf5d383f187827eb`).
2. **Compiler consumers — demonstrated.** The unchanged 256 KiB local-nominal
   scope check passes (`/tmp/ash-context-amendment-stack.log`, SHA-256
   `243e744c67e270243ab15a700bbd989580f5b607cede47aaf8859ad09836ea53`).
   The combined graph returns 42 in the interpreter and its native executable
   returns 42 after the four copied Ash sources are removed
   (`/tmp/ash-context-amendment-native.log`, SHA-256
   `cfa9ebc883c6b5b49c366170aebb02deedad038d0c559eed3c842e1af4e1d9ff`;
   executable SHA-256
   `db6d7c3ba2d1ec4df329821d1c5079c638cceb3e06a306f36fb04c8605549deb`).
   The first fresh full gate stopped at `check`: a pre-existing polymorphism
   test's exhaustive value classifier omitted the macro host's syntax-handle
   variant (`/tmp/ash-context-amendment-full-gate.log`, SHA-256
   `848a91af229fd3e3186c2dae4db2f095033acbea796453f1ac3f9e7885ac00f7`).
   The classifier now names that variant, and the all-target workspace check
   passes (`/tmp/ash-context-amendment-all-targets.log`, SHA-256
   `05c239142bcc007f2d3cc2764b3baae64987fe01be26eb979df3f28e180054f1`).
   A second gate passed the all-target check and build, then stopped on
   Clippy findings (`/tmp/ash-context-amendment-full-gate-rerun.log`, SHA-256
   `6fbce2aff1d5164bef6b6e675e0ecff96505955e768c309720ce1c177682e5b7`).
   The repair keeps the public error types and work-reporting accessors while
   reducing private diagnostic storage, and resolves the other local lint
   findings. All-target, all-feature Clippy now passes with denied warnings
   (`/tmp/ash-context-amendment-clippy-final.log`, SHA-256
   `04f5dc9a1f43ff8af2fc8b4803f241304ee6adeb866f8320744a80da32dafbda`).
   Focused source and graph failures retain their work reports, the
   pre-census graph failure retains no report, and the unchanged 256 KiB
   canary passes after the repair. The next full gate passed those stages but
   exposed a stack overflow in the existing 64 KiB deep-abandonment query
   (`/tmp/ash-context-amendment-final-gate.log`, SHA-256
   `a6b399fd8130c913ec0e2bcb385a1815ac85b49ecdf380a58b761345f27439c1`).
   Moving continuation selection's temporary workspace out of the later
   discard path preserves its work and behavior; the unchanged test now passes
   (`/tmp/ash-context-amendment-deep-abandonment-green.log`, SHA-256
   `ddb0c6ffcca7dfb09567f21b4760dab060c99a82d7a699d7d6c7f49133c69493`),
   along with adjacent resume, discard and retained controls. The following
   gate passed all 1,729 library tests and stopped on stale architecture
   inventories (`/tmp/ash-context-amendment-final-gate-rerun.log`, SHA-256
   `523db7f382c06f1d90b7e67e9bf674c3899d7af2ab44ca40cc01be39772abe09`).
   The refreshed inventory retains its ownership and evaluator boundaries;
   its 47 tests pass (`/tmp/ash-template-amendment-architecture-final.log`,
   SHA-256 `3f3cd2ed50cc9596f13df537fd9fa955cdc3526461cbfb746acbdf5521190db8`).
   After the timing change, the combined graph again returns 42 through both
   interpreter and native executable, with all four copied sources removed
   before native execution (`/tmp/ash-template-amendment-native.log`, SHA-256
   `e6f33e4ef6eb84e00f60977d610357c69a1de370a6ce94d0bfd9ecb31070e0de`;
   executable SHA-256
   `18d12a0588cb32fbf216c28ac31f62dd3818e7c0331e94e5947868a8611c309c`).
   The next gate stopped at a Clippy finding left by the timing cleanup
   (`/tmp/ash-template-amendment-full-gate.log`, SHA-256
   `bd48f60c46d0cdd617d4ae92450515568370e3dd56f34fcb8e635af13602f90f`).
   The equivalent lookup and test-assertion cleanups pass all-target,
   all-feature Clippy (`/tmp/ash-template-amendment-clippy-final.log`, SHA-256
   `1cc5da17371f74347594366b9116b2da2baca08ee5f2b2c2c4058e0f63ff8b83`).
   The fresh full gate passed all seven stages without reuse on commit
   `6b72d2de7c3ea66e013102a83552214dd1dd6f38`, tree
   `32170c5f95ce2cc693eff7f8c4f554b7334c92f3`
   (`/tmp/ash-template-amendment-full-gate-final.log`, SHA-256
   `21228a9672dce2bfdb0b292bc0e7111211e5ac8aaed32dccf20680e6bf7537b0`;
   JSON receipt `/tmp/ash-template-amendment-full-gate-final.json`,
   SHA-256 `51d8b9346d705b29f9faa240f819ec085e0a87f44dd49d6afe8584c25b65a84b`).
   An exact-pin interpreter/native rerun returned 42 after removing
   all four copied Ash sources (`/tmp/ash-template-amendment-native-final.log`,
   SHA-256 `61cdeac0a913b6fb303ada0e19b1614510ddbae9009185119c61e3ceab49ae26`;
   executable SHA-256
   `f59b32916453b9e3c3c4d252cac76a62288bca07047fb990333035b5428f6dcf`).
3. **Review and retention — partial review passed.** Independent review found
   no blocking code issue at `6b72d2de` and verified the full-gate and native
   receipts. The remaining plan correction receives its own review. M01–M14,
   C1/C2 and milestone acceptance remain open.

A nested identifier-capture probe lost a combined origin: the outer transformer
supplied the caller invocation and outer definition, but the inner rejection
retained only the invocation and inner definition
(`/tmp/ash-identifier-origin-capture-red.json`, SHA-256
`04379c09b00ab95b4fbcd4e40d1d2bfabd2163355867f54cf11b2e7ef17928e4`). The
working-tree repair retains the identifier's original origin through direct
and template-forwarded capture. Both driver cases pass in
`/tmp/ash-identifier-origin-capture-green.log` (SHA-256
`0b3a4259fb1182b6d6eb97e7eeaef92208f8358a94296799ae6300316225d2e3`).
Independent review passed at `ffe80802`; broader P30/P31 causal-origin work
remains open.

### Pattern and matched-value diagnostic checkpoint

A generated Boolean pattern now reports a mismatched captured value as the
primary location, with the failing pattern and its `Bool` requirement as a
related cause. The original `pattern.type-mismatch` reason and `Int` fact are
retained. A nested tuple control keeps the leaf's type facts on that pattern,
not on the whole captured tuple. A caller-written pattern inside a captured
block remains primary at its own source and retains its enclosing frame.
Handwritten diagnostics remain unchanged, and valid controls run to 42.
Both human locales and JSON are covered. The private diagnostic field also
makes external Rust struct literals for `SurfacePattern` and `ResolvedPattern`
unavailable; their existing public kind and span access remains.

The original failure is `/tmp/ash-match-pattern-scrutinee-red.log` (SHA-256
`e1a9dc092d61814740b810662cd8886e64eb4b54dd89cc2ca4dedd34d5e43e94`). The
final macro and presentation suites pass 96 cases in
`/tmp/ash-match-pattern-presentation-final.log` (SHA-256
`e57f24a98170883e75815c846be726f6ae1b85d5de2ac29957d1cce101a71ff4`). The
earlier broader run passed 194 cases, including architecture and ordinary
pattern checks, before the final message-only change
(`/tmp/ash-match-pattern-affected-suite.log`, SHA-256
`2d846624dcec4aa9ed2b0d16acba2f4bf0a89329e0f7dc4d05bf3f6d5d31a54e`).
The final CLI human and JSON observations are
`/tmp/ash-match-pattern-human-final.log` (SHA-256
`155b99238ca1dd5a6c5cb586bb886a3d1b7644f6b7696fcaa729dd1cdf9115e3`) and
`/tmp/ash-match-pattern-json-final.log` (SHA-256
`49163605141ccfec8b3b1ac7723d585d9b401df8cd318c701e43d265d3e06db5`).
The all-target Clippy check passed (`/tmp/ash-match-pattern-clippy-final.log`,
SHA-256 `66c0cc6e47059f64c02672d7bd76ee00befcd485321e8e9d3f845190a4ad9ff6`).
The unchanged 256 KiB driver and pattern-disposal canaries also pass
(`/tmp/ash-match-pattern-stack-driver-final.log`, SHA-256
`427a7472fcd6ba67eed08afff479586e5c33c2af380839dd2ceae09fb382fca5`, and
`/tmp/ash-match-pattern-stack-mismatch-final.log`, SHA-256
`2fd3c8536f1a1f99bdd62a8be54328d9c3bef1cd63e84eeb918381199e301c5f`).
Independent review and broader causal/M01–M14 acceptance remain pending.

### Combined graph and matcher evidence

The new combined graph runs both the template and checked Ash transformer
versions to 42. Each duplicated capture reads and increments a cell; the final
cell value distinguishes two evaluations from one. A same-spelled caller DSL
is present while the expanded form uses its owner's separately authored DSL,
private helper, and opaque constructor. The existing `template-effects`
entry, handwritten, and reversed cases distinguish effect order (42, 42, and
33 respectively); the new symmetric sum alone does not.

The original `copied_macro_fragments_have_distinct_checked_local_identities`
test now also inspects each copied binder's body use, each local nominal's
wrap and unwrap, each resource handle use, and both initializers' reference to
the actual caller `outside` binder. Its receipt is
`/tmp/ash-acceptance-copied-uses-final.log` (SHA-256
`4f59ebe19675239fc7cef7a20ba6edac3c9eb84b42043a57b0851ec79066f539`).

The imported `if` cases execute both nesting directions with LF and CRLF,
check parenthesized application and final-capture precedence, reject missing
captures or separators and unparenthesized application, and preserve the
`Bool` cause for `if 42`. The five affected driver, host, module, and parser
suites pass 233 cases in `/tmp/ash-acceptance-graph-suite.log` (SHA-256
`21dd4e0bc88162d094413ab48931a57579e93ea628558bc76f423e7ff6e96364`).
The test-target Clippy check also passes (`/tmp/ash-acceptance-graph-clippy.log`,
SHA-256 `47b29dac0a3652d87fca542f99d2ec3b25b89abcc5702d6eeccb7fa7ddae0308`).

The interpreter returned 42 for the computed, effectful graph. After building
and deleting all five copied source files, the executable also returned 42.
The exact commands, source/compiler and executable hashes, and artifact path
are in `/tmp/ash-acceptance-native-final.log` (SHA-256
`b063481ac8751cf1597915cad7f73c57fca31cb9f2beb8c1cc91f0832ced74fb`); the
retained script is `/tmp/ash-acceptance-native-run.sh` (SHA-256
`cd014cd377853c3efdb185a2d87a9e91e8b3b0b2b5674b51d040adb6ea1ced2d`).
The initial build attempt used a stale compiler binary and correctly rejected
the runtime fingerprint; its log remains under
`/tmp/ash-acceptance-native-uwqzFm/.ash-build/`. The successful run rebuilt
the compiler from the matching source first. These are partial observations;
review, the remaining M01–M14 evidence, and C1/C2 remain pending.

### Host boundary evidence

The real Ash transformer in `acceptance_host_ops.ash` checks out-of-range and
oversized capture indices, invalid identifier and token requests, and an
empty origin combination, then forwards its valid captured expression to 42.
The private host test exercises a valid identifier capture and a negative
index, rejects live and stale inputs from other invocation tokens, and accepts
a valid output before rejecting the same payload under a different outer
constructor owner. A negative integer is injected at the host boundary because
ordinary Ash source has no negative expression syntax.

The corrected host and vocabulary unit tests pass in
`/tmp/ash-spec-host-unit-final2.log` (SHA-256
`9fb7c37fece82e9d7df834d578e02f98144ba5637d0d30e975cc04a78054b297`),
and the full host integration suite passes 43 cases in
`/tmp/ash-spec-host-suite-final2.log` (SHA-256
`242405179807d12b1b321fc8b361807e4c5408b7de7c043fc20f0f625830e462`).
The earlier identity test omitted the required output payload, so its refusal
for the wrong nominal was not discriminating; the retained
`/tmp/ash-acceptance-host-identity-final.log` is superseded for that claim.
This evidence awaits independent review and does not close M10.

The active-disposal probe built a tree of captured closures, reached a syntax
service after construction, and then exhausted transformer work. The actual
active root was dropped, but the disposal worklist made no growth attempt and
the injected refusal remained armed. This does not demonstrate either a
teardown failure or a leak. The paired active-disposal refusal remains open;
the intentionally failing probe is retained outside the candidate in
`/tmp/ash-active-disposal-probe.patch` and
`/tmp/ash-disposal-active-probe/`. Its result is
`/tmp/ash-active-disposal-curried-probe.log` (SHA-256
`fd7adf00c46d18dd4d6c2141a7a49c7ae5a83147a8fd32e6afb2ef1656496569`).
The production transformer handoff drops the machine within the same disposal
scope whose `finish` method combines an error with the first teardown failure.
Four existing tests now pass on this candidate for active-root destruction,
that common failure combination, first-secondary retention, and a real refused
environment disposal through ordinary `Machine::run`
(`/tmp/ash-active-disposal-composition.log`, SHA-256
`b7187769b6865b7b07dc86d8f1d53695fb91551f66e4ddc2bba950bbe7f2857e`).
These are separate observations; they do not claim a single injected refusal
in an active transformer.

### Specification and tool documentation candidate

The candidate describes the selected expression-syntax slice in a new
specification chapter and connects it to the existing grammar, names, typing,
elaboration, execution and tool chapters. The canonical token table and the
13 service signatures are checked against the existing lexer test and Ash
module. The documented `if` example runs and prints `42 : Int`
(`/tmp/ash-spec-if-example.log`, SHA-256
`93d158dc4f3e49e87da47f5208131722a2589ace79685e55de34a34302570487`).
The host and vocabulary unit tests pass in `/tmp/ash-spec-host-unit-final2.log`
(SHA-256 `9fb7c37fece82e9d7df834d578e02f98144ba5637d0d30e975cc04a78054b297`).
All-target test Clippy passes in `/tmp/ash-spec-host-clippy-final2.log` (SHA-256
`d33b5e8e5eb90c454bd45b83797477dc2d3344f23ce3882df36fd79f9bf5d48f`);
changed-document relative links and the preserved historical ledger also
pass manual checks. The documentation and host evidence await review. The
accepted proposal remains until the complete product checkpoint is retained.

### Reviewed progress update, 6 November

Independent review cleared the pattern diagnostic at `a3f6650b` and the
combined graph and identity evidence at `6216692f` and `cb9d8963`. The
following increments apply to the remaining work recorded below; the earlier
61.5-point ledger and its receipts remain historical records.

| Item | Newly reviewed evidence | Credit and remaining work |
| --- | --- | --- |
| P10 | Copied binder, nominal, and resource uses are associated with their own declarations; both resource initializers target the caller's actual `outside` binder. | +0.5; 4.75/5 reviewed. Mixed copied nominal/region and broader type-scope work remains 0.25. |
| P27 | The template and checked-transformer versions of the combined graph both return 42 under the caller's same-spelled DSL. | +0.5; 1.5/2.5 reviewed. Discarded and repeated nested invocation behavior remains 1. |
| P30 | The ordinary pattern mismatch retains the captured value, failing pattern, and tuple-leaf causes. | +0.25; 1.75/2.5 reviewed. Other causes remain 0.25 and bounded copying/relocation remains 0.5. |
| P31 | The pattern diagnostic presents its neutral value label and Boolean requirement in English, Bulgarian, and JSON, with the captured-block frame control. | +0.25; 1.75/2.5 reviewed. Other variants, frames, and catalog conformance remain 0.75. |

The amended original scope is 99 points: **63 reviewed and 36 remaining**.
The separately estimated 30 points of performed additional work give an
effort index of **93/129, approximately 72%**; that index is not feature
acceptance. The earlier seven-stage gate remains evidence for its exact pin,
but P36 is not credited until its C1 prerequisites are met. No native-work
credit is repeated here. M01–M14 and C1/C2 remain open.

The [20:34 operational update](../plans/2026-11-05-expression-macros.md#2026-11-06-operational-update-2034)
supersedes the earlier 4-hour-51-minute scenario. The host input and output
boundary tests are demonstrated and await review; the current connected-work
scenario is 186 minutes, conditional on the disposal investigation finding no
additional repair. This is an elapsed-work estimate, not point credit or an
acceptance claim.

The [20:42 disposal update](../plans/2026-11-05-expression-macros.md#2042-active-disposal-investigation-update)
records the completed probe and a 20-minute remaining owning-path review;
the conditional scenario is now 181 minutes. The composed test observations
above await the reviewer and do not by themselves close M11.

The [20:47 handoff](../plans/2026-11-05-expression-macros.md#2047-documentation-and-disposal-handoff)
records the completed documentation candidate and the common disposal-path
investigation. Both await review; the remaining conditional scenario is 131
minutes. No M/C criterion is closed by this estimate.

### Reviewed host and documentation update, 20:56

Independent review cleared `7ae26e76`. The following disjoint increments use
the host, specification and disposal evidence above; they do not alter the
earlier completed ledger or count any observation twice.

| Item | Newly reviewed evidence | Credit and remaining work |
| --- | --- | --- |
| P18 | An invocation accepts its own input and refuses live and stale inputs from other invocations. | +0.5; 1/2.5 reviewed. Other input ownership and bridge observations remain 1.5. |
| P19 | The capture service returns `MissingCapture` for negative, out-of-range and oversized indices while a valid capture succeeds. | +1; 3/3 reviewed. |
| P23 | Valid output transfers, while the same payload under a different outer nominal owner is refused. | +0.25; 2.25/4 reviewed. Other output and transfer observations remain 1.75. |
| P24 | Actual active-root destruction and the shared primary/teardown handoff are supported by the separate production-boundary tests above. | +0.25; 2.25/2.5 reviewed. The remaining failure-path audit is 0.25; no single injected active-transformer refusal is claimed. |
| P34 | The grammar, resolution, checking, elaboration and execution specification delta is documented. | +1; 1/2 reviewed. Executable positive and negative example reconciliation remains 1. |
| P35 | The canonical syntax API, token vocabulary and tool guide are documented. | +1; 1/2 reviewed. Final status and authority cleanup remains 1. |

The amended original scope is now **67/99 reviewed, with 32 remaining**. The
unchanged 30 estimated points of additional performed effort give **97/129,
approximately 75%**, for effort accounting only. No M01–M14 or C1/C2
criterion is closed by this partial review.

The [20:59 reproducibility handoff](../plans/2026-11-05-expression-macros.md#2059-reproducibility-handoff)
records the newly demonstrated repeat and changed-input observations. The
conditional remaining scenario is 101 minutes; review is still pending.

### Reproducibility evidence

The repeated copied-declarations check compiles the same graph twice and
compares its source-relative binder, nominal and resource ranges and result
type. In each compilation it independently checks distinct copied identities,
their own binder, constructor/conversion and handle uses, and both
initializers' connection to the caller's actual binder. It does not require
raw identities or Core node allocation order to agree across compilations.

In a fresh graph using the same copied body, changing the caller's value, a
transitive helper, or the imported nested syntax changes 42 to 44. Changing a
matcher literal makes the old invocation fail `parse.expected-form`; updating
the invocation restores 42. Changing a used interface method's result type
fails the ordinary `type.definition-result` check. The existing transformer
reuse test also verifies that a changed helper is prepared and validated again.
The first interface assertion expected the generic mismatch reason; the
ordinary checker reported its more specific definition-result reason, which
the final test now asserts.

The first three-test receipt is `/tmp/ash-repro-final.log` (SHA-256
`aa9b9784b3690a592ab9235993bf898f159ba45e0bbdb44895288766e2683e30`).
Review found that its repeated-graph test imposed unnecessary cross-compilation
identity and node-order comparisons. The revised existing copy/use test
passes without those restrictions; all three focused tests pass in
`/tmp/ash-repro-final3.log` (SHA-256
`4ddc97d36f031a88c2a7ce249599e58bb49ac3a77a96364ba8184af6b280304a`).
The first Clippy run found a test-only complex tuple; using one fixed array
removed the warning. The refreshed all-target test check passes in
`/tmp/ash-repro-clippy-final.log` (SHA-256
`0891611c4246b7b9bf97769ecbc96a208303175ccb70f7c38f8390d8fd43a4eb`).
The canonical interface is fixed by this compiler and no public version or
semantic-option switch was invented for this test. This evidence awaits review
and does not alone close M12.

### Reviewed reproducibility update, 21:09

Independent review cleared `787f5ef5`. P29 gains 1 point for the repeated
source-relative copy/use observations and 1 for the changed-input results,
completing its 2-point cap. This does not repeat P10 identity or P17 cache
credit. The current original scope is **69/99 reviewed, with 30 remaining**;
including the unchanged 30 estimated additional-effort points gives **99/129,
approximately 77%**, as an effort index only. M12 and C1/C2 remain open.

### Remaining point inventory, 21:12

This inventory accounts for all **30 unearned original-scope points** after
`787f5ef5`. “Evidence exists” means the named tests or receipts cover part of
the row and still need their complete scope reconciled. “Evidence gap” means
an observation has not been established; it is not a finding that the
feature is broken. Delivery actions remain gated on the complete candidate.

| Item | Remaining | Current evidence and next boundary |
| --- | ---: | --- |
| P09 | 0.25 | Evidence exists for captured patterns and sequential scopes in `surface_macros`; reconcile the broader contextual cases. |
| P10 | 0.25 | Evidence exists for copied nominals and resources. A copied lexical-region identity/use observation is not established. |
| P11 | 1 | Evidence exists for private helper, opaque and nested effect-signature closure graphs; reconcile the retained checked closure and ordinary privacy boundaries. |
| P13 | 1.5 | Evidence exists for definition/caller/fresh syntax contexts and selector parsing; reconcile leading-context, import, reservation and conflict cases. |
| P14 | 1 | The canonical module and token vocabulary are exercised. Reconcile identity and same-interface conformance; there is no selectable public version number. |
| P15 | 0.5 | Wrong type and effect are refused. Explicit polymorphic and constrained transformer refusal evidence remains to be checked. |
| P16 | 0.5 | The transformer-reuse test executes and changes a transitive helper; reconcile that checked helper closure with the entry handoff. |
| P17 | 1 | Real transformer requests and invocation-handle authentication are tested; reconcile the complete issued `Input` and its captures at the checked entry. |
| P18 | 1.5 | Identifier origins and foreign/stale handle refusal are tested. A complete mixed token/group/fragment/context/origin round trip is not yet established. |
| P20 | 1 | Protected and explicit unwrapped parsing are tested. Reconcile broader parse contexts and an explicit trailing-output refusal. |
| P21 | 2 | Fresh, definition and caller identifiers work in separate graphs. Exact reuse of one fresh identifier versus distinct same-spelled fresh identifiers remains to be checked. |
| P23 | 1.75 | Output decoding, group transfer, malformed output and one wrong-owner constructor are tested; reconcile the remaining output and failure cases. |
| P24 | 0.25 | Active destruction and first-teardown preservation have reviewed compositional evidence. Complete the remaining failure-path audit without claiming a direct paired injection. |
| P26 | 0.5 | Service, transfer and recursive-expansion limit cases exist; reconcile their exact closed-invocation results. |
| P27 | 1 | Discarded nested syntax is tested. A discriminating observation that duplicated nested transformer occurrences each expand remains to be checked. |
| P28 | 2.5 | Checked dependency reuse, compile-time entry validation and Core mutation tests exist; reconcile them through the actual macro graph and its owning boundaries. |
| P30 | 0.75 | Operator, match, application and pattern causes are reviewed. Other semantic causes and bounded copy/relocation preservation remain unverified. |
| P31 | 0.75 | English/Bulgarian and JSON cases exist for selected failures; complete the remaining variant, frame and catalog audit. |
| P32 | 2.5 | The supported combined graph builds and runs after source removal; reconcile image reconstruction and corruption controls. Handwritten and generated local newtypes both hit the existing unsupported `RegistryMetadata` image boundary. |
| P33 | 0.5 | Source-removal native execution is observed. Reconcile cleanup and the absence of runtime syntax-service requests. |
| P34 | 1 | The syntax and API text is reviewed. Finish executable positive/negative example reconciliation. |
| P35 | 1 | API and tool text is reviewed. Finish status, links, authority and transition cleanup at the owning checkpoint. |
| P36 | 1.5 | Connected C1 review and a fresh full gate remain delivery actions. |
| P37 | 2.5 | Whole-path independent review and M01–M14/consumer evidence audit remain delivery actions. |
| P38 | 1.5 | C2 gate and retained-input/evidence readback remain delivery actions; identical-input verification may be reused only under its owning gate rules. |
| P39 | 1.5 | Milestone integration, retained verification and acceptance readback remain delivery actions. |
| **Total** | **30** | |

The approved amendment removed one unearned P11 point for grant objects and
grant-only mutation checks. It did not remove source privacy, checked routes,
ordinary Core checks or their remaining evidence. The old unused-template
name-admission work had no separately weighted pending point; its removal is
not counted as completion. Grant-only image data is likewise superseded,
while the mixed P32 cap remains above.

### M01–M14 evidence inventory, 21:20

The following maps the acceptance matrix to evidence already recorded in
this task and the remaining observation or delivery boundary. An unverified
observation is an evidence gap, not a demonstrated product defect. The test
names refer to `tests/surface_macros.rs` or `tests/macro_host.rs` unless a
different owner is given. The focused receipts are recorded at the reviewed
checkpoints above; all rows still require the retaining checkpoint and
integration verification specified by the matrix.

| Case | Existing evidence | Remaining boundary |
| --- | --- | --- |
| M01 | `imported_if_preserves_boundaries_nesting_and_line_endings` covers the imported conditional, nesting, precedence, line endings and parser refusals. | Reconcile the complete case with the final candidate and gate. |
| M02 | `template_macro_preserves_expression_capture_grouping` and `expression_unwrapping_preserves_groups_and_nested_fragments` contrast protected and unwrapped expressions. | Explicit trailing-output and recovery-bearing fragment refusal observations need reconciliation. |
| M03 | `imported_templates_and_ash_transformer_run_through_the_driver`, `parse_expression_does_not_run_discarded_nested_syntax` and the host failure cases exercise both authoring forms and ordinary failures. | Reconcile the complete signature, row and failure set with the final candidate. |
| M04 | Captured and caller identifiers, non-capture, copied binders and their actual uses are exercised by the host and copied-fragment tests; the `Pair` cases distinguish same-spelled fresh type-parameter handles. | Reconcile distinct fresh-handle association in term-binder positions. |
| M05 | Copied local nominals, resources, their uses and the caller's free reference have checked-Core observations; region scope positives and negatives run through the driver. | A copied lexical-region identity and internal-use observation is not yet established. |
| M06 | `definition_context_keeps_private_helpers_and_types_through_linking`, qualified/facade and withheld-constructor cases, `generated_fresh_context_does_not_select_syntax_or_caller_binding` and expansion-time missing-helper cases exercise the source-access boundary. | Reconcile the checked dependency closure and all ordinary privacy/refusal cases; grant objects are superseded. |
| M07 | `tests/modules_syntax.rs::syntax_imports_are_contextual_and_preserve_ordinary_syntax_names`, `tests/modules_syntax.rs::syntax_selectors_reject_reexports_and_non_lowercase_names`, the missing-export staging test and unused-transformer test cover parts of the boundary. | Reconcile duplicate/conflicting selectors, complete-import non-activation, unsupported local forms and cycles against explicit observations. |
| M08 | The combined template/computed graph and `template_uses_its_defining_modules_syntax_imports` exercise nested separately authored syntax and caller shadowing. | Reconcile the complete graph on the retaining candidate. |
| M09 | Method-evidence, continuation-capability, effect-order and resource/region tests include ordinary failure controls. | Reconcile the full required capability and direct-builtin-import cases with the final candidate. |
| M10 | Captured identifier and combined-origin tests, `syntax_services_reject_invalid_requests_without_losing_a_valid_capture`, the private host identity test and parser-diagnostic tests cover individual bridge operations and failures. | A single mixed token/group/fragment/context/origin identity round trip and complete diagnostic-label audit remain unverified. |
| M11 | `src/eval/machine.rs::transformer_failures_dispose_the_real_invocation_root` and `src/eval/machine.rs::transformer_closes_root_and_preserves_rejection_on_teardown_failure` cover real completion and failure paths; the shared disposal handoff supplies the reviewed compositional evidence above. | Finish the failure/publication and limit audit. A direct combined active-transformer teardown injection was not observed and is not asserted by the composition. |
| M12 | The reviewed `src/driver.rs::copied_macro_fragments_have_distinct_checked_local_identities` repeat and `src/driver.rs::changed_macro_inputs_are_checked_in_each_compilation` cover the named fixture's copy relations and changed inputs. | Reconcile the matrix's full modulo-renaming claim and fixed compiler-interface/semantic inputs; no persistent cache is required. |
| M13 | The transformer-reuse test and existing generated-binder, local-nominal scope and origin mutation tests exercise checked and Core boundaries. | Confirm their complete association with the production macro graph and the independent compile-time/final validation paths. |
| M14 | `tests/parser.rs::out_of_place_dollar_is_a_parser_error`, existing ordinary-language suites and the supported source-removal native graph cover concrete compatibility cases. | Refresh affected verification and the supported native result for the retained candidate; reconcile runtime syntax-service non-use and the existing local-newtype image limitation. |

For P21, `syntax_constructed_ops.ash::make_line` already emits the same fresh
identifier as both binder and reference, and
`checked_transformer_fresh_identifier_does_not_capture_the_caller` executes
that path. `checked_transformer_emits_a_generic_local_newtype` also runs the
`pair_same` and `pair_repeated` cases: two independently created `A` handles
are accepted as distinct type parameters, while the same handle repeated is
rejected. The remaining association question is in term-binder positions.
This refinement does not award the prior positive evidence again.

### Syntax-name reservation repair in progress, 21:56

The M07 driver check found that a selected syntax spelling was still accepted
as a source global, parameter, local or pattern binder, as an ordinary term
import, and as a captured identifier subsequently used as a binder. The
six-case red receipt is `/tmp/ash-syntax-name-reservation-red2.log` (SHA-256
`05855a0513486b712cff789fbd182f7d245dc31e97fb25278891ad43b33cfe74`). The
current candidate retains whether a name was written through the ordinary
syntax path and enforces the existing reservation at term admission. It does
not infer authorship from a diagnostic origin or change lexical identity.

The focused check now rejects those six cases and also checks recursive,
interface-method, resource and region binders; each rejection names the
written occurrence and its syntax import in JSON. Renaming, complete imports,
qualified terms, effect operations and lexical evidence method selectors
remain usable (`/tmp/ash-syntax-name-reservation-final5.log`, SHA-256
`70ebc00080eaf0fcba42683eb73ac0bb154081d5b715a9184e0fa9f52911dd78`). An
unused generated caller-context binder with the same spelling remains valid
and executes to 42 (`/tmp/ash-syntax-created-binder-after.log`, SHA-256
`1c92050efde9145cc1290ccc06266250dbec1111122dba159fa1a54d4171b76e`).
An older fresh-context fixture combined a selected syntax name and a
same-spelled source global; it is split into separate caller-syntax and
caller-global negatives, both retaining `resolve.unknown-name`.

The affected six-suite run passes 297 tests before the final addition of the
qualified-member and evidence-selector assertions
(`/tmp/ash-syntax-reservation-suites-final2.log`,
SHA-256 `2ed9134670ed3dfa6e281a942edb92adf29a6079d8109d44f94f100ee8a7a767`);
the focused receipt above includes that assertion. Both unchanged 256 KiB
canaries pass: `/tmp/ash-syntax-reservation-stack.log` (SHA-256
`c500cee6286ebf2dce751d20c8527548371f2c262a44349e2d3f506da5ba6fb8`) and
`/tmp/ash-syntax-reservation-stack-pattern.log` (SHA-256
`9c9a815525e50e0655f12f455d4577dadfbd11a83946c7e735068fea4f8542e2`).
All-target Clippy passed (`/tmp/ash-syntax-reservation-clippy.log`, SHA-256
`49bcde4d192cea339a13b2d8a0186ac16ca3f4f7f42e040ca3f8388d83b4fd44`), as
did targeted Clippy after the last test-only addition
(`/tmp/ash-syntax-reservation-clippy-test-final.log`, SHA-256
`b2849856fc755bf5444d0b8ff6cbea86b3147ab343aa8bff1f2e691c1ab44607`).

Two independent remaining observations also pass: a transformer returning a
second expression is rejected with `parse.unexpected-token`
(`/tmp/ash-syntax-trailing-output.log`, SHA-256
`d90c552fe8029ff9258f919f0f1b5c8d31a15762d890cba39b6ff30afcdd280e`), and
`(twice (twice 10)) + 2` runs three transformer machines, returns 42 and
issues no further syntax requests during ordinary execution
(`/tmp/ash-syntax-copied-transformers-after.log`, SHA-256
`1247880929fdb706fce8e950eb00492c67b9d2bc6335a4305399957539817768`).
These results and the repair await the retaining pin and independent review;
no point or acceptance row is closed here.

### Reviewed reservation repair and copied-region finding, 22:05

Independent review passed `8c99b226` at 22:05:29 on 6 November. The reviewed
increment is 1.5 existing-scope points: P13 +0.5 for source-name reservation
(2/3), P23 +0.25 for rejecting a second output expression (2.5/4), P27 +0.5
for three actual nested copied transformer executions (2/2.5), and P33 +0.25
for ordinary execution issuing no syntax requests (2.25/2.5). The output
test does not call `parse_expression` and adds no P20 credit. No M or C row is
closed. Historical reviewed points and the separately estimated 30 points of
performed corrective work remain unchanged.

The next copied-region control exposes a distinct Core registry failure:
two copies of one captured `region<R>` fail independent validation, while
handwritten regions and a single captured region both compile and return 42.
The failing control is `/tmp/ash-syntax-copied-region-controls.log` (SHA-256
`750239783b80f95a68ea991580622c71a1954b33c4b5238f76748c15c870d31c`). A
debugger stopped at the source-order rejection for the second region's
retained source coordinate. The repair and its estimate remain open.

### Copied-region repair candidate

The ordinary Core registry now recognizes a lexical region identity in its
source-order fallback only when the actual non-entry region owner matches its
identity, access type, module and containing origins. Existing Core region,
type, scope and uniqueness validation remains in force. The real copied
fixture compiles and returns 42; checked Core has distinct identities and
access binders, with each copy using its own binder and the caller's original
`outside` binder. Handwritten and single-expansion controls also return 42
(`/tmp/ash-syntax-copied-region-driver-final.log`, SHA-256
`81767123a04ec00aa2320555cf70f4b472e5ead7293ac06f6283f43f427b653c`).

Identity traversal independently revalidates the result. Missing or
mismatched owner, access type and origin mutations are refused, as is a
same-typed sibling-access retarget (`/tmp/ash-syntax-copied-region-core.log`,
SHA-256 `22ce45a638dd686222200dc1935c063abc76a47bc85f61d85a7376b77c56f55d`).
The existing source-order set passes seven cases, including reversed headers
and the resource-carrier negative (`/tmp/ash-syntax-region-source-order.log`,
SHA-256 `110f0b12971b4f869bfa60ee62d3a90133f745e45c56f3fdf244b4ec60b5a5a7`).
The affected macro-host, region-runtime and surface-macro suites pass 179
tests (`/tmp/ash-syntax-copied-region-suites.log`, SHA-256
`fd23db0e242b2f65bbdb41e7012e38695e3d6f432c7ced42d54eb3a35f3cbc2d`).
The unchanged 256 KiB local-nominal canary passes
(`/tmp/ash-syntax-copied-region-stack.log`, SHA-256
`5e5932a816727ea2cbb864b856bc1b5cec70ea186fe6ff7dc4b55bb87492de60`), as
does all-target Clippy (`/tmp/ash-syntax-copied-region-clippy.log`, SHA-256
`644d905475073b19ec7d260c8e3fc60c71e2a5a7ea921805f7b16da4097c851e`).
This candidate awaits independent review; no additional point or M row is
closed here.

### Reviewed copied-region update

Independent review passed `ad9cedb0`. P10 gains its remaining 0.25 point for
the copied region identities and their own/caller uses, completing P10 at
5/5. This does not close M05 or repeat P28 credit. The current total is
**70.75/99 reviewed, with 28.25 remaining**. The separately estimated 30
additional-effort points are unchanged; **100.75/129** is an effort index,
not an acceptance percentage.

### Mixed bridge and transformer-admission observations

The private invocation-host test now captures a mixed tree, calls
`expression_syntax` with the issued fragment handle and transfers a normal
`Expanded` result. The exposed contents retain their group, token and
protected fragment; same-spelled caller and freshly issued identifiers keep
their different contexts and written status. The complete ordered combined
origin compares equal, and its frame and nested protected storage retain their
original shared identities. The original capture remains retained
(`/tmp/ash-syntax-mixed-roundtrip-final.log`, SHA-256
`effcab3eb30f8fc0e5b18886b2e7823a3dbe3d49c5f0c8b158e7e00f4399e32f`).
This is a private host observation alongside the existing real-Ash service
tests; it does not alone close M10.

Two unused `using` targets are rejected as `syntax.invalid-transformer`: an
open-row polymorphic target and an otherwise exact closed-row target with an
interface requirement. Each identical ordinary declaration first checks and
runs without the syntax declaration (`/tmp/ash-syntax-transformer-admission.log`,
SHA-256 `1fc3aff9469e2e986e7218760223e240e5dfb2944002877d66bc000b5358628e`).
The first case combines polymorphism and an open row; it does not isolate
those two restrictions. All-target Clippy passes
(`/tmp/ash-syntax-bridge-admission-clippy.log`, SHA-256
`2bf41681fed040c82ad126e9a326646353f28c9610797c1461b97ea124645fa4`). These
observations await independent review and add no points yet.

### Reviewed transformer admission and fresh-term observation

Independent review passed `a56d4f54`. P15 gains its remaining 0.5 point for
the paired polymorphic/open-row and constrained transformer-admission cases,
completing that cap. P18 gains 1 point: 0.5 for issued mixed-capture encoding
and 0.5 for the exact structure/context/origin round trip, bringing P18 to
2/2.5 without repeating handle-ownership or P17 entry-wiring credit. The
current total is **72.25/99 reviewed, with 26.75 remaining**; the separately
estimated 30 corrective-work points remain unchanged. No M or C row closes
here.

A further real-driver control issues two distinct fresh identifiers with
the same spelling, uses each as a term binder and in the final addition, and
returns 42. A paired transformer reuses one handle for both sequential
bindings and returns 4 through ordinary shadowing. Checked Core identifies
the caller's `temp` in the first initializer and the two distinct generated
binders in the addition's left and right operands
(`/tmp/ash-syntax-fresh-term.log`, SHA-256
`e5a49f5367f397124ad6f5f4b139a377082357b21c796b066d5e6e636a796af2`).
All-target Clippy also passes (`/tmp/ash-syntax-fresh-term-clippy.log`, SHA-256
`342d2943b458fb6b71d1582de4f4e556e58be9fc1621af26f223e55d026a8ff9`). This
fresh-term observation awaits independent review.

### Reviewed fresh terms and corrective-work record

Independent review passed `e0aa54ec`. P21 gains 0.5 point for the distinct
and reused fresh term-handle association, reaching 2/3.5. This does not repeat
the earlier single-handle or type-parameter evidence or close M04. The current
original scope is **72.75/99 reviewed, with 26.25 remaining**.

X7 records approximately 0.25 additional performed-work points for the
identifiable copied-region diagnosis and production correction. The recorded
tool intervals were 22:09:25.643–22:11:51.878 and
22:23:12.869–22:23:23.267 on 6 November: 2 minutes 36.633 seconds combined,
or approximately 0.24 points at the previously recorded 5.55 points per
elapsed hour, rounded to a quarter point. These are visible elapsed tool
intervals, not measured active time, a complete repair cost or a formal lower
bound. The session's developer records at lines 68540, 68593, 68819 and
68824 supply the interval endpoints. The mixed fixture/own-use observations,
review, documentation, waits and gaps are excluded. The original X30 history
remains unchanged; X7 makes the current additional-work estimate **30.25
points** and the effort index **103/129.25**. This index is not feature
acceptance.

### Current remaining evidence and delivery

The 21:12 inventory remains historical. The grouped amounts below account for
the current 26.25 unearned original-scope points; existing observations need
their owning audit, and an unlocated observation is not a proven defect.

| Boundary | Remaining points | Next evidence or action |
| --- | ---: | --- |
| Source and hygiene: P09, P11, P13, P20, P21, P27 | 5.25 | Reconcile captured and introduced names, privacy/routes, parsing and nested expansion against existing tests. Establish the recovery-bearing fragment boundary if existing parser evidence does not already do so. |
| Checked entry and host: P14, P16–P18, P23, P24, P26, P28 | 7.75 | Audit canonical input, checked helper closure, output, limits, teardown and independent Core against the existing driver, host and machine observations. |
| Diagnostics and image: P30–P33 | 4.25 | Repair the reproduced combined-origin resolution failure below; reconcile other causal copy/relocation, catalog variants and supported image/native evidence. |
| Documentation: P34–P35 | 2 | Reconcile executable examples, status, links and artifact authority at the retaining checkpoint. |
| Delivery: P36–P39 | 7 | Complete whole-path review, the fresh gate, retained verification and authorized milestone integration. |
| **Total** | **26.25** | **M01–M14 and C1/C2 remain open until their owning evidence and handoffs are accepted.** |

### Combined-origin resolution failure

A disposable variant of the existing nested identifier-origin graph returns
the captured identifier instead of issuing an authored rejection. Ordinary
resolution correctly rejects the unknown name and presents both invocation
frames, but drops the ordered inputs of the identifier's combined origin as
causes. The inputs happen to recur as frame locations, so frame presence alone
does not establish their causal roles. The human and JSON red observation is
`/tmp/ash-syntax-identifier-resolution-probe.log` (SHA-256
`7b817a5b13ef5b51cb2219ab99e6f5fe46714008a3ea103248401c3b67fc2c1e`). The
ordinary source-origin missing-helper case retains its exact definition token
and frames. Repair of the combined-origin handoff remains open.

### Combined-origin resolution candidate, 7 November

The candidate retains the existing diagnostic location when the ordinary
resolver rejects an unqualified name expression. It fills only a missing
primary location, and merges active expansion frames before the occurrence's
own frames using their existing identities. Other resolver failures and their
semantic checks are unchanged. The real nested-transformer test now asserts
the unknown-name reason, the primary input, the additional combined input,
and both outer-to-inner invocation/definition frame pairs. It also checks the
human cause label in English and Bulgarian. The existing missing-helper
control still points at the written definition token, with its one frame pair
and no invented combined cause.

The original missing-cause red recorded above was independently inspected and
its hash verified during the `d14cd6e1` review. Its temporary file no longer
exists after the session interruption. On 7 November, the stronger frame-order
assertion failed at 05:39:58 before the ordering correction and passed at
05:40:37 afterward. Those receipts are
`/tmp/ash-combined-origin-frame-order-red.log` (SHA-256
`bc83ca756161d49042e111757964d371a9e2414d2ba762c5f24e08ef97fa06bc`) and
`/tmp/ash-combined-origin-frame-order-green.log` (SHA-256
`6022b6a44296e8218388dd83d642acccc81ae77b4206ff852556c03c7d5e358a`).

The final single-job affected run passed 223 tests across `diagnostics`,
`macro_host`, `module_resolution`, and `surface_macros`:
`cargo test -j 1 -p ash --test surface_macros --test macro_host --test diagnostics --test module_resolution --no-fail-fast`
(`/tmp/ash-combined-origin-suites-j1.log`, SHA-256
`82503301fbcb1ca0d7e7986e0b8f164abacfea3e87f3784e45d6858b88dd83ba`).
The existing 256 KiB resolver-disposal test passed via
`cargo test -j 1 -p ash --lib late_expression_resolution_errors_discard_deep_completed_work_on_a_small_stack`
(`/tmp/ash-combined-origin-stack.log`, SHA-256
`db69e9da8e35ef7875bab16a8345cd954890dc0dd54b511e3c6ab2361edd5824`).
`cargo clippy -j 1 -p ash --all-targets -- -D warnings` passed
(`/tmp/ash-combined-origin-clippy.log`, SHA-256
`53eea506c7dfcbeee77a19b79224fb23a6f17d45ad18e4452e1780ac45e9d9db`).
Direct CLI JSON and both human locales also retained the cause and ordered
frames; the JSON receipt is `/tmp/ash-combined-origin-cli-json.log` (SHA-256
`f42bf81e02afe1b5c1af5bd9af138cb8020bae09ad4ecabd4274f52b5ded097d`).
This candidate awaits independent review. It does not establish origin
transport for every resolver position or close any M/C acceptance row.

### Reviewed combined-origin handoff and malformed-capture control

Independent review passed `fcd3325e`. The exact unqualified-name handoff and
its ordered frame/cause evidence are reviewed; broader resolver positions and
M/C acceptance remain open. Its distinct ordinary semantic cause adds P30
+0.25 (2/2.5 reviewed); bounded copy/relocation remains 0.5. No P31 rendering
credit is repeated. The previous 72.75 reviewed points and the separately
estimated 30.25 additional-work points are unchanged historical records.

An additional test-only candidate exercises the recovery boundary through the
real driver. The existing `parsed_discard 41` transformer receives a valid
capture, runs once, discards the parsed nested expression, and produces 42.
Changing the capture to `(1 +)` returns the ordinary `parse.expected-operand`
error before any transformer drop, syntax request, or transfer attempt. The
focused test is
`cargo test -j 1 -p ash --lib malformed_capture_is_rejected_before_a_discarding_transformer_runs`
(`/tmp/ash-discard-malformed-capture-test.log`, SHA-256
`24eca03b0bcbc45b3a4973146987d37e176152a8685bea30a5115d1caf376f5c`). A real
CLI JSON observation gives the same parser reason
(`/tmp/ash-discard-malformed-capture-probe.json`, SHA-256
`048ec9f1b552045a8d5ea5843f6cc9634aa56f4163f5560c100588f751ec7b0c`).
All-target Clippy passed after the test addition
(`/tmp/ash-discard-malformed-capture-clippy.log`, SHA-256
`7b86761702fcb38939e5ff1da0ce47739ace57f5b3fb55c80ffbc573945c14b0`).
This observation awaits independent review and does not by itself close M02.

### Reviewed malformed capture and existing image evidence

Independent review passed `1631b1b5`. Rejecting a recovery-bearing source
capture before host admission adds P20 +0.25 (3.25/4 reviewed); broader
parsing and fragment contexts remain 0.75. No M02, P23, P09, or additional
corrective-work credit is claimed.

On `1631b1b5`, the existing
`build::image::tests::syntax_builtin_image_reconstructs_and_refuses_changed_or_duplicate_roles`
test passed with `cargo test -j 1 -p ash --lib syntax_builtin_image_reconstructs_and_refuses_changed_or_duplicate_roles`.
It encodes the real four-file graph, removes its source tree, admits expected
native facts, restores and evaluates the image to 42, and refuses changed and
duplicate canonical syntax roles. The receipt is
`/tmp/ash-syntax-image-reconstruction-current.log` (SHA-256
`c08ecf88056c16eb6c398e38a3e3ad6e4a1c77cdec03348b9fcd90bcc27115e4`).
Independent review reconciled this test with the canonical syntax role,
ordinary checked Core/source/origin image records, wire encoding and both
restore paths: P32 +2.5 (records 1, reconstruction 1, corruption refusal
0.5), closing that row at 2.5/2.5. This does not repeat P33 native-execution
credit or close M14/C gates. The earlier source-removal native build remains
historical until retained-input refresh; the unsupported local-newtype image
boundary is unchanged.

The existing `driver::tests::unchanged_transformer_entry_is_reused_only_within_one_compilation`
test also passed on `1631b1b5`. Its transformer uses a transitive Ash helper
to choose token spelling, returns 42 across two imports with one entry
preparation and validation, then rejects after the helper changes in a fresh
compilation. The receipt is `/tmp/ash-syntax-entry-helper-current.log`
(SHA-256 `225a9b9b772d39c195e9f0bcbd7f19eaa012f12d29e48a22cdf9f05fa3a3ed17`).
Independent review confirmed that this test and its checked reachable-module
handoff establish the remaining retained-helper-closure observation: P16
+0.5, closing that row at 3/3. The earlier P17 reuse and changed-compilation
credit is not repeated.

### Core validation and published examples

Four existing generated-graph Core tests pass on `7becbffc`:
`generated_local_newtype_rejects_tampered_construction_origins`,
`generated_local_type_parameters_reject_tampered_origins`,
`procedural_local_type_parameters_retain_parser_order_for_revalidation`, and
`copied_region_order_requires_its_actual_owner_and_scope`. They exercise
generated origin, parameter-order, region-carrier and cross-sibling scope
mutations, including original linked and post-identity validation. The receipt
is `/tmp/ash-syntax-core-validation-current.log` (SHA-256
`8d076c2861e418a147597ce7148472044db865ddb55830685018d6367788ed8a`),
completed at 05:56:10 on 7 November, Europe/Sofia.

Independent review reconciled those mutations with the distinct compile-time
entry and final linked Core validators, and with the reuse of already checked
reachable module owners and fragments. This adds P28 +2.5 (independent
mutations 1, separate validations 1, checked dependency reuse 0.5), closing
P28 at 2.5/2.5 without repeating P10/P17 observations or closing M13/C gates.

Independent review also traced the canonical checked syntax module and its
`Input`, `MacroResult`, and `Ops` identities from macro-entry validation to
the host. That establishes P14 +1 (3/3) for canonical API identity and
same-interface conformance; it does not claim a selectable version or
cross-implementation testing, and does not repeat vocabulary/image credit.
The validated entry's binder and occurrence then supply a fresh host's
authenticated `Input` at that occurrence. The existing real recursive
transformer consumes its identifier, initializer and body captures in order
and runs to 42 in the reviewed 223-test suite. This establishes P17 +1 (2/2)
for entry wiring without repeating P18 bridge/ownership or P17 reuse credit.

The published `if` definition in the specification and tool guide matches the
existing fixture exactly; the guide's entry module matches its precedence
fixture. On `7becbffc`, the real CLI returns `42 : Int` for the published
example and rejects missing capture, missing separator, and unparenthesized
application with `parse.expected-form`. The receipt is
`/tmp/ash-published-syntax-examples-current.log` (SHA-256
`87a449ecd107b10d8b0c19991c7180c1ecbb94dfc3e5afb5e98270a417ef5960`),
completed at 05:58:08 on 7 November, Europe/Sofia.
Independent review confirmed P34 +1 (2/2) for these executable positive and
negative examples; P35 status and transition cleanup remains separate.

### Current remaining work, 7 November

The older 26.25-point inventory above is retained as a historical checkpoint.
The reviewed reconciliations since then leave these 17.25 original-scope
points; an evidence audit does not assume a product defect or a new test.

| Boundary | Remaining points | Next action |
| --- | ---: | --- |
| Source and hygiene: P09, P11, P13, P20, P21, P27 | 5 | Reconcile existing contextual binding, access, parse/fragment and nested-expansion observations against their exact requirements. |
| Host and completion: P18, P23, P24, P26 | 2.75 | Reconcile existing handle, output, failure and resource-limit observations at their owning boundaries. |
| Diagnostics and native execution: P30, P31, P33 | 1.5 | Audit remaining cause/copy and catalog variants; refresh the supported source-removal native result at retention. |
| Documentation: P35 | 1 | Complete status, links, authority and transition cleanup at the owning checkpoint. |
| Delivery: P36–P39 | 7 | Complete independent whole-path review, the fresh gate, retained verification and authorized milestone integration. |
| **Total** | **17.25** | **M01–M14 and C1/C2 remain open until their owning evidence and handoffs are accepted.** |

### Completion and limit evidence, 7 November

Independent review reconciled the existing real transformer failure and
teardown tests with the common disposal scope and the host's service and
structural-depth limits. The two lifecycle tests pass in
`/tmp/ash-syntax-lifecycle-current.log` (SHA-256
`e3dcc3a03458e41ee6756fb900e5fc6dbe122653bc8206badb8b11b05cd0d3ba`), and the
reviewed host suite exercises the relevant limits. This adds P24 +0.25 and
P26 +0.5, closing those rows at 2.5/2.5 and 0.5/0.5 respectively. It does
not repeat the earlier disposal-composition or divergence credit. Active
transformer destruction and failure combination are supported by their
shared production handoff and separate observations; a single directly
injected active-transformer teardown refusal was not observed.

The remaining original-scope work is now 16.5 points: source and hygiene 5,
host and completion 2, diagnostics and native execution 1.5, documentation 1,
and delivery 7. These are outstanding evidence and handoffs, not a claim of
unimplemented functionality. M01–M14 and C1/C2 remain open.

### Qualified-name diagnostic candidate, 7 November

A nested transformer can emit a qualified name whose member has multiple
causes. A real unavailable-member error retained the ordinary reason and
frames but lost the member's additional definition cause
(`/tmp/ash-qualified-combined-origin-probe.json`, SHA-256
`83f8495c1140994526968af2f31d40a3f464d55438de4fe8f3d491f562b44c9f`).
A successful qualified lookup followed by an argument error lost that same
cause (`/tmp/ash-qualified-success-origin-probe.json`, SHA-256
`3a7c17fa58b43ac59cc97bc9936c6c0e88a6b81dd60e5f80c02c0baf19abc95d`).
The focused real-driver tests reproduced both losses before the candidate:
`/tmp/ash-qualified-origin-red.log` (SHA-256
`d49a653da8c663867275824cdac98cc941c734d815b5836b8913b1111a45fb13`)
and `/tmp/ash-qualified-success-red.log` (SHA-256
`b830e8ae6ea2b23eb4ca5d9365966999991475c44c1ea7aa9262d9b172f534a6`).

The candidate carries each projected name's actual output-node origin as
diagnostic metadata without changing its identity or lookup context. An alias
miss uses the alias location; a member miss uses the member location. A
successful qualified expression retains both component locations for the
existing type-error path. The source-origin control does not acquire the
identifier handle's different construction origin. The tests assert the
original reasons and facts, component-owned primary locations, the member's
additional cause, and outer-to-inner frame pairs. The successful case's
focused green receipt is `/tmp/ash-qualified-success-green.log` (SHA-256
`d90204b19d3a48b564cdb8745ffa880d22e3ee2c2a657c866e2b5d820e00052b`).

Six affected integration suites pass 283 cases in
`/tmp/ash-qualified-origin-suites-final.log` (SHA-256
`d1b039df4dfa9a8ee0ac0919a843850f351e5d2f5e69a93e011a5c24d687528f`).
The unchanged resolver and local-nominal 256 KiB stack checks pass in
`/tmp/ash-qualified-origin-stack-a-final.log` and
`/tmp/ash-qualified-origin-stack-b.log` (SHA-256
`fca365e514280aca0c39f7ccfc2ab20072d87f38a99fc0057ebe3d70c655caf7` and
`4123b24148c78d6ba9a1aa16829f11e6dd5036d9d9fbcc9c77eb7f85b9c491e2`).
Real CLI JSON cases and English/Bulgarian human output are checked in
`/tmp/ash-qualified-origin-cli-final.log` (SHA-256
`2e66e83f35006aea7a2696710ed51e824bc2c1e04da53e16b1dd25af6f4eaf95`).
All-target Clippy passes in `/tmp/ash-qualified-origin-clippy-final.log`
(SHA-256 `24cd19b8aaebcee518b81d48bc1df70c19a3ee076332f672864fd3aa51748c2b`).
This bounded candidate awaits independent review; no new points or M/C
closure are inferred, and other qualified-name positions are not claimed.

## Progress

The weighted ledger records **61.5/100 reviewed delivery points**. The latest
reviewed implementation pin is `49575c1d`. These are partial implementation
observations, not acceptance of the whole feature.
M01–M14 and C1/C2 remain pending.

### Weighted delivery progress

The cap is 100 estimated effort points for the complete milestone through
verified retention in `integration/expression-macros`; Main integration is
excluded. Weights reflect expected work, not an equal share per acceptance case
or feature. They are approximate: display about 62%, not a precise completion
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
| P09 | 4 | Dev / R3.75 | Procedural captured binder with preceding initializer scope (0.5), `/tmp/ash-syntax-captured-binder-driver.log`. An introduced function parameter avoids a same-spelled caller binding (0.5), and a captured parameter binds its captured body without escaping its scope (0.5); review cleared these function cases at `abd2e26f`. An introduced mutually recursive group retains a same-spelled caller binding (0.5), reviewed at `bc431118`. A captured recursive binder scopes over its initializer and body without escaping (0.5); template and procedural variants, fresh binders, and same-spelled distinct recursive members run to 42. A later sequential initializer sees the preceding captured binder (0.5), `/tmp/ash-syntax-recursive-capture-regressions.log` (SHA-256 `55937b612d95a37d110402814301820f0832c0113f5e1a6aed54337c0c541810`). Four ordinary recursive-resolution cases pass, `/tmp/ash-syntax-recursive-capture-ordinary.log` (SHA-256 `ea829a715c07691b22d1c07c85977e911398f57d0836ebf9685785edfd9974a0`). These cases and the R12 repair were reviewed at `a1135e26`. Captured `resume` expressions use the actual inner or outer clause selected by their expanded position (0.5, reviewed at `89b21a51`). Both execute to 42; duplicate/missing handler clauses and nested-function capture retain their ordinary refusals. A further graph captures caller `value = 40` inside a clause with its own `value = 2` and returns 42. Captured constructor and nullary pattern contexts preserve actual duplicate checks (0.25, reviewed at `81eefcc9`; `/tmp/ash-captured-pattern-refactor-suite.log`, SHA-256 `e24f5ffce0620b25e019971e4df3e2e213a0921b406dc2ea241576838eff0758`). Broader patterns and sequential scopes remain pending (0.25). |
| P10 | 5 | Dev / R4.25 | Duplicated captures retain distinct local binder IDs (0.5), local newtype and constructor IDs (0.5), and resource identity and handle IDs (0.5); the combined graph preserves nested syntax and a caller free reference and executes to 42. The independently validated Core is inspected in `/tmp/ash-syntax-copy-identities-batch.log` (SHA-256 `98dac1c11adf058b33a84ec3a6efb1fe95b3662a93796aacc8ea6163112b3afd`); review cleared these cases at `82d2f219`. A template-introduced local newtype and its constructor remain distinct from the caller’s same-spelled nominal and constructor; the captured caller annotation retains its own type and the real graph executes to 42 (0.5, reviewed at `9b1cb854`), `/tmp/ash-syntax-generated-newtype-origin.log` (SHA-256 `88b3373f0c8cfac57aa157f315748da7e55e56effa3d4cca981a7be1cdd131a4`). Independent Core rejects ten construction-origin and representation mutations and continues to reject wrapped source-only origins; five local-newtype checks pass in `/tmp/ash-syntax-newtype-lib-batch.log` (SHA-256 `2ae8d4a8ea3f5808eceed197f1515fcac1bd28ccde4fc357d0123a3b22afed7c`). An unqualified annotation selects the owner’s private nominal or an introduced local nominal instead of a same-spelled caller nominal or type parameter (0.5, reviewed at `47524835`). Both valid graphs return 42; distinct caller types, direct caller private access, and an unused unknown annotation are refused. A unique template-local nominal now resolves in its lexical scope even without a same-named owner nominal. Renamed targeted and qualified imported nominal annotations follow the checked owner route, including through a facade and under caller shadowing (0.5, reviewed at `d2d377bf`); wrong caller types, owner-only aliases, and an unused dependency-private qualified type are refused. Applied targeted and qualified types, including nested type arguments, use the defining context; one- and two-parameter template-local newtypes also execute to 42, while a parameter cannot escape its representation (0.5, reviewed at `ac1561e5`). Introduced cell and region scopes preserve caller bindings, initializer/provider order, generated type identities and ordinary escape checks; real graphs execute to 42 (0.5, reviewed at `57ce1f1f`). Captured effect-row members and tails retain caller context and avoid introduced-name capture (0.25, reviewed at `eeec9e7f` and `24c8d51c`; `/tmp/ash-captured-row-tail-suite.log`, SHA-256 `e2f0b01d88b3545dfe9e9e92e62cc82b046e595ba4b4e98c7d45466cfdd40198`). Other copied binder/use cases (0.5), and copied nominal/region cases and broader type scopes (0.25) remain pending. |
| P11 | 5 | Dev / R3 | A template's direct and facade-qualified public term retains the owner's route despite a conflicting caller alias; unused dependency-private references and ordinary caller use of the owner's alias are refused (0.5), `/tmp/ash-syntax-owner-qualified-regressions.log` (SHA-256 `c7c147b247ef8307a18adf5e65bfcbd719b14eade02b09ee2684f135cd6ebab9`), reviewed at `98613915`. A renamed targeted public import works in template and procedural output, through a facade and under caller shadowing; captured caller references retain caller access and ordinary caller access to the owner-only name is refused (0.5), `/tmp/ash-syntax-owner-targeted-regressions.log` (SHA-256 `625b357e3890ca7a2c59b11bd19c0266afd6e164e8fb83a51273c080c212f996`), reviewed at `1bd1a08e`. Owner-qualified public constructor expressions, match and function-parameter patterns work with caller shadowing; dependency opaque constructors remain refused and ordinary access/re-export coexists (0.5), `/tmp/ash-syntax-copy-constructor-final.log` (SHA-256 `6546d7ff826e169e5e32b31983fd3362e6381b8c07b6e50bdc86d56cb0bce5b2`), reviewed at `82d2f219`. A renamed targeted constructor works in template expressions and patterns, procedural output, a facade, and caller shadowing while ordinary caller access is refused (0.5, reviewed at `9b1cb854`), `/tmp/ash-syntax-targeted-constructor-current.log` (SHA-256 `90534ec49a44823be92f9f09f5bb6a36307558106c753fe98b0389959925b707`); the current batch is based on `0cd326dc`, with combined SHA-256 `7091e75c5d1b1e51aed543614a9be923f34bc38c1de1c69d92997fd6b011a1cb` for the six changed Rust files and generated-newtype and targeted-constructor fixtures. A generated local-evidence graph retains its owner’s checked private interface and a private signature type, and validates its generated method binder through Core (0.5, reviewed at `4a79dcf9`); its checked routes, caller shadowing and privacy controls are described above. Checked public effect routes and contextual interface routes retain their original identities and privacy boundaries (0.5, reviewed at `2ad6e6be`, `ee521864`, and `e9d873c5`; `/tmp/ash-qualified-interface-suite.log`, SHA-256 `5a31d975c1d1a8fba852a7802e2605f25fa58deb196af93864ca8b3e415012eb`). Remaining full authenticated grants/access (0.5), broader retained private closure and Core consumers (1), and route mutation refusals (0.5) remain pending, beyond P07. |
| P12 | 3 | Dev / R3 | A template or checked transformer selects a definition-site method, renamed targeted import, qualified import or public facade using caller-local evidence and executes to 42 under caller shadowing. Without caller evidence each fails `constraint.unsatisfied`; a syntax import does not introduce an ordinary caller method (1, reviewed at `b70c6bb3`), `/tmp/ash-macro-method-procedural.log` (SHA-256 `24cf1c1979cc1f0329109b71a2aca577b54e8c0cedf598f96e9ad6765830b84a`). Broader private-method cases remain pending. Six affected suites pass 167 cases in `/tmp/ash-macro-method-regressions.log` (SHA-256 `28baa45f8ca63a7b3b371c36f6398bcadb324b548fb3856af352ec6435e3363d`); the combined hash for the four changed Rust files and method fixtures is `0df274f24e1f2b92cb4f8d4f50abc2b71cb3273aced54ef728521b86c2af5a59`. Template-generated `resume`, `discard` and `retain`, plus a checked transformer producing `resume`, execute to 42 in their valid handler contexts; outside-clause, nested-function capture and outside-retained-root forms keep their ordinary refusals (1, reviewed at `d1e16df4`), `/tmp/ash-macro-continuations-procedural.log` (SHA-256 `160da5e3367be104cedfb308f77c13f4d588310569e9c6c0138c14091544f505`). Six affected suites pass 180 cases in `/tmp/ash-macro-continuations-regressions.log` (SHA-256 `243105483287c22e3ae8fe1d79b4b1c8acf79a708eef96ebf536a700ab4ec5a7`); the combined hash for the two changed Rust files and continuation fixtures is `46b508ae457b2574e94159fed18fc652744ce07499cc24f3bd338d0a92d53a42`. A copied effectful capture runs twice; two captured requests produce 42 in written order and 33 when reversed, with the handwritten control also producing 42. A captured resource read returns 42, and a captured closure escaping its resource is refused with the same `type.resource-escape` reason as handwritten source (1, reviewed at `47524835`), `/tmp/ash-macro-effects-resources.log` (SHA-256 `0fcd09a863e99691ed433f3061d2256c95dd8d527695f491ab2d0c5ba55eb31a`). The named-type and effect/resource batch passes 236 tests across seven affected suites in `/tmp/ash-macro-type-context-regressions.log` (SHA-256 `9fe3960da0c7118aa6c93713a91af245312d01f80f9c550fe91524c77027167c`); its combined Rust and fixture hash is `dfd5400b8d9f902dcf8072a259b6f6f6336d9b7b99029c853e0688286bd04483`. |
| P13 | 3 | Dev / R1.5 | Generated definition context selects its owner's imported syntax, caller context selects a different caller import, and fresh context selects neither caller syntax nor binding (1), `/tmp/ash-syntax-generated-context-driver.log` (SHA-256 `3f3815fdaedc6ee7a41ff6053c64a75aa832ef96d10d2a5ca36f09cef955833a`). An outer template's literal identifier retains its context as the binder and body of a separately imported nested syntax; its local 32 and the caller's same-spelled 10 produce 42 (0.5, reviewed at `c5bf51f3`), `/tmp/ash-macro-definition-admission-regressions.log`. Broader leading-context, import, reservation and conflict cases remain pending. |
| P14 | 3 | Dev / R2 | Reviewed canonical module load/check/link (0.5); complete vocabulary (1) and lexer/declaration conformance (0.5), `/tmp/ash-syntax-token-vocabulary.log`; API identity and interface-version conformance remain pending. |
| P15 | 2 | Dev / R1.5 | Entry-time exact checked transformer type admission (1); definition-time missing, wrong-type and disallowed-effect refusals (0.5), `/tmp/ash-transformer-review-repair-regressions.log`; polymorphism and constraint refusals (0.5) pending. The repair passed review at `ad8ca9cc`. |
| P16 | 3 | Dev / R2.5 | Mainless compile-time entry (1), independent entry validation (1), and real checked Ash body execution (0.5), `/tmp/ash-transformer-machine-step.log`; retained helper closure (0.5) pending. |
| P17 | 2 | Dev / R1 | Unchanged validated-program reuse (0.5) and changed-program revalidation (0.5) are demonstrated above and were reviewed at `f19b1ab2`. Complete authenticated invocation Input remains pending (1). |
| P18 | 2.5 | Dev / R0.5 | Actual identifier capture and origin round trip (0.5), `/tmp/ash-syntax-captured-ident-driver.log`; complete input encoding (0.5), handle ownership (0.5), and broader round trips and stale/foreign/forged refusal (1) pending. |
| P19 | 3 | Dev / R2 | Reviewed expression capture (0.5) and `Plus` construction (0.5); token kind/spelling round trip and mismatch refusal (0.5), `/tmp/ash-syntax-token-ops-driver.log`, and identifier spelling (0.5), `/tmp/ash-syntax-captured-ident-driver.log`; remaining total capture pending. |
| P20 | 4 | Dev / R3 | Structured parse rejects an incomplete expression, accepts an unresolved name without resolving it, and returns a protected fragment executing to 42 (0.5), `/tmp/ash-syntax-parse-service-driver.log` (SHA-256 `cb3b9e9e8f9376c505c8dd2c484a04940ba4b0d281e94b5ecb63b8b509024ee4`). Unwrapping `1 + 2` before `* 10` yields 21; protected, reparsed, and written-group forms yield 30, and template forwarding yields 21 (1), `/tmp/ash-syntax-unwrap-driver.log` (SHA-256 `5be6520598b42c1218239c23032279a0d5d682b009717f52b8c170cadbe005f2`). Parsing then discarding a nested rejecting transformer does not run it (0.5), `/tmp/ash-syntax-parse-no-expand-driver.log` (SHA-256 `4dd073d143a1f2da9658b8f22fc631d5a46fd488a57990f4332e16e3bd09b133`). Unwrapping a caller-qualified term retains its import and yields 30 (0.5), `/tmp/ash-syntax-qualified-after.log` (SHA-256 `dfbe5239cb5aa17305ed3648e85ed916bc030ca645b537f870b56a443b06db5e`). `SyntaxDiagnostic` retains a parser reason and construction location (0.5), `/tmp/ash-syntax-parser-diagnostic-driver.log` (SHA-256 `e8954105f99c7e0ff104fd5651ec14344b07bfda87310b58855e99ebd74d7472`); broader parse and unwrapping contexts remain pending. |
| P21 | 3.5 | Dev / R1.5 | Fresh binder avoids caller `temp` (0.5), definition identifier selects a private helper under caller shadowing (0.5), and caller identifier binds a caller body (0.5), `/tmp/ash-syntax-constructed-ident-driver.log` (SHA-256 `19f2462c862910b90739cfb207b2cdbf286bbe85ac0c1207714f5e5a287d29fa`); distinct fresh allocations and broader authority/context cases remain pending. |
| P22 | 1 | Dev / R1 | Empty origins return `MissingOrigins`; nonempty and nested combinations cross parse and unwrap before the graph executes to 42 (0.5), `/tmp/ash-syntax-combine-origins-driver.log` (SHA-256 `ca483c2b063c55e27a151adf79e1644a0b8e6f7f6e380c6fe11943688aa8dedd`). A transformer-authored rejection preserves its message and ordered caller/definition causes (0.5), `/tmp/ash-syntax-rejection-driver.log` (SHA-256 `dd3b9eea67d1ef9ac6191fdfa6b15df46fc270e969ab70018b23d6a0077ecccb`); final generated-program causal-origin propagation remains pending. |
| P23 | 4 | Dev / R2 | Reviewed expression/token decoding, transfer and protected-fragment parsing (1.5); parenthesis/brace group decoding and parsing (0.5), `/tmp/ash-syntax-vocabulary-groups-regressions.log`; complete output, failure and observed root-close behavior pending. |
| P24 | 2.5 | Dev / R2 | Malformed direct output reports `parse.expected-operand` (0.5), `/tmp/ash-syntax-invalid-output-driver.log` (SHA-256 `7d4df37046fea2bae1e0b14ac144bcd232809730f05ccd0df94be4edd455ef05`). Evaluator failure retains its underlying cause and invocation/definition locations (0.5), `/tmp/ash-syntax-diverge-after.log` (SHA-256 `4be2d989431d7da8b0844bb3af9dfe0a6e21afde7ba15f897f2dcda7ffbfd1a9`). A normal transformer closes its root before its output executes; an injected close failure retains authored or parser rejection plus teardown, and prevents successful output publication (0.5, reviewed at `93c0aa04`), `/tmp/ash-transformer-teardown-final.log` (SHA-256 `69eec7daac5be0f7f9cc4d7f76477ae5a24ebcb6f8f6c4580b67675ff0707d41`). Active-machine destruction on real evaluator and service failures, plus transfer failure and paired completed-root refusal, add 0.5 reviewed at `50ed262f` (`/tmp/ash-transformer-lifecycle-stack-final.log`); paired active-disposal refusal and remaining failure paths are pending (0.5). |
| P25 | 1 | Dev / R1 | A real non-requesting recursive transformer terminates as an expansion failure under the existing execution limit, `/tmp/ash-syntax-diverge-after.log` (SHA-256 `4be2d989431d7da8b0844bb3af9dfe0a6e21afde7ba15f897f2dcda7ffbfd1a9`). |
| P26 | 0.5 | Dev / 0 | Required service, output, and expansion limits produce ordinary closed-invocation failures. |
| P27 | 2.5 | Dev / R1 | Frozen computed graph to 42 (1), `/tmp/ash-transformer-combined-driver.log`; template/procedure equivalence (0.5), discarded and repeated nested invocation behavior (1) pending. |
| P28 | 2.5 | Dev / 0 | Independent declaration-coordinate/scope/type/provenance mutation checks (1), distinct compile-time/final validation (1), completed dependency reuse (0.5). |
| P29 | 2 | Dev / 0 | Repeat compilation modulo fresh identities (1), changed semantic inputs update/reject output (1). |
| P30 | 2.5 | Dev / R1.5 | Ordered occurrence causes and distinct expansion-frame representation (1), reviewed at `621f801c` and `79d3aad7`; demonstrated ordinary operator, match and application locations (0.5), reviewed through `a1fec7d7`. Other ordinary semantic causes/locations (0.5) and bounded copying/relocation preservation (0.5) remain pending. |
| P31 | 2.5 | Dev / R1.5 | Authored rejection (0.5) and retained parser failure (0.5) render their messages and caller/definition causes in human and JSON output, `/tmp/ash-syntax-rejection-driver.log` and `/tmp/ash-syntax-parser-diagnostic-driver.log`. Distinct ordinary type errors render occurrence and frame labels in both formats (0.5), reviewed at `621f801c`, `79d3aad7`, and `a1fec7d7`; the latest receipts are `/tmp/ash-origin-argument-human-final.log` and `/tmp/ash-origin-argument-final.json`. Remaining diagnostic variants, complete frame structure, and locale/catalog conformance remain pending (1). |
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
Reviewed effort is 61.5, demonstrated provisional effort is 0, and 38.5 points
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
| Pending | M06: definition authority | Private helper and own opaque construction; targeted/qualified/facade imports with caller shadowing. Reject ordinary caller private access, another module's withheld constructor, fabricated definition contexts, and missing definition helpers when expanded. |
| Pending | M07: imports and staging | Renamed and duplicate syntax imports, term-name conflicts, no activation through complete import, missing exports, unsupported re-exports/local definitions, and canonical dependency cycles. Unused imports cannot run transformers. |
| Pending | M08: DSL composition | Two separately authored forms nest and embed Ash. A template invokes a syntax dependency absent from caller imports. A same-spelled caller syntax import cannot redirect a generated identifier. |
| Pending | M09: current checks | Generated method obligations require ordinary evidence; wrappers preserve current handler selection and observable effect count/order. Test valid/invalid `resume` and resource escape/use, including a nested function and required direct builtin import. |
| Pending | M10: bridge and origins | Identity transformer round-trips token/group/fragment structure, contexts, and origins. Check total negative/out-of-range capture indices, empty origin combination, invalid identifier/token construction, and `parse_expression` without name resolution or expansion; returning `SyntaxDiagnostic` preserves parse causes/origins. Reject wrong nominal constructors, malformed data, stale/foreign handles, and authority gained from strings/origins/caller syntax. Assert multiple input origins and nested frames in human/JSON diagnostics. |
| Pending | M11: completion and limits | Successful output survives evaluation-root teardown; authored failure, malformed output, evaluator/transfer failure, and exhausted budgets publish no partial result and retain teardown information. Bound self-producing recursive expansion. |
| Pending | M12: reproducibility | Repeat equal compilations modulo fresh identity renaming; change caller binding, matcher, helper, imported syntax, and interface/semantic inputs and show updated output or rejection. No persistent cache is required. |
| Pending | M13: module/Core boundary | Reuse a completed dependency without repeating its source proof; validate new compile-time and final linked Core independently. Reject scope, type, and provenance mutations at their owning boundaries. |
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
