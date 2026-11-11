# TASK-0068: Top-Level Declaration and Derive Macros

- ID: `TASK-0068`
- Status: active; partial deliveries retained
- Related: [GitHub parent issue #206](https://github.com/dikini/ash-lang/issues/206),
  [CP-0034](../proposals/CP-0034-top-level-declaration-macros.md),
  [DN-0062](../design/DN-0062-hygienic-surface-macros.md),
  [slice 2 delivery plan](../design/macros/slice2-delivery-plan.md),
  [reviewed work structure](../design/macros/slice2-work-structure.md),
  [integration corpus](../design/macros/fixtures/README.md).

> This task tracks delivery of the accepted transition. CP-0034 is partially
> implemented on the retaining branch; this task does not define current Ash
> semantics or extend the authorized scope.

## Dependencies

The retained [expression-syntax specification](../../spec/syntax-expansion.md)
is the slice 1 baseline. CP-0034 is accepted, and the C1–C4 contract and corpus
checks are recorded in the delivery plan. The E4 checkpoint was retained by
[PR #298](https://github.com/dikini/ash-lang/pull/298) at
`17788de140a48a1c1d4a1d3aeb1d1ef2878d0a92`, tree
`2a9235f9c52c39376a12c724fbfa18394b04a419`. I19 was subsequently retained by
[PR #299](https://github.com/dikini/ash-lang/pull/299) at
`6e089e2e0c299c5ac158301bd132e28dd94f9f2e`, tree
`86e8d1a258e6fc1ea04790dc5d224c33facb10fc`. Recheck refs and worker ownership
before dispatch. The plan records earlier retained squash commits, their
partial criteria and the remaining producer/consumer interfaces.

The reviewed work structure is filed under [issue #206](https://github.com/dikini/ash-lang/issues/206)
as seven workstreams and 45 child issues. All 112 native blocking links still
match the reviewed graph. The retained acceptance records below identify the
closed units; later connected criteria remain open. The user has authorized
delivery and squash merges into the retaining branch; Main remains separate.

The active `/root` orchestrator inherits its launching model/effort and owns
integration. Planning uses GPT 6.1 Sol Max; development uses GPT 6.1 Terra Max;
independent QA uses Terra 6.1 Medium; independent review and acceptance checking
use Sol 6.1 Max, including replacements. Sol independently checks the developer's
acceptance record; the developer applies the checked record and performs
readback; the orchestrator confirms. Keep these roles independent,
assign shared-file ownership before parallel edits, and use one assigned
heavy-build operator with one Cargo job and the compatible cache.

## Work

Deliver imported top-level declaration macros and type/newtype derives,
including declarative templates, checked procedural transformers, quotation,
executable escapes, repetitions and state-threaded generators. Preserve syntax
contexts, protected fragments and source origins through the existing parser,
host and downstream compiler. Establish the early connected declaration path
at D8, the early quote/escape path at E4, and the complete public-driver path
at V3. The linked work structure records each unit's deliverables, acceptance
cases, prerequisites and hard boundaries.

### Do not do

- Do not add or change downstream type checking, inference, semantic checking,
  name resolution, elaboration, publication rules or Core validation. Ordinary
  compiler stages check generated code and report its errors. Preserve spans,
  contexts and origins; if a downstream consumer is deficient, record its
  concrete gap separately and stop the affected path.
- Do not add a macro-specific semantic checker, second resolver, per-reference
  grants, automatic conflict repair, new host or new error protocol. Do not
  change slice 1 behavior except for CP-0034's accepted `syntax` reservation
  and syntax-service sum extensions.
- Do not implement local declaration macros, generated imports or generated
  syntax definitions, typed reflection, a generic conversion interface,
  implicit primitive conversion, an ambient compiler input for generator
  helpers, effects redesign, Wasm support or unrelated refactoring.
- Do not cross an individual work item's explicit prohibition because it
  appears convenient. Record the reason, return a contract change to its owner,
  and continue independent work within scope.

## Progress

The reviewed original 45-unit delivery prediction is **142 points**. C1–C4's
recorded planning scope is **8 predicted points**, giving **150 points** for
the full scope. Preserve these fixed predictions and all original DAG edges.
D1, S1 and D8 account for ten original predicted points; the later retained
acceptances below add completed units. These figures do not measure remaining
effort or grant partial acceptance credit. Earlier
partial-delivery records below describe their state at the time and are
superseded where the later retained checkpoints say so.

### Later retained acceptances

- D2 [#216](https://github.com/dikini/ash-lang/issues/216), D7
  [#217](https://github.com/dikini/ash-lang/issues/217) and H1
  [#220](https://github.com/dikini/ash-lang/issues/220) are closed on their
  original focused criteria, supported by the D8 checkpoint in
  [PR #295](https://github.com/dikini/ash-lang/pull/295), retained at
  `ac3a70d3bd2e24fd316d7bee3b98c08458ccdee1`.
- H2 [#224](https://github.com/dikini/ash-lang/issues/224) and H3
  [#229](https://github.com/dikini/ash-lang/issues/229) are closed on their
  original focused context and refusal criteria using retained evidence and D8.
- E4 [#242](https://github.com/dikini/ash-lang/issues/242) is closed after the
  independently reviewed E4 checkpoint and the retained PR #298 tree above.
  E1 [#226](https://github.com/dikini/ash-lang/issues/226) and E2
  [#239](https://github.com/dikini/ash-lang/issues/239) remain partial.
- S3 [#221](https://github.com/dikini/ash-lang/issues/221) is closed on its
  original focused host-transfer criteria. The exact I16 mutation and other
  later connected cases remain at their original gates.
- D3 [#218](https://github.com/dikini/ash-lang/issues/218), D4
  [#222](https://github.com/dikini/ash-lang/issues/222), D5
  [#223](https://github.com/dikini/ash-lang/issues/223), and G1
  [#228](https://github.com/dikini/ash-lang/issues/228) are closed on their
  original focused criteria after the I19 delivery and independent readback.
  G2 [#231](https://github.com/dikini/ash-lang/issues/231) remains open: its
  delivered scope is held on D6 [#219](https://github.com/dikini/ash-lang/issues/219),
  which still needs the checked procedural transformer Import-output refusal.

### Introduced module-constructor candidate

The focused [#306](https://github.com/dikini/ash-lang/issues/306) candidate
retains the existing module constructor identities under their admitted
declaration-template introductions. The original no-Derive generated and
handwritten controls both return 42 on the candidate. The unchanged I09
nested graph advances beyond its constructor lookup and then stops at the
separate introduced nominal lookup in
[#308](https://github.com/dikini/ash-lang/issues/308). A generated Newtype
constructor likewise reaches a later Core registry refusal; its handwritten
control returns 42. These later results do not establish the nested or
generated Newtype runtime criteria.

Focused identity, context, visibility, duplicate and resource checks, review,
retention and acceptance remain required for #306. The bounded #308 repair is
separately authorized and remains outside this candidate.

### Connected derive and checked-host candidate

**Candidate:** Draft [PR #307](https://github.com/dikini/ash-lang/pull/307)
connects imported derive definitions, complete original subject capture,
ordered output admission and the existing checked declaration host. It also
includes the approved declaration-only keyword metanames and the bounded
[#288](https://github.com/dikini/ash-lang/issues/288) Data origin and exact
primary-span tie repair. On candidate `55aff55e10988ab316ae1466a4ecbaa84a678ae6`,
the unchanged I09 and one-, two- and three-constructor Indexed consumers
execute to 42. Focused observations cover subject and output order, constructor
contexts and emitted equations, transfer before host teardown, Import refusal,
and resource exhaustion with retry. The selected run recorded 41 passing
tests and 59 public success or refusal cases with matching input snapshots.

**Remaining:** The unchanged I04 relation graph now passes source checking and
elaboration, then reaches the parameter-order validation guard tracked by
[#303](https://github.com/dikini/ash-lang/issues/303). The fixed I09 nested
generated-constructor graph reaches
[#306](https://github.com/dikini/ash-lang/issues/306); the separate effect-row
coordinate issue [#304](https://github.com/dikini/ash-lang/issues/304) also
remains open. Generator clauses, matcher-capture reads in escaped code and
per-iteration escapes remain under development. The full I16 native and
source-free image path, hygiene and exact identity mutations, V3, V7 and V8
remain at their original gates.

**Awaiting:** Independent final review and QA, retention, and acceptance of
each original issue in its native prerequisite order. Earlier progress entries
below describe their state at the time.

**Owner:** The developer owns the candidate and evidence; independent QA and
review own their checks; the orchestrator owns integration and acceptance.

### Connected I19 capture and repetition delivery

The retained I19 delivery connects the extended definition and template,
category-aware matching, nested capture lookup, repeated output, and the
ordinary module collector. The unchanged I19 main, counts, and binder graphs
execute to 128, 42, and 42; their handwritten controls match. The fixed
missing-driver, unequal-driver, empty-plus, trailing-separator, and ambiguous
definition cases reach their specific causes. Fresh incomplete and
two-declaration capture mutations reject at the caller boundary. The candidate
also exercises the shared ledger and atomic collector on actual repeated and
caller-authored declaration output. PR #299 was independently reviewed and its
retained tree and issue acceptance records were verified.

The earlier empty-template producer and Identifier-only structured matcher
were insufficient for the connected graph. A further attempted nested
invocation exposed an invalid cross-source span join; the projector now uses
the existing enclosing occurrence for the aggregate invocation while retaining
the caller and definition origins on their original nodes. Repetition escapes,
direct protected quoted-AST copying, and the separately tracked downstream
origin and nominal-context gaps remain separate. The next fresh full-workspace
checkpoint is V7.

### Downstream diagnostic and global origin repairs

PR [#300](https://github.com/dikini/ash-lang/pull/300) retained the separately authorized
[#263](https://github.com/dikini/ash-lang/issues/263) and
[#287](https://github.com/dikini/ash-lang/issues/287) repairs at
`0b25aa896a210a7f2347bdf545f313acc6f60557`. An unknown
matcher capture now reaches ordinary syntax diagnostics with its source span
and spelling. A literal global introduced by a declaration template retains
its invocation and definition origin through ordinary binder allocation. The
original public-driver graphs and focused controls passed; independent review,
retention and issue acceptance readback completed.

### Downstream definition-context nominal classification

**Delivered:** The separately authorized
[#277](https://github.com/dikini/ash-lang/issues/277) repair authenticates an
introduced unqualified type reference using its existing definition context
before retaining an otherwise implicit free parameter. The original graph
without a caller import and its three controls compile, independently validate
and execute to 42. The original 40-application and 46-tuple capture graph also
executes to 42; one additional tuple retains the structural-depth refusal.
The retained nominal identity, parameter kind and hidden summary fact remain
available without exposing constructors. Explicit parameters and row tails
keep their existing discovery rules. The repair was retained at
`8defbbaf98e1cdac0eaaf18deb600148ee19f94c` and accepted.

### Downstream explicit parameter contexts

**Candidate:** The separately authorized
[#301](https://github.com/dikini/ash-lang/issues/301) repair registers the
already allocated explicit parameters using their retained source contexts.
The original generated global and handwritten control execute to 42, as do
isolated generated and handwritten interface, higher-kinded interface,
implementation, nominal, effect and operational-global controls. An unrelated
caller type remains unbound. These observations await final review and retention.

**Remaining:** The original integrated macro gates remain open. The fixed I03,
I04 and I08 graphs currently stop while parsing their shared template source.
An explicit method-parameter consumer reaches the separate Core ordering guard
recorded in [#303](https://github.com/dikini/ash-lang/issues/303); a row-parameter
consumer reaches the source-coordinate refusal in
[#304](https://github.com/dikini/ash-lang/issues/304). Their handwritten controls
execute to 42. The fixed I09 generic derive, I17 main generator and original I22
categories and nested graphs stop earlier at their existing projection or parsing
boundaries; no result for their later paths is inferred.

**Awaiting:** Independent candidate review and QA, retaining verification,
and the author acceptance record with independent readback.

**Owner:** The developer owns the candidate and acceptance update; independent
QA and review own their checks; the orchestrator owns retaining integration
and final acceptance confirmation.

**Delivered:** Thirteen earlier reviewed squash deliveries establish D1/S1,
partial declaration selection/matching/admission, type/pattern capture producers,
identifier-only declaration collection and H2/H3 tests. The refreshed plan is
retained by [PR #276](https://github.com/dikini/ash-lang/pull/276) at
`ea76717de64934244b7626f96c720a1c01f63ab2`.

- [PR #278](https://github.com/dikini/ash-lang/pull/278) retains two early I13
  public-driver controls at `6e75b6a03a5ea95b693cadb3f8a6949ff5e31d32`.
  The [H5 record](https://github.com/dikini/ash-lang/issues/225#issuecomment-6743017228)
  covers their bounded hygiene and direct-private-access assertions.
- [PR #279](https://github.com/dikini/ash-lang/pull/279) retains focused S3
  host and parser-handoff controls at `c2b6c5fbdf5d2fd75a59e236e03639b6d909b552`.
  The [S3 record](https://github.com/dikini/ash-lang/issues/221#issuecomment-6743274210)
  identifies the constructed D7 frame and the remaining host consumers.
- [PR #280](https://github.com/dikini/ash-lang/pull/280) retains protected Type
  capture accounting at `9e89ac126c1f67b1cd7bb83bc2245c7dd0c8c5e9`. Its
  [D4 record](https://github.com/dikini/ash-lang/issues/222#issuecomment-6744016005)
  reports 357 distinct focused passes and one ignored nominal-context case.
  The original I01 and I07 graphs and handwritten controls compile and execute
  to 42 through the public driver; the I07 missing-Type mutation reports its
  ordinary parser cause and invocation location.
- [PR #281](https://github.com/dikini/ash-lang/pull/281) retains the accepted
  inline escape amendment and its planning record at `3613a863`. Quote and
  escape implementation remains open.
- [PR #282](https://github.com/dikini/ash-lang/pull/282) retains the direct
  protected expression and pattern path at
  `3a30b75307cb9c4208b71ddc15efb7fa0ecc1bb2`, with tree
  `94420e402b5bec57099f94a33e0a9c15b70a6133`. The partial records for
  [D3](https://github.com/dikini/ash-lang/issues/218#issuecomment-6748440248),
  [D4](https://github.com/dikini/ash-lang/issues/222#issuecomment-6748443693),
  [D6](https://github.com/dikini/ash-lang/issues/219#issuecomment-6748447094)
  and [H3](https://github.com/dikini/ash-lang/issues/229#issuecomment-6748450548)
  have been applied and read back.
- [PR #283](https://github.com/dikini/ash-lang/pull/283) retains the bounded
  source declaration-capture path at `3dc43762`. The checked
  [D5 record](https://github.com/dikini/ash-lang/issues/223#issuecomment-6750107621)
  leaves the full D5 and I19 criteria open.

For the original I15 `type_error.ash`, a fresh human and JSON driver readback
at `9e89ac12` reports the ordinary expected-Int/found-Bool cause with the
generated body, invocation and definition locations. The selected name is
traceable within the invocation source; no separate name-specific label is
claimed. The [D8 record](https://github.com/dikini/ash-lang/issues/232#issuecomment-6744362138)
links the bounded readback; its receipt SHA-256 is
`24245017679e2f8d417036813d6b10cfa88331f4046bf7ded4b081737a63cdf5`.
Independent QA and Sol checked these focused deliveries and readbacks; the
orchestrator confirmed them. Their original issue criteria remain unchecked.

### Retained expression and pattern path

**Delivered:** The reviewed source candidate for
[D3 #218](https://github.com/dikini/ash-lang/issues/218),
[D4 #222](https://github.com/dikini/ash-lang/issues/222),
[D6 #219](https://github.com/dikini/ash-lang/issues/219) and
[H3 #229](https://github.com/dikini/ash-lang/issues/229) is
`f2ff93084c2f064695eb2b1faa2522725d8aabf8`, tree
`0d8c6c7bd710dcf68f5df371dad2b4850504bbff`. PR #282 retained this source
through its TASK-only successor and the verified `3a30b753` squash. It connects
protected expression and pattern captures through direct declaration templates,
using the existing shared syntax budget for capture, substitution, staging and
projection. D6
uses its existing admission budget through placeholder creation, parsing and
validation. The retained Type path remains active. Protected fragments in
generated expression-syntax arguments and protected expressions containing
nested expression syntax remain refused before their unbudgeted expression
consumers; procedural declaration execution remains guarded.

The unchanged I19 binder graph and handwritten control execute to 42 through
the public driver. Imported forwarding and a duplicated expression also execute
to 42. A driver-level selection and collector check observes caller binder and
body contexts, origins and invocation frames. Other path and depth checks use
constructed protected originals or metadata and are component evidence. The
unchanged I01 and I07 driver controls and missing-Type refusal remain in the
focused regression set. The original I01–I22 fixtures are unchanged.

The focused receipt at
`/tmp/ash-task0068-retained-evidence/expr-pattern-3613/complete-f2ff9308/receipt.json`
has SHA-256 `95a88e0d99e70857797b6799749b5ec3988fc838ba867ecc50f75f7a9830a9f3`.
The earlier TASK-only candidate `d6d41373` carried this evidence from
`f2ff9308` through unchanged product source, tests, specification, tool
configuration and fixed corpus inputs. The retained `3a30b753` tree equals
that reviewed TASK-only candidate. The focused gate ran on `f2ff9308`.
It records 396 distinct passing test names and one ignored original no-import
nominal case, tracked separately by [#277](https://github.com/dikini/ash-lang/issues/277).
Both protected expression/pattern and Type paths have actual 512 KiB
success/drop, late-depth and late-work cleanup runs. The fresh I15 human and
JSON readback retains the ordinary expected-Int/found-Bool cause, generated
body, annotation, invocation and definition locations. The selected name is
traceable within the invocation source; there is no separate name-specific
label claim. The caller-import control does not replace #277's ignored graph.

The candidate repairs three accounting findings: the second pattern copy in
match and handler projection, the generated parameter-order Arc and boxed
occurrence diagnostic depth, and the second D6 matcher traversal's literal
visits. An early architecture check also exposed six missing borrowed-field
inventory entries; the candidate adds those entries without changing scanner
rules. The receipt preserves the failed checks and subsequent repairs. A
temporary `b6b8e9fa` test-only trace observed earlier output in the same short
failure run; `e4cc9b5b` restored the preceding tree. That trace is supplemental
evidence, not an input to the final uninstrumented gate.

**Remaining:** D3 still needs its full capture and missing-input criteria; D4
still needs its full category and connected-corpus criteria. D6 retains its
full definition-admission criteria and procedural-output import refusal for
the S3/S4 consumer. H3 retains its full nominal, constructor, interface and
pattern context and duplicate-source criteria. The complete I19 graph still
needs D5 and G1. No original criterion for these issues is closed by this
candidate. Full V4 specification and tool documentation follows its reviewed
V3 prerequisite; accepted but unimplemented forms remain outside current Ash.

**Awaiting:** Independent QA and Sol cleared the focused source and receipt, and
checked the PR and applied partial issue records. Full D8, E4, V3 and V7
gates remain open.

**Owner:** The developer owns subsequent changes and their evidence.
Independent QA and Sol own their checks; the orchestrator owns retaining
integration and acceptance confirmation. Main is a separate boundary.

### Retained declaration-capture path

**Delivered:** The source-only D5 candidate for
[#223](https://github.com/dikini/ash-lang/issues/223) is
`aabaf99455762b36ffd6cc4ab6942bed24669589`, tree
`de0c2e1aef89ac4e416f8b0a39ed76c6ce18c570`, based on retained `3a30b753`.
A real imported empty-output declaration template accepts each of eight ordinary
source declaration categories through the public driver. Component checks retain
the I19 signature and equation excerpt, introduction-zero source names and
source origins. The packet retains the ordinary declaration child's token order
and omits the capture braces and boundary line ends.
Incomplete, multiple and excluded source forms report parser failures at their
observed caller locations. These checks do not establish the complete I19
graph or declaration-fragment consumption.

The existing syntax budget covers source packet construction, including nested
groups, payloads and retained copies. Packet-phase checks use exact, short and
retry allowances. On a 512 KiB stack, the component constructs, converts and
drops a 128-layer packet and refuses a 129-layer packet before construction.
The test-constructed host component pairs supported nested-expression
construction and drop with first and later Declaration refusals on the same
stack. The injected request control is a separate invalid-state component; it
is not a host-transfer or macro-owner provenance claim.

The focused receipt is
`/tmp/ash-task0068-retained-evidence/d5-3a30/final-aabaf994/receipt.json`
(SHA-256 `18dcd05e196e39ebc1b0fb339921f6340148d828dae90e65be34e254af10abfc`).
It records 429 distinct passes, including 47 architecture tests, with equal
before/after input snapshots. Two separate tests are ignored: the existing
[#277](https://github.com/dikini/ash-lang/issues/277) nominal-context case and
a supplemental valid nonempty-template positive awaiting D5/D6. Repeated stack
runs are not additional distinct tests. Independent QA and Sol cleared the
focused candidate and evidence. The gate ran at `aabaf994`; the TASK-only
successor `15c3f8ce` retained identical product source and tests, and PR #283
retained its exact tree at `3dc43762`. The checked #223 record reports this
bounded delivery; its original criteria remain unchecked.

The initial public red pin `400652b2` failed at the declaration capture header
before the port. At preliminary pin `7ad738ae`, an inherited host refusal test
used an empty effect registry and could fail before the capture guard. The
separate red receipt
`/tmp/ash-task0068-retained-evidence/d5-3a30/host-red-f53a8acd/receipt.json`
(SHA-256 `41048c12ab2259dcc8fdd36e482fe6610c56b9867a727f483b70e2241b3495ed`)
preserves that observation. The corrected component first proves that its
test-constructed entry, validated program and matching effect registry construct
a host with the supported capture. The existing selection and definition clone
precede standalone matcher refusal;
the corrected interface removes the proposed extra matcher scan and refuses a
Declaration before constructing its packet. Supported prefix work may already
have happened. A constructed nested Declaration is refused by the singleton
entry's original-token scan and by composed projection; its packet count is
supplemental evidence. The existing generic `Invalid` mapping for temporarily
unsupported nonempty/procedural definitions is not a required diagnostic.

An earlier independent candidate `72b5bed1` overflowed a 512 KiB stack. The
separate `abda1098` phase witness localized the failure to packet construction
after parsing and preflight; the D5-only iterative builder repaired that phase
without changing the shared limit. Candidate `079cbdbc` then exposed three
missing physical carrier inventory entries; its successor added those entries
and the necessary transient profile without changing scanner rules. The earlier
failed-gate receipt is
`/tmp/ash-task0068-d5-evidence/repair-079c/architecture-failure-receipt.json`
(SHA-256 `db86b92c7cc5a140753c00734f90956b251fff7eae09bfc215497d60d6b992dd`).
Those observations belong to the earlier candidate; the current combined gate
checks the integrated source independently.

**Remaining:** The full D5/I19 criteria, declaration splices and host transfer,
generated or structured recapture, procedural declarations, deriving and the
connected consumers remain open. A valid unused nonempty template remains a
positive obligation, not a language rejection.

**Awaiting:** D8, E4, V3, V7 and the fresh full-workspace gate remain open;
D8 is the next full checkpoint once its required connected paths are ready.

**Owner:** The developer owns subsequent changes and evidence. Independent QA
and Sol own their checks; the orchestrator owns integration and acceptance
confirmation.

### Retained quote and escape parser slice

**Delivered:** The parser-only E1 source candidate for
[#226](https://github.com/dikini/ash-lang/issues/226) is
`74f5e024faf67db185ba97f3c75f00cd9aa93c58`, tree
`b669b3b00a537cdb4bd955d15249e712e23dddad`, based on retained `3dc43762`.
PR [#284](https://github.com/dikini/ash-lang/pull/284) retained its reviewed
TASK-only successor as `c4548296edeb570d9685830737587f5e6686ea53`, tree
`42335773fb29446bda649a42a3ecf5c311d3d8a0`, with product and test inputs
unchanged from the focused candidate.
It parses expression quotes, multiline escapes and the accepted inline
result-expression form while preserving ordinary Block grammar and the distinct
template-splice, escape-capture and quote-hole scopes. The ordinary and staged
projection paths refuse unconsumed quote and escape nodes; this candidate does
not admit or execute them.

The unchanged full `early_categories_forms.ash` now parses without recovery.
Its test checks all eight escape positions and their capture operands, including
the final declaration capture. This is parser evidence; it does not establish
the full categories graph's admission or execution. The unchanged I17
`malformed_helper.ash` reaches its missing-operand parser failure through the
public driver. The `unbound_outer_forms.ash` component preserves the outer
splice; its required definition-time rejection remains open.

The focused receipt at
`/home/dikini/Projects/ash-lang/.worktrees/task-0068-handoff/evidence/e1-final-74f5/receipt.json`
has SHA-256
`b442345aff25ce4dc1d169b9bbef63efa0300ed5484540e2f4efbd87f3fc43d7`.
It records 465 distinct passing tests and two retained ignores: the #277
nominal-context case and a valid nonempty template using a Declaration capture.
The source and structured quote controls cover exact/short/retry work and composed
depth 128/129. A constructed structured input uses the existing D6 admission
wrapper and its pre-spent ledger: successful quote parsing reaches the
intentional `Invalid` projection refusal, while insufficient work and excess
depth retain their separate resource failures. This is a component check, not
quote admission. Nested quote and inline-escape tests each observe success,
refusal and drop on a 512 KiB stack; repeated runs are not additional tests.
The fixed I15 human and JSON diagnostics and retained D5, Type, expression,
pattern, slice 1, S3, H5, parser and architecture controls also pass.

The red test at `e9ae8c6d` failed at `syntax` before this port. Independent QA
and Sol cleared the focused source and evidence. The focused gate ran at
`74f5e024`; this TASK-only record preserves identical product, test,
configuration and fixed-corpus inputs. The gate was not rerun on this record.
The constructed quote metadata and nonstaged protected-expression tests remain
component evidence, not public host or quote-transfer results.

**Remaining:** Full E1 quote admission and unknown-outer rejection, the E2
checked-host quote consumer, E4 escape execution and the original I17/I22
connected and diagnostic criteria remain open. No original criterion is closed
by parser-only evidence.

**Retained:** Independent TASK review, PR review, retention and the
[partial #226 record](https://github.com/dikini/ash-lang/issues/226#issuecomment-6751073601)
were confirmed with independent readback. D8, E4, V3, V7 and the fresh
full-workspace gate remain open.

**Owner:** The developer owns the candidate, evidence and acceptance record.
Independent QA and Sol own their checks; the orchestrator owns publication,
retaining integration and acceptance confirmation.

### Retained derive parser slice

**Delivered:** The parser-only R1 source candidate for
[#227](https://github.com/dikini/ash-lang/issues/227) is
`f0060437ffcd51a5df037698ab5bc27377eb49c4`, tree
`2225de79b50d9c0385a70411e921c5e8e5a9f3f7`, based on `c4548296`.
PR [#285](https://github.com/dikini/ash-lang/pull/285) retained its reviewed
TASK-only successor as `3ae2c3e1d4a7bb5678d002b72bdd1314ffccd699`, tree
`01c05d00c6889823843f802e49692b74f0fdb834`, with product and test inputs
unchanged from the focused candidate.
It retains contextual derive headers and a final token-only deriving clause on
module type and newtype CST subjects. Existing whole-root and generated
projection checks refuse unconsumed forms before publishing owners or source
Declaration packets. Ordinary expression and declaration syntax, local
newtypes and selected import precedence retain their focused controls. This
candidate does not admit or execute derives.

The unchanged I09 main, renamed, generic, opaque and duplicate fixtures reach
their CST/refusal boundary; empty and unsupported clauses reject. I14 and I15
derive definition fixtures also reach CST/refusal only. The D5 source sink
retains each complete type or newtype subject and its ordered clause in CST,
then refuses before packet preflight; no-clause controls execute to 42. Generated
Type/Newtype clauses and derive headers reach the existing D6 and generated
projection wrappers and refuse there. The structured carrier and frames are
component evidence, not an authenticated completed derive invocation.

The focused receipt at
`/home/dikini/Projects/ash-lang/.worktrees/task-0068-handoff/evidence/r1-recovery/combined-f0060437/receipt.json`
has SHA-256
`e48fc38066925173517884e674901a637cf30eb812208519ed8d7bb4fe6fba33`.
It records 569 distinct passing tests and two ignored obligations: the valid
nonempty Declaration template and the #277 nominal-context case. Source and
generated paths cover exact/short/retry work, metadata and depth boundaries;
source and generated 512 KiB subprocesses observe construction, refusal and
disposal. The derive header composition checks nested inline escapes and quote
modes; the retained full E1 suite supplies the multiline regression. The
D5, expression/pattern, Type, H1/H2/H3/H5, S1/S3, parser, host and architecture
controls also pass. Separate stack reruns are not additional test names.
Independent QA and Sol checked the pinned source and receipt.

**Remaining:** Full R1 derive definition admission, name and category
selection, I09 successful imported and renamed derives, I14 definition-time
refusal of an unused malformed derive, and I15 returning 42 with an unused
unresolved derive free name remain open.
R2 and its S2 handoff, R3 ordering, R4/R5 execution and R6 generated subjects
remain separate. This parser-only candidate closes no original criterion.

**Retained:** Independent TASK review, posted PR review, retention and the
[partial #227 record](https://github.com/dikini/ash-lang/issues/227#issuecomment-6759764232)
were confirmed with independent readback. The D8/E4/V3/V7 checkpoints and
the fresh full-workspace gate remain open.

**Owner:** The developer owns candidate, evidence and acceptance update;
independent QA and Sol own their checks, and the orchestrator owns integration
and acceptance confirmation.

### Retained procedural declaration slice

**Delivered in the local candidate:** The first S2/S4 Declaration/Transformer
slice is `c5063fa7b0ac468ed9e6ff0e6845f706549d7cd9`, tree
`6625add9201093b6d0934ea288ab7f61612dcfd5`, based on retained R1 commit
`3ae2c3e1d4a7bb5678d002b72bdd1314ffccd699`. [PR #286](https://github.com/dikini/ash-lang/pull/286)
retained its reviewed TASK-only successor at `b8cad02c`; the retained tree is
`a7753f6009613fdaaee9b5b5a5bc701e42ea9b29`. The existing checked host issues
and unwraps source Declaration captures, transfers raw identifiers, tokens and
groups into compiler ownership before teardown, and resumes declaration
staging on the same graph syntax budget. Identifier captures are supported
alongside Declaration captures on this route. Legacy expression host callers
retain their existing allowances; protected Type, Pattern and expression bridge
paths are not enabled here.

The unchanged supplemental `procedural_declaration/main.ash` and `forms.ash`
run through the public driver and return `42 : Int`. The unchanged
`rejected.ash` retains its authored message, distinct caller and definition
sources, human and JSON labels, and returns no compiled program. Inspected
staging source flow returns before owner publication and drains the failed
graph; the rejection test does not directly inspect those graph fields. The
checked real graph uses one budget from discovery through host and staging:
exact and retry trials return 42, and one-short refuses without graph or program
publication. Real-graph constructor, active-service and transfer shortages
retain their paid work and complete cleanup; a separate injected root-close failure
preserves the original transfer failure. Constructor refusal precedes the test
observer, so its counters do not establish a root-drop event.

The focused receipt is at
`/home/dikini/Projects/ash-lang/.worktrees/task-0068-handoff/evidence/s2-s4-interface/final-gate-c5063fa7/receipt.json`,
SHA-256 `7f801051b110e6f6b5a55f64203a561666c71d32d346ff43c26e6df11dff0cd7`.
It records 587 distinct passes and two retained ignores: a valid nonempty
template with a Declaration capture in its matcher and no used splice, and
the #277 nominal-context case. Its 512 KiB component
witness constructs the capture, uses actual host capture, unwrap and transfer,
and drops the final aliased origin owner: capture composition 128 becomes raw
transferred output depth 127; composition 129 refuses before host retention.
That synthetic validated-registry component is separate from the checked public
graph. Source snapshot path growth and combined text/line-index growth are
charged; the atomic shortage precedes source cloning by the inspected source
flow. Retained parser, staging, legacy service, image and architecture cases
remain regression evidence. Independent QA and Sol cleared the focused source
and evidence.

**Remaining:** Full S2 I11/I19 and I14 protected categories and their mixed or
generated consumers remain open. The two supplemental S4 positive and rejection
criteria have the focused public-driver evidence above and were checked in the
independently read back
[#234 record](https://github.com/dikini/ash-lang/issues/234#issuecomment-6761689308).
Its other three criteria remain unchecked. All five original S2 criteria remain
unchecked in the [#230 record](https://github.com/dikini/ash-lang/issues/230#issuecomment-6761681230).
The original I16 derive and teardown graphs remain at V3. D8, E4, V3, V7 and
the fresh full-workspace gate remain open.

**Awaiting:** The S2/S4 retention and issue records have independent readbacks.
Full S2 and S4 work, original I16 graphs and subsequent checkpoints remain open.
The developer owns candidate and acceptance updates; the orchestrator owns
integration and acceptance confirmation.

### Grouped source identifier and empty declaration candidate

**Delivered in the local candidate:** The bounded [G1 #228](https://github.com/dikini/ash-lang/issues/228)
source is `478eb4a443a4f12fa744cb5fea5a1feaa791da48`, tree
`64ae2d7e3674be07968e238647fcc4028d8c2bfb`, based on retained `b8cad02c`.
It accepts source-Identifier leaves within declaration matcher groups and
nested repetitions when the declarative body is exactly empty. The real
imported source graph materializes ordered and ragged captures, then stages an
empty output through the ordinary checker; its written `main` executes to 42.
The observer inspects those captures before staging. Separate real graph
controls cover inline and multiline empty template bodies, logical line ends in
braced matchers, zero-row, nested-empty, literal-only and nonempty Group cases.

The same graph syntax budget covers source parsing, matcher construction and
capture materialization. Focused checks cover pre-spent, exact, one-short and
fresh retry boundaries; refused work retains its paid prefix and the failed
graph publishes no module or program. Actual 512 KiB trials cover header
128/129, pure and mixed live 127/128, real capture construction, shallow
aliasing and final-owner disposal. The post-capture shortage drains the graph;
the source flow establishes that depth refusal precedes materialization.
The renewed flat-parser comparison preserves full ordered events, CST,
diagnostics and exact allowances for its three selected flat inputs. It does
not establish all legacy behavior by itself; the focused gate includes the
retained regression targets.

The fresh focused receipt is
`/home/dikini/Projects/ash-lang/.worktrees/task-0068-handoff/evidence/g1-source-ident/final-gate-478eb4a4/receipt.json`,
SHA-256 `1bb4e7a25b84b66bef4a5c66b4f0146f4b4e9fea3fb32eb24ecd2a7ee6bdf8fd`.
It records 640 distinct passes and two retained ignores: the valid nonempty
template with a Declaration matcher capture and no used splice, and the #277
nominal-context case. Marker and stack-child reruns are not additional passes.
Independent QA and Sol cleared the focused source and evidence. The four
ownership inventory entries were added after the preserved architecture failure;
scanner rules were not changed. The corrected host test executes under
`eval::machine::syntax`; an earlier zero-match command is retained as
non-execution.

**Remaining:** Full G1 and I19, repeated output and host consumption,
generated/protected/mixed paths, literal declaration output and D8 remain open.
The separate literal consumers are stopped at the confirmed downstream
[#287](https://github.com/dikini/ash-lang/issues/287) and
[#288](https://github.com/dikini/ash-lang/issues/288) origin gaps. The original
fixed integration graphs and all original criteria remain unchanged.
Expression matcher specification and the expression-only tool documentation
remain accurate and unchanged. The complete CP-0034 specification and tool
documentation update remains at V4 after V3; this candidate does not establish
current Ash semantics or close that verification item.

**Awaiting:** Independent TASK checks, exact-head Sol PR review, retaining
integration and checked issue readback. The developer owns the candidate and
acceptance record; the orchestrator owns integration and acceptance confirmation.

### Protected Type host retained contribution

**Delivered:** [PR #290](https://github.com/dikini/ash-lang/pull/290) retained
the bounded Type contribution at `b1a93e041826991d8d2f0a8edde267696e4d8f52`,
tree `9080fb533f5a7be423d178244933b4532f589cc8`. The tested Type source for
[S2 #230](https://github.com/dikini/ash-lang/issues/230) is
`bbe06818dd8eeddaa5b59002374bbd69da7851a7`, tree
`14b86d01741de83e659bc0ae357ba50cadc778ff`, based on retaining commit
`d737b323e1a2613cf7a93e589ef8bdad8ce53291`. It connects eligible flat source
Type and Identifier captures to the existing checked declaration transformer
host. The canonical compiler syntax module adds `type_syntax` and `parse_type`;
the host issues Type handles and transfers protected Type nodes through the
existing staging path. Retained syntax, owner copies, host scratch and output
share the existing graph budget. Transformer output refuses an actual protected
Type node inside a generated declaration-invocation argument.

The supplemental imported Type host graph captures a caller Type, unwraps and
parses it, and returns a protected TypeNode in an ordinary generated function;
the public driver executes that function to `42 : Int`. The checked real graph
also covers shared-budget exact, one-short and retry behavior. A separate real
source graph observes 124 written Function layers in its Type capture, then
uses the host capture, unwrap and parser on a 512 KiB thread. That graph stages
empty output and executes its handwritten main to 42; it is not the generated
function result. Constructed-host components separately cover protected 124/125
and raw 126/127 returned-owner boundaries, actual metadata, shortages and final
alias disposal. The unchanged 126-Group imported graph executes 42 on 512 KiB;
the adjacent 127-Group graph refuses without publishing a program.

The final focused receipt is
`/home/dikini/Projects/ash-lang/.worktrees/task-0068-handoff/evidence/type-host/final-gate-bbe06818/receipt.json`,
SHA-256 `7f9ac4c628768800e325adb39f9d1617818efe76bdbcb082997fd15ffa0091e4`.
It records 661 distinct passing tests and two existing ignored obligations:
the unused nonempty Declaration template and the
[#277](https://github.com/dikini/ash-lang/issues/277) nominal-context graph.
Stack child and marker reruns count once. Independent QA cleared this receipt
in audit `06c729710822f591813941d96fe6dd2067f25619d4ae794856d6c691ba3e3b6f`;
Sol independently cleared the source, command set and receipt. The unchanged
strict I14 test still fails: the ordinary category cause and caller location are
present, but its required definition-origin presentation is missing. The separate
[#265 finding](https://github.com/dikini/ash-lang/issues/265#issuecomment-6766825789)
tracks that downstream presentation obligation. The I14 failure is not a pass.

The earlier `10af6746` focused run exposed an unchanged 256 KiB local-nominal
regression. The retained base passes the same test; the candidate's Type
projector had a larger debug frame. The reviewed `bbe06818` extraction retains
the same single projector and budget operations while reducing its frame. Its
controlled receipt
`9fff5bce5293f34aae0431ef98e82ce8da1856703169f5d606bc51c2ca3768ba`
records the unchanged local-nominal test, Type budget and 512 KiB controls; the
final focused gate checks them again.

**Remaining:** Full S2 Type, Pattern, Expression and mixed/generated
consumers, used splices, original I11/I19 and I14 criteria, and the connected
downstream paths remain open. Full G1 and its repeated host/output consumers
also remain open.
All original #230 criteria remain unchecked. The original fixed I01–I22 corpus
remains unchanged. The original I16 derive, teardown and build/image paths, D8,
E4, V3, V5–V8 and the fresh workspace gate remain open.

The candidate adds Type operations to the compiler syntax module. The current
expression-focused specification's enumerated interface and tool manual do
not yet document this partial candidate. The complete CP-0034 language and tool
documentation update remains at V4 after V3; this partial record does not make
unimplemented forms current Ash.

**Awaiting:** Full S2 work remains. The bounded Type contribution and its
[partial issue record](https://github.com/dikini/ash-lang/issues/230#issuecomment-6771823209)
have independent retention and readback checks; this is not full S2 acceptance.

**Owner:** The developer owns the candidate, evidence and acceptance update;
independent QA and Sol own their checks, and the orchestrator owns retaining
integration and acceptance confirmation.

### Protected Pattern host retained contribution

**Delivered:** [PR #291](https://github.com/dikini/ash-lang/pull/291) retained
the bounded Pattern host contribution at
`ee54a766b18c0573af4fbd43baa4a45c3478d957`, tree
`e11df876d0765d287da6d6e69ff394be08325ca2`, on retaining base
`b1a93e041826991d8d2f0a8edde267696e4d8f52`. Source/test candidate
`1bc3eab32c01364aef0b759db308514c44253ee7` adds `pattern_syntax` and
`parse_pattern` to the existing checked host. Eligible flat Pattern,
Identifier and mixed Type/Pattern captures use invocation-owned Pattern handles
and the existing graph budget. Protected Pattern output uses the existing
staged projector; generated declaration-invocation arguments containing a
protected Pattern are refused before recapture.

Separate imported graphs generate an identity function from a caller Pattern
and from mixed Type/Pattern captures; both execute `42 : Int`. Further actual
graphs build a Pattern from Identifier-only or Type/Identifier captures and
execute 42. The capture observer checks the caller binder and read at their
distinct source spans. A 512 KiB real-source graph reaches identity 42 with 15
written groups, releases its final observed contents alias, and refuses 16
groups before capture. Constructed-host controls separately exercise issued
Pattern contents at retained 128, adjacent refusal, deep unwrap and reparse,
raw Pattern metadata and final alias release. A separate real graph records
transfer shortage, graph drain, root close and an injected teardown failure.

The fresh focused gate on `1bc3eab3` records 685 distinct passing tests and
2 existing ignores. Its receipt SHA-256 is
`7c36987ecf90c65c4029158cb212481f0b6bef8dc0446e2ed5cebd016882f450`, at
`evidence/pattern-host/final-gate-1bc3eab3/receipt.json` in the delivery
handoff. It covers the affected host, parser, staging and public regressions,
architecture, and the retained Type and G1 stack controls. Independent QA
audited the receipt, with audit SHA-256
`df1473704fe0987c632834e2c4e67c0ad16022e8eba1f261c25c30711b5ddf33`. The
unchanged strict I14 test separately fails 0/1 and is excluded from the
passing count.
Its caller location and category cause remain available; missing definition
origin presentation remains the
[#265 finding](https://github.com/dikini/ash-lang/issues/265#issuecomment-6766825789).
This candidate does not close I14 or any original #230 criterion.
The original fixed I01–I22 corpus remains unchanged. Full S2, used splices,
Expression and mixed/generated paths, full G1, original I16 derive/teardown/
build-image paths, D8, E4, V3, V5–V8 and the fresh workspace gate remain open.
The complete CP-0034 specification and tool update remains at V4 after V3.

**Awaiting:** The bounded Pattern contribution and its partial issue record
have independent retention and readback checks. Full S2 remains open.
**Owner:** The developer owns the candidate and acceptance record; independent
QA and Sol own their checks, and the orchestrator owns retaining integration
and acceptance confirmation.

### Protected Type to declarative expression retained contribution

**Delivered:** [PR #292](https://github.com/dikini/ash-lang/pull/292) retained
the bounded contribution at `bf145e287cf3217257cfafdee367637652ff40f5`,
tree `4b5baa26e1b3127902348ed7d7948c2908c31252`. The tested source candidate
`ffdbc313b7e1aa40856fab898f8719da766f6028` connects a captured Type in a
source declaration Template to an expression Template invocation generated
from it. The selected expression expansion borrows the existing graph syntax
budget. Repeated expression copies, their Type annotations, metadata and
projection buffers use that same budget. The guard continues to refuse the
protected bridge to an expression Transformer or through a nested expression
invocation. It does not introduce new host operations.

Separate imported keep and twice graphs execute `42 : Int`, including a
caller-side shadow of the selected imported expression syntax. A real graph
observes the caller Type capture and exercises the shared budget with a
pre-spent amount, exact allowance, one-short refusal and fresh retry. On a
512 KiB thread, the source graph with 121 nested Type groups executes 42; the
122-group graph reaches a structural-depth refusal after capture. Both release
the final observed contents alias. A separate constructed-owner component
covers its 128/129 retained-depth boundary; these are distinct observations.

The fresh focused gate on `ffdbc313` records 703 distinct passes and two
retained ignores. Receipt SHA-256
`e6adf0a8135c0373d667d9068b23c10d4f030ced844ccfb7e3e1eabfccdae744` is at
`evidence/type-expression/final-gate-ffdbc313/receipt.json` in the delivery
handoff. It includes the affected parser, staging, host and public suites,
architecture 47/47, and the retained 256 KiB and 512 KiB controls. Stack
children and marker reruns count once. Independent QA reconstructed the
result in audit
`d07ec8b8cb2a9efa3d71f368c11ab7c32ecda008e05d2f64b44d259ff678ed5b`.
The unchanged strict I14 test remains a separate failure at the missing
definition-origin presentation tracked in
[#265](https://github.com/dikini/ash-lang/issues/265#issuecomment-6766825789).
No original #230 criterion is closed by this candidate. The fixed I01–I22
corpus, broader S2/H1 and mixed consumers, used splices, full G1, I15 refresh,
original I16 derive/teardown/build-image paths, D8, E4, V3, V5–V8 and the
fresh workspace gate remain open. The complete CP-0034 specification and
tool documentation update remains at V4 after V3.

**Awaiting:** The bounded contribution and its partial issue record have
independent retention and readback checks. Full H1 remains open.

**Owner:** The developer owns the candidate and evidence; QA and Sol own
independent checks; the orchestrator owns retention and acceptance confirmation.

### Protected Expression host retained contribution

**Delivered:** [PR #293](https://github.com/dikini/ash-lang/pull/293) retained
this bounded contribution at `640b8311d99d3b7a5af34d7804632e130592ff80`,
tree `ca12a1349105646173113846c67679c9f8559ede`. Tested source candidate
`ce28168c9e2babc393734dc2558dbb557d1ecd21` extends the existing checked
declaration host to flat Expression, Type, Pattern and Identifier captures.
Expression capture, unwrap, parse and protected output share the existing
graph syntax budget. The existing guard refuses protected Expression nodes
in generated declaration and expression invocation arguments. Legacy None
accounting and the prior declarative Type-to-expression path stay distinct.

A real imported Expression graph and a mixed Expression/Type/Pattern/Identifier
graph each execute `42 : Int`. The mixed source observer checks the caller
binder and read as distinct spans with the same caller context; caller and
transformer definitions also contain a shadowed `value` name. A measured
real graph exercises a pre-spent budget, exact allowance, one-short refusal,
fresh retry and drained graph. The Expression one-short case reports the
existing projection resource failure; the Type control reports syntax failure.

On a 512 KiB thread, a real Expression source graph with 64 nested groups
executes 42 and releases its observed final contents alias; a separate graph
with 129 groups refuses structural depth. Those are chosen source controls,
not an adjacent source threshold. A synthetic checked-host component issues
42 nested wrappers, checks retained owner 128 and the adjacent 129 refusal,
unwrapping, future-owner preflight and final alias release. A separate
parser-built 124/125-layer Resume AST control uses a validated Some host with
a test-injected constructor to exercise intake, capture, unwrap and transfer
on the same stack. Both raw ASTs parse; the 124-layer protected copy succeeds
and the 125-layer future-owner copy refuses. Returned Expression location,
cause, capture flag and actual frame identity are checked on an issued result.
Category/EOF, foreign, stale and wrong-kind controls and initial, growth, spare,
short and retry arena checks are distinct component evidence.

The fresh focused gate on `ce28168c` records 713 distinct passes and two
retained ignores. Receipt SHA-256
`2f46a6a98a4f97b8be7ff5dc2161b5a185cde69fe2caba098e3d4febaa00b402` is at
`evidence/expression-host/final-gate-ce28168c/receipt.json` in the delivery
handoff. Architecture passed 47/47; child and marker reruns count once.
Independent QA reconstructed the result in audit
`1193a6d96caf496e7679af3070ee6daf5227b1c1309bc073194a0ac7975b50ef`.
Sol source and command-map review is
`073c318e450b4d0e1b8f73daa8892a0d4abd94d9af221b7d7865caf5630a488c`.
At this test pin strict I14 failed separately because definition-origin
presentation was missing, as recorded in
[#265](https://github.com/dikini/ash-lang/issues/265#issuecomment-6766825789).
The diagnostic candidate below addresses that presentation gap. The fixed
I01–I22 corpus remains unchanged. Full S2/H1, used splices,
repeated and generated consumers, full G1, original I16 derive/teardown/
build-image paths, D8, E4, V3, V5–V8 and the fresh workspace gate remain
open. The complete CP-0034 specification and tool documentation update
remains at V4 after V3. No original #230 criterion is closed by this candidate.

**Awaiting:** The bounded Expression contribution and its
[partial issue record](https://github.com/dikini/ash-lang/issues/230#issuecomment-6780442850)
have independent retention and readback checks. Full S2 remains open.

**Owner:** The developer owns the candidate and evidence; QA and Sol own
independent checks; the orchestrator owns retention and acceptance confirmation.

### Retained diagnostic origin delivery

**Delivered:** The existing reviewed diagnostic change for
[#265](https://github.com/dikini/ash-lang/issues/265),
[#272](https://github.com/dikini/ash-lang/issues/272) and
[#274](https://github.com/dikini/ash-lang/issues/274) is adopted unchanged at
`6458c4ee32c010e73103b787d3113aa06a478ee2`, on retaining base
`640b8311d99d3b7a5af34d7804632e130592ff80`. Parse presentation includes actual
invocation and selected-definition locations. Duplicate-name diagnostics carry
the real location for each name while preserving existing label spans and
resolution behavior. The shared presenter retains source origins that differ
from their label spans.

The fresh focused gate records 175 distinct passes and no ignores. It includes
the strict I14 test, fixed I14/I15 human and JSON origin assertions, H2/H3
duplicate conflicts and handwritten controls, structured duplicate locations,
and the current Expression-host tests. Two early suites and the Bulgarian
parent-locale rerun are excluded from the distinct count. The locale rerun
uses English diagnostic output. All-target and diff checks passed; C.UTF-8 and
Bulgarian before/after input snapshots match. The
receipt SHA-256 is
`d01666c3e7a85d6d866436407fda25eb6aa17cf5db14bf84d8c275721febf35b`, at
`evidence/downstream-diagnostics/focused-6458c4ee/receipt.json` in the handoff.
Independent QA cleared the receipt in audit
`9deab82714baed7ab02d5503493cd42ff8bc0ddbf59f1eced6f861d07072b2a4`.
[PR #294](https://github.com/dikini/ash-lang/pull/294) retained the reviewed
change at `04d0d957213c32fc90ec838866f91ae3c6ccd9bf`. All three original
diagnostic issues were closed after independent acceptance readback.

**Remaining:** The full TASK-0068 verification and the original H2/H3 and
issue #230 criteria remain open.

**Awaiting:** No further acceptance is pending for #265, #272 or #274.

**Owner:** The developer owns the candidate and records; independent QA and Sol
own their checks; the orchestrator owns integration and acceptance confirmation.

### Retained D8 checkpoint

**Delivered:** [PR #295](https://github.com/dikini/ash-lang/pull/295) retained
the reviewed D8 tree as `ac3a70d3bd2e24fd316d7bee3b98c08458ccdee1`. The
unchanged seven-stage fresh workspace verification completed at candidate
`bd1ae6f9395e0f83fc76fb4fb51aac2ca6d1465c`; the retained tree was identical.
The human and JSON I15 checks were refreshed against that candidate's actual
binary. Independent QA and review checked the gate, named cases and retained
result. All five original D8 criteria were accepted and
[issue #232](https://github.com/dikini/ash-lang/issues/232) was closed after
independent readback.

**Remaining:** E4 and the later full corpus, integration and final acceptance
remain open. The D8 checkpoint does not close the original H1/H2/H3 criteria.

**Awaiting:** No further D8 acceptance is pending. E4 is the next fresh
workspace checkpoint.

**Owner:** The developer owns the next implementation and evidence; independent
QA and review own their checks; the orchestrator owns retention and acceptance.

### Retained equational-origin repair

**Delivered:** The separately authorized
[PR #297](https://github.com/dikini/ash-lang/pull/297) retained
`ded4a06f3810d67884f0e9ec3af4441169aed768` for
[issue #296](https://github.com/dikini/ash-lang/issues/296). Its existing
expansion origin preserves the actual caller and protected-expression sources
for the affected cross-source equation. Same-source origins, ordinary checking
and Core validation remain unchanged. Focused controls passed and independent
review confirmed the retained result and completed issue readback.

**Remaining:** The quote and escape implementation and E4 acceptance are
separate. A local combination produced `44 : Int` on the unchanged early nested
fixture and `42 : Int` on the I17 dependency control; the full E4 criteria and
fresh workspace checkpoint remain open.

**Awaiting:** No further #296 acceptance is pending.

**Owner:** The developer owns the quote and escape continuation; the
orchestrator owns integration and acceptance.

### Connected quote and escape candidate

**Delivered in the candidate:** Checked ordinary helpers can construct
expression fragments using quotes and holes, and declaration templates can
evaluate an escaped expression or block. The unchanged early nested case
returns `44 : Int`, the fixed I17 helper slice crosses an ordinary dependency,
and the fixed quote token roundtrip and its handwritten control return
`42 : Int`. The existing identity observation checks the returned token and
group structure, the captured identifier's context and source origin, and the
actual capture-owned quote call. A reached ordinary quotation without the
compile-time host refuses before publishing its internal representation.
Focused controls cover ordinary type failures, output admission, the shared
syntax budget and the atomic failure's lack of module publication.

**Remaining:** Direct forwarding of a protected quoted expression is not yet
implemented. The separate unknown outer-splice diagnostic in
[#263](https://github.com/dikini/ash-lang/issues/263), the complete E1 and E2
criteria, the full generator and repetition graphs, and later integrated and
final checks remain open. E4 acceptance is pending its own focused review,
fresh workspace checkpoint, retention and checked issue readback.

**Awaiting:** Independent review and QA of this candidate, the E4 checkpoint,
retaining integration and acceptance readback.

**Owner:** The developer owns source and evidence; QA and independent review
own their checks; the orchestrator owns retention and acceptance confirmation.

**Remaining:** Complete protected-fragment accounting/consumption, declaration
captures, repetition, host transfer and procedural declarations, quotes/escapes,
derives, generators, publication handoffs, full corpus/diagnostics,
specification/tool documentation and integrated acceptance. D3's full I19
criterion awaits D5/G1; D6's procedural-output import refusal awaits S3/S4.
Prior partial H1/H2/H3 tests do not close their original criteria. The fresh
D8 checkpoint is retained; E4, V3 and the final gate remain open.

**Awaiting:** Each further delivery requires independent QA, Sol PR review,
retained-result verification and acceptance readback. Keep every
incomplete original criterion unchecked with Delivered/Remaining/Awaiting/Owner
and its PR, commit and evidence. The next fresh full checkpoint is E4; V3 joins
the complete public path and V7 supplies the final fresh full gate before V8
retaining acceptance.

**Owner:** The orchestrator assigns the next eligible delivery and integration;
the developer owns product changes, builds, repairs and acceptance updates;
independent QA and Sol own their respective checks. The orchestrator tracks
these separate downstream issues:
[#263](https://github.com/dikini/ash-lang/issues/263),
[#265](https://github.com/dikini/ash-lang/issues/265),
[#272](https://github.com/dikini/ash-lang/issues/272),
[#274](https://github.com/dikini/ash-lang/issues/274) and
[#277](https://github.com/dikini/ash-lang/issues/277), plus the separate
introduced generic-binder issue [#301](https://github.com/dikini/ash-lang/issues/301).
The diagnostic-origin deliveries above closed #263, #265, #272, #274 and #287
after retained evidence and independent readback. Dependent original criteria
remain open. Verify live issue status before reporting progress.

The plan preserves the fixed inputs, supplemental early cases and original full
graphs. Component or handwritten-control results do not replace their connected
assertions. Its forecast includes the full remaining chain and separately names
the unresolved downstream wait; a bounded completion ETA is not established.

## Verification

- [ ] Exercise I01–I22, including their fixed positive, negative, mutation,
      hygiene, origin and diagnostic cases, through the specified component
      and connected paths. Preserve the supplemental early cases and the full
      original integration graphs.
- [ ] Run the retained slice 1 regression cases; exercise the real macro
      library, caller and importer through the public driver, interpreter and
      supported build/image path. Verify existing host bounds, transfer and
      teardown, and I16's specified independent validator and handle controls.
- [ ] Update implementation, tests, specification and tool documentation
      together. Check that accepted but unimplemented behavior is not reported
      as current Ash before it is retained.
- [ ] Obtain independent QA and review on the pinned integrated candidate;
      repair and re-review findings. Run the agreed fresh full gate and retain
      its receipts for the exact inputs.
- [ ] Integrate to the authorized retaining branch, verify retained evidence
      and complete independent acceptance readback. Main integration remains a
      separate gate under the project workflow.

## Discoveries

The S2 broad expression-admission proposal would route both host
`parse_expression` and driver post-host expression admission from their current
fresh allowances through the remaining shared syntax budget and add adapter and
projection preflight. That changes possible legacy allowance consumption and
error ordering; shared accounting alone does not establish slice 1 preservation.
The reviewed finding is in
`/home/dikini/Projects/ash-lang/.worktrees/task-0068-handoff/evidence/host-consumer-plan/s2-admission-3dc4376.md`
(SHA-256 `801df2a0c32307afab3e867786f70ea78cb321d73bad1da5de23095be3013aaf`).

The narrow S2/S4 plan supersedes that broad route for the first Declaration
slice. It proposes a source Declaration capture through the existing host and
staging path while leaving both legacy expression callers and their allowances
intact. The reviewed interfaces compiled at `8e1d1a8a`; the later first-path
candidate was retained by PR #286 as recorded above. The original plan is
`/home/dikini/Projects/ash-lang/.worktrees/task-0068-handoff/evidence/host-consumer-plan/s2-s4-narrow-c4548296.md`
(SHA-256 `70907e327c3c50f6232916149c99694efd70c1fec2363f208fa8c99206782da0`).
It changes no original DAG edge, criterion or difficulty and does not establish
full S2 or S4 acceptance.

The reviewed draft includes isolated early host, quotation and hygiene cases so
those focused checks do not depend on unrelated definitions in the full corpus.
The original full-module graphs remain required integration evidence.

The preserved `/home/dikini/Projects/ash-lang-task-0068` worktree remains at the
verified base on `codex/task-0068-protected`, with the inspected untracked
`tests/declaration_type_capture.rs` preserved. Its hash and existing type-first
working evidence are recorded in the plan. The retaining path uses the
existing syntax budget for the reviewed direct expression/pattern consumers.
The local first source Declaration path is recorded above; unaccounted
protected, mixed and generated consumers remain guarded.

The plan names the
[protected type-to-expression accounting and release gate](../design/macros/slice2-delivery-plan.md#protected-type-to-expression-accounting-and-release-gate).
It requires separate independent review. The retained Type delivery established
the narrow refusal for protected types in generated expression-macro invocation
arguments, then activated its accounted Type path. The retaining branch at
`3613a863` still guarded Expression and Pattern declaration captures; PR #282
subsequently connected the direct-template lane with shared accounting.
Keep the Type-to-expression refusal and guards on unaccounted consumers.
Required real imported
consumer, repeated-copy, exact/short allowance, depth, late-failure,
small-stack/drop/cleanup and slice 1 regression evidence cannot be replaced by
an isolated projector check. If that connection cannot preserve language and
slice 1 behavior, stop it and return the concrete finding for a decision.

The expression/pattern inventory found that raw pattern projection can repeat
origin walks and frame comparisons for grouped wrappers, including diagnostics
later discarded by projection. Account for the operations actually performed
before activating that path, or review a narrow removal of the redundant work.

The separate local D5 candidate `273b5ec012254d5bdb06f6db4e4f8f104193207a`
passed 298 focused checks. A 512 KiB construction overflow was localized and
repaired with a precharged iterative packet builder; its packet control reaches
depth 128 and refuses 129 before construction. An earlier 297-pass, one-failure
gate exposed three missing ownership inventory fields; the candidate records
their repair without changing scanner rules. These receipts apply to that local
candidate, not an integrated tree. Full D5 and I19 remain open.

## Deviations

On 2026-11-09, the user accepted one inline result-expression alternative for
escapes; PR #281 retained the explicit CP-0034 amendment. It does not add inline
outer local declarations or change ordinary block grammar. Quote and escape
implementation and their specification update remain open; this decision is not
current Ash. The resource and diagnostic findings above preserve the reviewed
boundaries and original criteria. Return other semantic gaps to CP-0034 or
design work; retain separately owned downstream repairs outside macro machinery.
Preserve main's unrelated effects work. Main integration remains outside this
task's current permission.
