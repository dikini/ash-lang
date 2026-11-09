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
checks are recorded in the delivery plan. On 2026-11-09, the verified retaining
commit is `3dc43762930eda907e6a75c6d78123019833f5c6`, tree
`854af3aa615906f56ee905ba32951dfaec72d902`. Recheck refs and worker ownership
before dispatch. The plan records the earlier retained squash commits, their
partial criteria and the remaining producer/consumer interfaces.

The reviewed work structure is filed under [issue #206](https://github.com/dikini/ash-lang/issues/206)
as seven workstreams and 45 child issues. All 112 native blocking links still
match the reviewed graph. D1 #214 and S1 #215 are closed; 43 child issues remain
open. The user has authorized delivery and squash merges into the retaining
branch; Main remains separate.

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
D1/S1 account for seven fully closed predicted points; the 43 open units total
135 original points and include retained partial work. These figures do not
measure remaining effort or grant partial acceptance credit.

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

### Local quote and escape parser candidate

**Delivered in the local candidate:** The parser-only E1 candidate for
[#226](https://github.com/dikini/ash-lang/issues/226) is
`74f5e024faf67db185ba97f3c75f00cd9aa93c58`, tree
`b669b3b00a537cdb4bd955d15249e712e23dddad`, based on retained `3dc43762`.
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
public driver. The `unbound_outer.ash` component preserves the outer splice;
its required definition-time rejection remains open.

The focused receipt at
`/home/dikini/Projects/ash-lang/.worktrees/task-0068-handoff/evidence/e1-final-74f5/receipt.json`
has SHA-256
`b442345aff25ce4dc1d169b9bbef63efa0300ed5484540e2f4efbd87f3fc43d7`.
It records 465 distinct passing tests and two retained ignores: the #277
nominal-context case and a valid nonempty declaration-template positive. The
source and structured quote controls cover exact/short/retry work and composed
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

**Awaiting:** Independent TASK-record checks, PR review, verified retention and
the partial #226 issue record. D8, E4, V3, V7 and the fresh full-workspace gate
remain open.

**Owner:** The developer owns the candidate, evidence and acceptance record.
Independent QA and Sol own their checks; the orchestrator owns publication,
retaining integration and acceptance confirmation.

**Remaining:** Complete protected-fragment accounting/consumption, declaration
captures, repetition, host transfer and procedural declarations, quotes/escapes,
derives, generators, publication handoffs, full corpus/diagnostics,
specification/tool documentation and integrated acceptance. D3's full I19
criterion awaits D5/G1; D6's procedural-output import refusal awaits S3/S4.
Prior partial H1/H2/H3 tests do not close their original criteria. No TASK-0068
fresh full-workspace receipt or completed D8/E4/V3/final gate is established.

**Awaiting:** Retain the independently reviewed E1 parser candidate before
treating its source changes as delivered on the retaining branch. Each delivery
also requires independent QA, Sol PR review, retained-result
verification and acceptance readback. Keep every
incomplete original criterion unchecked with Delivered/Remaining/Awaiting/Owner
and its PR, commit and evidence. The next fresh full checkpoint is D8, after the
first declaration path, integrated H2/H3 and protected-copy/composed-depth gates
are ready; E4 is the second checkpoint, V3 joins the complete public path and
V7 supplies the final fresh full gate before V8 retaining acceptance.

**Owner:** The orchestrator assigns the next eligible delivery and integration;
the developer owns product changes, builds, repairs and acceptance updates;
independent QA and Sol own their respective checks. The orchestrator tracks
these separate downstream issues:
[#263](https://github.com/dikini/ash-lang/issues/263),
[#265](https://github.com/dikini/ash-lang/issues/265),
[#272](https://github.com/dikini/ash-lang/issues/272) and
[#274](https://github.com/dikini/ash-lang/issues/274) and
[#277](https://github.com/dikini/ash-lang/issues/277). All were open and unassigned
at inspection; active repair owners and timing are unverified. Verify live
owner/status before reporting further progress. Dependent criteria remain
blocked, and repairs stay outside this task; continue independent authorized
work without patching those consumers.

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

The reviewed draft includes isolated early host, quotation and hygiene cases so
those focused checks do not depend on unrelated definitions in the full corpus.
The original full-module graphs remain required integration evidence.

The preserved `/home/dikini/Projects/ash-lang-task-0068` worktree remains at the
verified base on `codex/task-0068-protected`, with the inspected untracked
`tests/declaration_type_capture.rs` preserved. Its hash and existing type-first
working evidence are recorded in the plan. The retaining path uses the
existing syntax budget for the reviewed direct expression/pattern consumers;
unaccounted consumers and procedural declaration execution remain guarded.

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
