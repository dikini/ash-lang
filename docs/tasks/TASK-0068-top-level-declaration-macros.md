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
commit is `3613a863a7a2870b0906fd20925bd641d0598ea2`, tree
`7c5c3802e0793e5fe396be68abcfc9e388e40189`. Recheck refs and worker ownership
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

For the original I15 `type_error.ash`, a fresh human and JSON driver readback
at `9e89ac12` reports the ordinary expected-Int/found-Bool cause with the
generated body, invocation and definition locations. The selected name is
traceable within the invocation source; no separate name-specific label is
claimed. The [D8 record](https://github.com/dikini/ash-lang/issues/232#issuecomment-6744362138)
links the bounded readback; its receipt SHA-256 is
`24245017679e2f8d417036813d6b10cfa88331f4046bf7ded4b081737a63cdf5`.
Independent QA and Sol checked these focused deliveries and readbacks; the
orchestrator confirmed them. Their original issue criteria remain unchecked.

### Local expression and pattern candidate

**Delivered in the local candidate:** The unretained candidate for
[D3 #218](https://github.com/dikini/ash-lang/issues/218),
[D4 #222](https://github.com/dikini/ash-lang/issues/222),
[D6 #219](https://github.com/dikini/ash-lang/issues/219) and
[H3 #229](https://github.com/dikini/ash-lang/issues/229) is
`f2ff93084c2f064695eb2b1faa2522725d8aabf8`, tree
`0d8c6c7bd710dcf68f5df371dad2b4850504bbff`. It connects protected expression
and pattern captures through direct declaration templates, using the existing
shared syntax budget for capture, substitution, staging and projection. D6
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
This TASK-only record carries that evidence from `f2ff9308`: product source,
tests, specification, tool configuration and fixed corpus inputs are unchanged.
The focused gate was run on `f2ff9308`, not rerun on this record commit.
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

**Awaiting:** Independent QA and Sol have cleared the focused source and
receipt. Independent checks of this record are pending. The candidate still
needs a published PR, independent PR review, verified retention and partial
issue-record readback. Full D8, E4, V3 and V7 gates remain open.

**Owner:** The developer owns this candidate, its evidence and the eventual
partial issue records. Independent QA and Sol own their checks; the orchestrator
owns publication, retaining integration and acceptance confirmation. Main is
a separate integration boundary.

**Remaining:** Complete protected-fragment accounting/consumption, declaration
captures, repetition, host transfer and procedural declarations, quotes/escapes,
derives, generators, publication handoffs, full corpus/diagnostics,
specification/tool documentation and integrated acceptance. D3's full I19
criterion awaits D5/G1; D6's procedural-output import refusal awaits S3/S4.
Prior partial H1/H2/H3 tests do not close their original criteria. No TASK-0068
fresh full-workspace receipt or completed D8/E4/V3/final gate is established.

**Awaiting:** Retain the independently reviewed expression/pattern candidate
before treating its direct-template lane as delivered on the retaining branch.
Each delivery also requires independent QA, Sol PR review, retained-result
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
working evidence are recorded in the plan. Resume using the existing syntax
budget/shared accounting; keep expression/pattern/procedural activation guarded
until their required accounting and consumers are independently verified.

The plan names the
[protected type-to-expression accounting and release gate](../design/macros/slice2-delivery-plan.md#protected-type-to-expression-accounting-and-release-gate).
It requires separate independent review. The retained Type delivery established
the narrow refusal for protected types in generated expression-macro invocation
arguments, then activated its accounted Type path. The retaining branch at
`3613a863` still guards Expression and Pattern declaration captures; the local
candidate above connects the direct-template lane with shared accounting.
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
