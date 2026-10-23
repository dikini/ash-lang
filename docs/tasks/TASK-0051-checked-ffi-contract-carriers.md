# TASK-0051: Checked FFI Contract Carriers

- ID: `TASK-0051`
- Status: active
- Related: [F3 issue #59](https://github.com/dikini/ash-lang/issues/59),
  [CP-0024](../proposals/CP-0024-checked-foreign-host-profile.md),
  [TASK-0050](TASK-0050-checked-ffi-regions-control-program.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md)

> This task organizes F3 delivery under accepted CP-0024. It does not define
> Ash semantics or accept a Linux executor architecture.

## Dependencies

The user authorized autonomous recommended choices, unsigned commits and a
separate worktree on 2026-10-21. The orchestrator adopted independently reviewed
CP-0024 under that delegation and assigned the developer as product writer,
build operator, integrator and acceptance owner. The reviewer checks exact
candidate heads; the orchestrator confirms acceptance updates.

Work starts on `codex/checked-ffi-core` in `.worktree/checked-ffi`, based on Main
`7949b6d9136b0152ee9104e67bd0451cb9db4727`. Preparation commit `1cf1014` retains
the accepted proposal and reconciled planning context. Main and the milestone
retaining branch have separate integration gates. The original planning checkout
and unrelated work remain intact.

The later user instruction changes future PR integration to GitHub
squash-and-merge, with a GitHub merge commit when squash is unavailable. Local
commits remain unsigned; GitHub's merge signing behavior follows that chosen
method. Fetch and synchronize local/origin retaining refs after integration.
Earlier local squash receipts remain historical evidence and are not rewritten.

F3 is independent of Linux deployment realization. F2's actual controls and
accepted architecture gate F6/F7; no carrier, flag or unsupported path may bypass
that gate. The [program plan](plans/checked-ffi-regions-control.md) owns the whole
milestone acceptance map and F-core checkpoint scheduling.

## Work

Follow the [task-owned implementation plan](plans/checked-ffi-contract-carriers.md).

1. Parse and retain the explicit checked library boundary without turning a
   checked marker into executable permission. Preserve legacy source behavior.
2. Carry original assumption identities and exact selected H through source
   declarations, complete Type/Row vectors, checked ownership and wrapper facts.
   Implement the authenticated host expression and exact effect subtraction.
3. Preserve complete contract facts through body-free exports, re-exports,
   linking, specialization and Core transformations. Reject hidden dependency,
   assumption or host-effect erasure and wrong-host use.
4. Reconstruct checked facts independently in Core/private image admission;
   never trust surface markers, constructor shape, matching hashes or stale
   projections. Unsupported/incomplete paths fail without partial permission.
5. Update specification sections with each retained implemented subset, preserving
   the distinction between accepted CP-0024 and current Main semantics. Leave
   whole-task acceptance unchecked until all original F3 obligations pass.

## Progress

Issue [#114](https://github.com/dikini/ash-lang/issues/114) tracks a separate
current-specification correctness defect discovered during PR110 review. Mixed
pure, explicitly empty-effectful and nonempty-effectful function arguments can
form a comparison cycle. A genuine test-only baseline on retained `a2f1c938`
passes the raw-representation and pure/empty equality/hash prerequisites, then
fails when normalizing the same effect row twice. Later permutation and
duplicate assertions were not reached. This violates the existing unordered,
idempotent row rule; it requires no new language proposal.

The repair compares every function representation through its existing semantic
view, in domain, result-value and latent-row order. The iterative paid work queue
defers the latent-row distinction until the earlier components have been
compared. Full Type/Row arguments and independent Core admission remain
unchanged. The final batch passed 341 distinct selected units across 351 outer
test occurrences and Clippy with warnings denied. These include raw comparison
laws, work/storage/deep controls, affected type/Core/private-image cases and all
three unchanged default startup controls (327335, 320427 and 324976 against
327680). Three older exact-work expectations now explicitly account for existing
reserved-source scans and empty-table scalar authentication; fresh independent
phase measurements and exact/short/retry controls pass. The
[reconstructible evidence](evidence/effect-row-comparator/README.md) preserves the
baseline red, partial failures, corrected attribution and final frozen results.
Independent delivery review and retention remain required. This separate fix
does not accept the pending PR110 dependency images or any whole-F3 criterion;
the connected F-core gate remains scheduled by PM and run by the developer.

- [x] Explicit checked declaration boundary and safe incomplete-path refusal.
- [ ] Original assumptions, exact H and source/wrapper dependency carriers.
- [ ] Host introduction/elimination and checked owner effect correspondence.
- [ ] Body-free module/link/specialization correspondence and negatives.
- [ ] Independent Core/image reconstruction and transformed-contract tests.
- [ ] Charged checking work, exact/one-short bounds and affected regressions.
- [ ] Independent review and retained verification of complete F3 scope.

PR [#83](https://github.com/dikini/ash-lang/pull/83) retains the first slice at
`0c220ea2a0b16afa21977380173d9fc39b4ee1ba` on the milestone branch after independent
exact-head review of `196ef7f1a6bd256796ff3d802970e3b9630bf6b7`. Source equality
with the combined F2/F3 retained tree was verified before synchronizing the clean
product checkout; all 1,791 file contents/modes matched and no working bytes changed.
The subset passes 35 focused tests,
targeted library/test Clippy, formatting, changed Markdown lint and source
whitespace checks. Captured Cargo logs preserve their exact EOF blank line and
are excluded from that whitespace claim.
The [verification receipt](evidence/checked-ffi-marker/verification.json) records
source/configuration hashes, compiler/cache settings and the observed red cases.
[Raw review reproduction](evidence/checked-ffi-marker/review-reproduction.json)
retains exact final test/Clippy outputs and before/after pin equality.
The author applied/read back the partial acceptance in
[F3 issue #59](https://github.com/dikini/ash-lang/issues/59); whole-issue boxes remain
unchecked. Reviewer audited the live partial acceptance update; the orchestrator confirmed advancement.
Remaining: assumptions/H, host scopes, module/Core/image carriers and complete F3
acceptance. Owner: developer supplies/retains the candidate and updates acceptance;
reviewer checks the exact head; orchestrator confirms advancement.

The next candidate extends the same canonical prepared library with original
assumption-member coordinates, exact H selections and automatic role-linked
native premises. Its explicit authoring preparation API grants no resolved binding
or execution permission. Library-local assumption names publish no ordinary
binder. Legacy symbol/owner binding and private reconstruction cannot erase the
checked projection. The candidate passes 51 focused tests (6 profile unit, 1 resolver collision and
44 integration/regression cases), targeted Clippy and formatting. The
[raw verification receipt](evidence/checked-ffi-contracts/verification.json) retains
exact commands, logs and unchanged source/configuration pins. Independent review cleared head `e90b0b81f06f1811e5f740c7889169e758087551`;
[PR #84](https://github.com/dikini/ash-lang/pull/84) retained its exact tree at
unsigned `f7f13071851a4abfdd344f0bb5a1d5b99a2fbb1f`. The author applied/read back
the issue #59 partial acceptance; reviewer audited it and the orchestrator
confirmed advancement. No additional whole-task criterion is accepted. The
owned plan records the next connected static scalar-host checkpoint.

The first slice is deliberately incomplete: it retains the checked marker and
refuses legacy ABI preparation for that declaration. It grants no checked
execution, assumption discharge, host authority or milestone acceptance.

The third candidate introduces an explicit static checked-profile resolver,
contextual lexical hosts and appended canonical checked builtin codecs. Source
and linked Core checks cover scalar native/host correspondence, lexical escape,
transforms, independent role reconstruction and sealed-handler/mode mutations.
Legacy image compatibility admits only exact inert builtin metadata; actual
checked hosts still refuse runtime and image admission. The subset passes 46 focused tests, including legacy owner regressions and an
actual generated legacy build/run, plus targeted Clippy. The
[verification receipt](evidence/checked-ffi-hosts/verification.json) and
[capture notes](evidence/checked-ffi-hosts/README.md) retain final source/configuration
pins, raw logs and the two diagnosed compatibility repairs. Independent review cleared head `f19c55d835ba95b1cfc2051acbf4f0e29a696d73`;
[PR #85](https://github.com/dikini/ash-lang/pull/85) was GitHub squash-merged at
`bdae57436e33158c931b740886f05ad335b98106`, preserving its exact reviewed tree.
The author read back GitHub merged state, matching local/origin refs and a clean
worktree. Reviewer audited actual retention and the issue #59 partial acceptance;
the orchestrator confirmed advancement. These observations accept no additional
whole-task criterion and supply no checked native execution or Linux containment
evidence.

The next wrapper slice starts from the GitHub-retained scalar checkpoint on
`codex/checked-ffi-f3-wrappers`. Its early draft publishes the owned plan before
product work. Delivered and remaining criteria stay separate: scalar host/Core
correspondence is retained; checked owner lifecycle correspondence and complete
wrapper/module/image obligations remain open.

The first wrapper controls pass imported generic and closed generic wrapper
source/Core checking. They expose a body-free admission gap: a default-profile
consumer accepts the outward-pure closed wrapper. The [initial red receipt](evidence/checked-ffi-wrappers/README.md)
records two passes and this expected failure before product changes. The draft
remains incomplete. The first guard repair now passes all three controls by
requiring explicit profile from authenticated retained contracts, independently
of the outward row. Subsequent controls cover aliases/re-exports, opaque access,
branches, recursion and returned functions through independent Core. A private
capture-erasure probe exposes missing defining-global correspondence. Checkpoint
`1c70442` retains the repair: immutable completed global publications shared
through imports, projection authentication, and iterative final-owner teardown.
Seven private controls pass for that checkpoint, including donor/stale originals,
coordinated erasure, alias/import identity, prefixed work bounds and deep teardown.
The final wrapper candidate passes 181 distinct focused tests, including distinct
nonempty row actuals, exact two-contract/assumption union, body-free default-profile
refusal, publication/source/table erasure controls, deep teardown and affected
legacy regressions. The generated legacy build/run and targeted Clippy pass on
the same final source/configuration manifest. The
[verification receipt](evidence/checked-ffi-wrappers/verification.json) retains
all commands, raw logs and pins. Independent review cleared head `2a99cd3`;
[PR #86](https://github.com/dikini/ash-lang/pull/86) was GitHub squash-retained at
`83d050b40c92572b98b2d337f04126311373cd22` with its exact reviewed tree. The author
read back partial issue #59 acceptance, reviewer audited actual retention and PM
confirmed advancement. No additional whole-task criterion was accepted.
Selected-evidence carrier/anti-erasure coverage, complete nominal/resource
closure erasure, checked owners and primitive/image/runtime obligations remain
outside this partial delivery; their original criteria stay unchecked.

The selected checkpoint started from retained `284e604` on
`codex/checked-ffi-f3-selected-evidence`. Its
[owned plan](plans/checked-ffi-contract-carriers.md#selected-ordinary-implementation-method-checkpoint)
first establishes body-free module-level selected-method/prerequisite controls,
then tests capture/table erasure against canonical completed facts. It covers
exact original owner/head/actuals/assumption union, aliases/opaque/re-export routes,
independent Core transforms and paid work. Implementation follows demonstrated
failures; nominal/resource closure, owners/copy/runtime/image and whole F3 remain
pending. The early draft publishes this plan before long implementation. The
[first retained controls](evidence/checked-ffi-selected/README.md) pass direct
module-level selection and a generic prerequisite chain through independent
Core. They expose accepted capture/table erasure in a canonical selected summary
and a source-order-dependent host registry refusal. Checkpoint `458d848`
repairs the two summary erasures with completed implementation publications and
passes four actual-host ordering controls. Its later checker-boundary mutation
still exposes acceptance after an imported original is erased following real
resolution. The next frozen batch authenticates imported originals before
checker use, preserves bounded prerequisite provenance, and adds selected
method union, opaque/re-export, complete native row and independent Core controls.
The final [verification receipt](evidence/checked-ffi-selected/verification.json)
retains 473 distinct passing focused tests, including 15 selected private/Core
controls, 58 implementation regressions, 86 integrations and targeted Clippy.
The imported selection is explicitly 33/34: its one default-startup failure also
occurred at the exact retained base; that historical failure was later repaired under issue #91. A paid lazy
host census preserves the ordinary no-host ordering tariff; it grants no host
permission. Independent review cleared `9ad7ce15`; GitHub squash-retained
[PR #89](https://github.com/dikini/ash-lang/pull/89) at
`a301a654bff2b7caed4befc32ce038abcf85dd7e` with its exact reviewed tree. The
author read back partial issue #59 acceptance, reviewer audited actual retention
and the orchestrator confirmed advancement. No whole-task criterion is accepted.

The selected checkpoint's affected regression selection historically reproduced
an imported native-buffer default-startup failure, followed by a dependent-discard
failure. [Issue #91](https://github.com/dikini/ash-lang/issues/91) is now closed:
PRs [#92](https://github.com/dikini/ash-lang/pull/92) and
[#93](https://github.com/dikini/ash-lang/pull/93) retained the fixes through
`036c366834c839e4f0a503cf63e9db46448bb486`. Author acceptance, independent retained
review and PM confirmation are complete. Both unchanged-default startup cases,
image 16/16, 117 focused tests and Clippy passed. The completed
[historical TASK-0052](https://github.com/dikini/ash-lang/blob/036c366834c839e4f0a503cf63e9db46448bb486/docs/tasks/TASK-0052-source-resource-default-startup-budget.md)
is retired at this documentation checkpoint; its durable evidence remains.
The PR #89 imported result stays labelled historical 33/34. Whole F3 and F-core
remain pending.

PR #94 retained `2d04de76463febaaf36e082e7bccd8f6e85dc26b` with exact reviewed
tree equality. The author partial readback, independent retained-result audit and
[PM confirmation](https://github.com/dikini/ash-lang/issues/59#issuecomment-6318443119)
are complete. Capture-root nominal-kind membership, selected parity and the
assigned TASK-0052 retirement/link cleanup are delivered; whole F3 remains open.

The [constructor-payload checkpoint](plans/checked-ffi-contract-carriers.md#constructor-payload-declaration-closure-checkpoint)
starts from that retained commit on `codex/checked-ffi-constructor-closure`.
Its actual Leaf/Envelope payload-only control passes source, summary, body-free
consumer, linking, independent Core and identity/fold checks. Missing hidden
Leaf already rejected; coherent Donor substitution exposed summary and
checker-admission gaps. The repair retains the existing defining registry on
constructor projections and forwards it unchanged, with paid exact owner,
formals, effective payload, scheme and origin checks. A latent-row mirror guard
preserves exactness while avoiding duplicate summary traversal. The final
[evidence](evidence/checked-constructor-closure/README.md#final-delivery-verification)
records 331 distinct passes and Clippy on uniform inputs, image 16/16 and both
unchanged-default startup cases. Independent review, integration and partial
acceptance are pending; broader declaration/resource graphs and whole F3 remain
open.

## Verification

Use one Cargo job and reuse compatible artifacts from the existing product cache
through explicit `CARGO_TARGET_DIR`; preserve the old product source checkout.
Each slice records exact commands, outcomes, candidate/retaining commits and
review findings. Add behavior/negative tests before changing product code.

The first slice ran `foreign_source_syntax`, `foreign_source_contracts` and
`foreign_source_admission`, plus formatting and affected lint/doc checks. Later
slices add imported/opaque/re-exported full Type/Row substitutions, forged
independence, hidden captures, host-effect erasure, wrong-host/stale sessions,
transformed contracts and exhausted reconstruction. Requirements come from
CP-0024 and the [63-row map](../design/foreign-authoring/checked-ffi-evidence-map.md),
not accidental test behavior.

F3 criterion-wide acceptance remains pending until all its obligations pass.
The next full workspace gate is F-core after F3/F4/F6 connect to a real generated
host. The orchestrator schedules it; this developer serializes heavy builds.
F2 acceptance remains required for F6. No old full-gate receipt is a fresh pass.

## Discoveries

The baseline already has phase-specific checked foreign contracts, generated
bridges, source owner/window provenance and independent Core/image checks.
Extend these canonical carriers rather than building a parallel metadata system.
Its `checked_source` module name denotes existing validation, not the new checked
execution profile. The current parser recognizes contextual `foreign library`;
`checked` must remain contextual and preserve legacy declaration recognition.

The initial PR #94 data-only Held fixture parsed and checked after a constructor
pattern correction, but its actual callable inventory contained no Held type
edge. This is rejected fixture evidence, not an observed product defect. The
revised control passes Held through an ABI-unused native Type actual in the
existing generic closed wrapper. The [test-first checkpoint](evidence/checked-nominal-closure/README.md)
passes the actual capture/hidden-kind and unrelated Spare controls plus body-free
consumer, linking, independent Core and identity/fold revalidation. Coherent
required Held hidden-row erasure still authenticates successfully, exposing a
summary-admission gap. The corrected graph walk now uses paid exact membership in that summary's
existing authenticated kind environment, including established kind-only
resource families. Final [delivery evidence](evidence/checked-nominal-closure/README.md#final-delivery-verification)
records 141 distinct passes and Clippy, selected-only parity, exact missing-kind
and budget controls, separate consumer/Core mutations, hidden re-export and
identity/fold positives. Images pass 16/16, with original buffer/dependent startup
318827/314696 under unchanged 327680. Independent review, GitHub integration and partial acceptance completed at
`2d04de76`; broader declaration/resource closure and whole F3/F-core are incomplete.
Hidden identity/kind metadata carries no constructor access, so the control uses
the metadata actually retained by that route.

The PR #95 constructor-payload controls establish private Leaf through public
Envelope's payload and constructor scheme, with no Leaf root in public global
schemes or callable types. Missing Leaf metadata already rejects. A coherent
same-kind Donor substitution preserves both hidden kinds and completed global,
native and source facts but passes summary authentication and real body-free
consumer resolution/checking. Independent linked Core rejects both changed
payload and missing final-ordinal Leaf after valid controls. These separate
[test-first results](evidence/checked-constructor-closure/README.md) justify
binding the existing constructor projections to the completed defining registry;
source coordinates do not reconstruct semantic payload meaning. The bounded
repair forwards that same registry reference through imports and re-exports,
with paid exact correspondence and independent checker entry. The final focused batch passed; independent review, GitHub integration at
`2532f528` and PM-confirmed partial acceptance completed. No new constructor access or execution authority
follows from retaining the reference.

## Deviations

None. A semantic gap returns to CP-0024; an unsupported partial route refuses.
Runtime protocol/completion and executor realization are separate F4/F2/F7 work.

The next authorized checkpoint starts from PR #95 retained
`2532f528795e5cdc3974685d10313e6cb4b778a9`, independently audited and
PM-confirmed in issue #59. The owned plan splits exact checked owner/symbol
original binding from connected resource host/checked_scope lifecycle admission.
The prerequisite grants no lifecycle or runtime permission. Complete static
source/summary/Core owner correspondence remains required after that bounded PR;
all original incomplete criteria above remain unchecked.

PR #96 delivers the passive checked-owner binding prerequisite, with selected
original H/R and complete nullable/void teardown signature relations preserved.
The real binding refusal and unintended legacy Scope-header admission were
recorded before repair. The shared header now refuses checked owners for both
legacy codecs. [Final evidence](evidence/checked-owner-binding/README.md#final-delivery-verification)
records 223 distinct passes, source-resource 30/30, images 16/16 and Clippy;
startup 318857/314727 remains below unchanged 327680. A baseline-confirmed
node-location assertion was corrected without weakening standalone Registry
refusal or the four independent scope mutations. PR #96 review and GitHub
integration completed at `91e6dee0`.
This accepts no whole F3 criterion or connected lifecycle/Core/runtime authority.

PR #96 is retained at `91e6dee0` after independent audit and PM-confirmed partial
acceptance. Its passive binding/import and legacy-codec refusal prerequisite is
complete; connected lifecycle was not accepted. The next authorized
[plan checkpoint](plans/checked-ffi-contract-carriers.md#connected-static-checked-owner-lifecycle-checkpoint)
connects dependency-free Probe<H,R> under an exact lexical host and canonical
checked_scope, with private owner/request/outcome finish lineage and separately
retained source continuation. Actual source/body-free consumer/Core/transforms
precede negative and paid-budget evidence. Broader witness transport returns to
CP-0024 if ambiguous. Whole F3, runtime/images, owner dependencies and F-core
remain incomplete.

PR #97 connects the bounded dependency-free static checked-owner lifecycle.
Actual source and summary publication, a body-free consumer and linked
Core/identity/fold controls precede its hostile mutations. The immutable
flow-checked template carries exact finish request/outcome/payload lineage;
Core independently authenticates headers, specialization and copied forests.
Boundary inspection keeps only the original whole payload's witness, and
post-attempt Current access does not regain native permission. Source continuation
and latest private-data E dependencies remain separately checked.

The connected path also repairs the existing mixed preflight/checked codec memo,
hidden local provider publication/import, referenced private foreign State
metadata and synthetic Host value ports. Internal pending provider rows retain
paid exact H subtraction and late result/row escape obligations. No owner
interpretation is added to the host. The
[delivery record](evidence/checked-owner-lifecycle/README.md) separates authentic
red cases, rejected fixture setups, the retained-base deep-work assertion
comparison and final uniform checks. The final uniform 584-input batch records 399 distinct passes (430 passing
lines), source-resource 30/30, images 16/16 and Clippy with warnings denied.
Buffer/dependent-discard startup work is 318936/314929 under unchanged 327680.
Exact-head review and integration remain pending; these final receipts are
separate from the historical checkpoints above.

This accepts no whole-F3 criterion. Private local acquisition-codec constructor
closure, combined producer/Cell original-template and multi-library lifecycle
cases, broader witness helper transport, declared C-to-S owner dependencies and
remaining declaration closure stay visible. Checked runtime/native/image
execution, K realization, deployment, F4/F6, Main and F-core remain separate.
The existing generated-host connected F3/F4/F6 trigger still schedules F-core.

PR #97 is retained at `73a982f0` after independent retained-result/readback audit
and PM-confirmed partial acceptance. The next authorized
[scalar Current Borrow checkpoint](plans/checked-ffi-contract-carriers.md#static-scalar-current-borrow-checkpoint)
adds one opaque Current-to-scalar checked native request solely through its
owning resource's direct handler. A genuine prepared-positive/binding red
precedes implementation. Body-free import/re-export, independent Core/transforms,
exact original/Host/assumption facts and hostile/budget controls are required.
No byte/window/dependency/runtime or deployment permission follows; whole F3
and the existing F-core/Main gates remain pending.

The scalar Borrow candidate now passes real source/summary, body-free import and
re-export, linked independent Core/identity/fold, exact copied Read vector/Host/
membership mutations, and distinct nonempty row actuals around nonfirst H/R.
Binding controls cover exact/prefix/short/spent/fresh work, original/formal/
operation identity, direct State shape and extra-operand refusal. Genuine native
summary erasure controls and the final eight-command uniform affected batch pass:
527 distinct names / 562 passing lines on 589 equal inputs; source-resource 30/30,
images 16/16, Clippy zero and startup 318956/314948 below unchanged 327680. The separate appended ordinary-formal versus
unused lexical-host source-order limitation remains visible; no census guard
was relaxed. [Borrow evidence](evidence/checked-scalar-borrow/README.md) retains
all failed prerequisites and precise attribution. Exact-head review, root-assigned
GitHub integration and partial acceptance follow; whole F3 and F-core remain open.

PR #98 is retained at `c8a1fee5`; actual retention/partial acceptance and PM
confirmation are complete. The next authorized
[checked byte/copy window checkpoint](plans/checked-ffi-contract-carriers.md#checked-byte-and-copy-window-checkpoint)
implements all four distinct checked primitives with real initialized State,
view/Extent/window and any required declared dependency lineage. Source, body-free
import/re-export, independent Core/transforms and static private-image validation
must precede closure claims. Existing runtime activation remains refused. The
first expected-positive preparation/admission gates and their actual failures
are retained in the test-first evidence below. Whole F3 and its remaining generated-host/runtime/full-gate obligations
stay open.

The byte/window checkpoint's [test-first evidence](evidence/checked-byte-windows/test-first/README.md)
records genuine initialized State and view/extent preparation, missing checked
builtin exports and the isolated checked Bytes-owner binding refusal. The
[candidate evidence](evidence/checked-byte-windows/candidates/README.md) retains
reconstructible compile/preflow failures and the exact codec-family and defining-H
kind repairs. The current candidate passes all five focused controls, including
real all-four source checking and summary construction; two paid family/kind
controls also pass on the same 591-input map (`c74e45c0`). Body-free import/
re-export, linked independent Core/transforms, passive images, hostile controls,
bounds and affected regressions remain assigned delivery work. No runtime or
image activation claim follows.

The next byte/window checkpoint passes actual direct/facade body-free consumers,
linked independent default Core and identity/fold, retaining the exact original
native/header/access facts and all four flow-proved calls. Its startup probes
now expose real Resource regressions at unchanged 327680; these block delivery.
Passive-image hostile completion, remaining window/Host/original controls and
bounds/regressions remain pending. The candidate evidence records both positives
and reds; no whole-F3, checked execution or image activation claim follows.

The [owned-call State checkpoint](evidence/checked-byte-windows/candidates/owned-call-move/README.md)
passes its focused controls and all three unchanged startup probes on the isolated
parallel F3 configuration. Integration onto the retained passive milestone,
affected regressions, Clippy and final review remain pending; no whole F3 or
public checked execution acceptance follows.

The [combined native-interpreter discriminator](evidence/checked-byte-windows/candidates/combined-native-fixture/README.md)
records two fresh passing two-owner startup repeats, followed by a genuine
native-interpreter fixture inventory failure in the affected batch. At that checkpoint the
reviewed fixture-only complete-declaration repair and omission control were
uncompiled. The final combined verification below supersedes those pending gates.


The [final combined byte/window verification](evidence/checked-byte-windows/candidates/final-combined-verification/README.md)
passes 473 distinct selected unit tests, two additional exact two-owner startup
repeats, the compile/link-only producer-receipt integration, and Clippy with
warnings denied on one frozen source/configuration map. The unchanged startup
allowance is 327680: two-owner uses 327365, nested cleanup 320457, and dependent
cumulative reconstruction/correspondence 325006. The dependent control retains
exact, one-short, prefix and fresh-retry checks.

The complete native fixture now includes authentic checked declarations; a
canonical-first omission control rejects the same registry with only those
declarations removed. Full checked private static-image reconstruction, hostile
records and paid bounds pass. Earlier positive-fixture and lint failures remain
qualified in evidence; no generated program was started by the receipt
integration. Independent published-head review and milestone retention remain
pending. Whole F3, public checked execution/protected activation, and the connected
F-core gate remain open. The developer owns the next full workspace verification
when F3/F4/F6 connect to the generated-host path.

PR #101's bounded static byte/window delivery is GitHub-retained at
`c51089c8b6de76384361283f671d1f2dbf3ad58e` with exact reviewed tree equality;
[partial #59 acceptance](https://github.com/dikini/ash-lang/issues/59#issuecomment-6351849293)
is independently read back and PM-confirmed. All whole-F3 boxes remain unchanged.
The next assigned static slice is the declared enclosing C-to-S owner dependency
checkpoint in the existing task-owned plan. It begins with a genuine checked
parent/child source expected-positive discriminator; no new test/build success,
production dependency admission or runtime permission is claimed yet.


The [initial declared dependency checkpoint](evidence/checked-owner-dependencies/initial-connected/README.md)
records a genuine checked dependent-library InvalidLibrary red after the existing
canonical control, then a repaired opaque parent/child source/body-free/link/Core
and identity/fold positive. This is an early candidate, not whole F3 acceptance.
Hostile H/C/donor/full-vector/private-data controls, private image reconstruction,
work bounds, affected regressions and independent current-head review remain
pending. No runtime/native activation or general helper transport is added.

The [declared dependency matrix and Row-image observation](evidence/checked-owner-dependencies/matrix-and-row-image/README.md)
retains interrupted/setup attempts and the latest eight-of-ten matrix result.
Complete nonempty-Row Core and retained scalar Borrow controls now pass; the base
private image passes with hostile and work-bound controls. The required full-Row
private image still exhausts the unchanged restore budget during final independent
validation. The access Borrow base passes, while its exact-line Row fixture
correction remains uncompiled. This is pending repair, not a partial-budget waiver
or completed dependency delivery. The source-only correction and all old failures
remain qualified separately; no native activation or F3/F-core completion follows.


The [carrier and reconstruction checkpoint](evidence/checked-owner-dependencies/carrier-and-reconstruction/README.md)
records the rejected conditional-row hypothesis and the current checked Access
full-kinded carrier progress. The latest frozen batch passes seven focused
controls and eight of ten dependency tests. Genuine Access now reaches
independent Core, and genuine dependent headers still refuse runtime entry
before owner/callback activity. Both required full-Row private images remain
work failures; later image hostiles, startups, final specification wording,
affected regressions, Clippy and current-head review remain pending. The
consuming-row implementation has semantic parity evidence but no demonstrated
required-image budget fit. No broader F3, runtime or F-core criterion is closed.


The [member reconstruction refinement](evidence/checked-owner-dependencies/member-refinement/README.md)
retains one compile-only test repair and the next genuine seven-focused-control
plus eight-of-ten dependency result. Formal-kind-driven static Access matching
and its erased-descriptor Core refusal now pass. Both required full-Row images
still fail at their distinct work boundaries; startups and final gates remain
unrun. The tested source is preserved before rebase onto the retained F6
producer checkpoint; no result transfers automatically to that newer tree.

The [decoder-local Row representation checkpoint](evidence/checked-owner-dependencies/row-representation/README.md)
records fresh rebased failures, two bounded actual failure-path observations and
six passing structural-data controls after a wire-lacks fixture correction.
Repeated Row data now reuses only decoder-local immutable representation with
paid fresh clones; no registry, header, forest or Core proof is shared. The base
private image completes at 261284, but the required full-Row image still returns
Validation(Resource), and the separately observed Access image returns direct
Resource. Their current failure paths remain unlocalized after the change.
Both canonical images, subsequent image bounds/hostiles, startups, final spec,
regressions, Clippy and current-head review remain delivery gates. All whole-F3
criteria stay open; this checkpoint does not authorize native activation.
