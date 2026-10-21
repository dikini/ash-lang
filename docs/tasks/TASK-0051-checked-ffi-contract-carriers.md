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
of the outward row. Erasure, alias/re-export, branch/higher-order and bounded-work
evidence remain pending.

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

## Deviations

None. A semantic gap returns to CP-0024; an unsupported partial route refuses.
Runtime protocol/completion and executor realization are separate F4/F2/F7 work.
