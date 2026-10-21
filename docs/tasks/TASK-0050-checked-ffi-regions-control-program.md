# TASK-0050: Checked FFI, Regions, and Scoped Control Program

- ID: `TASK-0050`
- Status: active
- Related: [AD-0002](../decisions/AD-0002-documentation-system.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [AD-0012](../decisions/AD-0012-proof-development-feedback-and-build-reuse.md),
  [DN-0053](../design/DN-0053-scoped-generic-cells-without-native-owners.md),
  [DN-0054](../design/DN-0054-base-lexical-region-memory-contracts.md),
  [DN-0055](../design/DN-0055-algebra-of-regions-lifetimes-and-ownership.md),
  [DN-0056](../design/DN-0056-scoped-continuation-retention-and-library-scheduling.md),
  [DN-0057](../design/DN-0057-checked-ffi-module-boundaries.md)

> This task organizes the program. It defines no Ash semantics. The original
> documentation-only preparation and subsequent M1 local launch are recorded
> separately below. Semantic adoption uses the user's later explicit delegation;
> Main integration retains its separate gates.

## Current local launch

The user subsequently directed: “proceed autonomously, using unsigned commits.
work in a separate worktree. choose your recommended answers to questions.”
On 2026-10-21 the orchestrator adopted independently reviewed CP-0024 under this
delegation and authorized local M1 product delivery. Work proceeds in the separate
Main-based `.worktree/checked-ffi` checkout, branch `codex/checked-ffi-core`, with
`codex/checked-ffi-milestone` as retaining anchor. Both started at the pinned Main
commit below. The planning source checkout and all its unrelated edits remain
intact. The user later authorized publishing the planned issues and overall
milestone and individual work-item PRs after successful review. The latest user
instruction requires GitHub squash-and-merge, with a GitHub merge commit when
squash is unavailable. The [published issue map](plans/checked-ffi-regions-control.md#authority-and-github-workflow)
links the [parent #51](https://github.com/dikini/ash-lang/issues/51),
[M1 #52](https://github.com/dikini/ash-lang/issues/52), and remaining work.
Preparation PR [#69](https://github.com/dikini/ash-lang/pull/69) carries P0/F1
preparation and the initial F3 task. Keep locally authored commits unsigned;
GitHub merge signing follows the selected GitHub method. After required
review/checks and GitHub integration, fetch and synchronize local/origin milestone
refs. Earlier local squash receipts remain historical evidence; future delivery
must use the current GitHub method, which overrides AD-0011's normal merge method.
Main integration retains its separate gates.

The developer owns implementation, build serialization, integration and
acceptance updates; the assigned reviewer checks exact candidate heads; the
orchestrator owns scheduling and confirms acceptance updates. The platform
developer owns F2 continuation. F3 may start under accepted CP-0024; F6/F7 work
relying on Linux realization requires accepted F2 evidence/architecture first.

On 2026-10-21 the user authorized agents to work toward M1 under this plan.
The orchestrator assigned local P0 provenance reconciliation, F1 proposal
preparation and F2 bounded experiment preparation/nonprivileged probes. The
developer is the design author and acceptance-update owner; independent review
uses the assigned reviewer. Product implementation requires accepted F1 and
appropriate F2 architecture; GitHub publication, pushes, merges and Main
integration are not part of this local preparation assignment.

Delivered candidate: [CP-0024](../proposals/CP-0024-checked-foreign-host-profile.md),
its [63-row evidence map](../design/foreign-authoring/checked-ffi-evidence-map.md),
and [F2 experiment contract](../design/foreign-authoring/linux-profile-experiment.md)
with [Stage A observations](../design/foreign-authoring/linux-profile-probe/README.md).
P0 confirms the pinned Main foundations; the original source planning tree remains unsuitable as
a product restart point. IDs were checked against available full Git history;
CP-0024 was new. That initial preparation created or accepted no AD.

Independent review repairs now specify exact checked-native subtraction, concrete
checked call/finish/report codecs, explicit H-selected byte/copy primitives,
mandatory assumption floors, fixed runtime records distinct from source payloads,
required authored finish control, and generic group quarantine without consumption
or completion forgery. The 63-row map and Stage A scope were checked independently;
final preparation review cleared SHA-256
`87480f9f8dda2d218e59099e6ca179ae1bdfb18616e2bb4908727b4c1456f854`.
The orchestrator then adopted CP-0024 under the user's delegation. These accepted
future semantics are not current Ash before complete product/Main retention.

The retained preparation at `1cf1014` passed independent authority/history review:
Main parent, all six design pins, unchanged product/spec/old cell evidence,
no restored retired artifacts, and 453 local committed links/anchors. Two minor
wording/index findings are repaired in this preparation revision.

The later F2 [generated Ash packaging comparison](../design/foreign-authoring/linux-inprocess-probe/generated-ash/README.md)
retains actual compiler/generated bridge/private-payload digests, the initial
parser refusal and corrected fixture, successful whole-static linking, ELF data
and linked-input provenance. No image execution accompanied packaging. Retained
libc loader paths leave the proposed no-loading requirement unmet. A separately
[approved diagnostic](../design/foreign-authoring/linux-inprocess-probe/generated-ash/diagnostic-addendum.md)
observes host `Returned(7)` and sandbox EACCES with reaping under explicit
known-loading/host-trust premises. Independent evidence review cleared that
bounded scope; those observations supply no strict per-image approval or product
execution authority.

On 2026-10-21 the orchestrator accepted independently reviewed
[AD-0015](../decisions/AD-0015-linux-scalar-inprocess-whole-images.md) under the
user's delegation: owner-free scalar GNU in-process mechanisms, explicit trusted
closure premises and before-startup refusal obligations. The
[acceptance readback](../design/foreign-authoring/linux-inprocess-probe/scalar-closure/acceptance-receipt.json)
pins the reviewed proposal/example. This is partial F2 architecture acceptance;
strict per-image approval, protected store/context enforcement and connected
F4/F6 product evidence remain pending. Isolated, owner/resource and SQLite scope
are excluded, and whole F2 criteria remain unchecked.

Remaining: concrete delegated Linux controls and Stage B enforcement evidence,
isolated/SQLite/owner scope, product implementation and all product gates.
Stage A is environmental evidence,
not isolated-profile validation. F-core (F3/F4/F6 connected) remains the next full
workspace checkpoint; the orchestrator owns scheduling and build serialization.
No full product gate is claimed for these project-management documents.

## Dependencies

The original preparation authorization on 2026-10-21 covered: this coordinating
task, its [execution plan](plans/checked-ffi-regions-control.md), and updates to
the task index and development trajectory. The authorization excludes product
implementation, agent dispatch, GitHub publication, commits, and merges.
That historical authorization did not start delivery. The later local launch
above extends preparation scope without changing semantic acceptance gates.

The observed local Main baseline is
`7949b6d9136b0152ee9104e67bd0451cb9db4727`. Its
[foreign declaration rules](https://github.com/dikini/ash-lang/blob/7949b6d9136b0152ee9104e67bd0451cb9db4727/spec/static-semantics.md#source-foreign-declarations)
and
[generic cell rules](https://github.com/dikini/ash-lang/blob/7949b6d9136b0152ee9104e67bd0451cb9db4727/spec/static-semantics.md#generic-cell-foundation)
are implemented foundations. The
[generic-cell evidence](https://github.com/dikini/ash-lang/blob/7949b6d9136b0152ee9104e67bd0451cb9db4727/docs/design/generic-cell/evidence.md)
records checkpoint and Main retention, including retirement of CP-0023 and
TASK-0045 through TASK-0049. Those artifacts remain in this older planning
checkout; their presence does not reopen their work. Do not reimplement cells
or restore retired transition artifacts on the product branch.

The bounded FFI foundation preserves passive modules, canonical foreign facts,
generated bridges, scoped owners, and consumption distinct from reporting.
Generic cells add ordinary payload storage and contents dependencies without
native acquisition. Neither foundation establishes DN-0057's checked host and
isolation profile, explicit ordinary-object regions, owned continuation stores,
or concurrent resource sharing. Planning must preserve exact identities, hidden
dependencies, handler precedence, independent Core validation, and required
completion across those new boundaries.

The agreed delivery order is checked FFI, lexical regions, local retention and
library scheduling, then two pinned workers with copied channels and checked
bidirectional shutdown. Checked FFI is an opt-in profile; existing supported
builds remain supported. Mechanized bounded proofs must precede reliance on new
ownership or completion-checking rules for release. These are planning choices,
not acceptance of the notes' proposed semantics or architecture.

## Work

1. Maintain the task-owned plan with proposed GitHub parent/milestone issues,
   child issue scopes, dependencies, governing-artifact requirements, acceptance
   criteria, expected PR slices, and responsible roles.
2. Separate contract, architecture, experiment, proof, implementation, and
   closure work. A future product issue needs accepted semantic/architectural
   authority, a repository task, and a launch assignment before implementation.
   An experiment needs its bounded question, comparisons, and retention or
   disposal conditions. This plan grants no such authorization.
3. Record full-gate checkpoints, exact-head handoffs, acceptance ownership,
   and Main's separate gate using the existing
   [agent workflow](../project/agent-workflow.md). Keep issue progress on GitHub
   only after publication is separately authorized; add no independent tracker.
4. Update the [task index](README.md) and [trajectory](../trajectory.md), marking
   the completed foundations and planned extensions by their actual status.
5. Verify the four-document change under the
   [documentation policy](../project/documentation.md). Preserve the existing
   edits to the shared workflow and launch template.

Future coordination uses `ash-orchestrator`; delivery uses `ash-developer` and
independent review uses `ash-reviewer`. The future launch assigns named people
or agents, a build operator, an integrator, and an acceptance owner. Roles in
the plan are responsibilities, not assignments made by this task. The author
prepares and applies acceptance updates after verified retention; the reviewer
checks evidence and PM confirms the update before advancing.

## Progress

The original documentation preparation is complete; product delivery remains
unstarted. The later local M1 contract/experiment preparation is recorded above. All issue keys
remain local plan references. The original preparation established no GitHub
issue numbers, PRs, implementation branches, team assignments or product
acceptance. The current preparation team and candidate artifacts are recorded
in Current local launch; product acceptance remains pending.

- [x] Confirm TASK-0050 is unused in the working tree and available Git history.
- [x] Pin Main and distinguish completed FFI/cells from the planning checkout.
- [x] Record milestone order, opt-in compatibility, bounded endpoint, and proof gate.
- [x] Draft issue scopes, dependencies, PR slices, roles, and handoffs in the plan.
- [x] Link the task and plan from the index and trajectory.
- [x] Complete Markdown, link, dependency, authority, and preservation checks.

The launch described above supersedes the original no-agent boundary for local
M1 preparation. Product launch remains gated on the accepted artifacts.
Keep this task and its owned plan while they organize pending program work.
When that work is superseded or complete, consolidate durable conclusions and
remove the task/plan under the artifact lifecycle; Git retains the record.

## Verification

For this documentation delivery, inspect the four changed documents, their
relative links and pinned Main references, artifact ID/status, issue dependency
order, role ownership, and semantic authority. Run Markdown lint and
`git diff --check`. Compare the shared workflow/template contents and Git refs
with their pre-edit state. No Rust, native, or Lean implementation changes
require a product gate for this prose-only delivery.

The 2026-10-21 documentation checks passed: Markdown lint on all four documents
with MD013 disabled for long links/tables; 154 link/anchor checks including 11
pinned Git targets; task structure and all six required fields in each of the
25 issue records; tracked/new-file whitespace checks; and manual dependency and
authority review. Shared workflow/template hashes, HEAD and Main matched their
pre-edit values. No product test gate or independent delivery review is claimed.

The later M1 preparation passes Markdown lint with MD013 disabled, tracked and
new-file whitespace inspection, Python probe syntax, 77 local/pinned link and
anchor checks, all 63 unique evidence-row checks, six canonical design-input
hashes, and preservation hashes for the existing workflow, launch template,
task index and trajectory. HEAD and Main remain at their original pins.
Independent review reproduced the system-Python observation field-for-field;
semantic preparation review is cleared. Transplant review remains pending. No
product full gate was run.

Future delivery gates are specified in the execution plan. They include focused
checks, independent review, frozen Lean integration where required, real native
evidence, full workspace checkpoints, and verification of the retained result.
No historical receipt is presented as a fresh gate for this task.

## Discoveries

The planning checkout predates the product integration of both FFI and generic
cells. Current Main is a descendant of `ffi-base`, peeled commit
`354c76b391fe4af665cf6a03479a9874a57cb3e3`. This changes the backlog from building
those foundations to extending them and preserving their evidence.

DN-0057's common transitions have proposed design resolutions, while Linux
deployment acceptance remains open. DN-0055 and DN-0056 still need bounded
preservation/checker soundness evidence. Those gaps belong to explicit future
design and proof issues, not local implementation choices.

## Deviations

The original preparation had no deviations from its documentation-only request.
The later authorized local launch adds proposed concrete source/build syntax and
checked codecs in CP-0024 plus bounded environment probes. Wire encodings, runtime
representations and F2 architecture remain pending; CP-0024 acceptance is recorded
above, and product tasks require their bounded assignments. The issue catalogue is a proposed
delivery sequence rather than premature product implementation tasks.
