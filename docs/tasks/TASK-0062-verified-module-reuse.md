# TASK-0062: Verified Module Reuse

- ID: `TASK-0062`
- Status: active
- Related: [issue #201](https://github.com/dikini/ash-lang/issues/201),
  [issue #190](https://github.com/dikini/ash-lang/issues/190),
  [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [elaboration](../../spec/elaboration.md),
  [name resolution](../../spec/name-resolution.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

Imports remain acyclic and are checked dependency-first. A module's compiler-owned
output must preserve its checked implementation and contracts; importing code
must discharge its own actual obligations against those contracts. The final
linked program must preserve the current independent Core and execution
boundaries. Arbitrary module loading, a stable module format and new language
semantics are outside this task.

## Work

1. Reproduce the full-binding case from #190 at unchanged budgets and trace the
   module producer, linking, evidence lowering, cleanup and final consumers.
2. Agree a concrete retained representation and its relocation, evidence,
   cleanup and caller-obligation boundaries with the independent reviewer.
3. Add connected reuse and caller regressions, then implement the reviewed path
   without repeating dependency body, pattern or coverage checks.
4. Verify linked execution and the affected safety, budget and native paths;
   update governing decisions and current documentation to match the result.

## Progress

Investigation has started from `2725cc2c01770ab318ec29c54e0263cedeab05f4`.
The reviewer and developer agreed the owned-fragment boundary below. On the
base, the connected diamond regression returned `42` after checking each
authored body twice. The first retained-root implementation passes that same
public compile, independent Core validation and execution path: it returns
`42`, and the three observed authored bodies are each checked once.

The Pure and Effect producers now complete their physical graph, selected evidence,
catalogue, closure layouts and cleanup before publishing a checked module. The
linker structurally relocates those nodes, catalogue rows and anchors; its final
row work is limited to new entry and assembly nodes. The full scoped-evidence
target passed 54 tests on the reviewed catalogue slice. The imported-discard,
nested generic-cell and nested allocating-cleanup cases pass through execution
with the new owner-specific cleanup transfer. An imported generic method whose
type parameter occurs in a cleanup effect also returns `42`. A manually checked
Pure module publishes its completed graph, links, passes the independent Pure
Core validator and executes to `42`.

Registry and interface consumers reuse completed defining rows while retaining
new link and route checks. A resource-bearing diamond observed each provider
initializer safety root twice before the repair and once afterward; the same
compile and independent Core validation execute to `42`. A facade regression
executes the valid case to `42` and rejects an escaping resource.

The merged PR source passed 1,702 library tests, 17 resource-scope module tests,
54 scoped-evidence tests and five targeted caller, cleanup and small-stack
checks. Formatting and warning-denied Clippy passed. Seven program-build tests
and the three existing supported native tests passed; the latter include the
full binding's lifecycle with static and shared linkage after source removal.
The earlier reviewed candidate also passed the architecture, compiler-work,
effect-module, interface-module and newtype targets before lint-only changes.
Its source/configuration manifest covers `src/`, `Cargo.toml`, `Cargo.lock`
and `rust-toolchain.toml` (SHA-256
`b4085ecb1f9bffbe9511e188471d8a7689d59f791d3a2224799d0f120f444178`).

The fresh full workspace checkpoint on that PR's exact tree passed format,
metadata, check, build and Clippy, then failed the test stage: 66 of 67 Core
validation tests passed. The failing manual fixture mixed distinct publications
of the same implicit dependencies. The input snapshot included the unchanged
README and benchmark files and remained stable through the failed run;
documentation was not reached. A follow-up retains one publication per
dependency in the affected Core and library-import fixtures, preserving the
real identity guard and all existing assertions.

The same focused audit exposed a separate default-budget refusal for a valid
192-export module. Cleanup row completion now uses one strict pass when its
paid scan proves there are no resumes and every structural child precedes its
parent. Forward references and resume edges retain the existing fixed-point
path and rollback. The original 192-export test passes without changing its
input or budget. The follow-up also passes all 67 Core validation, 17 library
import and 23 newtype tests, plus the postorder refusal/retry, nested-resume,
forward-cleanup and imported generic-cleanup controls.

The next fresh workspace checkpoint passed the first five stages and 1,703
library tests, but its test stage refused the original 10,000-member data cycle
at the default type-work limit; documentation was not reached. Its inputs stayed
unchanged. The postorder path now uses the strict replay's existing rollback
journal instead of retaining a duplicate snapshot. The fixed-point fallback
still snapshots before mutation. The original cycle passes on its 320 KiB stack
without changing its input or budget.

A diagnostic run of 91 integration targets then found five failures across four
targets. One exposed a source/Core mismatch: collecting initializer replies had
unintentionally enabled a more precise call analysis for a discard-only module.
Reply observation now leaves the existing call-proof mode unchanged. Other
corrections preserve the physical capture of strictly passed evidence and update
work-budget expectations and probe inventories after removed replay. The five
affected targets pass all 156 tests. Both original 64 KiB stack checks,
initializer-reply relocation, the shared-module execution case and the
observed-call transaction controls also pass.

On the current follow-up source, the original #190 full-binding input compiled
at unchanged limits: source checking used 53,730,163 of 368,770,000 units, final
elaboration used 31,935 of 29,501,600, and independent Core validation used
67,377,437 of 921,925,000. All three phases completed. On the merged PR source,
the full binding and Network program also executed to `42` through the
source-native interpreter after all six source files were removed. The base
final-elaboration count was a refused prefix, so it does not establish a
complete baseline cost. An attempted generated-host Network test was outside
the accepted build profile.
[AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md)
excludes Network scopes and operations from generated images.

The implementation boundary is:

1. A dependency-first module producer checks each source body once. After
   inference and evidence selection, it constructs the final module graph,
   evidence and anchors, physical closure layouts, settled cleanup rows and
   conditional value/control contracts before publishing the module. Imported
   contracts and the module's own lowered calls use the same physical evidence
   arguments. Refusal publishes no partial module or permission.
2. The linker relocates completed fragments and their metadata without
   reopening provider source or rebuilding its evidence, layouts or cleanup.
   It preserves module-qualified external identities and applies one complete,
   injective relocation to arena nodes and generated binders, type and row
   variables, handler/resume owners, catalogue indices and evidence anchors.
   New import, caller, entry and actual-context obligations use the retained
   contracts.
3. The newly assembled linked Core receives the existing independent validation
   once, including ordinary type, scope, provenance, evidence, capture and
   Store-release checks. Source checking and validation of this new Core are
   distinct proofs; no later consumer repeats the unchanged Core proof.
4. The existing compiled-program consumer executes the linked result. The
   connected regression must demonstrate reuse from checking through execution,
   including a shared dependency and caller-specific negative cases.

Each module retains its own completed graph, ordered roots, evidence, layout
and cleanup metadata. On the baseline, the scratch builder alone was not that
carrier: it could erase Effect operations and recorded evidence placeholders
rather than final lowered arguments and anchors. Source checking stages those
selections; module finalization consumes them before publication.
Every successful public file graph admits the private compiler Region
dependency, linking retains its group, and that group's nonempty `DefaultAlloc`
scheme makes the existing program-wide selector choose Effect. An explicit
empty-row entry also selected Effect in a normal compile/prepare observation.
This supports one Effect profile for that path; standalone and manually
assembled Pure APIs remain separate. The change must preserve source failure
order and existing budgets. Existing capture summaries retain control/value
graphs, but `check_builder` is not an independent Core validator and does not
prove Store release; the final linked-Core validator continues to do so. The
contract must distinguish new actual
caller obligations from replaying an imported module's internal proof,
including callback targets, owner enclosures, handler selection, cleanup rows,
retained continuation and release. Actual calls may traverse the retained graph
for new caller/focus obligations; they must not seed another autonomous provider
proof. Each defining producer checks its own initializer and retains the exact
observed reply to a generated closure-creation query. Imports reuse that reply,
the initializer value equations and callable control for new caller contexts;
they do not seed autonomous provider initializer or function roots. Each
producer solves its cleanup rows after evidence and region lowering. A new
open-module validator is not needed for this path.

The remaining delivery is an exact-commit review and one fresh seven-stage
workspace checkpoint. The PM coordinates the checkpoint review and follow-up
PR; acceptance and cleanup follow the actual result.

## Verification

The focused PR evidence must show actual reuse, supported imports and evidence,
positive and negative caller obligations, and linked execution at unchanged
work, depth and stack limits. Record the exact full-binding #190 result separately
from intrinsic replay savings. The independently reviewed candidate must receive
the full workspace checkpoint on the pinned follow-up commit before its PR;
the PM coordinates it and the developer owns the Cargo run. The
[prior full gate](https://github.com/dikini/ash-lang/pull/200#issuecomment-6550774584)
passed seven fresh stages on local Main
`8fbc84dd87b752fc26227a1233baca8c2ebaac38` (remote tree `2725cc2c` plus the
user's `AGENTS.md` addition); receipt SHA-256 starts `1f3f471f`. It is not
verification of this change.

## Discoveries

On the base, module checking published checked source and summaries while
discarding its scratch Core and separate cleanup state. Final synthesis
elaborated the retained bodies again with different evidence lowering and
rebuilt cleanup inference. The retained scratch builder alone still does not
meet the linked consumer's requirements.

The full-binding #190 variant uses the existing
`tests/fixtures/source-native/cases/network-binding.ash` entry with
`tests/fixtures/source-native/binding.ash` in place of the narrow binding,
alongside `native.ash` and the three current network library modules. On the
base with normal limits, the public `compile_path` reports 14 modules and
36,877 canonical source bytes. Source checking completed at 53,927,101 /
368,770,000 units; final elaboration refused at 29,501,600 / 29,501,600 and
independent Core was not reached. The CLI also exited 2 with empty stdout and
`internal.resource.type-work`. The final count is a refused prefix, not the
total work required to compile the program.

`ExportSummary::freeze` authenticates the completed defining summary, but the
resolver authenticated it again for every importing module. In the shared
diamond, a focused observation counted three authentications for the base
summary: one at publication and one for each importer. The consumer now reuses
that immutable publication while still checking the new import edge. Defining
global, implementation, interface, constructor, effect and nominal facts are
also retained through imports; summary assembly continues to check its new
routes, names, collisions, coherence and hidden dependency closure. The linked
registry and interface consumers now make the same separation.

Removing imported initializer roots exposed a necessary value dependency: a
generated closure initializer needs its already-observed allocation-context
reply to materialize the callable value. The defining producer now retains that
reply with the graph, and imports relocate it with the other metadata. Actual
calls still apply the retained control equations in their own contexts; the
assembled Core receives its full independent proof.

## Deviations

None.
