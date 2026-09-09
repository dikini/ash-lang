# Effect Ash milestone closure evidence

This informative report audits the combined milestone from `035b456` on
`integration/effect-ash-foundations`. Signed main merge
`5d126b2dc1ca82bd7c9dff196c914e7da2199716` retains all selected slices.
Final merged-main verification and documentation checks passed, closing all
100 relative planning units. The
[specification](../../../spec/README.md) governs the implemented
contracts; [DN-0028](../DN-0028-effect-ash-milestone-plan.md) defines the milestone
completion obligations, not language semantics.

## Combined conformance

Independent high-reasoning semantic review inspected actual tests and shared
compiler/runtime boundaries. It found no demonstrated cross-slice defect. The
following witnesses complement the retained reports for individual slices.

| Obligation | Retained evidence |
| --- | --- |
| Local identities, exact evidence, generic selection and native captures compose | [Native imports](../../../tests/native_buffer_imports.rs), `imported_constrained_call_retains_selected_native_capture`, combines local newtype, scoped methods, imported generic selection and native capture. Copied-value acceptance is paired with handle-capture rejection. [Scoped interactions](../../../tests/scoped_evidence_interactions.rs) check coalescing polymorphic method effects and resource-dependent lexical factories. |
| Generic rows, hook coincidence and cleanup preserve exact authority | Native imports' `imported_native_cleanup_row_requires_existing_hook_lacks_authority` and `generic_hook_coincidence_preserves_imported_native_capture` pair row-lacks and equal/different instantiated-handler cases. |
| Closing order and continuation ownership compose | [Native interactions](../../../tests/native_buffer_interactions.rs) observe mixed cell/registration/cleanup/native order `210`, recursive owned discard, skipped suffixes and running/outside-owner rejection. [Cleanup interactions](../../../tests/cleanup_interactions.rs) separately cover overlapping recursive-site activations. |
| Transforms do not preserve forged authority by accident | [Core validation](../../../src/core/validate.rs) rederives same-typed callback/resource dependencies on original, identity and folded Core, including generic handler coincidence. Native transformed positives execute `Success(5)`; twelve mutations per transform and constructor forgeries leave native counters zero. |
| Linked authentication remains independent | [Linked validation](../../../src/evidence_validation.rs) mutates native provider, owner, builtin, method order/kind, handle, brand, origin and operation, and independently authenticates constructor payloads. |
| Pure retains its closed dialect and no acquired effect state | [Architecture tests](../../../tests/architecture.rs) close the Pure operation family; [effect Core tests](../../../tests/effect_core.rs) retain Pure selection for unused effects. Pure initialization and the locality test in [the machine](../../../src/eval/machine.rs) establish no live resource, registration, cleanup or captured-control owners. |
| Diagnostic and migration contracts remain distinct | [Effect diagnostics](../../../tests/effect_diagnostics.rs) retain ordinary-error precedence and clause/method barriers. [Resource typing](../../../tests/resource_scope_typing.rs) and scoped interactions retain causal escape/evidence labels. [Cleanup evidence](reliable-cleanup-evidence.md) distinguishes migrated owned-abandonment positives from retained outside/running-owner negatives. |
| Compiler budgets and runtime failure ownership remain separate | Linked/Core tests retain exact, one-short and fresh compiler budgets. [Native runtime boundaries](../../../src/eval/native_buffer_tests.rs) cover committed initializer effects, prepared refusal delivery, storage refusal, mixed-owner failure stop, incomplete teardown and deep captured disposal. |

The Core inventory in `spec/elaboration.md` omitted implemented `Cleanup`.
Closure corrects that documentation from its existing Core and independent
validation contract; no language or runtime behavior changes.

## Downstream pressures and residual risks

Independent high-reasoning architecture, resource and simplification review
inspected these named cases. It found no demonstrated contradiction in retained
behavior. These observations are bounded evidence, not future feature designs.

| Pressure case | Retained boundary | Residual work |
| --- | --- | --- |
| Proof evidence must not be fabricated from ordinary method/provider evidence | [Interface evidence](../../../src/interface.rs) has closed lexical/abstract/implementation sources. [Resolved acquisition](../../../src/resolved.rs) separately authenticates builtin origin, identity, handle and forwarding equations. Source fabrication and transformed Core forgery reject. | Define proof introduction, elimination and authentication separately. Shared validation patterns do not make authority kinds interchangeable. |
| Hidden values may cross a boundary without exporting identity or authority | [Local newtypes](../../../tests/local_newtypes.rs) distinguish identity-free closures from outward identity exposure. Scoped factories can export ordinary closures, while resource-dependent closures still reject and copied scalars can escape. | Existential identity/authority packages require explicit ownership transfer and elimination rules. Current closures are not such packages. |
| Suspension must transfer owned restricted state | Captured continuations own non-Clone frames; resource handles copy only private non-owning activation keys. Resume transfers ownership and checked discard consumes its owned capture. | Escaping suspension and cancellation need new rules. Evaluator-local disposal observation must be reconsidered for independently scheduled suspended executions. |
| Concurrency or multi-shot use must not follow from ordinary value copying | The explicit machine retains ordered handlers and one-shot completion owners. Hook nesting does not replay pending callbacks; Core independently reconstructs capture obligations. | Thread-safe transfer and scheduling are unproved. Multi-shot requires both duplicable captures and replayable interpretation. Arc-backed metadata proves neither. |
| Dynamic loading must not reuse fixed builtin identity accidentally | Closed cell/native APIs and payloads use authenticated static acquisitions and separate private runtime activation keys. [Instantiation](../../../src/eval/instantiation.rs) excludes runtime-only atoms from checked Core and unification. | Loaded identity, compatibility, ABI and library acquisition remain undefined. Runtime reflection would need to revisit the private activation-atom representation. |

## Simplification disposition

No carrier, validation pass or runtime owner was found removable within this
bounded audit without weakening an existing obligation:

- Shared nominal/row/type operations avoid separate semantic type systems.
  Static identities, activation keys and ownership frames have different roles.
- Module callable summaries support separate checking; final Core capture
  analysis independently reconstructs actual linked dependencies. Cleanup-row
  inference computes results that later safety validation checks.
- Registration ownership must survive periods when its generated handler is
  inactive, preserving pending callbacks and release authority during forwarding.
- Pure and Effect share one explicit evaluator. Pure creates no live effect
  owners or handler/continuation frames, but the machine contains zeroed effect
  accounting fields and shared evaluator-local disposal observation. No claim
  of an effect-free physical layout is made.
- Native ownership reuses resource scope, capture and disposal. No general
  provider registry, scheduler, replay mechanism or authority calculus is added.

Similar clone helpers have different staging and work accounting. Consolidation
without a new concrete need and resource-bound evidence is not a justified
closure refactor.

## Verification and limits

On 2026-09-09, parent reran 1,214 library and 14 CLI tests successfully, then
passed `cargo xtask verify` after the closure documentation corrections. This
includes formatting, build, strict lint, the complete workspace test corpus and
rustdoc. Independent documentation review approved the pre-integration changes.
Changed-document Markdown has no new lint findings against the baseline;
existing overlong lines remain. All 96 relative file links resolved.

Final merged-main `cargo xtask verify` passed on 2026-09-09. Independent final
documentation review approved the current/historical status and retained limits.
All 297 relative file links resolve; Markdown has no new findings, and
`git diff --check` passes.
TASK-0031 and its execution plan are removed with inbound links updated; Git
retains their work history. The user's existing main documentation changes were
shelved before integration and verified unchanged after the signed merge. The
user-authorized
signed annotated `effect-ash` tag identifies the final documentation closeout
above signed main merge `5d126b2`. No push was performed.

Detected runtime resource failures stop source execution and preserve bounded
primary/first-teardown reporting. Prepared atomic allocation refusal may return
without further allocation, preserving earlier initializer effects. Infallible
host allocation termination is not intercepted; incomplete teardown carries no
eventual-release promise. Native ARM64 compilation is not native execution or
release conformance.

The combined recursive native-owner/cleanup stress case remains unadmitted at
the retained checker limit. Separate admitted witnesses cover recursive discard,
mixed closing order and deep teardown; no limit was raised and no execution of
the combined case is claimed.

At this milestone closure, TASK-0024's compiler repair had not started and
remained separate post-main work. Its later
[verified repair](../migration-repair-evidence.md) is not part of this
milestone. The ash-doc documentation migration remains separate downstream
work. General FFI, files and library acquisition remain later work.
