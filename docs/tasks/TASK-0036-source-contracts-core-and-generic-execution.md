# TASK-0036: Source contracts, Core and generic execution

- ID: `TASK-0036`
- Status: active
- Related: [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [GitHub issue #2](https://github.com/dikini/ash-lang/issues/2)

> This task organizes authorized work. It does not define Ash semantics.

## Dependencies

Accepted CP-0022 and AD-0013; the linked contract issue #1 supplies review and
acceptance evidence. Coordinate the executable boundary with TASK-0037. Library
ports depend on this generic mechanism, rather than granting native authority.

## Work

1. Admit the complete foreign/resource/access grammar and passive module exports,
   retaining exact defining origins, kinds and complete ordered Type/Row arguments.
2. Prepare one immutable checked foreign contract and checked template per defining
   occurrence. Use phase-specific types and authenticated native projections;
   specialize with fresh local identities without replaying source checking.
3. Implement generic native-effect interpretation, private resource data, finite
   copy windows, initialized output/extent evidence and guarded ownership phases.
4. Reconstruct and independently validate final Core through modules/transforms;
   preserve handler precedence, capture/resume/discard and quarantine dependencies.
5. Update affected specification sections alongside verified behavior. Preserve
   bounded work, fallible allocation, iterative traversal/disposal and depth limits.

## Progress

Assignment, blockers, live progress and PR status belong to the linked GitHub
issue. This task retains scope, ordered work and durable implementation findings.

## Verification

Use public-pipeline integration cases for source admission/publication, exact
identity and tagged argument checks, malformed/transformed Core, invalid access
and escape. Observe actual native acquisition, refusal, partial-owner cleanup,
window copies, completion order, resume/discard and retained-dependent blocking
through TASK-0037 bindings. Retain the open-Delta case and separate captured-control
witness. Run connected compiler/Core/evaluator regressions with one Cargo job;
run the full architecture/workspace gate at integrated delivery.

## Discoveries

DN-0036 supplies reusable guarded scopes, owner arguments and validation, but
Rust-authored manifests/adapters are experimental comparison evidence. They
cannot become the source authoring API. Private replaceable payloads and finite
window contracts are new obligations in CP-0022.

A zero-argument `void` call exposed a nonempty-outcome grammar gap: no output
or owner exists to justify a fact. CP-0022 now permits empty outcome fact lists
with mandatory semantic coverage, accepted on 2026-10-10. Ash still reports
Unit after the call; no native result is read.

ABI preparation must price string comparisons and NUL scans by inspected bytes
before scanning. A single borrowed mapping table decodes each authored ABI
position once, rejects repeated positions and projects each mapped source path
once. Preparation alone has no resolved type or operation authority; binding
must still authenticate the canonical result codec and complete owner arguments.

Imported opaque result errors retain defining identity, kind and provenance,
without exposing hidden constructor bodies. Canonical codec authentication must
use those retained facts rather than requiring source access to the constructor.
Native descriptors follow selected or signature-referenced effect facts through
imports; copying every descriptor from a dependency would introduce authority
without its declaring effect. Module effect copies, canonical registry effects
and the exact operation table retain the same immutable descriptor allocation.

Failure after resolving an earlier effect needs iterative guards around staged
operations and declarations, before their final owner exists. Retained spelling
bytes and origin chains require priced, fallible copying. The registry's existing
exact-ID table supplies duplicate rejection; a second linear scan per effect
adds quadratic preparation without a separate validation obligation.

Independent export-summary admission must authenticate its native operation
table before selected imports can reconstruct local tables. Otherwise a missing
summary entry can be silently recreated from an effect tag. The same charged
effect walk now checks exact table/tag correspondence, retained signatures and
ordered parameter identities/kinds, including facade publication.

Retained native signatures also need exact operation, annotation and binder
provenance. Summary and registry authentication borrow the original spans,
guarded origins and shared annotation arena; equivalent type shapes alone
cannot authorize a substituted defining occurrence.

Foreign declaration setup increased the live debug-build resolver frame enough
to overflow an existing 256 KiB nested-cleanup witness before evaluation.
Separate completed declaration preparation from body resolution so setup
temporaries leave the stack first. The unchanged witness passes without raising
stack or work limits; retained setup fields use existing iterative owners.

Separating reusable compilation from execution adds a containing compilation
timer. The calibration consumer must recognize it without making it another
charged-work owner or requiring it in historical traces. Public Pure and Effect
observer cases now pass their actual logs through the consumer; both retain the
same six work owners, and containing timers must not be summed with child phases.

## Deviations

None authorized. Return concrete semantic gaps to CP-0022 instead of resolving
them locally. Keep excluded features outside this task.
