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

Ordinary effects and native symbol groups need one source-ordered identity
inventory. Library ranges, retained declaration indices and complete parameter
vectors must follow that inventory together; appending native parameters after
ordinary parameters breaks interleaved declarations. Preparation now uses paid
linear walks and crosschecks each retained library range against declaration order.

An imported opaque nominal can be an ordinary domain leaf without becoming an
ABI operand. Its exact retained nullary `Type` fact authenticates this use without
materializing private constructors. Scalar source-path checks still require `Int`;
unsaturated nominal constructors and resource roles remain inadmissible here.

Source-native execution needs a mandatory exact Core interpreter distinct from
ordinary handler selection. Program binding admission precedes every Ash step;
request admission retains the same canonical symbol allocation and complete
ordered actual vector under the saved lexical instantiations. Row arguments
remain part of identity even when the native ABI projects only Type arguments.
The final linked expression's outward row is empty after that interpretation;
a source `main` may still name the admitted native requirements.

Scalar calls narrow borrowed mathematical integers after charging magnitude
work. Readiness prepays bounded reporting and recording work and reserves the
Returned constructor slot. The consuming return receipt removes callback
capability; the next step records fixed-size raw facts before disposal, result
construction or continuation work can refuse. A focused Machine witness injects
only ledger exhaustion after a valid Rust callback returns, then observes
recording and prepaid reporting before ordinary String work refuses. One call
and a successful fresh activation distinguish no replay from a ban on later calls.
This is injected resource evidence, not a failure from the external library.
Mathematical Integer storage still allocates internally after recording.

Runtime conversion refusal needs the original nullary private error-constructor
role from the combined builtin module. Imported source checking continues to
use only the opaque nominal's retained kind and origin; runtime admission does
not require that constructor to become a public source export.

Generic helpers use implicit ordinary term instantiation. An EffectRow parameter
in a native effect's complete vector is supplied as a row, such as `{| Before}`;
using the bare parameter there does not supply a tagged row argument. Concrete
helper annotations can constrain independent closed instances without dropping
unused row parameters or adding explicit source term type application.

Latent effect arguments must report their authenticated binder uses to the same
scheme-coverage observer as value types. A separate unrestricted observer lost
uses present only in nested row arguments and incorrectly rejected an imported
generic helper. Registry-backed environments also lacked that latent argument
traversal. They now borrow original facts and check encountered latent rows on
demand. An internal ADT assigns nested obligations to the iterative effect queue;
it supplies no validation certificate. This adds the missing paid latent work
without a metadata prepass over Pure types or a copied effect inventory. Runtime
request admission checks the Type-only projection in the complete tag scan,
without a second row walk or an increased allowance.

## Deviations

None authorized. Return concrete semantic gaps to CP-0022 instead of resolving
them locally. Keep excluded features outside this task.
