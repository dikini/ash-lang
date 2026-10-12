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

Provider association checks exact method/operation names and substituted value
types, with the single associated effect row. Interface order is independent of
operation order. Checked lexical forwarding carries complete Type/Row arguments
through ordinary calls and constrained helpers, final Core and the private image.
Copied binder, operation, operand, effect and resource-owner claims require their
original correspondence; a same-typed application alone supplies no activation
authority.

Expanded source-scope construction must not enlarge the fixed transform frame
used by unrelated operations. The private source-scope rebuild routine retains
the same charged fallible forwarding and copy-map reservations, guarded Type
ownership and independent admission, without adding a heap allocation. The
ordinary-handler exact/one-short/retry/deep-disposal witness keeps its established
64 KiB stack and unchanged depth/work policies.

Retaining passive implementation census facts enlarges owning resolved-module
results. Kind checking and provenance publication run after name resolution in a
separate routine, so their result temporaries do not burden the active source
traversal. The same original-header census, sealing order, budgets and fallible
retention remain in force. The predecessor 256 KiB cleanup witness resolves its
source before evaluator execution; resolution preserves that established bound.

Canonical method spelling retention charges the original UTF-8 byte length
before fallible allocation. Independent ledger fixtures must count their actual
names, including `use`, `first`/`second`, `relate` and `relation`; equal numeric
deltas from different fixtures do not establish shared provenance.

An inner source scope already owns normalized immutable descriptor metadata.
Enclosing late normalization preserves that descriptor; final independent
admission still rejects altered or unresolved actuals and changed original
forests. This prevents both accidental rewriting of certificates and admission
through a compiler-only copying claim.

Selected source-handler entry authenticates the unique live guard, original
owner and exact activation before traversing every typed access position,
including nominal payloads. Ordinary handler selection precedes this check.
Modeled guard/frame tests and real generated-native lifecycle tests establish
different boundaries. Byte access, outward control, retained dependencies and
quarantine remain subsequent obligations.

The acquired_only delivery authenticates the instantiated nominal report fields
in defining constructor order: body answer first, acquisition error second.
It does not impose an extra report-parameter order, so a concrete-error
`Outcome<T>` and an error-parameterized report share the same role check.
Capture-value analysis must preserve that result shape while retaining finish
as a cleanup obligation; reusing Scope/Completion assembly would fabricate a
completion field. A source consumed-completion error becomes terminal after
native consumption and cannot publish success or retry release. Native retained
outcomes, byte access and outward control remain subsequent CP-0022 obligations.

Initialized-byte acquisition projects the original declared source leaf before
native entry, independently of ABI operands and private data. Readiness retains
the checked nonnegative `size_t` extent; infallible recording attaches it only to
the exact non-null unique guard. A zero extent preserves ownership. Missing facts
are refused during canonical foreign resolution, before resource or bridge
admission. Preflight work exhaustion follows the existing effect-work diagnostic
and remains terminal; post-return cleanup does not replay acquisition or release.
The image retains representation and original extent facts separately from the
checked executable resource template. Byte access and broader control remain
separate obligations.

A self-consistent image can reconstruct a different valid integer source path;
reconstruction alone does not prove correspondence to a generated call site.
The private executable gate compares its original `EXPECTED_FACTS` before
restoration or binding. Changed initialization paths or representations must
fail that comparison; a missing required byte-initialization fact also fails
structural reconstruction.

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

Native entry construction must lend its Core builder the caller's cumulative
final-elaboration meter. A builder's separate default allowance omitted paid
interpreter payload admission from that caller's ledger. The phase boundary now
restores the builder meter after both success and refusal; exact and one-short
cuts retain the caller's prior charges and fresh retries use a fresh caller.

The product resource header has its own Surface and resolved carriers. They retain
the explicit owned selector, complete Type/Row actuals, private data and lifecycle
codecs, ordered native interpretations and lifecycle patterns. The experimental
header remains a separate comparison carrier. Body-free publication retains the
original header allocation; parsing and a published header grant no executable
resource permission.

Dependency-free owner ABI preparation uses mutually exclusive scalar/acquire/
teardown call variants and tagged owner arguments. Original library member
coordinates and assumption spans survive preparation, restoration and exact
correspondence. Each symbol is normalized once; teardown checks borrow those
prepared facts. Byte owners require an initialized extent; opaque acquisition
need not declare one. An authored initialization fact remains a foreign promise,
not a consequence of its address representation or non-nullness.

Private owner restoration checks flat phase, coordinate, tag and span consistency.
It cannot recheck a source path's leaf type without the original signature; exact
correspondence authenticates the retained path, and canonical source binding
authenticates its leaf type. The executable scalar path explicitly refuses owner,
current-state and address facts. Scalar members of a library containing owners
use that same scalar path; the library's name supplies no ownership permission.

Original resource acquisition, completion and handler forests are checked once
per defining occurrence. A prepared instance owns its selected template, complete
arguments and substitutions through initializer checking into body admission.
This avoids computing those facts again after the initializer. Phase checking
lends the caller's remaining work and restores setup and builder charges on both
success and refusal; it also takes and restores one base context instead of
cloning it for each forest.

Source instance arguments retain the ordinary expected-row qualification before
entering the complete substitution. Independent evidence checking derives the
same preceding equation row; qualifying only its temporary validation copy would
leave retained rigid-row exclusion facts inconsistent with the checked instance.

Each original forest needs its own resolver-binder reservation before generated
binders are allocated. Rewalking the whole module for each reservation introduced
`1 + 3R` inventories for `R` resources, including an unused initial reservation.
Source template preparation now pays for one iterative module inventory and
reuses its immutable identities for each forest's fallible, collision-checked
reservation. Independent final validation remains a separate obligation.

The first executable resource checkpoint admits dependency-free opaque state,
one acquisition and a single-Current-operand void teardown, the exact `scope`
codec, private independent data and one Unit-domain associated operation. Client
code requests that operation directly. The checkpoint refuses nonempty residual
client rows, phase-local ordinary helper calls and provider `given` forwarding.
Native bytes, windows, dependent owners, outward control, retained completion and
library migrations remain required work. These are implementation boundaries,
not amendments to CP-0022.

A public source resource currently needs a public provider interface. Retaining
an interface declared privately in the same module as a hidden resource-header
dependency is not connected to the shared export closure yet. An imported hidden
interface dependency has a different existing retention route; matching names
cannot substitute for either route.

Constructor-free native state needs its own authenticated nominal category at
publication, import, linking and linked-evidence boundaries. State-only imports
retain the exact original owner declaration and formals, without selecting native
operations.
Resource headers also contribute their provider interface to the existing hidden
signature dependency closure; a facade does not need to export that interface's
spelling. Source resource parameters and the result binder belong to the exact
linked canonical-variable inventory.

Defining experimental registries retain abstract family metadata before their
separate checked provider certificates are attached during linking. Category
coverage at that boundary must first authenticate the original code and defining
export certificate, then count only their exact family identities alongside
source resource and native owner categories. Closed registry validation still
requires its attached certificates, complete canonical formals and linked native
closure. Applying the closed check prematurely rejected existing SQLite, arena
and provider-helper programs before independent Core validation.

A defining registry omits imported nominal dependencies that its closed checking
view retains. An imported opaque category can be reconstructed only in the view
that actually contains it. Final linked and restored Core must still reconstruct
every selected native codec independently; an immutable source receipt does not
replace that consuming check.

Capture projection must check the actual constructor identity before exposing
its payload. Conflating `Finish.Retained(State, E)` with `ConsumedFailure(E)` made
an independent completion error retain native state. Constructor identity changes
must also wake the projection's existing dependency equation.

Ordinary callable state restrictions apply to unused equational definitions as
well as anonymous functions and call occurrences. Independent Core needs the same
restriction, while admitting only the exact synthetic original lifecycle
wrappers. A separate source-resource capture conversion frame also preserves the
existing small-stack witness; its overflow occurred on the first ordinary node,
before any deep traversal.

The existing 256 KiB owned-cleanup witness also reached a larger source-checking
dispatcher frame before the evaluator ran. Source-resource body and completion
branches now pass their existing boxed phase carriers to separate non-inlined
helpers, keeping their local values outside unrelated expression-dispatch calls.
The branch order, guards, allocations and paid work remain the same; the witness
retains its predecessor stack bound.

Owned substitution maps must dispose displaced types iteratively. Temporary
argument and handler buffers transfer their contents through consuming,
infallible owner methods; exposing raw backing moves can leave a later error
path responsible for recursive disposal. The architecture carrier inventory
also covers named aliases introduced for shared checked-code maps and borrowed
Core image views. These repairs preserve traversal charges and fallible reserves.

Product resource instances now install checked lexical forwarding for their
associated methods. Linked evidence authenticates the exact original source
header and complete actuals, and places the fresh identity only in the body
scope. Experimental provider certificates do not grant product authority.
Passive source declarations remain admissible without executing a resource.
Associated methods' exact effectful value types select the existing Effect
carrier even when the ordinary entry has an empty row.

Header input and private data walks must prepay owner-candidate lookup on the
same cumulative validation meter. An ordinary nominal can require inspecting
the entire passive owner table; charging only its type node omits work that
grows with both payload width and owner count. Original and reconstructed
headers use the same admission check and retain the existing work limit.

The accepted pure scalar preflight functions reuse `Foreign.Call<Int>` and
preserve the input mathematical integer on success. Their canonical immutable
facts travel on the existing selected-global publication route; a facade retains
the hidden `Call` constructor family needed for independent checking without
adding source name routes or exposing `ConversionError` constructors. Shared
image annotation arenas require checking the five reachable provenance nodes
from their root, rather than requiring a five-node whole arena. Lifecycle flow
tracks these pure checks as identity-independent results; it does not enumerate
both ordinary result variants for every independent field check.
Original template structural validation borrows only those authenticated scalar
global facts; final executable graphs still require ordinary binder closure.

The full workspace gate exposed an unnecessary second scan of every published
global while collecting scalar result-codec dependencies. It charged ordinary
modules with no scalar facts and broke two exact freeze-budget regressions.
The existing paid publication walk now stages only actual codec owner IDs with
fallible storage. The later constructor closure consumes those IDs in source
order, preserving original facts, hidden-family authentication and existing
seed ordering. Ordinary globals incur no additional charge or allocation;
neither work limits nor regression expectations changed.

Matching an unknown scalar result beside current state exposed a skipped-arm
owner-flow defect: the first possible arm could hide a later `Consumed` report
without teardown. Symbolic patterns now distinguish possible from definite
matches. Only a definite match stops the arm walk; the public pipeline rejects
the mixed scalar/state counterexample without enumerating scalar variant products.

Ordinary source does not currently spell negative numeric literals, and source
foreign constants remain unimplemented. Boundary evidence obtains negative
integers through the existing owner-free scalar reply path. Image fixtures use
ordinary mathematical arithmetic on admitted i64 literal payloads for larger
values, preserving the private image's existing literal limitation.

## Deviations

None authorized. Return concrete semantic gaps to CP-0022 instead of resolving
them locally. Keep excluded features outside this task.
