# DN-0038: Resource Properties and Mutable Variable Usage

- ID: `DN-0038`
- Status: exploring
- Related: [DN-0013](DN-0013-session-and-resource-protocol-stress-tests.md),
  [DN-0031](DN-0031-resource-composition-concept-map.md),
  [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md),
  [DN-0034](DN-0034-one-shot-kernel-soundness-and-practicality.md),
  [DN-0035](DN-0035-region-memory-management-and-verified-providers.md),
  [DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md),
  [DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This design note maps candidate resource properties and mutable-variable
> usage. It defines no current Ash semantics, selects no surface syntax or
> checking architecture, and authorizes no implementation. It is separate from
> DN-0036's ongoing experiments and does not add completion requirements to them.

## Question

How should resource contracts describe linear, affine and unlimited usage,
uniqueness, mutation, borrowing, lifetime and completion? Can convenient mutable
bindings elaborate to checked resource operations while preserving these
properties through calls, closures, branches and effect handlers?

Compare semantics, Core representations, proof obligations and surface forms
before choosing a design. Evaluate utility and memory/performance opportunities
alongside soundness, checking cost and annotation burden. A useful property can
justify an optimization without selecting its implementation in advance.

Always follow the types. Identify what a value represents, which operations
consume it, what those operations return, and what authority survives before
proposing a spelling for a resource or mutable binding.

## Context

The [current cell contract](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
separates a scope-owned release obligation from a duplicable non-owning handle.
Its operations read and write integers. Aliases and repeated calls through
capturing closures are admitted within the owner's lifetime. Reading copies an
integer; it neither consumes the handle nor proves unique access.

Current [effect checking](../../spec/static-semantics.md#effects) consumes each
hidden resume capability once on every normally completing clause path. That
capability is not a general source value. Ordinary values remain duplicable
subject to resource dependencies. General linear/affine value types, uniqueness
types and borrow qualifiers are proposed directions, not current Ash.

[DN-0013](DN-0013-session-and-resource-protocol-stress-tests.md#keep-usage-properties-independent)
already distinguishes usage from alias authority and asks where restrictions
belong. [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md#computation-and-usage-kernel)
explores transforming ownership/protocol contexts without copying them.
[DN-0035](DN-0035-region-memory-management-and-verified-providers.md#reusable-values-heap-storage-and-restricted-authority)
separates storage, reusable access and ownership, including borrowing pressure.
The mutable-variable case gives those directions a concrete comparison.

## Constraints

- Linearity means exactly one use of a linear value. Repeated operations require
  distinct successor values or another separately justified access mechanism.
- Affinity means at most one use. It permits discard but does not, by itself,
  specify destruction or prove uniqueness.
- Unlimited use imposes no static upper bound on uses. The unrestricted form
  permits both duplication and discard; whether discard is allowed remains an
  independent property.
- Uniqueness concerns usable aliases and authority over storage. It does not
  specify an exactly-once use count.
- Keep the usage of an owner, an access value and the stored payload separate.
  A reusable handle does not duplicate its owner's completion obligation.
- Preserve current shared cell behavior as a comparison case. A future unique
  or linear resource does not silently change existing cell contracts.
- Surface syntax may infer identities and thread values, but cannot create
  duplication, discard, borrowing or completion authority.
- The initial comparison concerns synchronous operations and scoped resources.
  It does not introduce owner transport, arena-owner packages, concurrent
  mutation, callbacks, asynchronous execution or a new memory collector.
- Concurrency and process implementation are outside this study. Sharing means
  aliases within an ownership domain. Record consequences for future processes
  without introducing scheduling, cross-process sharing or `Send`/`Sync`-like
  properties. Sequential effect-handler reentrancy remains in scope.
- Exactly-once checking does not prove termination or eventual release under
  divergence or external termination.

## Candidate directions

### Property map

| Property | Question answered | Consequence to check |
| --- | --- | --- |
| Usage | Is use exactly once, at most once or unlimited, and may the value be discarded? | Uses, transfers, fields and captures preserve its permissions. |
| Uniqueness and alias authority | Which references may access the same storage? | No incompatible usable alias coexists with claimed unique authority. |
| Mutability | Which operations may change state? | An operation requires the corresponding access permission. |
| Borrowing | Which temporary permissions are granted and suspended? | Conflicting access remains unavailable for the complete borrow interval. |
| Identity and lifetime | Which acquisition does access depend on, and when is it valid? | Aliases, stored values, closures and requests cannot outlive required owners. |
| Protocol state | Which operation is legal next? | An operation returns the stated successor state; stale state cannot authorize use. |
| Payload discipline | May contents be copied, removed or discarded? | Read, replace, take and completion account for the actual payload. |
| Completion | Who must complete the resource, with what effects and outcomes? | Required completion is neither lost nor duplicated; failure preserves the stated authority. |
| Storage policy | Where is data held and how is its storage reclaimed? | Physical reuse or reclamation preserves all other contracts. |

Usage, uniqueness and storage are separate axes even when a particular resource
requires them together. For example, a shared handle can be unrestricted while
the scope has one completion obligation; a linear state token can authorize
updates to the same physical allocation through a sequence of successor values.

### Usage permissions

| Logical discipline | Contraction: duplicate | Weakening: discard | Usage obligation |
| --- | --- | --- | --- |
| Linear | No | No | Exactly one use. |
| Affine | No | Yes | At most one use. |
| Relevant | Yes | No | At least one use; duplication allowed. |
| Unrestricted: unlimited use | Yes | Yes | Zero, one or arbitrarily many uses; no static upper bound. |

This table records logical possibilities, not four required Ash features. A
candidate must state whether permissions attach to types, bindings, parameters,
arrows, captures or resource obligations, and how they propagate. A name such
as `LinearCell` cannot supply the checking rule by itself.

Unlimited use must be an explicit comparison case, not an accidental default or
an unexamined consequence of ordinary function arrows. It permits repeated
access through aliases and closures when their access and lifetime contracts
allow it. It does not copy physical storage, duplicate completion authority or
establish unique access. A unique-access candidate may also permit unlimited
operations while preserving its alias invariant.

Unlimited use and unrestricted use are not identical statements: the former
sets no upper bound, while the latter also permits discard. The relevant row
illustrates unlimited duplication with a requirement to use the value. No
quantitative qualifier spelling, such as `omega`, is selected by this map.

Moving a linear value to another binding consumes the previous binding; the new
binding carries the obligation onward. Completion is one possible consuming
operation. Passing a value to a function must respect that function's usage
contract rather than count only occurrences in the caller's source text.

Discard permission does not determine physical reclamation or effectful
destruction. An affine access value may disappear while a separate scope owner
still has to complete the resource. An affine surface owner with implicit
destruction would need an explicit elaboration and effect contract; that choice
remains open.

### Typed resource roles

| Role | Required meaning |
| --- | --- |
| Acquisition identity `R` | Fresh identity relating the instance, its effects, dependencies and completion. |
| Payload type `T` | The contents and their independently checked duplication/discard properties. |
| Protocol state `S` | A static description of legal operations, when the resource needs one. |
| Provider state | Private representation and authority needed to implement operations. |
| Client access | Non-owning shared access, an owned state value, or a scoped permission, as specified by the candidate. |
| Effect interface | Exact operation input/output types and effect requirements. |
| Usage and access contract | Consumption, successor values, alias rules and retained permissions for each operation. |
| Completion contract | Required consumption, payload disposal, ordering, effects and failure outcomes. |

Neither an effect signature nor an ordinary implementation declaration alone
establishes the usage or alias contract. The compiler must check its source
implementation or rely on an explicitly admitted primitive/foreign contract.
Public facts must retain enough information to check clients independently.

### Compare three mutable-resource models

| Candidate | Representation of access | Repeated mutation | Main evidence needed |
| --- | --- | --- | --- |
| Shared mutable access | Unrestricted non-owning handles with unlimited use; provider mediates operations. | Reuse the handle under its scope and operation contracts. | Alias behavior and completion agree with the declared semantics. |
| Linear state threading | Each current state/access value is linear. | Consume one value and receive its successor at each operation. | Old-value reuse, lost successors and duplicated captures reject. |
| Uniqueness checking | A checked unique reference or permission, with specified borrow/transfer rules. | Preserve uniqueness through repeated access or temporary loans. | Conflicting aliases, invalid loans and retained access reject. |

Current cells provide the first comparison. The other two require new checking
contracts. A hybrid may use linear permission tokens to implement a uniqueness
discipline, but must explain both properties separately. These are semantic
alternatives, not a selection of compiler representation.

### Linear operation contracts

For comparison, let `C<R,T,S>` denote a linear current-state value for one cell.
`R` is its acquisition identity, `T` its payload type, and `S` one of the nominal
states `Full` or `Empty`. Each input value is consumed once; a returned `C` is a
successor value with the same acquisition identity. It may reuse the physical
storage. Whether this value is source-visible or retained only in Core is open.

The following are schematic signatures, not accepted Ash syntax. `tensor` is a
pair whose components retain their usage properties; `-o` is a linear arrow.
Each operation also has its exact cell effect requirement, omitted here to
keep the usage relationship visible.

```text
read_copy : C<R,T,Full> -o (C<R,T,Full> tensor T)
replace   : (C<R,T,Full> tensor T) -o (C<R,T,Full> tensor T)
take      : C<R,T,Full> -o (C<R,T,Empty> tensor T)
put       : (C<R,T,Empty> tensor T) -o C<R,T,Full>
finish_empty : C<R,T,Empty> -o Unit
```

`read_copy` requires permission to duplicate `T`: one instance remains stored
and one is returned. `replace` consumes the incoming payload and returns the
previous payload alongside the successor cell. `take` moves the payload out;
`put` moves a payload into an empty cell. A read from `Empty` has no contract.

Completing a full cell must account for its payload. A consuming disposal
operation `dispose_T : T -o Unit ! delta` can contribute effects `delta` to
completion. Alternatively, an operation may return the payload while consuming
the cell. Neither freeing storage nor ignoring a successor disposes of a linear
payload. A `write` that returns no old payload requires a permitted discard or
checked disposal of that old payload.

These state indices apply to the linear candidate. A duplicable handle cannot
retain an authoritative `Full` index after another alias takes the contents
without an additional shared-state/access mechanism.

### Unique access contracts

A uniqueness candidate must identify what remains unique: the storage reference,
the mutation permission or another checked authority. It must specify whether
other references may exist but be unavailable during an exclusive operation.
Being non-duplicable alone does not establish that invariant.

For each operation, state its parameter mode: transfer authority, temporarily
borrow read access, temporarily borrow exclusive access, or use mediated shared
access. The contract gives the returned authority and any retained loan.
Repeated source uses are checked against that contract; they are not repeated
uses of one linear value unless successor threading explains them.

Borrow intervals must include captured control and retained foreign access when
applicable. A call boundary alone cannot end a loan that the called operation
retains. A one-shot continuation does not establish freedom from alias conflicts.

### Rust-like usage and lifetime regimes

Rust supplies a useful comparison of combined properties. The Ash column below
is an interpretation for this study, not a claim that Rust names or implements
these logical disciplines as Ash resource contracts.

| Rust mechanism | Usage, access or lifetime behavior | Ash correspondence or gap |
| --- | --- | --- |
| `T: Copy` | A value can be copied while its original remains usable. [Copy documentation](https://doc.rust-lang.org/std/marker/trait.Copy.html). | Candidate unlimited/unrestricted value use; copying does not duplicate resource ownership unless that is separately justified. |
| Owned non-`Copy` value | Moving consumes the previous binding; moving out deinitializes the place until refill. [Move rules](https://doc.rust-lang.org/reference/expressions.html#moved-and-copied-types). | Affine move behavior at the source level; mandatory exact use and required protocol completion are separate questions. |
| `&'a T` | Shared, copyable access constrained by a lifetime; interior mutability is an explicit exception to ordinary shared-reference mutation restrictions. [Reference types](https://doc.rust-lang.org/reference/types/pointer.html). | Unlimited borrowed access with a validity dependency, plus a separately stated shared-mutation policy. |
| `&'a mut T` | Non-copyable exclusive borrowed access; the referent has another owner. [Mutable references](https://doc.rust-lang.org/reference/types/pointer.html). | Affine access-value usage combined with unique access during the loan, not linear ownership of the referent. |
| Mutable place | Assignment and mutable borrowing require a mutable place. [Mutability rules](https://doc.rust-lang.org/reference/expressions.html#mutability). | Permission to update a binding or location remains distinct from payload usage and alias authority. |
| `FnOnce`, `FnMut`, `Fn` | Calls respectively consume the closure, borrow it mutably, or borrow it through shared access. Capturing by move alone does not determine the call mode. [Closure call traits](https://doc.rust-lang.org/reference/types/closure.html#call-traits-and-coercions). | Separate closure-value usage, call parameter mode and captured dependencies. Unlimited calls need not imply a copyable closure. |
| `Drop` and drop scopes | Initialized values are normally dropped on scope exit or overwrite. [Destructors](https://doc.rust-lang.org/reference/destructors.html). | Candidate implicit completion requires Ash's effects, ordering and outcome contracts; discard permission alone does not specify it. |

Reading the owned non-`Copy` row as affine is a usage interpretation: Rust
permits an owned binding to receive no explicit source use and be dropped.
Moreover, safe `mem::forget` can suppress destruction, so Rust cleanup cannot
stand in for an Ash contract requiring a particular completion operation.
[Forget documentation](https://doc.rust-lang.org/std/mem/fn.forget.html#safety).
Exactly-once value use and required resource completion remain separate even
when one operation discharges both.

This comparison does not adopt Rust's syntax, compiler, allocation strategy or
every borrowing rule. It identifies combinations to express and test. Shared
interior mutation remains a separate provider/access policy; it does not gain
exclusive access merely because a handle is affine.

### Lifetime alternatives

Keep an acquisition identity, storage lifetime, borrow interval and completion
point distinct. Rust reference lifetimes describe validity constraints, and
inferred live borrows can end before their lexical binding scope ends.
[Borrowing examples](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html).
Rust also elides signature lifetimes when its rules determine them; ambiguous
relationships need explicit information.
[Lifetime elision](https://doc.rust-lang.org/reference/lifetime-elision.html).

| Candidate lifetime regime | Meaning to specify | Utility and cost to compare |
| --- | --- | --- |
| Owner scope dependencies | Access remains valid within the owning acquisition; no general loan endpoint. | Reuse the current scoped-resource boundary, while recording cases needing finer conflict control. |
| Lexical loan scopes | An explicit nested interval grants access and suspends incompatible permissions until its checked exit. | Simple endpoint and proof structure; may reject safe programs or retain restrictions longer than needed. |
| Inferred live loans | Branches, calls and actual retained uses determine endpoints finer than textual scope. | Less annotation and earlier permission recovery; requires additional flow, capture and failure analysis. |
| Public lifetime relationships | A signature relates returned/stored access to its inputs and required owners. | Independent client checking without exposing bodies; requires a precise contract and inference boundary. |

These regimes can combine rather than replace one another. An owner may remain
live across many shorter loans; ending a loan need not release its storage.
An inferred last use must include destructor access, closure invocation,
captured control and foreign retention where their contracts require it.
Completion remains checked even when every ordinary read has finished.

Public borrowing contracts must identify the owner and valid interval of any
returned access, permission recovery and outlives requirements. Whether Ash
represents those relationships through inferred dependencies, indices or another
checked form remains open. No Rust lifetime spelling or new Ash kind is selected.

### Surface forms derived from the contracts

The illustrative spelling below represents an integer mutable binding. It does
not select a keyword, assignment operator or grammar:

```text
var x : Int = 41
x := x + 1
x
```

Acquisition checks the initializer before introducing the fresh identity and
binding. For the linear candidate it introduces `x0 : C<R,Int,Full>`. The body
can elaborate schematically as follows, using the operation contracts above:

```text
let (x1, n) = read_copy x0
let (x2, old) = replace (x1, n + 1)
let _ = old
let (x3, result) = read_copy x2
(x3, result)
```

Each cell value is used once. Integers permit copying and discard. The final
pair is an internal body result: the resource boundary consumes `x3` through
the completion contract and returns the independent integer. It must not both
insert this completion and schedule a second completion of the same authority.
The scope and its current state need an explicit account for owned abandonment
as well as this normal path.

The source binding can support unlimited reads and updates without treating
`x0` as unlimited. Each evaluation threads its current successor; a loop or
recursive helper must do the same. Unlimited source operations and linear Core
values are different levels of the elaboration contract.

The uniqueness candidate can present the same surface example while elaborating
to permission-checked access and updates. Its Core must retain the unique/borrow
facts that justify those operations. Comparing the two requires equivalent
observations, evaluation order and completion, not identical Core nodes.

For a linear payload, plain expression use cannot silently copy it. Assignment
cannot silently discard the previous contents. The surface must distinguish
copy, move/take, borrow and replace where the contracts require that distinction;
inference can remove annotations only when it establishes the intended action.

The first surface comparison uses simple bindings. General assignment places,
field updates and compound assignment need separate evaluation-order and alias
contracts. No example licenses repeated evaluation of an effectful operand,
implicit deep copying or movement of storage between lifetimes.

### Composition and inference

| Boundary | Required account |
| --- | --- |
| Branches | Each normally completing arm accounts for incoming authority; the join receives compatible successors or an explicit branch-dependent result. |
| Recursion or loops | Thread the current successor or preserve the declared unique-access invariant at each iteration and exit. |
| Tuples and constructors | Wrapping a restricted value preserves its restrictions; independent duplicable fields can still be projected safely. |
| Closures | Capturing owned linear authority restricts use of that closure value. Capturing scoped mediated access may permit repeated calls under a checked call contract. |
| Generalization and imports | Polymorphism and body-free public contracts preserve usage, access, effects and dependency facts. |
| Effect requests and handlers | Operands and captured control preserve the authority they carry; handler substitution cannot fabricate a successor or conflicting access. |
| Completion and failure | Normal return, owned discard, partial acquisition and fallible completion each account for current authority and payloads. |

Infer local successor flow, effects, actual captures and structural usage
consequences from checked declarations and bodies. Explicitly specify public
parameter modes, allowed aliasing, foreign retention/invalidation and completion
behavior where bodies cannot establish them. Decide the annotation boundary
from concrete ambiguous cases rather than requiring every local use to be marked.

### Process implications as future pressure

Memory disciplines will constrain a later process design even while Ash remains
sequential. Record the facts a future design would need, without defining
processes, communication or concurrency here. The shared-nothing direction and
exclusion of transportable arena-owner packages remain the design boundary.

| Memory fact to establish now | Consequence to retain for later process work |
| --- | --- |
| Copying can duplicate access rather than independent data. | A future communication contract must distinguish copied references from independent payloads. |
| Sharing preserves common storage and lifetime dependencies. | Sharing within one domain does not establish permission to share across domains. |
| Uniqueness excludes specified conflicting aliases. | Uniqueness alone does not prove that storage, foreign handles or dependent values can cross a process boundary. |
| A move transfers authority within its checked lifetime contract. | Moving a binding is not automatically transport of its allocation or owning scope. |
| An arena bounds the lifetime of its dependent allocations. | It may inform a later process-heap discipline; this study keeps owners scoped and nontransportable. |
| Completion has payload, ordering, effect and failure obligations. | Later process termination rules must account for those obligations; none is selected here. |

The present alias and loan proofs concern sequential execution, including
effects and retained control. They establish no race-freedom or synchronization
contract for hypothetical concurrent use. Memory optimization measurements
likewise concern sequential programs, not a process scheduler.

### Semantic and Core comparison

Decide the source contract and its Core encoding separately. For example,
uniqueness at the source may be implemented through linear Core permissions;
that would need both an alias invariant and an exactly-once token account.

| Option | Source semantics | Candidate Core account | Surface consequence |
| --- | --- | --- | --- |
| Shared mediated access | Unlimited handle use within the owner; mutations follow the provider's shared-access contract. | Handle, exact requests and scope-owned completion, with retained dependencies. | Reads and assignment request operations; sharing remains explicit in the resource contract. |
| Linear state threading | Each current resource value is used once; operations return successors. | Typed successor values, consumption/flow facts, protocol states and completion. | Named successors or mutable sugar that threads them without copying or silently dropping payloads. |
| Unique access and borrowing | Transfer and loans preserve a specified alias invariant; compatible operations can repeat. | Unique-access facts, loan grants/recovery and retained dependencies/control obligations. | Borrowing and assignment infer temporary permissions where the call and lifetime contracts permit. |
| Unique source with linear Core permissions | Unique/borrowed source access as above. | Linear permission succession encoding the source invariant, plus explicit loan relationships. | Source may retain convenient bindings while Core makes authority succession explicit. |

The hybrid is an encoding comparison, not a fourth independent usage discipline.
None of these rows selects a new node family or permits using an unchecked side
table as authority. Derive types, rows, public contracts, source origins and
independent validation before choosing the concrete representation. Compare
using existing Core forms with retaining new facts or semantic nodes only where
the contract requires them.

### Proof obligations

These are proposed obligations, not proved results. A candidate first needs a
precise admitted fragment, primitive contracts, observations and operational
rules. Follow [DN-0034](DN-0034-one-shot-kernel-soundness-and-practicality.md):
proofs about a model and correspondence with implemented Core/runtime are
separate claims. Existing one-shot results transfer only under their premises.

| Boundary | Common obligation | Candidate-specific part |
| --- | --- | --- |
| Typing and execution | Preservation of types, effects, dependencies and valid protocol states at each transition. | Linear successor consumption or unique/loan permission preservation. |
| Use accounting | No unsupported contraction or weakening through calls, wrappers, captures or generalization. | Linear values are used once; affine elimination and unlimited use follow their own contracts. |
| Aliases and lifetime | Every admitted access targets valid storage with the required permission. | Unique candidates exclude conflicting usable aliases; loan endpoints include retained uses and control. |
| Progress and failure | An admitted operation has a lawful next step or declared failure outcome, under stated native assumptions. | No empty read, stale-state reuse or unaccounted consumed/refused authority. |
| Completion | Required normal/owned-abandonment completion is neither duplicated nor lost, with valid payload handling and order. | Dropped access does not erase its owner; taking contents changes what completion must consume. |
| Elaboration | Surface evaluation and its Core translation preserve the selected observations. | Assignment, implicit loans, successor threading and cleanup preserve order and ownership. |
| Validation and transforms | Independent validation checks the retained contract; each transform preserves it and observations. | Changed nodes/calls cannot reuse stale consumption, loan or provenance evidence. |
| Runtime correspondence | Validated Core and the evaluator agree on state, access, results and failure/completion. | Token representation or permission metadata corresponds to the actual provider/native state. |

Observations include results, failure, dispatchable requests, completion order
and any accounting exposed by the provider. The same returned integer alone
does not establish equivalence. A theorem about exactly-once use does not prove
uniqueness, termination, correct foreign behavior or required completion unless
those premises and conclusions are also present.

### Memory and performance opportunities

| Opportunity | Required evidence before optimization | Cost or limit to measure |
| --- | --- | --- |
| Destructive update and storage reuse | A checked access/protocol contract excludes incompatible observers and preserves retained views and payload obligations. | Avoided allocations/copies versus permission and bookkeeping cost. |
| Local cell elimination or scalar replacement | Equivalent execution without the storage or request machinery; identity, intercepted operations, failure and completion remain consistent. | Runtime work, retained Core metadata and observable provider accounting. |
| Avoiding payload copies | Ownership transfer or borrowing supplies every required validity and independence property. | Copied bytes, peak storage, retained storage and rejected useful programs. |
| Earlier permission recovery or reclamation | All relevant uses, including cleanup and captured/foreign access, are accounted for. Ending a loan alone does not authorize release. | Peak live storage versus inference work and completion effects. |
| Removing dynamic access checks | Static evidence discharges the actual primitive's access assumptions. | Runtime checks saved versus checking complexity; foreign assumptions remain explicit. |
| Fewer reference-count or barrier operations | A later storage policy provides them and the checked use/alias facts prove a corresponding optimization sound. | Policy-specific runtime savings; this does not add counting or tracing to the initial study. |

Linearity of a token alone does not prove uniqueness of every reachable payload.
A unique outer reference does not establish exclusive access to shared children.
Provider operations may expose allocation failure, capacity, usage or request
interception, so an apparent storage optimization must preserve that contract.
These are opportunities to investigate, not automatic benefits of a qualifier.

Measure annotation burden, diagnostic quality, checking time/work, Core and
retained-fact size, runtime overhead, allocations, copied bytes and peak memory.
The shared candidate may already optimize well through ordinary dependency
analysis; the stricter candidates must earn their additional complexity.

## Evidence and experiments

This note first asks for a typed comparison, not an implementation task. Before
any prototype, select its candidate contracts, named cases, Core obligations,
positive/negative outcomes and retention conditions. Do not reopen DN-0036's
selected native boundary to answer these questions.

| Case | Positive evidence | Nearby rejection or failure |
| --- | --- | --- |
| Repeated integer update | Convenient syntax elaborates to lawful successors or checked unique access. | An old linear state remains usable. |
| Unlimited access | Repeated reads/writes and reusable scoped closures have no static use-count bound under their access contract. | Unlimited access duplicates completion authority or bypasses a live exclusive loan. |
| Linear payload replacement | The previous payload is returned and consumed lawfully. | Read duplicates it or assignment discards it without authority. |
| Take and refill | An empty successor is refilled before reading. | A stale full-state value authorizes a read. |
| Affine access | Unused access is permitted while required scope completion remains accounted for. | Discard permission silently removes required completion. |
| Aliases | Shared mediated access or compatible loans follow their declared contract. | Affinity is accepted as proof that no conflicting alias exists. |
| Branch and loop | Successors and exit obligations remain coherent. | A branch loses authority or an iteration recreates an old state. |
| Closure capture | Owned authority and scoped access produce the appropriate call restrictions. | A tuple, closure or polymorphic binding restores duplication. |
| Handler capture | Resume preserves authority; admitted discard accounts for owned completion. | A surrounding handler performs conflicting access while a loan remains captured. |
| Loan endpoints and public contracts | Short loans permit later access, and returned access has independently checked owner/lifetime relationships. | A loan ends while a destructor, closure, handler or foreign operation can still use it. |
| Scope exit | Copied independent output survives; completion consumes the current resource once. | Access escapes, linear contents disappear or completion runs twice. |

Compare public types and contracts, annotation burden, diagnostics, Core size,
checking cost, native/storage observations and rejected useful programs. Under
[AD-0007](../decisions/AD-0007-typed-core-dialects.md), independent Core validation
must reconstruct usage/access obligations before and after transforms. Core
operational semantics must state state succession, alias permissions, payload
movement and completion before a product implementation is authorized.

For each case, compare the same operation and completion contract across the
candidates. First derive its types and operational rules, then its Core account
and proof obligations, then candidate surface forms. Use a bounded prototype
only when it answers a named unresolved question. Measure optimizations against
the unoptimized implementation of the same supported semantics; retain semantic
differences explicitly rather than attributing them to a faster representation.

Choose after this comparison. Record which properties become general language
mechanisms, which remain resource/provider policy, which Core encoding has the
required evidence, and which source defaults reduce friction without ambiguity.
A successful case need not imply one global discipline for every resource.

Retain coherent designs and reproducible counterexamples as evidence. Replace
or discard candidate machinery when the comparison justifies it. A successful
language change still needs a proposal, implementation, tests and matching
surface/Core specification updates; converged non-language architecture needs
a decision. This property map establishes neither adoption nor a merge gate.

## Open questions

- Where should usage permissions and uniqueness facts live in checked types,
  parameter contracts, captures and Core, and what can inference recover?
- Which resources expose successor values to library authors, and which can
  keep them internal to elaboration without weakening independent checking?
- Can one mutable surface serve both linear and unique candidates without
  ambiguity about copying, transfer, borrowing or disposal?
- How should unlimited-use contracts be expressed for values, access, arguments
  and captures while preserving independent discard and alias restrictions?
- Which contents support plain assignment, and when must the surface return or
  explicitly dispose of the previous value?
- How is the current state recovered for owned abandonment without duplicating
  or losing the authority threaded through the body?
- What minimum loan representation handles closures and effect capture without
  requiring broader borrowing machinery immediately?
- Which common proof interfaces cover both linear succession and uniqueness,
  and which obligations remain specific to one candidate or lifetime regime?
- Which optimization gains require these contracts, and which can current
  shared-resource analysis already establish at lower implementation cost?
- Which memory and dependency facts should later process design reuse without
  treating copyability, uniqueness or local moves as transport permission?
- Which concrete cases justify quantitative use counts, finer borrow endpoints
  or field-level places beyond this qualitative map?
