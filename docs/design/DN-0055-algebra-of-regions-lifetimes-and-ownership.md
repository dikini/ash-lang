# DN-0055: Algebra of Regions, Lifetimes, and Ownership

- ID: `DN-0055`
- Status: exploring
- Related: [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md),
  [DN-0035](DN-0035-region-memory-management-and-verified-providers.md),
  [DN-0054](DN-0054-base-lexical-region-memory-contracts.md),
  [DN-0053](DN-0053-scoped-generic-cells-without-native-owners.md),
  [DN-0051](DN-0051-userspace-concurrency-and-scheduling.md),
  [generic cell checkpoint](generic-cell/evidence.md),
  [DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md),
  [DN-0013](DN-0013-session-and-resource-protocol-stress-tests.md)

> This design note is informative. It records candidate definitions, elementary
> derivations, and open proof obligations. It defines no current Ash semantics,
> accepts no architecture, and authorizes no implementation or prototype. No
> complete algebraic soundness, memory-safety, or compiler-correctness theorem
> is claimed.

## Question

Can an algebra connect region placement and allocation with ownership,
lifetimes, and reclamation while keeping those concepts distinct? Which laws
follow from definitions, which depend on a region type or ownership scheme,
and which require a proof of observable program equivalence?

The target includes a shared base of constraints with protocol-dependent
variations. Each protocol specializes that base and must preserve it; it does
not waive shared validity, authority-provenance, or reclamation obligations.

The working candidate combines a lifetime order, placement facts, restricted
ownership contexts, and typed state transitions. Lexical scope is the first
ownership scheme; a fixed arena with bulk reclamation is the first storage
and reclamation composition.

A future comparison considers sequential processes communicating through
dedicated channels. It tests ownership across communication without requiring
shared mutable storage. It remains separate from the first sequential proof
model and defines no current concurrency facility.

## Context

The [specification](../../spec/README.md) governs current Ash. Its
[resource rules](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
track dependencies through values, captures, selected evidence, and operation
metadata. [Execution](../../spec/dynamic-semantics.md#scoped-cell-execution)
separates non-owning access from scope-owned completion. Capture and resume
move the same owner; checked discard completes owned abandoned scopes.
These are constraints on a future region algebra, not a general implemented
region interface or a proof of this candidate.

[DN-0032](DN-0032-algebra-of-scoped-resource-composition.md) derives bounded
sequencing and context-composition laws, with conditional scope movement and
counterexamples. Its context product and lifetime envelope do not merge storage
regions, select their allocators, or transfer their ownership.

[DN-0035](DN-0035-region-memory-management-and-verified-providers.md) and
[DN-0054](DN-0054-base-lexical-region-memory-contracts.md) record the direction:

- Regions provide placement and allocation.
- An ownership scheme determines who owns a region and its lifetime. Lexical
  scope is the first scheme, among other possible schemes.
- Region ownership includes its allocated objects. Valid object use requires
  the region to remain valid; choosing storage cannot shorten a required use.
- Region types may specify different object reclamation policies. Individual
  objects may be reclaimed earlier; reclaiming the region reclaims all
  remaining objects en masse, after required completion.
- Mutation and access permissions remain separate. A cell can use region
  storage without placement determining its logical access lifetime.

The [generic cell checkpoint](generic-cell/evidence.md) is implemented and
integrated into local Main; its original accepted proposal is retained in Git
history. Its strict retained-payload dependencies and resource-scope cell lifetime
remain constraints. This note changes neither current cells nor their evidence.

DN-0035's [later process comparison](DN-0035-region-memory-management-and-verified-providers.md#later-process-ownership)
starts with isolated storage and requires transport to establish receiver-owned
data. [DN-0051](DN-0051-userspace-concurrency-and-scheduling.md) separates task
ownership, suspension, and parallel sharing contracts. Neither supplies an
implemented channel or proof of safe message transport. Their distinction
between copying, sharing, and ownership transfer governs the comparison below.

[DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md) separates
operation permissions, alias authority, value usage, and completion. Current
cells permit mediated reads and writes through reusable aliases; their scope
owns release. The polarity comparison below proposes additional access facts,
not a reinterpretation of those handles as exclusive references.

## Constraints

- Begin with a sequential execution model and lexical ownership. Include
  suspended owned continuations; inactivity does not end their lifetimes.
- Separate usable lifetime, resident object storage, and backing protection.
  Source completion need not establish physical reclamation.
- Preserve region and object identities through aliasing. Model names do not
  imply source-visible addresses, runtime registries, or heap inspection.
- Keep completion authority distinct from reusable access. Copying a handle
  must not create another owner or another permission to reclaim storage.
- Distinguish ordinary object-reference graphs, which may be cyclic, from
  resource-owner dependency graphs constrained by the ownership scheme.
- Preserve request-payload boundaries and checked construction authority.
  Lifetime inequalities alone cannot authorize an outward payload transfer.
- Account for allocation failure, partial construction, retained backing,
  cleanup, and observable operation order before claiming execution laws.
- Separate common preservation constraints from protocol-specific ownership
  construction, access compatibility, lifetime schemes, and completion rules.
  Do not promote one protocol's exclusion or phase rule into a base axiom.
- Keep other ownership schemes, owner transport, moving collection, concurrency,
  implicit construction lowering, and source proof syntax outside the first
  proof model. The channel comparison below explores additional obligations;
  it does not enlarge that model's established evidence or authorize execution.

## Candidate directions

### Comparison and working choice

| Approach | Useful property | Limit |
| --- | --- | --- |
| Lifetime constraints alone | Express outlives relations and bounds on use. | Do not establish placement, reclamation authority, initialization, or required completion. |
| Typed transitions with lifetime and ownership contexts | State how allocation and management preserve validity; reuse bounded sequencing arguments. | Need a precise state, operation premises, and a preservation proof. |
| A general permission algebra for every ownership scheme | Could expose common structure across later schemes. | Premature before a second scheme supplies concrete obligations and contrary cases. |

Use the second approach first, with the lifetime order as one component.
Extend its ownership rules only when another named scheme supplies a contract.
This is a working choice for exploration, not an accepted architecture.

### Base constraints and protocol variations

Use a shared base of constraints and explicit protocol-dependent refinements.
The following is a candidate base to test against the comparisons in this
note, not a proved minimal, independent, or complete axiom set:

| Candidate base constraint | Protocol-dependent variation |
| --- | --- |
| Ownership and authority facts have a justified construction or transition origin. Aliasing a name or observing an operation does not create them. | How storage and polarity ownership are established, partitioned, shared, borrowed, delegated, transferred, or recombined. |
| Every admitted use is covered by its required authority, usable validity, backing protection, and actual retained dependencies. | Lexical ownership, transportable regions, read leases, task or channel support, and the extents of their lifetimes. |
| Operations preserve admitted representation, initialization, payload, and access invariants. | Compatible reader/writer configurations, simultaneous or alternating access, publication, atomics, locks, or other mediation. |
| Facts remain attached to the correct identities, actors, footprints, and operation extents. Ownership or access authority is not inferred solely from equal lifetimes or shared placement. | Which actors own which polarities, which grants coexist, and whether a protocol uses changing phases. |
| Declared ownership and completion obligations remain accounted for through every transition. Nonduplicable authority is not duplicated; required completion is not lost. | Unique, joint, or otherwise specified polarity ownership; closure, cancellation, failure, return, and completion policies. |
| Reclamation cannot invalidate an admitted use or required completion. Reclaiming a region releases all remaining resident objects collectively. | Early object collection, bulk-only reclamation, lease settlement, draining, deferred reclamation, and retained backing. |
| An operation respects the layout, execution-domain, and visibility constraints applicable to its support. | Required alignment, affinity, memory-order guarantees, backing policy, and locality preferences. |

The base constrains the relationship between storage and polarity ownership
without equating them. A region's owner owns its resident object storage, while
other actors may own the read and write polarities. Their rules must jointly
preserve the required uses of the objects. The base does not impose one reader,
one writer, exclusive mutation, alternating phases, or lexical lifetime equality
for every ownership scheme.

For protocol `Pi`, write `B(S)` for the common state constraints and `V_Pi(S)`
for its additional invariant, including any instantiation of shared parameters.
Its well-formed states satisfy:

```text
WellFormed_Pi(S) = B(S) and V_Pi(S)
```

The protocol supplies its establishment and transition rules. Establishment
must produce a well-formed state from justified input authority and support.
For every admitted step from `S` to `S_after`, the preservation obligation is:

```text
WellFormed_Pi(S) implies WellFormed_Pi(S_after)
```

This implication is a proof target conditional on the particular admitted
transition and its premises, not a claim that every state change is valid.
Include failure, partial construction, cancellation, closure, and deferred
completion steps; committed effects need not roll back. Protocol refinements
may strengthen or instantiate the base but cannot waive its guarantees.

For example, one access protocol can permit overlapping read and write polarity
owners and another can require alternating producer and consumer access. Both
must keep each admitted access authorized, its dependencies valid, and its
storage protected. Those preservation constraints are common; exclusion and
phase choices are protocol variations.

Composition requires more than independently valid protocols. State the mapping
of shared storage, polarities, grants, and obligations. Show that local steps
and cross-protocol handoffs preserve the combined constraints. A channel that
allows retained reads and a pool that reuses bytes immediately on receipt have
incompatible assumptions unless their composition establishes another admitted
handoff or lifetime contract. Conjoining invariant names is not that proof.

Progress, fairness, eventual completion, and quantitative bounds require their
own protocol and execution assumptions. State preservation alone establishes
none of them. Further comparisons may reveal missing or redundant base
constraints; record that evidence before treating a candidate as a common law.

### Process-calculus and Links comparisons

Primary sources checked on 2026-10-19 supply comparison techniques and known
boundaries. This is a focused reading map, not a complete literature review or
an adoption of their calculi. The interpretations for Ash in the last column
are proposed transfer questions, not results established by the cited work.

| Source | Relevant treatment | Transfer question and boundary for Ash |
| --- | --- | --- |
| [CSP semantic models and refinement assertions, FDR documentation](https://cocotec.io/fdr/manual/cspm/definitions.html) | Distinguishes traces, failures, and failures-divergences models; deadlock assertions use the latter two rather than traces alone. | Choose observations before claiming behavioral refinement or equivalence. Well-formed ownership states alone cannot distinguish refusal, deadlock, or internal divergence. |
| [Milner, Parrow, and Walker: A Calculus of Mobile Processes, II, section 1](https://www.pure.ed.ac.uk/ws/portalfiles/portal/16426068/A_Calculus_of_Mobile_Processes_II.pdf) | Bound-name output and scope closing account for scope extrusion, retaining the private name while expanding its scope under freshness conditions. | Relate identity and endpoint transport across actors. Moving a name's binding scope is not permission to extend a region lifetime, move backing, or change completion ownership. |
| [Pierce and Sangiorgi: Typing and Subtyping for Mobile Processes](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/abs/typing-and-subtyping-for-mobile-processes/66AE6A341BAA19D1C6C5422759622C77) | Distinguishes channel input, output, and combined capabilities, with a corresponding subtype relation. | Compare the representation and restriction of read/write polarity authority. Mapping a channel capability to Ash polarity ownership still needs construction, usage, lifetime, and storage relations. |
| [Giunti and Vasconcelos: Linearity, Session Types and the Pi Calculus](https://doi.org/10.1017/S0960129514000176) | Describes both ends of a single channel in a type constructor, uses session types for individual ends, and distributes their descriptions through typing-context splitting. Compares polarized-variable, accept/request, and linear pi calculi. | Study explicit complementary authority and its distribution without requiring different runtime objects for the ends. The paper's typing and operational correspondences do not establish ownership of Ash backing regions. |
| [de Vries, Francalanza, and Hennessy: Uniqueness Typing for Resource Management in Message-Passing Concurrency, sections 2 and 3](https://staff.um.edu.mt/afra1/papers/res-pi.pdf) | Extends pi-calculus with channel allocation and deallocation. Combines affine usage with uniqueness, including splitting a unique assumption into affine access and a delayed uniqueness guarantee. Unique whole-channel authority permits type revision and deallocation. | Compare temporary delegation and recovery of exclusive authority. This paper's whole-channel uniqueness is stronger than uniqueness of one polar endpoint; transferring its rules to complementary endpoints and Ash regions needs a separate argument. |
| [Igarashi and Kobayashi: A Generic Type System for the Pi-Calculus](https://www-kb.is.s.u-tokyo.ac.jp/~koba/papers/generic-pi-full.pdf) | Uses abstract processes as types and environments in a generic framework; specialized instances can establish properties such as race or deadlock freedom while reusing preservation machinery. | Study the generic proof assumptions and instance obligations as a precedent for the shared base plus protocol variations. Their parameters and process semantics do not already establish Ash's memory or region constraints. |
| [Lindley and Morris: Lightweight Functional Session Types](https://homepages.inf.ed.ac.uk/slindley/papers/fst.pdf) | Combines session types, linear and unlimited usage, row polymorphism, and subkinding, with a Links implementation. Explicitly distinguishes usage linearity from alias freedom; sections 1.1 and 1.4 distinguish guarantees after adding recursion or access points. | Compare inference and environment splitting while keeping polarity ownership, alias authority, and storage ownership distinct. Record which guarantees depend on the chosen fragment. |
| [Fowler, Lindley, Morris, and Decova: Exceptional Asynchronous Session Types](https://homepages.inf.ed.ac.uk/slindley/papers/zap.pdf) | Gives explicit cancellation and asynchronous buffers, including delegated endpoints and closure dependencies. Section 4.2 preserves typing with access points while allowing cyclic topologies and losing deadlock freedom. | Require queued and captured authority to have a disposition on failure. Endpoint cancellation is not automatically Ash object disposal or region reclamation. The paper leaves general linear effect-handler formalization outside its scope. |
| [Tang, Hillerstrom, Lindley, and Morris: Soundly Handling Linearity](https://arxiv.org/pdf/2307.09383) | Tracks control-flow linearity to protect linear values captured by effectful continuations, with core safety arguments and a Links implementation. | Test ownership of polarities through capture, resume, and discard. Ash's current one-shot boundary remains the starting point; this comparison neither introduces multi-shot handlers nor transfers the paper's proofs to Ash. |

Ordinary pi-calculus has input/output action polarity and name mobility, but
does not impose an ownership handover merely because a name is sent. In a
schematic ordinary communication step, sending `a` on `c` substitutes it for
the receiver's bound name `x`:

```text
c<a>.P | c(x).Q  ->  P | Q{a/x}
```

The sender's continuation `P` may still use `a`; nothing in this rule consumes
its input or output authority. Thus name possession and scope can express
accessibility without separately tracking ownership of each polarity. I/O
capability typing restricts the directions available to the receiver. Linear
and session disciplines add rules for distributing, consuming, or delegating
authority; their particular context rules determine which rights the sender
may retain. This example explains the cited calculi, not Ash syntax or a new
Ash transition. Their polarity treatment must be examined at the chosen typed
variant rather than assumed to be an ownership discipline of plain pi-calculus.

Three further distinctions matter for the base constraints:

- State refinement by `B(S) and V_Pi(S)` differs from behavioral refinement in
  a chosen observation model. Connecting them requires a semantics and proof;
  invariant conjunction does not establish a CSP refinement result.
- Channel direction, endpoint usage, name scope, and ownership of backing are
  different facts. Endpoint transport must preserve the relevant relationships
  without treating name extrusion as physical storage lifetime extension.
- Session fidelity, alias freedom, deadlock freedom, and valid reclamation are
  different properties. The cited calculi establish particular combinations
  under particular assumptions, not a single guarantee attached to the phrase
  session typed. No result here establishes zero-copy, affinity, or allocator
  correctness for Ash.

Useful later stress cases include transporting one owned polarity while its
complement stays with another actor; cancelling a message carrying delegated
authority; and capturing a continuation that retains that authority. A shared
access-point comparison should test preservation separately from progress.
These extend beyond the first data-only dedicated-channel case and require
their own bounded assignment before executable work.

[DN-0013](DN-0013-session-and-resource-protocol-stress-tests.md) already uses
session-like protocols to evaluate general Ash mechanisms without selecting a
privileged session calculus. Reuse that comparison boundary: identify which
facts need checking before choosing source syntax, type-system machinery, or
a runtime representation.

### Lifetime order

For one execution, let a lifetime be a set of event positions at which the
corresponding validity holds. Define `a <= b` by set inclusion. Source checking
would need to establish its constraints for every admitted execution, not just
one observed run. Lifetime extents include suspension where the same ownership
remains valid.

The following are elementary consequences of set inclusion. Equality here is
equality of lifetime extents; two different owners or regions can have equal
extents without having equal identities:

```text
a <= a
a <= b and b <= c  implies  a <= c
a <= b and b <= a  implies  a = b
```

Intersection is the greatest common bound. Its laws follow from membership in
both operand sets:

```text
a intersect b <= a
a intersect b <= b
c <= a and c <= b  implies  c <= a intersect b

a intersect b = b intersect a
(a intersect b) intersect c = a intersect (b intersect c)
a intersect a = a
```

This mathematical domain does not imply that every set, intersection, or union
can be expressed by an Ash scope. Nor does containing two lifetimes in an
enclosing interval authorize moving acquisition or completion. The interval
envelope in DN-0032 is an analysis bound, not a storage-region fusion rule.

For a fixed execution event set `E`, the full domain of lifetime sets forms a
complete lattice: intersection is meet, union is join, the empty set is bottom,
and `E` is top. Expressible lexical lifetimes need not be closed under union;
an enclosing scope gives an upper bound rather than necessarily that exact
union. This lifetime lattice does not establish a lattice of placements,
owners, ownership schemes, or reclamation policies. Those would need their
own orders and proofs that the required bounds exist.

### Placement, ownership, and usable lifetime

Use `r` for a region, `x` for an allocated object, and `o` for an owner.
`place(x) = r` records placement. `Own(o, r)` records ownership of the region
and responsibility for its resident object storage. This ownership alone
grants no additional mutation, resource access, or early-reclamation operation.

An ownership scheme supplies the rules establishing `Own` and region lifetime.
For the first scheme, a successful region-owning scope activation `s` provides:

```text
Own(s, r)
region_lifetime(r) = owner_scope_lifetime(s)
```

These equalities describe logical availability under lexical ownership.
Retained or static backing may physically remain longer. Copying an access
value preserves placement and ownership; it does not copy `Own` authority.
Deep copying, relocation, and ownership transfer would require separate rules.

For each object define `required_use(x)` from its ownership and access
contracts, and `valid(x)` as its usable lifetime. Required use includes uses
and pending completion justified by those contracts, not merely accesses that
happened to execute. The candidate preservation condition is:

```text
required_use(x) <= valid(x) <= region_lifetime(place(x))
region_lifetime(r) <= backing_protection(r)
```

The first inequality prevents premature loss of required validity. The second
bounds object use by its region. The last permits protected backing after
ordinary access ends without granting a longer usable lifetime.

These are obligations to establish, not theorems obtained by naming a region.
Once placement is fixed, an escaping use rejects rather than silently
extending the owner scope or shortening the object's required lifetime.
Initial placement inference may instead select an existing enclosing region,
as explored below. Other schemes must establish the same validity relationship
under their own owner rules.

### Establishing and discovering ownership

The ownership scheme establishes `Own(o, r)`; equal lifetimes or lexical
visibility alone cannot establish it. A checker then propagates that fact
through region access and object placement. Allocating into `r` puts the new
object under its established owner's collective storage ownership. The helper
executing the construction does not acquire ownership merely by allocating.
Aliasing and borrowing preserve that relationship. Ownership transfer would
require a separate scheme rule.

For the inference comparison, consider a variant where each entered lexical
scope activation `s` successfully establishes one region `r_s`, owned by `s`
and available for that activation's lifetime. This is a candidate variant,
not a change to DN-0035 or DN-0054's explicit allocation baseline, where an
ordinary binding, block, or call does not acquire a region. It selects no
physical representation or source annotation syntax.

The three annotation variations constrain the same relationships:

| Variation | Established facts and remaining inference |
| --- | --- |
| No placement or owner annotation | Each scope establishes its region's owner and lifetime. Construction defaults locally; usage requirements can require an enclosing region, whose owner then owns the object's storage. |
| Object annotated with region `r` | Placement selects `r`; its established owner supplies collective storage ownership. The region must be accessible with allocation authority, and dependencies still bound usable lifetime. |
| Object annotated with storage owner `o` | Placement must select a region `r` for which `Own(o, r)` holds. One region per scope determines it; multiple regions per owner require another selection rule. |

An owner annotation here denotes storage ownership, not merely the object that
holds a reference. Neither annotation by itself promises usable validity for
the owner's entire lifetime. If that stronger promise is required, all retained
dependencies must support it. Region and owner annotations constrain inference;
conflicting requirements need a diagnostic rather than silent retargeting.

### Dependency bounds and projection

Let `deps(v)` describe the storage and capabilities required by the particular
value or access being checked. It follows actual retained fields, captures,
evidence, and operation metadata. An unused environment entry alone is not a
dependency. Bounds on usable lifetime take the following form:

```text
valid(v) <= storage_validity(v)
            intersect intersection(valid(d) for d in deps(v))
```

Independent ordinary values add no capability dependency. A closure allocated
in outer region `A` that reads scoped cell `C` still requires `C`; the closure's
longer-lived storage cannot restore cell access after `C` closes.

For a worked derivation, suppose `B` is lexically owned inside `A`, and `y` is
allocated in `B` while retaining an existing reference into `A`:

```text
region_lifetime(B) <= region_lifetime(A)

valid(y) <= region_lifetime(B) intersect region_lifetime(A)
         = region_lifetime(B)
```

The intersection equality follows from inclusion. This derives a bound on
`y`, not an escape permission. Projecting the existing outer reference can
remove the dependency on `B` if the result needs no storage in `B`. A view into
an inline field would retain that dependency instead.

The current generic cell contract remains stricter for retained mutable payloads: their resource owners
must strictly outlive the cell owner. The intersection calculation does not
admit temporary younger storage, self-capture, or cycles of cell owners.
Ordinary immutable graph cycles are a different relation and remain possible.
Likewise, constructing the closure above cannot send a younger-dependent
payload to an outer interpreter. DN-0054's reservation and local initialization
boundary remains a separate construction obligation.

### Access polarity and lifetime-indexed permissions

Read and write polarities are facets whose authority can belong to different
actors. Keep their ownership distinct from storage ownership and from the
individual accesses admitted under that authority. Channel endpoint direction
and positive or negative type occurrence are related comparisons, not identical
concepts. A polarity label alone establishes none of these ownership facts.

#### Ownership of polarities

Use `OwnPolarity_S(a, x, p)` for actor `a` owning polarity `p` of object or
footprint `x` in state `S`. The candidate distinguishes these simultaneous
facts, with `R` and `W` denoting read and write polarities:

```text
OwnPolarity_S(A, x, R)
OwnPolarity_S(B, x, W)
Own_S(C, r)
place(x) = r
```

Here `A` owns the read polarity, `B` owns the write polarity, and `C` owns the
region and the object's resident storage. This does not require `A`, `B`, and
`C` to be distinct, but permits them to be. Owning a polarity is not merely
having performed an operation or holding a temporary access grant.

A protocol supplies, within the base constraints, construction and transition
rules establishing these facts. It may establish different polarity owners or
admit a checked partition of existing authority. It determines whether a
polarity is uniquely or jointly owned, and which sharing, borrowing, delegation,
transfer, recombination, and completion operations are admitted. No general
split or duplication law follows from the labels `R`, `W`, or `RW`.

For example, a protocol may permit transferring the write polarity from `B`
to `D` while `A` retains the read polarity and `C` retains region ownership.
Such a transition need not change placement or the read polarity's lifetime.
Its preconditions and effect on pending operations remain protocol obligations.
Neither region ownership nor a write operation alone establishes the authority
to create, transfer, or delegate a polarity.

An access protocol derives admitted operations from owned or lawfully delegated
polarity authority, its state, and the remaining validity conditions. Owning a
polarity can carry responsibilities beyond an individual access, and does not
necessarily permit that operation in every protocol state. Conversely, a
borrower may have access without owning the polarity. The relationship must be
specified rather than recovering ownership from an access trace.

Polarity ownership, any derived grants, and storage protection have related
lifetimes, but need not have equal extents. The region must protect every
admitted use and required completion justified by either polarity. Ending the
write polarity may mean end-of-input while a reader continues; whether that is
the protocol's meaning is an explicit choice. It does not by itself reclaim
the region. Region reclamation must settle the outstanding polarity and access
obligations under the selected composition.

#### Linearity and uniqueness of polar endpoints

For channels, review usage and alias authority separately for each polar
endpoint. Following [DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md#unique-access-contracts),
neither property follows merely from making a handle non-copyable. These are
candidate protocol profiles, not new restrictions on current cells or a
selection of channel syntax or representation.

| Property | What it constrains | What remains to specify |
| --- | --- | --- |
| Linear current-state authority | Each current authority value is consumed once by a lawful operation, transfer, or completion path; it cannot be duplicated or silently discarded. | Which transitions produce a successor, settle the obligation, or retain it in a pending operation or captured continuation. |
| Affine current-state authority | The current value cannot be used more than once, but may be discarded. | Whether a separate owner or an explicit cancellation/completion mechanism must settle the resource when access is discarded. |
| Unique endpoint authority | No incompatible usable alias to the same endpoint authority coexists with the claimed exclusivity. | Which aliases may exist but be suspended, which loans are compatible, and how exclusivity is recovered. |

Linearity concerns use accounting; uniqueness concerns the authority of aliases.
A linear token alone does not prove that a provider issued no conflicting
token. Uniqueness alone does not require eventual use, successful communication,
or completion. A protocol may combine both properties or use linear permissions
to establish its uniqueness invariant.

Let `e = (c, p)` identify one endpoint role of channel `c`, and let `E(e, q, L)`
denote its candidate current authority at protocol state `q`, with validity
extent `L`. An ordinary successful operation can have the schematic form:

```text
step(E(e, q, L), input) -> (E(e, q', L'), output)
```

The old authority is consumed and its successor carries the next state. This
permits arbitrarily many operations when the protocol permits them; linearity
does not make the channel a one-message channel. Successors must preserve
lifetime and backing constraints. This notation neither extends `L` implicitly
nor selects the failure or terminal outcomes. Those must account for retained,
returned, transferred, or settled authority explicitly.

[Lightweight Functional Session Types, sections 1.3.1 and 1.3.2](https://homepages.inf.ed.ac.uk/slindley/papers/fst.pdf)
provides a concrete comparison: send returns an updated channel, receive returns
a payload and updated channel, and the authors distinguish usage linearity
from alias freedom. This supports comparing state succession with uniqueness;
it does not supply Ash's authority-construction or backing rules.

Uniqueness must name its boundary. Uniqueness of `(c, p)` need not exclude
another actor owning `(c, dual(p))`, or a third actor owning the backing region.
For the dedicated one-way comparison, the roles can be fixed send and receive
polarities, usable by different actors over overlapping lifetimes. For richer
session protocols, a stable endpoint role may alternate send and receive
actions as `q` changes. Endpoint identity, the current action's direction, and
memory read/write authority therefore need separate descriptions. A unique
endpoint also does not establish uniqueness of its payload or reachable graph.

Compare three profiles before choosing a mechanism:

| Profile | Repeated operations and delegation | Main obligation |
| --- | --- | --- |
| Linear state succession with exclusive endpoint authority | Each operation returns a successor; delegation moves the current value. | Establish exclusive issuance and preserve it through context splitting, capture, and handoff; linear use checking alone is insufficient. |
| Reusable unique authority with checked loans | Operations preserve the alias invariant; transfer removes the former holder's usable authority. | Track loans and suspended aliases, including across callbacks and pending operations, until uniqueness is recovered. |
| Shared or asymmetric polar authority | A protocol may share one polarity while keeping the other exclusive, or mediate both. | Define arbitration, ordering, state evolution, and completion without assuming the exclusive profile's rules. |

The first two can describe the same dedicated-channel behavior with different
checking mechanisms. The third is a useful later multi-producer or
multi-consumer comparison. It need not inherit the same session-state or
progress guarantees. Shared authority at an access point that creates fresh
sessions also differs from sharing an endpoint of an existing session.

The cited resource pi-calculus offers a related recovery construction: a unique
whole-channel assumption can split into affine access and authority that
becomes unique after a matching communication consumes that access. Its
countdown measures communications, not elapsed time. Applying this idea per
endpoint would require a new compatibility and preservation argument; it is
not already a polar-endpoint rule, a general loan mechanism, or proof that the
required communication eventually occurs.

Endpoint delegation adds obligations beyond ordinary name transmission. At
commit, the sender loses the delegated current authority; a buffered transport
must account for it in the queued message until the receiver claims it. The
complementary endpoint may remain with its existing owner throughout. Failure
before commit must specify whether authority is returned or otherwise settled;
cancellation after commit must account for queued authority without restoring
a usable sender alias. A first exclusive comparison can require no outstanding
loan or pending operation on the delegated endpoint. Handover of those states
needs an additional contract.

The endpoint's authority, the queued message's storage owner, and the channel's
backing owner remain distinct. Ending one endpoint does not release storage
still needed by its peer, buffers, loans, waiters, or external completion.
Whole-channel reclamation requires settlement of all relevant obligations and
the backing owner's authority. Per-endpoint uniqueness alone cannot justify it.

#### Operation modes and their order

For a fixed view and operation contract, consider the abstract modes:

```text
none = {}
R = {read}
W = {write}
RW = {read, write}
```

Order modes by set inclusion. Their meet is intersection and join is union,
giving a four-element permission lattice with incomparable `R` and `W`.
This describes operation sets, not source types or a rule for issuing authority.
The equation `R union W = RW` does not let a client manufacture a combined
capability. Restricting a view's offered operations does not copy or discharge
its ownership, payload, loan, or completion obligations.

Swapping the read and write labels is an involution fixing `none` and `RW`.
It preserves this order; it is not Boolean complement or an order reversal.
Nor is it an operation that converts an actual reader into a writer. Channel
duality needs its own interpretation below.

A read permission concerns its specified footprint. It does not prove deep
immutability, stable contents across calls, permission to copy a payload, or
freedom from metadata effects in the implementation. A write permission does
not imply permission to read uninitialized storage, reclaim backing, or transfer
its owner. Initialization and disposal of overwritten contents need separate
protocol and payload rules.

#### Permissions depend on time and phase

Here a phase is a state of a chosen access protocol, such as construction,
published reading, or reusable storage. The protocol can vary the permissions
granted to each participant by phase while ownership and placement stay fixed.
Read/write modes remain a separate concept; phase-dependent access is an
optional composition, not a requirement that every object changes polarity.
Another protocol may admit the same modes throughout its usable lifetime.
Phases are not a global read-versus-write switch: different actors can hold
different permissions over overlapping lifetimes.

For a fixed execution event set `E`, client `a`, and view `v`, let
`G(a, v)` be a subset of `{read, write} cross E`. Membership records an
operation admitted at an event position, not merely an operation that executed.
It describes derived access, not the ownership of the underlying polarity.
Source checking must establish the relationship for every admitted execution;
this semantic relation is not an assumed computable future-use oracle.

For example, actor `A` can have read access to view `v` while actor `B` has
write access to the same footprint:

```text
G(A, v) = {read} cross L_A
G(B, v) = {write} cross L_B
L_A intersect L_B != empty
```

Overlapping grants need not alternate or end when the other actor receives
its grant. Their compatibility is an obligation of the selected access
protocol, including visibility and synchronization where required. A protocol
can admit both while defining how reads observe updates. Grant coexistence
and simultaneous execution of raw memory operations are separate questions.
The example supplies neither a general exclusion rule nor an unrestricted
shared-memory permission.

The region owner can remain a third actor throughout. Its protection must
cover both grants' admitted uses and required completion. The clients can have
different grant lifetimes and admitted execution domains while referring to
the same placement. Combining their facts must preserve the actor index; it
cannot grant `RW` to either actor merely because both operations are present.

This relation retains correlations that a pair of mode and lifetime summaries
can lose. As a separate example, suppose one client's interface permits writes
during construction and reads after publication, over different nonempty
extents `L_build` and `L_read`:

```text
G = ({write} cross L_build) union ({read} cross L_read)
G subset_of {read, write} cross (L_build union L_read)
```

The inclusion can be strict. Replacing `G` by the larger rectangle grants
unintended reads during construction and writes after publication. Thus taking
the union of modes and lifetimes independently is not generally a sound
capability join. For fixed identities and `E`, the full relation domain is a
set lattice, but arbitrary unions need not be admissible access contracts.

Descriptive restriction to modes `M` and lifetime `L` is
`G intersect (M cross L)`. Such restrictions commute and are idempotent by
intersection laws. These set facts do not authorize discarding pending loans
or required completion, duplicating authority, or widening an existing grant.

For each admitted access, require the operation's permission and protocol
phase, initialized storage where needed, valid dependencies, live region
protection, an admitted execution domain, and the required visibility or
synchronization. A lifetime bound or a mode alone cannot discharge that check.
All granted uses of a view remain bounded by its usable lifetime and every
required backing region, as in the dependency and borrowing bounds above.

#### Composition, ownership, and storage

Combining permissions held by clients is not the lattice join. Define a
separate partial compatibility relation over clients, overlapping footprints,
lifetimes, and protocols. For unmediated ordinary storage, a candidate permits
overlapping readers and excludes an overlapping writer against another reader
or writer. Proven disjoint fields or buffers may permit independent writes
within the same region. This does not require a lock or an exclusive permission
for an entire region merely because two objects share placement.

Mediated shared mutation, atomics, and locks need their own operation contracts.
A reusable public write handle is not a raw exclusive-storage grant. The
candidate rule does not change current cells. Likewise, `R union R = R` says
nothing about whether two live readers exist, whether an access value may be
duplicated, or whether all read loans have ended. A separate loan or permission
ledger must preserve those facts; no fractional or linear representation is
selected here.

Where the protocol admits it, a polarity owner may delegate access without
transferring that polarity or region ownership. A writer can therefore be a
non-owner of storage and may be a borrower of write authority; a storage owner
need not have usable mutation authority during a loan. Reclamation requires its
distinct authority and the settlement of outstanding admitted uses. `RW` adds
no ownership or reclamation authority.

Using a read view requires its backing, and returned borrowed views retain
their actual backing dependencies. Copying an independent value can remove a
dependency; the operation must establish the payload's copy contract.
Writing a reference into retained storage introduces dependencies that must
cover all subsequently admitted reads and required completion, not just the
write event. The current generic cell contract's strict retained resource-owner rule remains
stronger than this necessary lifetime condition; clearing later does not relax
it. Placement in a longer-lived region cannot repair an expired grant or an
unsupported stored dependency.

Execution domains may differ by operation: reading could be admitted on several
workers while mutation or reclamation requires home support. A read-only
interface still needs the representation and metadata checks from the affinity
comparison. Mode attenuation neither relocates bytes nor establishes thread
safety; ownership transfer must settle or transfer existing grants under its
own rule.

#### Payload variance and endpoint duality

Under a value-flow convention, reading produces a `T` and writing accepts a
`T`. For comparison only, suppose `A <: B` is a safe payload substitution
relation and the remaining interface contracts are fixed. Simple producing
and accepting interfaces then have the candidate variance relationships:

```text
Source<A> <: Source<B>
Sink<B> <: Sink<A>
```

A source promises an output; a sink promises to accept an input. An interface
offering both generally requires payload invariance. This does not introduce
Ash subtyping or lifetime-coercion syntax. Shortening a loan's own lifetime is
different from changing a reference lifetime inside a payload that aliases may
write. The [Rust variance reference](https://doc.rust-lang.org/reference/subtyping.html#variance)
is an external comparison: function results and inputs have opposite variance,
and a mutable reference is invariant in its referent type while covariant in
its own reference lifetime. These rules are not adopted by this note.

For a channel, sending accepts a payload from its caller and receiving produces
one. Matching endpoint directions are dual, but the direction does not select
the permissions of that payload. A sender may read or transfer an immutable
message; sending does not require permission to mutate its bytes. A receiver
may obtain a read-only lease or an owned writable region, depending on the
transport contract.

At the single-message direction level, use explanatory labels `Send(T)` and
`Receive(T)` with `dual(Send(T)) = Receive(T)` and the reverse equation, so
`dual(dual(p)) = p`. Protocol continuations, closure, cancellation, and payload
transfer must still match. This is separate from swapping memory-access labels
and does not grant both directions to either endpoint.
[Propositions as Sessions](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions-jfp.pdf)
provides an external account of session duality. Its calculus and progress
results do not follow from these explanatory endpoint equations.

For a zero-copy pool, the producer can hold construction permission, the
consumer a later read lease, and the pool retain storage ownership throughout.
Publication must establish initialization and the required visibility while
ending incompatible producer access. Reuse waits for reader loans and pending
operations, including external completion, rather than merely observing a
receive event. These are separate phase transitions from ownership transfer
and backing relocation.

### Sequential placement inference

Keep validity constraints, placement inference, and optimization separate.
The constraints determine which placements are admitted. A heuristic selects
a candidate satisfying them. Later optimization may change placement or its
physical representation only while preserving the established guarantees and
observable behavior, including any exposed allocation or completion effects.

For the one-region-per-scope variant, start with the construction scope's
region. Widen toward existing enclosing regions only when required uses cannot
fit there. For sequential execution with properly nested scope activations,
a useful candidate is the least common ancestor of the construction activation
and all required use activations:

```text
candidate_scope(x) = least_common_ancestor(
    construction_scope(x), required_use_scopes(x))
candidate_region(x) = region(candidate_scope(x))
```

These scopes denote related dynamic activations, not just source locations.
Including construction ensures that the candidate region is already available
when allocation executes. Required uses include aliases, retained fields,
closures, and pending completion obligations justified by contracts, rather
than only direct uses or accesses observed in a run. Loops, recursion, and
function boundaries require summaries that preserve activation relationships;
a syntactic common ancestor alone is not a complete inference algorithm.

For example, the following is schematic control flow, not Ash syntax:

```text
scope P:
    x = scope A:
        construct object
        return object
    scope B:
        use x
```

The object is constructed inside `A` but used after `A` ends, inside its
lexical neighbour `B`. The value reaches `B` through the binding in `P`;
inference does not change name visibility. If all constraints permit it,
inference selects `P`'s region before allocation. `P` owns that region and
therefore the object's storage. No object is first allocated into `A` and then
moved, and neither scope's lifetime is extended.

The candidate still needs live exact allocation authority, compatible region
type and construction, dependency validity, and agreement with annotations.
In particular, placing a closure in `P` cannot make a resource owned by `A`
available to a later call in `B`. Related ordinary value allocations may need
joint placement constraints; this does not authorize extending resource owners
or automatically promoting every reachable dependency. If no admitted region
satisfies the requirements, the use must reject.

Widening required by use belongs to initial placement inference. Additional
placement choices for efficiency belong to optimization and need an observation
contract. This heuristic is limited to the sequential fragment with nested
lifetimes; the general algebra remains the validity constraints and ownership
facts above. Suspension can preserve an owning activation after control leaves
its body, and later concurrent work can introduce other lifetime relationships.
Lexical ancestry alone cannot solve those cases. Their contracts remain open;
this heuristic does not replace the model's existing capture obligations.

### State and reclamation

A candidate state `S` records region identities and types, ownership
obligations, resident objects, placement, initialized representations,
permitted access, roots and references, pending construction, and required
completion. This is model state, not a selected runtime representation.

Let `Resident(r, S)` be the objects still allocated in `r`. Let `Need(r, S)` be
the subset whose preservation valid ownership, access, or completion requires.
Its specification must account for references from other regions, closures,
captured control, provider state, and pending cleanup. Region ownership does
not by itself require every unreachable object to remain individually live.

`Need` is a semantic obligation, not an assumed computable oracle. A checker
or collector may retain more objects through a conservative approximation;
proving that it misses none of the required objects is part of its contract.

A region type `K` supplies its allowed object reclamation policy. Any early
reclamation transition removing objects `D` must satisfy:

```text
D subset_of Resident(r, S) minus Need(r, S)
Resident(r, S_after) = Resident(r, S) minus D
```

The type may impose stronger conditions or support no early reclamation. A
fixed arena initially uses `D = empty`. Counting and tracing require their own
accounting, roots, cycle, failure, and possible reference-update obligations.
Neither policy changes region ownership or lifetime merely by being selected.

Whole-region reclamation is a separate transition, authorized by the ownership
scheme after remaining permitted uses end and required completion no longer
needs the storage. It consumes reclamation authority once and establishes:

```text
Resident(r, S_after) = empty
no permitted access remains to an object allocated in r
```

All remaining objects are reclaimed together, including ordinary cycles that
an earlier policy retained. Objects merely referenced in another region are
outside this reclamation. Ending lexical source access and consuming a physical
owner remain distinct: a retained dependent can block backing release after
ordinary access has been revoked. The model must preserve that protection.

### Ownership contexts and typed transitions

Let `Delta` be an ordered context of ownership and completion obligations.
Compatible concatenation `Delta tensor Gamma` preserves exact identities and
dependency order, with no duplicated completion authority. `I` is empty.
Reassociation changes grouping, not order or scope boundaries:

```text
(Delta tensor Gamma) tensor Theta
    = Delta tensor (Gamma tensor Theta)
I tensor Delta = Delta = Delta tensor I
```

These structural equalities follow from concatenation, conditional on complete
context compatibility. They do not justify exchange, owner duplication, scope
fusion, or merging region identities. Reusable handles remain separate from
these restricted obligations.

Use `C : Delta0 -> Delta1` for a model computation transforming a checked state
under one ownership context into another. Compatible transitions sequence only
when their intermediate state and ownership contracts agree. For finite paths,
relation composition gives associativity:

```text
(f ; g) ; h = f ; (g ; h)
```

Failure outcomes, committed effects, and ordered traces must be included in
the eventual computation model. This regrouping must not restart or undo an
earlier operation. DN-0032 supplies the bounded sequencing comparison; a
concrete region calculus must still establish its typing and operational laws.

### Sequential processes and dedicated channels

This future comparison composes sequential processes with isolated local
regions. Begin with a dedicated unidirectional channel `c` connecting one
producer `P` and one consumer `Q`, with a fixed message type and payload
contract.
Distinguish synchronous rendezvous from a bounded FIFO buffer; neither
interpretation is implied by the word channel.
Endpoint delegation, multiple producers or consumers, shared mutation, and a
multicore memory model remain outside this case. No scheduling API is selected.

#### Network composition and communication order

Write `P parallel_c Q` for the network with that connection. This composition
combines process states, channel state, pending operations, and ownership facts.
It is distinct from ordered ownership-context concatenation `tensor`; the
channel connects obligations belonging to different process activations.

Let `a precedes b` be the transitive closure of each process's event order and
the matching communication order. For buffered delivery, publication precedes
claim by the receiver. For rendezvous, both processes participate in one
handoff event. Communication orders the relevant events; it does not establish
that one process's entire lifetime contains the other's. Thus lexical common
ancestry alone cannot determine message placement.

Regrouping a network is a candidate structural law only when it preserves the
same process identities, channel connections, capacities, and observations.
It does not reorder events within a process or imply a scheduling policy.
Commuting independent local steps would need separate premises about disjoint
support and observations; shared allocation capacity can invalidate that law.

For a buffered channel without message discards, record sequences of distinct
message identities in publication order, receive-commit order, and the queue.
The candidate FIFO invariant is:

```text
published(c) = received(c) ++ queued(c)
0 <= length(queued(c)) <= capacity(c)
```

Here `++` is sequence concatenation. It has an empty identity and associative
grouping, but does not commute. These elementary sequence laws do not permit
arbitrary concatenated executions: capacity, closed state, and message ownership
still constrain every prefix. A discard policy needs an explicit disposition
record instead of silently deleting a message from this accounting. Rendezvous
has no persistent queue; it requires a matching participant, rather than being
an ordinary buffered send into a permanently full zero-capacity queue.

#### Payload contracts

Dedicated endpoints do not by themselves establish a message's storage or
access permissions. Compare three contracts explicitly:

| Contract | Ownership and placement | Additional obligation |
| --- | --- | --- |
| Copy data | Construct a fresh message graph in independently owned storage. The source graph retains its placement and owner. | Specify copying of sharing and cycles, permitted payloads, observations, failure, and costs. A copied local resource handle still depends on its original owner and is not independent data. |
| Transfer a message region | Move responsibility for one complete region and its resident objects; placement and region identity remain unchanged. | Establish transferable backing and completion support, no remaining sender or third-party access, and no unsupported external dependencies. |
| Share storage | Keep the original region owner and grant specified cross-process access. | Prove the shared lifetime and access/visibility contract. Immutability or a long lifetime alone does not establish safe sharing. Excluded from the first isolated comparison. |

Copying data is the initial isolated-storage baseline from DN-0035. Region
transfer is a second ownership scheme to compare algebraically, not an implied
optimization of copying: object identity, failure, and storage observations may
distinguish them. Begin either comparison with data-only payloads; transporting
resource handles, handlers, endpoints, or captured control needs further rules.

Transferring one reference into a general process region cannot transfer that
object's storage ownership independently. Region ownership covers all resident
objects. Either copy the message into independent storage, or prepare a whole
detachable message region. Splitting regions is not assumed. A unique completion
owner is insufficient evidence that sender aliases or hidden captures are gone.

#### Ownership during delivery

Use `Own_S(o, r)` for ownership in state `S`. The following is an ownership
history for successful buffered transfer of a prepared message region `r_m`;
it is not an unconditional operational rule:

```text
Own_S0(P, r_m)
    -- publication commits --> Own_S1(c, r_m)
    -- receive commits -----> Own_S2(Q, r_m)
```

Here `c` denotes the channel's obligation for accepted undelivered messages,
not either endpoint's observation handle. A surrounding owner must preserve
channel support until accepted messages, waiters, and cleanup are settled.
The receiver can retain the accepted region after the queue slot is reused.

Each successful handoff removes the old ownership fact and establishes the new
one together. Placement, region type, and internal reclamation policy remain
unchanged; future collection must use the new owner's roots. On a synchronous
rendezvous, ownership passes directly from `P` to `Q` in the matched event,
without a persistently queued message owner. Copying first creates a distinct
message region under a construction owner; publishing that region follows the
same delivery obligations while the source graph remains owned by `P`.

For every unreclaimed message region, the candidate invariant is:

```text
|{ o : Own_S(o, r_m) }| = 1
required_use(m) <= valid(m) <= region_lifetime(r_m)
```

Every live state must have an owner protecting the region, including periods
with no running user. Its lifetime must cover construction, pending delivery,
receiver use, and required completion. It need not equal either process's whole
lifetime. This transportable-region scheme replaces the lexical lifetime
equality for those regions; it does not silently extend a region still bound
to an ordinary lexical owner. The owning obligation must be detachable from
the construction scope under an explicit rule before that scope can complete.

For transfer, all resident storage and closing obligations must be eligible,
and all remaining sender access must be ruled out. A closed ordinary object
graph may include internal cycles. References to sender-local resources,
foreign thread-affine support, or other non-transferable dependencies reject
unless a separate contract establishes their transport. Changing `Own_S` alone
does not establish access revocation, initialized data, or cross-worker
visibility. Those remain premises of a future handoff rule.

#### Zero-copy variations

Specify the boundary of a zero-copy promise. Here the candidate promise is no
additional payload copying during channel publication and receipt. Initial
construction, descriptor copying, allocation, synchronization, physical page
movement, and remote access costs are separate observations. An end-to-end I/O
promise needs a larger boundary. A guaranteed zero-copy operation cannot
silently fall back to copying; an optional fast path needs its own contract.

Compare these variations without conflating storage ownership with temporary
access. The borrowing, pooling, and sharing rows extend the isolated baseline
only under additional contracts:

| Variation | Placement and ownership | Conditions to compare |
| --- | --- | --- |
| Copy to independent storage | A fresh message region follows the delivery history above. Choose its backing policy separately. | Baseline payload-copy cost, failure, graph/identity observations, and receiver locality. |
| Transfer a prepared region | The complete region changes owner; payload storage stays in place. | No remaining sender access; admissible use and reclamation on the destination or through retained support. |
| Construct directly in final storage | The producer initializes reserved receiver- or channel-supported storage; publication changes access phase. | A checked construction permit, initialized publication, and precise responsibility for refusal, partial construction, or cancellation. No existing payload is copied. |
| Borrow a view | Storage ownership remains with the lender; the receiver gets a bounded lease. | The region covers the lease; incompatible mutation and reclamation wait for all admitted uses and acknowledgements. Dedicated endpoints alone do not prove this. |
| Reuse channel or pool slots | A stable region owner retains storage while write, queued, read, and reusable phases govern a slot. | Receipt does not imply the consumer finished using the bytes. Reuse waits for every view and pending operation; stale accesses must not become valid for a later slot generation. |
| Share immutable data | An enclosing or separately specified shared owner retains storage. | Cross-process lifetime, roots, representation safety, and reclamation accounting. This is a sharing contract rather than region-owner transfer. |
| Send descriptors for several buffers | A message names slices of one or more existing regions. | Every backing dependency remains protected. Descriptor transfer alone neither transfers those regions nor makes sender-local backing independent. |
| Use registered I/O or device buffers | A region provides storage with an external operation in flight. | Registration, layout, address stability, and completion acknowledgement protect bytes until the external user has finished, including cancellation races. No device contract is assumed here. |

For a borrowed view `v`, let `backing_regions(v)` include every region needed
for its descriptor and referenced bytes. Necessary lifetime bounds include:

```text
lease_use(v) <= valid(v)
valid(v) <= intersection(region_lifetime(r) for r in backing_regions(v))
```

These bounds do not establish mutation exclusion or synchronization; the
earlier resource-dependency bounds still apply. A pool can remain the storage
owner throughout; the producer's construction permission and consumer's read
permission are separate phase facts. Ending a queued entry therefore differs
from ending payload access and from reclaiming its region. Per-slot reuse is
not an assumed region split or a transfer of storage ownership.

The process comparison concerns logical Ash processes. Same-address-space
access, separate address spaces, and remote machines require different
transport contracts. A pointer or ownership fact alone does not establish a
valid mapping or representation at the destination.

#### Placement and execution affinity

Thread/processor alignment here means execution affinity and memory locality.
Keep byte alignment as a separate construction and access constraint. Extend
the model with distinct facts:

| Fact | Candidate meaning |
| --- | --- |
| `Own_S(o, r)` | Who holds the region's ownership and completion obligation now. |
| `place(x) = r` | Which logical region contains the object. |
| `backing_location_S(r)` | Where backing is resident, potentially across several memory nodes; allocation policy and actual residence are distinct. |
| `execution_domain_S(P)` | The process's current worker/thread/processor placement, with no assumption that these identities coincide. |
| `allowed_domains(r, op, S)` | Domains allowed to perform a particular operation with its transitive representation, provider, resource, and completion support. |

For an event `e` operating on `r`, admission requires its execution domain to
belong to the operation's allowed domains, in addition to ownership, access,
initialization, lifetime, and visibility obligations. Allowed-domain sets can
be intersected when several supports constrain one operation; an empty
intersection rejects that execution choice. This does not order complete
ownership schemes or prove that a legal domain is efficient.

Changing process placement, transferring region ownership, and relocating
backing are three distinct transitions. None implies either of the others.
Migration must account for retained support and later completion, not just the
next payload read. Compare same-worker execution, fixed per-core processes,
and migration among an admitted domain set without selecting one scheduler.

Hard restrictions and preferences also differ. A required thread for a foreign
operation or reclamation is an admission condition. Preferred processor/cache
or memory-node locality is a cost policy unless the contract makes it a hard
restriction. Byte, cache-line, page, and device alignment requirements must
state which are required for valid access and which are performance choices.
No universal alignment size or platform topology is selected.

Zero-copy ownership transfer need not produce receiver-local storage. Compare
leaving backing in place, constructing with a destination-oriented allocation
policy, copying to different backing, moving execution toward the data, and
explicit backing migration under its own stability contract. Measure payload
copies, retained bytes, metadata and synchronization work, remote accesses,
and completion traffic; zero copied payload bytes alone is not a cost order.

Reclamation may be restricted to a home worker even when remote payload access
is admitted. The receiving owner can then retain a unique completion obligation
and route reclamation through home support. If that obligation is delegated to
a completion record, the transfer must preserve its uniqueness until settlement.
Protect home support and backing while a return or acknowledgement is pending;
neither consumer completion nor a posted reclamation request proves release.

These distinctions have external precedents, not Ash implementation evidence.
[Seastar's multicore contract](https://docs.seastar.io/master/group__smp-module.html)
uses per-core services and routes destruction of a moved `foreign_ptr` back to
its originating core. Linux documents distinct
[CPU and memory-node restrictions](https://www.kernel.org/doc/html/latest/admin-guide/cgroup-v1/cpusets.html)
and [NUMA allocation policy](https://www.kernel.org/doc/html/latest/admin-guide/mm/numa_memory_policy.html);
changing allocation policy does not by itself relocate existing pages. They
motivate separate access, placement, and reclamation facts; they do not select
an Ash runtime or prove any candidate transition above.

#### Failure, closure, and reclamation

The publication and receive commits determine ownership even if notification
or process resumption happens later. Full, closed, or cancelled send before
publication leaves the prepared message with its sender or pending-operation
owner. After publication, sender cancellation cannot silently take it back.
Cancellation before receive commitment leaves the queued owner unchanged;
after commitment, the receiver or its completion path must settle the region.
A partially constructed copy must close its own obligations without publishing
readable data or consuming the original graph.

Closing admission is distinct from draining or discarding accepted messages.
Choose an explicit policy for queued messages and pending sends when an endpoint
closes or a process fails. The invariant requires every outstanding region to
remain owned until delivery, an explicit return, or authorized completion and
reclamation. Receiver failure cannot orphan an accepted message; sender exit
cannot invalidate one already transferred. Final channel reclamation waits for
its remaining support obligations. It cannot reclaim a region already received
by `Q` merely because that region travelled through the channel.

Queue entries, pending sends, and completion paths are roots for `Need(r, S)`.
No collector may treat a message as dead merely because neither process is
currently reading it. Reclaiming a transferred region still reclaims all its
remaining objects en masse after required completion. Queue capacity bounds
accepted entries, not message bytes, blocked producers, receiver-retained data,
or total protected backing; those need separate bounds.

The proof target is global validity preservation from checked process steps
and checked communication transitions, including publication, receipt,
cancellation, and closure. Unique ownership and lifetime coverage are safety
obligations. They do not prove deadlock freedom, fairness, eventual receipt,
eventual reclamation, or a bound on retained memory. Those need separate
protocol, scheduling, and capacity premises.

### Law status and limits

| Claim | Status in this note |
| --- | --- |
| Lifetime order and intersection laws | Elementary derivations from the chosen set model. |
| Nested-region dependency bound | Derived above from containment and the proposed dependency premises. |
| Context reassociation and identity | Structural equalities for compatible ordered concatenation. |
| Transition sequencing associativity | Conditional on the chosen typed relation and outcome composition. |
| Region ownership covers resident objects | Candidate ownership contract, not derived from placement alone. |
| Ownership recovered from selected placement | Conditional on the ownership scheme having established the region owner. |
| Common-ancestor placement | Candidate inference heuristic for the sequential fragment with nested activations, subject to all validity and allocation constraints. |
| Message-region ownership conservation | Candidate invariant for the future channel comparison; requires checked transfer, access, and failure transitions. |
| Network regrouping or independent-step commutation | Conditional proof targets preserving channel connections and observations; no general exchange law. |
| Ownership transfer, execution migration, and backing movement | Distinct transitions; no unconditional commutation or performance ordering. |
| Mode sets, grant relations, and descriptive restriction | Elementary set laws in their fixed domains; do not establish capability issuance or compatible permission composition. |
| Read/write polarity ownership | Candidate protocol-established facts, separately assignable from storage ownership; construction, partition, and transfer rules remain to be specified. |
| Endpoint linearity and uniqueness | Distinct candidate constraints on use accounting and alias authority, applicable per polarity. Their combination, successor rules, and delegation preservation remain protocol obligations. |
| Shared base with protocol refinements | Candidate common constraints; each protocol and their composition must establish preservation rather than waive the base. |
| Literature correspondences | External comparison evidence and proposed mappings; neither imported theorems nor a selected Ash calculus. |
| Payload variance and endpoint duality | Conditional interface comparisons; no Ash subtype system, session calculus, or progress result is established. |
| Allocation, collection, and completion preserve validity | Proof obligations for the operational model and each policy. |
| Lifetime widening, region fusion, or allocation reordering | No general law; observable failure, retention, and cleanup need comparison. |
| Correspondence with Ash source, Core, and runtime | Open; no implementation or compiler proof follows from this algebra. |

In particular, release is not an unrestricted idempotent operation: a second
release lacks the authority consumed by the first. An abstract empty-set
calculation does not justify double release. Garbage collection does not imply
source cleanup ran. One-shot capture moves ownership without copying it, but
does not itself prove exclusive access, liveness, or eventual completion.

## Evidence and experiments

The first proof target is preservation of well-formed state and required object
validity across each admitted transition. A finite execution then preserves the
invariant by induction, provided every transition case has been proved. The
allocation, initialization, root, dependency, and completion premises needed for
that argument remain to be specified and discharged.

| Case | Required positive evidence | Contrary case |
| --- | --- | --- |
| Lexical ownership | The scope determines the region owner and lifetime; required object uses stay within it. | A handle or hidden capture remains usable after the scope ends. |
| Nested placement and projection | Inner storage retains outer references; an independent projected outer reference can return. | An inline view loses its inner backing dependency. |
| Sequential inferred placement | Local-only construction stays local; use in a sibling activation selects a suitable common enclosing region before allocation and derives its storage owner. | Inference relocates an existing object, changes binding visibility, or silently extends an owner. |
| Annotation constraints | Region annotations resolve their established owners; storage-owner annotations select among that owner's compatible regions. | Equal lifetimes fabricate ownership, conflicting annotations are ignored, or one owner is assumed to have only one region outside that variant. |
| Placement versus dependency validity | A longer-lived region permits later use only when retained dependencies permit it too. | Outward placement makes an expired inner resource usable or bypasses the request-payload boundary. |
| Ownership versus access | Aliases use the same object without creating completion owners. | Copying a handle permits another region release. |
| Ordinary graph cycle | Initialized immutable cyclic data remains valid and is reclaimed with its region. | Object edges are confused with resource-owner cycles or tracing is silently required for bulk release. |
| Region type policy | An arena retains objects; a separately specified collector reclaims only unneeded objects while its region remains available. | A hidden root is missed or type selection changes ownership and region lifetime. |
| Whole-region reclamation | All remaining resident objects are reclaimed together after required completion. | A resident object survives reclamation or an object in another region is incorrectly reclaimed. |
| Captured control | Capture and resume preserve the same owner, object contents, and pending obligations. | Suspension is treated as scope completion, or resume recreates ownership. |
| Failed construction and retained backing | No partial readable object is published; unresolved dependent ownership protects backing. | Failure fabricates validity, or source completion is treated as successful backing reclamation. |
| Observations and costs | Comparisons retain failure behavior, external order, and any exposed allocation observations. | A scope rewrite changes capacity failure, cleanup order, or a declared usage report. |
| Buffered message ownership | Publication transfers one prepared region to the channel; receipt transfers it to the consumer without changing placement. | An unowned interval, duplicated owner, remaining sender alias, or channel close reclaims receiver-owned storage. |
| Rendezvous versus buffering | Matched direct handoff and queued handoff each preserve their stated ownership and lifetime contracts. | Zero capacity is treated as an ordinary full queue, or buffered messages retain sender-local dependencies. |
| Message copying and region granularity | A copy has independent eligible storage; a move transfers an entire eligible region. | Copying a handle fabricates independence, or moving one object leaves its backing owned by the sender. |
| Communication failure | Each side of publication and receipt commitment identifies the remaining owner and required completion. | Cancellation, endpoint closure, or process failure loses a queued or accepted region. |
| Queued roots and capacity | Pending operations, queued entries, and receiver-held regions remain protected and are accounted separately. | Collection drops an unread message or bounded slots are claimed to bound all retained bytes. |
| Zero-copy variants | State the copy boundary and separately verify transfer, construction, lease, slot, or descriptor obligations. | Zero-copy is inferred from a moved handle, hidden copying breaks a promise, or queue removal permits premature slot reuse. |
| Execution affinity and locality | Every admitted operation respects required domains while locality policies and actual backing are recorded separately. | Ownership change is treated as physical relocation, migration bypasses retained support, or preferred locality is mistaken for a safety proof. |
| Reclamation on a home worker | A unique retained completion obligation protects backing and home support until acknowledgement. | Receiver exit, allocator shutdown, or a posted free request prematurely releases support or duplicates reclamation. |
| Permission and lifetime correlation | Construction writes and later reads retain distinct allowed phases. | Joining mode and lifetime summaries grants reads before initialization or writes after publication. |
| Access compatibility and ownership | Compatible reader loans, disjoint writes, and mediated aliases retain their stated rules without transferring storage ownership. | `R union R` erases outstanding loans, a writer is assumed to own storage, or `RW` permits reclamation. |
| Overlapping actor grants | One actor's reads and another's writes coexist over overlapping lifetimes when the access protocol admits them, preserving their separate rights and visibility contract. | A global phase rule forbids all such overlap, the actor index is erased to grant both modes to either client, or grant coexistence is mistaken for permission for arbitrary raw memory races. |
| Different polarity owners | A protocol establishes separate read, write, and storage owners and preserves their stated obligations through admitted transitions. | Polarity ownership is reduced to an access grant, inferred from an operation, or assigned by placement without a construction rule. |
| Endpoint succession and exclusivity | Repeated communication uses lawful successors or preserves a checked uniqueness invariant while the complementary endpoint remains usable by its owner. | A stale state is reused, two conflicting authorities are issued, linearity is mistaken for exclusive issuance, or exclusivity of one end forbids its peer. |
| Endpoint delegation and recovery | Commit accounts for the current authority in the queue or receiver; loans and pending operations prevent premature exclusive handoff. | A sender retains a usable delegated end, cancellation loses a queued obligation, an unfinished loan is ignored, or endpoint closure frees backing still needed by its peer. |
| Base constraints and protocol variation | Contrasting protocols preserve the common validity and obligation constraints while making different access and ownership choices. | A local exclusion rule becomes universal, a protocol waives required lifetime coverage, or individually valid components are assumed to compose. |
| Read and retained-write dependencies | Returned views retain backing; retained payloads preserve all later admitted reads and completion. | Read-only access makes backing immortal, or a short write event hides an expiring stored dependency. |
| Endpoint and payload polarity | Dual endpoint roles match while payload permissions follow the transport contract. | A send endpoint implies payload mutation authority, receipt implies writable data, or duality alone proves progress. |

The fixed-arena case is the first bounded model. Compare a collector only after
specifying its root and reclamation contract; current scalar Arena evidence
does not prove these graph, lifetime, or collection cases. Record contrary cases
as well as successful derivations. No new executable or machine-checked proof
has been produced for this note.

Channel cases are future comparisons, not evidence for the first sequential
model. A later bounded assignment must specify copy or transfer payloads,
rendezvous or buffering, commit points, endpoint closure, cancellation, and
the observations used to compare network executions before claiming a proof.
For a zero-copy or affinity comparison, also name the exact copy boundary,
access phases, admitted domains, backing policy, and reclamation route.

The literature comparisons supply additional positive and contrary cases,
including name extrusion, I/O capability restriction, delegated cancellation,
captured linear authority, and shared access points that change progress
guarantees. They are evidence about their stated fragments, not experimental
results or correctness evidence for Ash.

A later prototype needs a separately bounded assignment naming the state and
operation fragment, observations, comparison policies, and retention conditions.
Retain reproducible proofs, countermodels, and measured policy differences as
design evidence. Discard machinery that silently extends owners, hides backing
dependencies, or assumes a runtime representation to make an algebraic law true.
Product adoption requires the proposal or decision and task workflow.

## Open questions

- Which candidate base constraints are necessary, which follow from others,
  and which need revision under the sequential, channel, polarity, and pool
  comparisons? What is the smallest useful shared basis?
- Which assumptions and instance obligations from generic process typing can
  be reused for the base, and which new premises connect polarity ownership
  to backing protection, region reclamation, and observable behavior?
- What precise state invariant connects initialized residency, permissions,
  ownership, and the required-object set without relying on future execution?
- Which lifetime extents and bounds can the first lexical checker express?
  How should later schemes replace that restriction while preserving validity?
- How do summaries and independent Core checking retain placement, actual
  captures, field projection, and ownership facts through abstraction?
- Which required-use and activation summaries make sequential placement
  inference conservative through loops, recursion, helpers, and closures?
- How should compatible regions be selected when one owner has several, and
  which allocation observations constrain optional placement optimization?
- Which operations can be framed by unrelated context without changing root
  accounting, capacity, exact dispatch, or completion behavior?
- What additional laws belong to a specific counted or traced region type,
  including cross-region roots and final bulk reclamation?
- How should pending construction and retained native dependencies participate
  in the same preservation argument without identifying source exit with free?
- Which observation model distinguishes sound lifetime reasoning from a
  semantics-preserving program transformation, and which costs stay separate?
- What checked contract permits detaching a message region's ownership and
  completion support while ruling out retained sender access and dependencies?
- Which channel close and cancellation policies account for every pending,
  queued, and received region, including process failure around commit points?
- Which network equivalence and visibility premises support composition laws,
  and which additional protocol or capacity rules establish progress or bounds?
- Which zero-copy variants need ownership transfer versus leases or phase
  permissions, and when may pooled storage safely be reused?
- Which support facts constrain access, execution migration, and reclamation
  domains independently, and how is home support retained through shutdown?
- Which locality and copy-cost observations guide policy without silently
  changing lifetime, alignment, failure, or visibility contracts?
- Which permission and loan facts preserve client, footprint, mode, and lifetime
  correlations through abstraction without inventing new grants at a join?
- Which protocol rules establish read and write polarity ownership, and permit
  its partition, sharing, borrowing, or transfer independently of storage
  ownership? What responsibilities and completion obligations does each carry?
- For each endpoint, which rules concern linear or affine use accounting and
  which concern unique alias authority? Can linear succession and reusable
  unique access preserve the same observable protocol and failure behavior?
- What checked construction establishes exclusive authority initially, and how
  can loans, delegation, capture, or protocol transitions recover or transfer
  it without forbidding the complementary endpoint's concurrent use?
- Which raw and mediated access protocols admit compatible aliases, and how do
  initialization, publication, retained writes, and reuse update those facts?
- Which payload variance and endpoint-duality relationships survive the chosen
  effects, usage, lifetime, and transport contracts without conflating them?

To resume: first fix the state, context compatibility, and transition premises
for lexical ownership with a fixed arena; then prove validity preservation and
exercise the nested/projection, cycle, capture, and failure counterexamples.
Specify the required-use summaries and check the sequential placement heuristic
against the local, sibling-use, annotation, and dependency counterexamples.
Use those results to identify the extra obligations for a second reclamation
policy or ownership scheme. Source syntax and runtime representation can follow
once that comparison exposes the facts they must preserve.
The dedicated-channel case supplies a later comparison: start with copied,
independent data, then compare transportable regions under the same message
protocol. Preserve the separation between memory safety and progress claims.
