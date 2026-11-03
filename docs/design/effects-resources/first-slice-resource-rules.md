# First Slice: Candidate Resource Rules

This record develops R1–R6 of the
[catalogue](first-slice-catalogue-and-map.md#resource-and-cleanup-rules) from
the [resource trace](first-slice-resource-trace.md). The rules are candidates
for composing established judgments; they are not Ash syntax, implemented
certificates, an accepted change, or a soundness proof. The
[specification](../../../spec/README.md) defines current Ash.
[CP-0031](../../proposals/CP-0031-remove-legacy-integer-cell.md) proposes
removing the legacy integer cell; that removal is not current behavior.

The question is whether a new acquisition, access, crossing or close can be
checked from facts already established for its constituents. The judgment
producer and consumer must agree on the subject, assumptions, activation and
point in control. A new composition checks its own relationships; it does not
reopen a checked initializer, body, method, imported helper or callback to
derive or re-verify its established behavior. These rules do not yet provide the
representation or checker needed to do that.

## Common resource judgments and concrete instances

The resource rules concern ownership, access and behavior at a scope boundary.
They are parameterized by an established resource contract `K`; neither the
payload type nor a cell's read/write operations define what a resource is.
Resource-specific behavior is expressed as declarations in the same type and
proposition language and checked by these common composition rules. It does
not introduce a separate cell-specific typechecking algorithm.
The same principle applies to effects and their operations: declarations
state their contracts and propositions, while shared request, handler,
matching and composition judgments use those facts. An effect row is the
coarser effect projection, not the operation's complete behavioral contract.
The current slice uses the existing cell resources as concrete instances and
also covers cleanup by its separate action and completion contracts. This
abstraction is a proposal for expressing their common facts, not a claim that
the current language already supplies a general user-defined resource API.
Private Store, registrations, regions, native and network resources remain
outside this slice and contribute only their established boundary facts.

The intended cell model is a mutable variable of type `T`. The resource that
provides its storage owns allocation, disposal and lifetime; the cell does not
introduce a second owner or a separate cell lifecycle protocol. Its state
operations and their effects use the applicable general contracts, while the
resource's established ownership, access, dependency and completion facts
are reused. The resource can be supplied through an existing boundary
contract; this slice does not define region or arena implementation rules.

The current generic-cell builtin, by contrast, has its own scoped activation,
provider and interpreter. The descriptions below record that current
operational and verification behavior as the before-state. They do not make
those special cell mechanisms requirements of the intended model. Mapping
the current behavior, including interception, read snapshots, dependency
crossings and failure, to the intended model requires correspondence evidence
or an explicitly specified semantic change; neither equivalence nor a new
implementation is assumed here.

| Question | Common judgment | Current concrete instance evidence |
| --- | --- | --- |
| What is introduced and who must complete it? | Acquisition introduces the activation and any completion obligations specified by its contract; failure and non-return retain their own cases. | A cell installs a fresh owned activation, its actual root, access, exact provider and interpreter; a cleanup arms a fresh action invocation with its context. |
| How can it be used? | An actual access or request must meet the resource's own authenticated operation and state contract. | Cell read/write select an actual target and root; cleanup invokes its already established action on completion. |
| What may cross or be retained? | The resource's declared crossing and retention contracts consume their applicable facts for the same actual value, owner and case. | Cells require complete dependency facts for their specified result and payload crossings and strict enclosing-owner retention; cleanup checks its action, saved result and operation payloads. |
| What happens when control moves or completes? | Capture, restore, normal completion and admitted abandonment preserve or transfer the same obligations according to `K`. | Cells release their root; cleanup distinguishes armed and running action phases and must finish the action under its close contract. |
| How are effects composed? | The resource's scope and completion contracts determine their exact row relationships and interpreter obligations. | The cell removes its exact local instance subject to the resource row rule; cleanup retains its action's applicable effects at close. |

### Resource parameters and interface requirements

The general declaration-requirement mechanism also applies when a resource
contract has a prerequisite on a parameter. For example, a hypothetical
resource parameter `T` might require `I<T>`. Its formation or acquisition
interface must instantiate that requirement under the same parameters, use
established evidence or retain an explicit scoped obligation, and carry the
result into typed Core. The [effect-parameter candidates](first-slice-effect-completion-rules.md#effect-parameter-interface-requirements)
illustrate the shared requirement, substitution and evidence rules; a resource
does not need a second checker merely because it is a resource. This does not
require every resource to have an interface bound.

Current Ash does not provide a general source resource-declaration facility.
Its [generic cell](../../../spec/static-semantics.md#generic-cell-foundation)
instead illustrates a different relationship: acquisition introduces a fresh
resource identity `R` and sealed `Provider<R,T>` evidence for the body. The
provider is an **output** of that successful acquisition, not evidence that a
hypothetical pre-acquisition `I<T>` requirement was supplied. Nor may the
acquisition assume its own future provider evidence to establish an earlier
prerequisite. The initializer is checked in the preceding scope; the new
identity and provider are available in the body.

A requirement on an existing parameter can apply before acquisition. A
requirement involving a fresh identity must instead be scoped where that
identity is bound; a fact about its actual runtime activation additionally
requires the corresponding successful acquisition case. Evidence and
obligations stay with their subjects, binders and authority policies. The
common substitution and composition rules must preserve them without
rechecking a resource implementation or a certified initializer. Effect or
resource parameters that specialize to the same type do not by themselves
identify their evidence, runtime activations or authorities.

Which resource contracts can declare such requirements, their syntax, the
precise input and output evidence interfaces and their source-to-Core
correspondence remain design gaps. A general parameter-requirement mechanism
does not by itself introduce user-defined resource families or change the
current builtin cell semantics.

Let `Resource(K)` denote a certified contract with applicable acquisition,
access, dependency, control and completion interfaces. Each interface retains
its subject, guard, actual activation, state and outstanding obligations. It
can be conditional and can have several guarded cases. It must not assume
that every resource has a mutable root, duplicable access, strict enclosing
retention, a sealed provider, an exact effect to remove, or a unique or
one-shot completion. `scope_K`,
`access_K`, `move_K`, `cross_K` and `complete_K` below are projections of
this established contract, not predicates true merely because a value is
called a resource. `Carry_J` denotes the outstanding obligations of this
particular new composition after its established discharges: it includes
every still-undischarged constituent, contract, premise and proof obligation,
with the same subject and original guard. It scopes local activation and case
witnesses at the boundary; it neither makes an ordinary structural obligation
conditional on runtime reachability nor treats an unknown as proved. This is
the obligation-preserving interface, not a chosen registry or an instruction to
repeat a proof.

```sequent
family abstract-resource-composition:
  J-Resource-Scope :=
    GAMMA |- Resource(K) [O_K] and the certified preceding behavior B_before [O_before] required by this scope
    GAMMA, local_K |- the certified body judgment B_body(local_K) [O_body], with its ordinary typing independent of case reachability
    each successful acquisition case is paired with the same actual preceding normal result, state and guard and supplies the activation and body-entry facts required by B_body and K
    scope_K covers preceding requests, failure and non-return before acquisition, and acquisition, body, completion, failure, non-return and unknown cases, and determines the same C, epsilon and B_scope
    each applicable cross_K, move_K and complete_K obligation is established or retained under its original guard and scope as O_ops
    O_scope = Carry_scope(O_K, O_before, O_body, O_ops, O_new), including the new composition's outstanding proof obligations O_new
    ===>
    GAMMA |- scoped_resource(K, B_before, B_body) : C ! epsilon ; B_scope [O_scope]

  J-Resource-Access :=
    GAMMA; L, phi |- the actual access or request satisfies the declared access_K premises for the same applicable activation and state
    GAMMA; L, phi |- the declared operation's operand, authority, selection and transition cases are covered by their certified contracts
    access_K determines B_access for this case and O_access = Carry_access includes all undischarged input, contract and new-composition obligations with their original scopes and guards
    ===>
    GAMMA; L, phi |- the new access composition has behavior B_access [O_access]

  J-Resource-Control-Transfer :=
    GAMMA; L, phi |- the actual activation a and applicable obligations belong to this control segment according to K
    GAMMA; L, phi |- this capture or restoration satisfies move_K for the same a and guarded source and destination states, giving disposition T
    O_move = Carry_move includes all undischarged input, contract and new-composition obligations with their original scopes and guards
    ===>
    GAMMA; L, phi |- this transfer has disposition T [O_move]

  J-Resource-Crossing :=
    GAMMA; L, phi |- this actual value v crosses the actual boundary of a in the same guarded case
    GAMMA; L, phi |- cross_K accepts the established facts it requires for this v, a and boundary
    O_cross = Carry_cross includes all undischarged input, contract and new-composition obligations with their original scopes and guards
    ===>
    GAMMA; L, phi |- this crossing is admitted by K [O_cross]

  J-Resource-Complete :=
    GAMMA; L, phi |- the same a has the completion obligations specified by K at this actual normal or admitted abandonment case
    GAMMA; L, phi |- complete_K covers its ordered work, dependencies, effects, outside obligations and all applicable failure or unknown cases as behavior B_complete
    O_complete = Carry_complete includes all undischarged input, contract and new-composition obligations with their original scopes and guards
    ===>
    GAMMA; L, phi |- this completion has behavior B_complete [O_complete]
```

These are composition schemas: each consumes certified constituent facts and
checks the relationships introduced at the new boundary. They do not traverse
or reverify an already certified fragment. A successful acquisition,
transfer, access or completion is a conditional case, not a claim that the
operation occurs or terminates. When a particular contract establishes unique
one-shot authority, moving it preserves that discipline; a reusable proposition
does not duplicate it. Other resource and future continuation capabilities
need their own contracts. Unknown facts stay as scoped obligations, and a closed no-error
result requires the applicable obligations to be discharged.

For example, the existing generic cell's declarations can express, for an
authenticated builtin selection of a particular activation, that a successful
read returns its current value and preserves the root, while a successful
write installs its actual replacement and returns `Unit`. Their propositions
must also state the applicable payload, dependency, retention, authority,
effect and failure conditions. The common request and selection judgments
still allow a nearer source handler to intercept either operation. A call's
effect row alone proves neither which interpreter is selected nor which value
is returned. These are contract descriptions for an existing builtin, not a
new surface syntax or a user-extensible resource facility.

The `J-Cell-*` statements below record concrete cell contract facts and their
operational correspondence, including its exact provider, read/write, root
and row facts. They are to be expressed as applications of the common rules
and declared propositions, not retained as separate cell-specific
typechecking rules or a second verification pass. The cleanup rules in the
[close record](first-slice-close-rules.md#introduce-and-complete-one-cleanup-owner)
record the action and phase contract in the same way. A fact established by
one rule is reused at the next boundary. The existing concrete statements
have not yet all been translated into declarations and applications of the
common rules; that translation and its correspondence and soundness remain
work to establish before replacing any legacy checks.

## Cases and assumptions

A covered execution case associates a condition with one entry and activation,
its actual value and ordinary type, dependency facts, relevant control and
completion facts, and a post-state. A case can summarize many executions; every
conclusion below must hold for all executions it covers. Guards are conditional,
not assertions that a path occurs. Unknown cases remain covered and cannot prove
independence, a target or a close merely because no contrary fact is listed. An
empty normal-return cover requires proof that there are no normal returns; it
does not imply termination or discard. The [normal-return
judgment](first-slice-normal-return-judgments.md) describes this coverage and
correlation.

For this record, `sigma` denotes the relevant symbolic resource state, not the
whole runtime heap or trace. When established, `live(sigma,a)` identifies a
particular live cell activation, `birth(a)` its strict enclosing activations at
acquisition, `root(sigma,a) = v` its current value, and `owns(sigma,a)` its
single completion obligation. The names describe facts rather than a chosen
runtime or certificate representation. A lexical `R` and a static acquisition
site do not identify a unique runtime activation; recursive or repeated entries
are distinct. Each case binds these facts together. A join may overapproximate
alternatives, but must not invent an exact pairing of a value, owner, root or
state from different cases.

`deps(v,D)` denotes established dependency facts for the actual value `v` in
this case, including applicable hidden captures, selected evidence and indexed
operation metadata. Such facts may be incomplete. `independent(v,a)` means that
the established facts prove `a` absent from the actual dependencies of `v`. A
sound complete upper bound with `a` outside it can establish independence. An
incomplete set without `a` cannot. The exact abstraction, completeness test,
condition language and derivation of these facts remain open; `deps` is a
required interface, not a claim that an ordinary type proves its result.
Ordinary value, call and evidence judgments supply their actual relationships,
including effects and possible requests. Selected allocation, backing-region and
other excluded-scope dependencies remain established external facts or explicit
obligations.

For a particular domain `S` of owners, `Cover(v, S, D)` guarantees that `D`
contains every dependency of `v` on an owner in `S`. The
[dependency-cover rules](first-slice-dependency-cover-rules.md#independence-retention-and-predecessor-facts)
give the shared consequence for deriving independence of a particular owner
from such a cover; the resource rule consumes that result without reexamining
the value or proving it a second time. An overapproximation may retain an owner
even if a particular execution does not depend on it. An incomplete summary or
an unknown case supplies no complete cover merely by omitting that owner.

## R1–R2: scope and row composition

The cell-named judgments in this and the following sections are worked
instances and correspondence obligations for the shared resource and effect
judgments above. Their names organize the existing trace; they do not specify
new cell-specific typechecker rules or authorize repeating a certified check.

The [legacy
scope](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
checks its initializer as `Int` before introducing its fresh `R`; the [generic
scope](../../../spec/static-semantics.md#generic-cell-foundation) checks it
against the fixed monomorphic payload `T`. In either case the body receives a
fresh rigid identity, a duplicable non-owning access, sealed provider evidence
and an exact local cell interpreter. `T` may be abstract in the surrounding
context. A polymorphic helper remains conditional on its type and row parameters
and selected evidence; specialization must preserve those constraints and actual
dependency facts. Neither `T` nor an identity-free result type proves
independence.

The following candidate judgment checks the outer scope from an established
initializer judgment `B_i` and a single established body judgment `B_b`,
conditional on the fresh owner and its access. `I` is the exact unary legacy or
binary generic effect instance, `P` is respectively `Int` or `T`, and `C` is the
body result type. `admit_init` means all covered normal initializer cases
satisfy the acquisition rule below. `admit_body` means all covered body returns,
crossings and completion cases satisfy the applicable rules in this record and
the separate control rules. Neither premise licenses rechecking the constituent.
`Scope` must cover all normal, request, unknown, non-return and failure behavior
under those premises, interpreting the cell's selected builtin requests and
preserving other applicable requests. Failure disposal is not necessarily the
same as a successful scope close. These names collect obligations; their checkable
representation and coverage rules remain unresolved.

The body has one certified judgment, with an ordinary type, row and scope
projection independent of behavioral assumptions, and a behavioral projection
parameterized by fresh symbolic indices for the actual post-acquisition case.
For each covered normal
initializer return, the successful acquisition case must establish the body's
entry assumptions for the **same** fresh activation, initial root and its
dependencies, birth enclosure, surviving outer state and guard. The symbolic
body judgment is instantiated with those facts; neither its body nor the
initializer is rechecked. If this correspondence is not established for a
covered acquisition, the unconditional scope conclusion does not follow.

```sequent
J-Cell-Scope :=
  GAMMA; L, entry |- initializer : P ! epsilon_i ; B_i
  R is fresh and rigid for the body and I is the exact cell instance at R, P
  a and sigma are fresh symbolic body-entry indices
  GAMMA, R, access : Handle(R,P), sealed_provider(R,P); L |- ordinary(body) : C ! epsilon_b
  GAMMA, R, access : Handle(R,P), sealed_provider(R,P); L, body_entry(a, sigma) |- behavior(body) : B_b(a, sigma)
  ordinary(body) and behavior(body) are projections of one certified body judgment
  GAMMA; L, entry |- admit_init(B_i, P, R)
  for each covered successful acquisition case yielding a_case, sigma_case, its correlated facts entail body_entry(a_case, sigma_case)
  each such case instantiates B_b at that same a_case, sigma_case
  GAMMA; L, entry |- admit_body(B_b, R, I)
  resource_remove(epsilon_b, I) = epsilon_rest
  epsilon_out = epsilon_i union epsilon_rest
  R is absent from C, epsilon_out, escaping schemes and retained outward evidence
  ordinary kind, type, row and structural continuation premises hold
  ===>
  GAMMA; L, entry |- resource(R, initializer, body) : C ! epsilon_out ; Scope(B_i, (a, sigma) -> B_b(a, sigma), I)
```

The notation `Handle(R,P)` abbreviates the actual API's handle type, not a new
common source type. The initializer is checked in the preceding environment; no
access, provider or runtime owner for `R` exists while it executes. A normal
initializer case may proceed to acquisition only after its own effects and value
have been produced. An initializer that requests, diverges or is abandoned
follows the ordinary sequencing and control rules, and does not by itself create
an owner. The result type and outward row are separate from the actual-value and
completion checks.

`resource_remove` is a candidate partial operation: remove the exact instance
when present; preserve the row if it is proved absent; reject removal when an
open tail makes presence ambiguous. The current
[source](../../../src/elaborate.rs#L14309) and
[Core](../../../src/core/validate.rs#L14133) paths use structural exact
removal and preserve the row on its `Missing` result. Source qualification
defers that removal as an equation when cleanup-row equations are pending;
the stated result applies when the removal is resolved. Core takes the direct
path. That result does not by
itself prove inequality of every unresolved parameterized instance. The
candidate's complete semantic absence premise is therefore not established
solely by the current `Missing` result. The closed-row correspondence below
uses the additional fresh-identity and successful scope premises; open tails
and unresolved substitutions still require their own correspondence evidence.
No current admission difference is asserted here. Union is the existing partial row union,
retaining initializer requirements and all unrelated body instances. Ordinary
handlers have a separate requirement for their target and this rule does not
relax it. The current resource-scope specification says to remove the instance
but does not spell out the absent and ambiguous cases; the intended
specification rule needs clarification before this candidate is treated as a
full normative translation. The [Core-validation
list](../../../spec/elaboration.md#validation-boundary) also says `Int` for each
resource initializer, whereas generic static semantics and [the
validator](../../../src/core/validate.rs#L14413) use `T`. These discrepancies
are not resolved here.

### Resolve the scope's type and row premises

For the proposed generic-cell judgment, the initializer's value type is the
same fixed monomorphic payload `T` used by the access, provider and operation
instance in the body. The initializer is checked in the preceding environment;
it does not receive the fresh owner or provider. This follows the generic
[static rule](../../../spec/static-semantics.md#generic-cell-foundation),
generic lowering and the current validator. The conflicting `Int` sentence in
the Core-validation list should be reconciled by a specification correction;
it is not a rule that a generic payload must also have type `Int`. This record
does not itself amend the specification. The legacy integer family remains
current until its separate removal proposal takes effect.

The resource row operation has a different admission rule from an ordinary
handler: a body need not actually request its newly introduced cell effect.
The following candidate rules make the present and proven-absent cases
explicit. `lacks(epsilon,I)` means absence throughout the complete row,
including its tail and exact instantiated arguments, under the same guarded
type and row substitution; a structural mismatch between unresolved
parameters does not establish it. Both rows must satisfy ordinary kind, scope,
row-formation and lacks requirements.

```sequent
family resource-scope-row-removal:
  J-Resource-Remove-Present :=
    GAMMA; Phi, phi |- {I | rho} row ok and rho lacks I
    ===>
    GAMMA; Phi, phi |- resource_remove({I | rho}, I) = rho

  J-Resource-Remove-Absent :=
    GAMMA; Phi, phi |- epsilon row ok and lacks(epsilon,I)
    ===>
    GAMMA; Phi, phi |- resource_remove(epsilon,I) = epsilon
```

In the first rule `{I | rho}` denotes a row with explicit member `I` and
remainder `rho`; it is metanotation and also permits a closed remainder. The
second covers a closed row or an open row whose known members and tail
establish absence. For a parameterized known member,
equality or inequality with `I` is established for the complete effect
identity and its arguments. If equality remains conditional, retain both
guarded cases and their constraints, or a conditional obligation; do not turn
failed matching into a proof of absence. A tail whose membership is unknown
does not satisfy either rule merely by being open. The separately proposed
[row relationship](first-slice-close-derivation-rules.md#retain-the-open-row-relationship)
can retain exact input/output information as a proposition, but does not by
itself authorize a new admission for an ambiguous tail. Any extension of the
current admitted cases requires its own semantic proposal and evidence.

For a closed known-absent example, a cell body whose only effect is an
unrelated `Log` has its `Log` requirement preserved. For a present example,
`{Ops<R,T>, Log}` becomes `{Log}` when the exact `Ops<R,T>` instance is
discharged. In both cases the initializer's already established effects are
then combined using the existing partial row union, and the fresh `R` must
not escape. The target operation is specified once for the composition; the
initializer and body are not rechecked.

These rules are a proposed precise account of the two scope cases, not a claim
that the current structural missing-member implementation establishes every
inequality needed for a generic specialization. The following restricted
correspondence does not resolve the missing specification wording or the
remaining cases needed before replacing the existing check.

#### Closed-row `Missing` under a successful resource scope

Suppose the resolved body row is closed, the exact removal of `I = Ops<R,T>`
returns `Missing`, and resource checking succeeds, including its deferred
escape checks. Assume each later substitution is well scoped at the resource
boundary: it fixes the fresh rigid `R` and cannot introduce `R` into any free
parameter or remaining inference variable in that row. Under these conditions
`lacks` for this closed body row and `I` follows; no body analysis is repeated.

The reasoning uses more than `Missing`. The [source removal](../../../src/elaborate/cleanup_rows.rs#L712)
keeps the resolved row on `Missing`, and the [scope](../../../src/elaborate.rs#L14297)
unions that row with the initializer's effects. Successful union retains its
known members, while the scope rejects `R` in the resulting outward row and
also checks [deferred inference escapes](../../../src/elaborate.rs#L13729).
Consequently a retained member such as `Ops<R,U>`, even with `U` different
from `T`, would expose `R` and the scope could not pass. A remaining member
such as `Ops<A,U>`, where `A` belongs to the preceding scope, cannot become
`Ops<R,T>` under the stated substitution: the specification makes `R` fresh
and rigid against enclosing parameters and other acquisitions. A different
effect identity also stays different. There is no tail to introduce another
member. For example, an inner resource `B` may retain an enclosing resource's
`Ops<A,Int>`; it is not the inner `Ops<B,Int>` and remains outward. The
existing [nested-cell test](../../../tests/resource_scope_typing.rs#L2235)
exercises distinct enclosing and inner identities with the same payload.

Current Core independently [preserves the row on `Missing`](../../../src/core/validate.rs#L14133)
and checks the resource node's expected union; its [type-scope traversal](../../../src/core/validate.rs#L12040)
binds the identity in the body, not in the resource node's outward annotation.
This is correspondence evidence for the conditional argument, not a request to
run Core validation again on a certified fragment. In particular, this does
not derive semantic absence from an arbitrary open-row `Missing`, an unresolved
cleanup equation, an unchecked escape or a substitution allowed to introduce
the local identity. Those cases retain their scoped obligations until their
own correspondence is established.

#### Open tails and deferred removal

For an open body row with no exactly matching known member, current exact
removal returns `Missing` only if the tail already records the **exact** target
in its lacks set; otherwise it returns `Ambiguous`. An exact known member is
removed by the separate present case. The tail constraint does not by itself
establish semantic absence of the target from every parameterized known member.
The [row kernel](../../../src/types.rs#L977) makes that distinction.

There is a narrower current-path consequence. If `Missing` is resolved on an
open row, the full effect row is used for resource checking, and that same
open tail and its lacks facts survive the initializer union to the outward
escape check, the scope cannot pass: the retained lack `Ops<R,T>` itself
mentions the local `R`. Successful [union](../../../src/types.rs#L892)
retains the lacks facts, and the source
[escape traversal](../../../src/types.rs#L395) visits their arguments. Core's
[scope-variable collection](../../../src/core/validate.rs#L12454) likewise
visits them, and its resource node's outward annotation is outside the body
binder. This is a conditional correspondence about the actual full row; it is
not a claim that every such internal row is reachable from a source program or
that every open-tail removal is rejected. In particular, a tail solved to a
closed row before the relevant outward check no longer carries tail metadata;
its resulting row, constraints and escape checks need to be considered at
that later point.

If cleanup qualification has a pending row equation, the source path records
`Remove(row, I, absent)` instead of deciding the removal immediately. Its
[solver](../../../src/elaborate/cleanup_rows.rs#L467) resolves the input and
applies exact removal during iteration, then checks deferred resource escapes
after solving. A `Missing` seen during an intermediate iteration is not a
certificate of the final case. If the converged input is the same closed row
and the final scope and substitution premises above hold, the closed-row
argument applies to that result. An open converged row that retains the target
lack at the outward check has the conditional escape consequence just stated.
The record does not establish all possible equation solutions or an admitted
source example for either case; those remain correspondence work, using the
existing row and scope facts rather than rechecking the body.

### Source-to-Core correspondence for the generic cell

The source rule checks the initializer and body under different scopes. The
Core constructor must preserve that difference, the fixed payload type and
the exact provider identity, together with the children's already established
behavior and outstanding obligations. This is a candidate correspondence
for the new type-system interface, not a claim that current Core already
carries these certificates or that current validation has been removed.

The current [resource scheduling](../../../src/elaborate.rs#L16630) checks
the initializer against the fixed generic payload before
[`enter_resource_body`](../../../src/elaborate.rs#L14218) installs the
body-local handle and active acquisition. The resulting body includes the
provider wrapper and the original user computation; it is the actual body
child of the [constructed resource node](../../../src/elaborate.rs#L14382).
The Core [`ResourceScopeNode`](../../../src/core/effect.rs#L353) stores the
acquisition authority, typed handle and two child node identities. Its exact
effect instance is reconstructed from the handle type, but shape reconstruction
alone does not authenticate the provider. Core
[`validate_resource_node`](../../../src/core/validate.rs#L14413) additionally
checks authority and origins, child types and outward row, and the unique
matching provider method owners and definitions. The
[type-scope traversal](../../../src/core/validate.rs#L12030) discharges the
resource identity from the body child, not the initializer child. These are
different checks; a typed handle alone does not establish all of them.

For the proposed correspondence, `i_core` and `b_core` are the *same checked
children* supplied by their source-to-Core judgments. `b_core` includes any
provider wrapper introduced for this acquisition. `theta` is the admitted
renaming or instantiation from source binders to the matching Core identities;
it preserves each obligation's subject, guard and binders. `Corr_init` relates
the initializer's source and Core values, states, guards, observations and
obligations; source and Core states need not be identical. `ProviderCore`
authenticates the exact sealed provider and method contract for this same
acquisition, not a provider inferred from a matching spelling. The provider's
established wrapper correspondence must account for its behavior and
obligations under an appropriate source/Core value and state relation; it
cannot be assumed to disappear merely because it is generated. Lowering and
scope obligations are separated by their actual scope and phase: preceding-
scope obligations remain outside, and body-local obligations are scoped below.
`ScopeObl` carries body and provider obligations inside fresh binders for
`R`, `h` and any activation, state or case witnesses they use. It preserves
their original guards and assumptions. An obligation about a body-entry case
is guarded by that same successful acquisition and its correlated entry;
an ordinary unconditional structural obligation is not made conditional on
runtime reachability. No local witness becomes free at the outer boundary.
`Scope_bind(R,h,...)` likewise binds the body-local identities in the
resulting behavior contract; they are not free names in the enclosing scope.

```sequent
J-Generic-Cell-Source-Core :=
  GAMMA |- initializer : T ! epsilon_i ; B_i [O_i]
  the initializer's certified source-to-Core judgment supplies i_core with T_theta, epsilon_i_theta and behavior B_i_core; Corr_init relates B_i and B_i_core, preserving O_i under theta
  R is a fresh rigid Type identity, absent from the initializer's scope, and h is this acquisition's fresh body-local handle
  GAMMA, R, h : Cell<R,T>, Provider<R,T> |- body : C ! epsilon_b ; B_b [O_b]
  the body's certified source-to-Core judgment supplies b_core under those same body-local bindings, preserving C, epsilon_b and O_b under theta
  ProviderCore(authority,h,R,T,b_core,B_core,Corr_wrapper) establishes its complete behavior B_core(a,sigma) and its correspondence to B_b under theta, with obligations O_provider
  node = Resource(authority, typed_handle(h, Cell<R,T>), i_core, b_core)
  the node's child scopes give R, h and provider authority only to the body and keep the initializer in GAMMA
  J-Cell-Scope's row removal, union, identity-escape, behavior and all-case premises hold for these same children and authority, or retain preceding-scope obligations O_pre and body-local obligations O_body_scope
  the node's Core result type and effects are C and epsilon_i union resource_remove(epsilon_b, Ops<R,T>), under theta
  ScopeObl binds R, h and applicable case witnesses around O_b_theta, O_provider and O_body_scope, preserving each original guard
  ===>
  GAMMA_theta |- node : C_theta ! epsilon_out_theta ; Scope_bind(R,h,B_i_core,(a,sigma) -> B_core(a,sigma),Ops<R,T>_theta) [O_i_theta union O_pre union ScopeObl(R,h,O_b_theta,O_provider,O_body_scope)]
```

`Scope_bind` here is the conditional behavior of `J-Cell-Scope`: it connects each
actual initializer result to the successful acquisition and the body judgment
at that same fresh activation. Requests, failure, non-return and unproved
boundary facts remain in their established cases and obligations. `B_core`
is the **complete body-child** behavior, including the wrapper according to
`ProviderCore`; it is not assumed identical to the unwrapped source body.
Its claimed correspondence to `B_b` needs the stated proof and obligations.
Likewise, the Core initializer's identity and
behavior are not reconstructed by traversing it a second time. If any
correspondence or row premise remains conditional, its obligation is carried
with the result in that scoped interface rather than silently assumed. A
closed use discharges each applicable obligation for the same guarded case;
the scoped interface does not assert that an acquisition or body executes.

The current Core validator reconstructs several metadata and provider facts
from the assembled program. This proposal identifies the facts a certified
constructor and child interfaces must preserve so a later composition can
reuse them. It does not claim that the current provider scans and all child
checks are identical to source checking, nor that this schema proves the
required source/Core behavioral correspondence or covers linked-only checks.
The exact provider-wrapper behavior relation, discharged versus outstanding
row constraints, and representation and transport of certified child facts
remain obligations for the implementation design and system soundness proof.

### Generated provider wrapper and method requests

The current generic-cell resolver constructs the provider wrapper around the
user body. For each fixed method ordinal it generates one binder, one fresh
parameter and a forwarding method whose body performs the corresponding
`Ops<R,T>` operation on that parameter; the generated lexical evidence
application is the exact `Provider<R,T>`. The wrapper is a block containing
that evidence declaration followed by the original body. See
[`finish_resource_expression`](../../../src/resolve.rs#L11298). Core
[resource validation](../../../src/core/validate.rs#L14460) checks, for each
method, the matching lexical owner and one definition whose callable body is
the corresponding request with its parameter as operand. It authenticates
the exact authority, method and operation identities and type arguments;
the check is not a proof that a call selects the builtin cell interpreter.

The following candidate rules isolate the facts the generated wrapper must
produce for the source-to-Core correspondence above. `ProviderDesc` is the
authenticated descriptor for this acquisition's actual generated evidence,
method binders and exact instantiated signatures. It contains the complete
argument and metadata contracts, not just the method names. `Corr_wrapper`
relates the source resource body and the Core wrapper's actual values,
states, requests, failures, obligations and observations; it is conditional
on the generated binding and callable contracts. A source and Core state
need not be identical. `O_wrapper` remains inside the body-local scope with
its original case guards; ordinary structural obligations remain
unconditional even on paths that never call a method. `LocalObl(R,h,O)`
attaches obligations to these already-bound body identities; the enclosing
resource interface scopes them when it closes the body.

```sequent
family generic-provider-correspondence:
  J-Generic-Provider-Descriptor :=
    GAMMA; Phi |- authority is this generic acquisition with fresh R, handle h, provider e and distinct method binders m_read and m_write
    GAMMA; Phi |- the authenticated API establishes Cell<R,T>, Provider<R,T>, Ops<R,T> and their exact ordered method and operation signatures
    GAMMA; Phi |- each generated method binder has the matching certified single-parameter forwarding callable contract for this same authority and ordinal, with obligations O_desc
    GAMMA; Phi |- the descriptor covers each callable's actual lexical inputs and type, operation and evidence metadata under those obligations
    ===>
    GAMMA; Phi |- ProviderDesc(authority,h,R,T,e,m_read,m_write) [LocalObl(R,h,O_desc)]

  J-Generic-Provider-Wrapper :=
    GAMMA; Phi |- ProviderDesc(authority,h,R,T,e,m_read,m_write)
    GAMMA; Phi |- the checked Core wrapper binds these same method callables and lexical evidence before the same certified user-body child
    GAMMA; Phi |- certified binding and callable-construction contracts compose with that body's certified behavior to give complete guarded B_core(a,sigma), including effects, failures, dependencies and normal entries
    GAMMA; Phi |- Corr_wrapper relates B_core(a,sigma) and the same body child to the source resource behavior, with obligations O_wrapper including O_desc
    ===>
    GAMMA; Phi |- ProviderCore(authority,h,R,T,wrapper_core,B_core,Corr_wrapper) [LocalObl(R,h,O_wrapper)]

  J-Generic-Provider-Method-Request :=
    GAMMA; Phi, phi |- ProviderDesc(authority,h,R,T,e,m_read,m_write) and the actual selected method is m_i for its authenticated read or write ordinal i
    GAMMA; Phi, phi |- the established callable and operand contracts produce an actual normal argument v with dependencies D and state s
    GAMMA; Phi, phi |- this invocation and its forwarding request preparation succeed in that same case
    GAMMA; Phi, phi |- the certified forwarding transition relates the request operand to the same actual argument v and establishes its sound dependency cover D_request at request formation
    GAMMA; Phi, phi |- the request frame uses the callable's actual saved instantiation theta for the exact generated operation op_i of Ops<R,T>
    GAMMA; Phi, phi |- all outstanding descriptor, operand, invocation and request obligations for this same case are retained as O_method
    ===>
    GAMMA; Phi, phi |- the call introduces request(op_i,instantiate(Ops<R,T>,theta),v,D_request) with its established local residual [O_method]
```

The descriptor rule produces static authority and callable interfaces; it does
not create a dynamic cell owner. The wrapper rule does not treat generated
bindings as semantically invisible: entering them and constructing callables
can have applicable representation, storage or disposal failures, and their
contracts must cover those cases or retain an unknown. It also does not run
either method just because the wrapper is entered. The method rule concerns
only an actual normal argument and successful invocation/request preparation;
argument requests, failure, non-return and call preparation failures have
their own cases. Neither rule rechecks the user body or a certified callable.

The request's payload and exact metadata carry their own complete dependency
cover. The access argument's ordinary type is not a substitute for that
cover, and `T` or selected evidence can carry additional metadata facts. The
generated method's dependency interface must account for the actual callable
captures and indexed operation metadata under the same instantiation; it may
not assume every method closure is resource-independent. The existing
[`Sources` and cover rules](first-slice-dependency-cover-rules.md#producer-contracts-for-a-new-value)
compose those established facts without inspecting the method again.

After the request is produced, ordinary nearest-boundary selection applies.
A nearer source handler can receive it; only an exact selected builtin cell
case uses the cell read or write contract and its actual target and root.
Selection, payload crossings, reply dependencies, eventual completion and
their failure cases remain separate. `ProviderDesc` or an effect row alone
does not establish a particular selection, a successful reply or a safe
replacement. The per-method correspondence, complete generated metadata
cover and wrapper construction/failure cases are still system and
implementation correspondence obligations, not completed proofs.

## R3 and R5: acquire, select, read and write

These rules describe normal successful cases of the [cell execution
steps](../../../spec/dynamic-semantics.md#scoped-cell-execution), not a
source-level exception model. `enclosing(sigma)` is the established set of
resource activations strictly enclosing the prospective acquisition at that
actual entry. For each case, `D subset-of birth(a)` checks every actual retained
resource dependency. It excludes `a` itself and younger, incomparable or cyclic
retention. Facts about backing or non-cell owners need their own applicable
external checks. The birth relation is fixed when `a` is acquired; restored
control cannot make a younger owner enclose an older activation.

```sequent
J-Cell-Acquire :=
  an established normal initializer case returns v : P in state sigma
  deps(v,D) is a complete upper bound for relevant retained resource dependencies
  a is fresh for this successful execution and birth(a) = enclosing(sigma)
  D subset-of birth(a)
  sealed API identity, handle, provider and exact interpreter authority are authenticated
  acquisition preparation succeeds
  ===>
  acquire(v,P,sigma) |- live(sigma',a), owns(sigma',a), root(sigma',a) = v, access(a,P)
```

The conclusion describes one successful case, with `sigma'` preserving unrelated
live owners and facts. It does not claim acquisition preparation always
succeeds. Each possible initializer result and activation needs its own proof,
under its own guard. Ordinary errors precede dependency admission. Current
analysis also accepts a conditional immutable predecessor proof when separate
validity and structural-birth premises establish the same safety relationship;
it is not a general rule that any older or unequal owner encloses `a`. The
[proposed predecessor interfaces](first-slice-dependency-cover-rules.md#focused-predecessor-producer-and-consumer-correspondence)
make the needed conditional facts explicit. Their coverage and correspondence
to current admission remain unproved, so the displayed subset rule is
sufficient, not a claim to admit every current program. See
[retention checking](../../../src/core/capture/value.rs#L5981).

A request first uses the ordinary operation and provider contracts and the
established [nearest-boundary
judgment](first-slice-nearest-boundary-judgments.md). Effect-row membership does
not select a cell. Only after the exact builtin boundary is selected do the
following candidate rules apply. The selected operation, complete instantiated
identity and actual handle must authenticate the same live activation. A source
handler can intercept first, including the exact cell instance; its own
established clause and reply behavior then apply. An intercepted write alone
does not update the cell, though its clause or resumed computation may perform
separate writes.

```sequent
family cell-access:
  J-Cell-Read :=
    selected_builtin(request, read, a, P) and authenticated_handle(request,a,P)
    live(sigma,a) and owns(sigma,a) and root(sigma,a) = v
    deps(v,D) holds for this root in sigma
    reply preparation succeeds
    ===>
    read_case(request,sigma) |- reply(v,D), sigma

  J-Cell-Write :=
    selected_builtin(request, write, a, P) and authenticated_handle(request,a,P)
    live(sigma,a) and owns(sigma,a) and root(sigma,a) = old
    replacement v : P and deps(v,D) is a complete relevant upper bound
    D subset-of birth(a)
    reply and replacement preparation succeeds
    ===>
    write_case(request,v,sigma) |- reply(()), sigma[a.root := v]
```

Each actual possible target and replacement must meet these premises in its own
correlated case; a possible-target set alone is not proof that any one target
was selected. Other owners, snapshots and unrelated roots persist. Read returns
a snapshot of the actual root and its dependency facts at that point. A later
write changes the selected current root, not the old snapshot; it does not
freeze mutable cells reachable from that snapshot. A write that fails
preparation leaves the old root intact even though its operand may already have
effects. Terminal disposal can fail after replacement. Neither failure is an
extra source branch. A later clearing write cannot make an earlier invalid
retention valid.

The [snapshot fixture](../../../tests/resource_scope_typing.rs#L1614)
distinguishes an independent old closure from a later same-typed closure
retaining an outer cell; [self and younger retention
cases](../../../tests/resource_scope_typing.rs#L1761) also include later
clearing. The [handler-reply
fixture](../../../tests/resource_scope_typing.rs#L1818) uses the actual
intercepted read reply, not the builtin root. These tests were inspected, not
run for this record.

## R4: actual result and payload crossing

The following rules apply to a covered normal result or request payload,
respectively. `crossed` is supplied by established ordered control and boundary
selection, not inferred from a row. `recipient` is the selected interpreter or
handler. `trusted(a,recipient)` applies only to the owner's own admitted
interpreter, not arbitrary source handlers. Every possible crossing and result
must satisfy its relevant premise; other dependencies are retained rather than
erased.

```sequent
family cell-crossing:
  J-Cell-Result-Cross :=
    a covered normal body-return case has actual value v and closing activation a
    independent(v,a)
    outward type, row, scheme and evidence do not expose the local identity
    ===>
    result_crossing(v,a) is admitted

  J-Cell-Payload-Cross :=
    a covered request case has actual operand v and recipient
    for every activation a in crossed(request,recipient), independent(v,a) or trusted(a,recipient)
    ===>
    payload_crossing(request,v,recipient) is admitted
```

An outer-dependent value may cross an unrelated inner scope if the recipient
remains inside its own owner; checking the inner owner does not discharge the
outer dependency. A known closure, selected field, imported helper, method or
reply supplies facts about its actual output. Merely executing a dependent
callback does not make its independent returned value dependent; returning the
dependent callback does. The [paired callback
cases](../../../tests/resource_scope_typing.rs#L667) illustrate this
distinction. A request payload is checked even when the eventual body result is
independent. Strict inputs must complete before their result is published. Where
a relevant independence proof is unavailable, the candidate leaves an obligation
and cannot admit unconditional crossing; current behavior conservatively rejects
unproved escape, although the exact current unknown-to-rejection path remains to
be classified.

## R6: capture, restore and completion

A cell owner and its current contents move with the selected captured segment.
`outside` denotes untouched control; it retains its own obligations. The next
rules consume established boundary-selection and close facts from the [discard
ownership trace](first-slice-discard-ownership-trace.md), not from the
value-dependency judgment. `capture` and `restore` describe transfer of the same
activation and obligation; they do not allocate, copy or release it.

```sequent
family cell-completion:
  J-Cell-Capture-Restore :=
    selected capture contains live activation a with root v and its completion owner
    the established capture and restoration contracts preserve ordered control and outside obligations
    ===>
    resuming that capture restores the same live activation a, root v and completion owner

  J-Cell-Normal-Close :=
    a covered normal body-return case has result v and live owned activation a
    result_crossing(v,a) is admitted
    required close and external backing obligations are established
    ===>
    normal_close(a,v) schedules release of a and preserves v and outside obligations

  J-Cell-Owned-Discard :=
    an established selected capture owns a live activation a
    the owned closure and its structural close order are established
    outside completion and interpreter requirements remain satisfied
    the close actions and their residual effects satisfy the separate discard contract
    ===>
    discard schedules a for close at its owned position and preserves outside obligations
```

These judgments require the contracts they cite; they do not prove closability,
action effects or absence of skipped completion by naming them. They schedule
release; they do not prove that preceding actions terminate or disposal cannot
fail. On a successful close reaching that position, the activation is released
once. Normal or
abandoned inner close precedes outer close. Captured cells remain live and
charged until completed; divergence is not evidence of release. An inner discard
that does not own a surrounding cell leaves that owner and its required
completion intact. The [owned and outside-owner typing
cases](../../../tests/resource_scope_typing.rs#L641) are evidence for the
distinction, not a proof of the candidate rules.

## Ownership facts for cell and cleanup control checks

The preceding rules say what a successful operation does. The following
candidate invariants connect those facts to specific malformed-control checks
in the current machine. They are propositions in the proposed judgment, not
runtime registries or a request to rewalk a verified fragment. All facts are
indexed by the same covered execution case and actual machine ledger. A
symbolic owner or count in one alternative cannot be paired with the state of
another. Unknown ownership, value representation or outside behavior remains
an obligation.

Let `M` be the finite set of owners charged to the machine's resource-owner
counter, including cells and any excluded owner kinds sharing that counter; let
`Q` be its cleanup invocation owners. These are logical accounting sets, not
source values. Each owned cell occurs exactly once in `M` with its actual
activation, fixed payload type, exact instantiated provider identity, current
root and one completion obligation. Each cleanup occurs exactly once in `Q`,
with phase armed or running and its actual action, context and applicable saved
result or close continuation. Handles, aliases and action copies are non-owning
and add neither owner nor count. A counted owner can be in active control, an
owned capture, an owned close, or a frame temporarily held by an in-progress
return step; a running cleanup still counts. Its exact location and phase are
part of the particular case. A capture may itself be nested: an established
ownership interface states which owners move without reopening that capture.

Write `OwnerInv(s, M, Q)` for those uniqueness and placement relationships,
`resource_count(s) = |M|`, `cleanup_count(s) = |Q|`, and the applicable
fresh-key and owner-identity facts. The equalities apply at the correlated
machine points where the count is used; in a return transaction, a popped
frame still held by the transition is included until its successful release or
finish. They do not promise a consistent live machine after terminal failure
disposal has begun. When the top-level machine starts with empty ledgers, its
initial interface establishes the empty case. A fragment entered inside an
existing context instead requires that context's certified accounting facts;
excluded mechanisms that share the ledger must state their own additions,
removals and transfers. No part of this slice derives those contracts from
their implementations.

### Introduce and move the counted owners

The first two rules are consequences of the successful cell and cleanup
acquisition cases, with their actual post-publication states. Freshness is for
the actual execution, not just a lexical binder. `Q + o` and `M + a` add one
fresh owner; `s'` includes the corresponding count increment. The cleanup's
action is the Core action and its established callback/context from
[`Core-Cleanup-Acquire`](first-slice-behavior-coverage-rules.md#frame-transitions).
Each acquisition's separate failure cases remain in its behavior cover.

```sequent
family owner-publication:
  J-Account-Cell-Acquire :=
    GAMMA; L, phi |- OwnerInv(s, M, Q)
    GAMMA; L, phi |- J-Cell-Acquire succeeds at s with fresh a, root v, payload P and exact instance I
    GAMMA; L, phi |- s' is this same successful publication and resource_count(s') = resource_count(s) + 1
    ===>
    GAMMA; L, phi |- OwnerInv(s', M + a, Q) and cell_owner(s', a, v, P, I)

  J-Account-Cleanup-Acquire :=
    GAMMA; L, phi |- OwnerInv(s, M, Q)
    GAMMA; L, phi |- Core-Cleanup-Acquire succeeds at s with fresh armed o and action contract A
    GAMMA; L, phi |- s' is this same successful publication and cleanup_count(s') = cleanup_count(s) + 1
    ===>
    GAMMA; L, phi |- OwnerInv(s', M, Q + o) and cleanup_owner(s', o, armed, A)
```

The publication cases must establish disjointness from existing owners, the
actual new count and preservation of the unrelated ownership facts. A fresh
resource key also requires the counter's actual freshness invariant, including
successful allocations by outside contracts that share it. Availability of
the live-owner limit does not by itself prove fresh-key availability. The
[separate failure rules](first-slice-failure-judgments.md#derive-capacity-cases)
account for exhaustion and preparation before publication.

The transfer rule uses the exact owned segment established by
[`H-Source-Capture`](first-slice-behavior-coverage-rules.md#select-a-source-handler-and-form-its-capture),
the atomic resume restoration, or an admitted discard's prepared close. `X`
contains the owners of that same segment; their owner records move, rather
than being copied or discharged. `outside` supplies the disjoint owners whose
positions and obligations must remain valid. A no-reply discard schedules an
owned close; it does not discharge all scheduled owners at transfer time.

```sequent
J-Account-Owner-Transfer :=
  GAMMA; L, phi |- OwnerInv(s, M, Q)
  GAMMA; L, phi |- the same exact capture, restore or prepared close transfers X once from position p to p'
  GAMMA; L, phi |- X and outside partition every counted owner in M and Q for this same case
  GAMMA; L, phi |- the transition preserves every owner in outside
  GAMMA; L, phi |- that successful transition takes s to s'
  GAMMA; L, phi |- the transition preserves M, Q, roots, phases and both counts while relocating X
  ===>
  GAMMA; L, phi |- OwnerInv(s', M, Q) with X at p' and outside preserved
```

Capture and restore preserve live counts and the current cell roots; a cleanup
that is already running remains running with its saved state. A write within
the resumed behavior can subsequently change a root under `J-Cell-Write`;
the restored root is not a promise about all later states. Copying a handle,
ordinary value or callable does not instantiate this transfer rule. A
selected capture and its outside context must be disjoint in the actual case;
a may-contain relation alone cannot establish that premise. On discard
preflight failure, the capability and capture accounting remain as they were
before consumption; terminal failure and disposal have their separate
[state-sensitive cases](first-slice-failure-judgments.md#construct-cases-for-ordered-primitive-phases).

### Derive the underflow and phase facts

Each of the following rules applies to a **reached** owner position established
by the preceding control, not to every syntactic occurrence. A cell release
uses the same `a` present in the accounted owner set. Cleanup finish uses the
same running `o` and the actual `Unit` result of its certified action. The
ordinary action type and its established value-representation contract supply
the latter fact on each actual normal return; starting an action or merely
having a `Unit` result type does not prove it returns.

```sequent
family accounted-owner-completion:
  J-Cell-Count-Positive :=
    GAMMA; L, phi |- OwnerInv(s, M, Q) and cell_owner(s, a, v, P, I)
    GAMMA; L, phi |- the next normal return or owned-close position is this same a
    ===>
    GAMMA; L, phi |- resource_count(s) > 0 and its decrement is defined

  J-Cleanup-Start-Phase :=
    GAMMA; L, phi |- OwnerInv(s, M, Q) and cleanup_owner(s, o, armed, A)
    GAMMA; L, phi |- the next normal return or owned-close position is this same o
    GAMMA; L, phi |- this start's preparation succeeds and takes s to s', changing only o from armed to running
    ===>
    GAMMA; L, phi |- OwnerInv(s', M, Q) and cleanup_owner(s', o, running, A)

  J-Cleanup-Finish-Valid :=
    GAMMA; L, phi |- OwnerInv(s, M, Q) and cleanup_owner(s, o, running, A)
    GAMMA; L, phi |- the matching completion receives the actual normal result of A
    GAMMA; L, phi |- A's certified result and representation establish that result is Unit
    ===>
    GAMMA; L, phi |- cleanup_count(s) > 0 and its decrement is defined and the Unit check succeeds
```

On successful release, remove only `a` from `M` and decrement the resource
count once. On successful finish, remove only `o` from `Q` and decrement the
cleanup count once. The actual retained value, outside owners and remaining
close plan are preserved according to their contracts. Capture, resume or a
request during a running action changes neither its phase nor its counted
identity. A second start cannot be derived from the running phase; no discard
rule may abandon a running owner or unfinished close. These are phase and
count facts, not a proof that a close or action terminates.

The following successful completion rules make those post-state facts
available to the next composition. They consume the positive-count and
completion facts above and the applicable result-crossing or close-plan
judgment. The transition contracts preserve unrelated ownership and update the
counter in the same post-state; their failure cases remain separate.

```sequent
family account-successful-completion:
  J-Account-Cell-Close :=
    GAMMA; L, phi |- OwnerInv(s, M, Q) and cell_owner(s, a, v, P, I)
    GAMMA; L, phi |- J-Cell-Count-Positive and the applicable normal or owned close admit this position
    GAMMA; L, phi |- successful release of this a takes s to s', removes a and decrements the resource count once
    GAMMA; L, phi |- unrelated owners and obligations are preserved in s'
    ===>
    GAMMA; L, phi |- OwnerInv(s', M - a, Q) and a is discharged

  J-Account-Cleanup-Finish :=
    GAMMA; L, phi |- OwnerInv(s, M, Q) and cleanup_owner(s, o, running, A)
    GAMMA; L, phi |- J-Cleanup-Finish-Valid and the applicable normal or owned finish admit this position
    GAMMA; L, phi |- successful finish of this o takes s to s', removes o and decrements the cleanup count once
    GAMMA; L, phi |- unrelated owners and obligations are preserved in s'
    ===>
    GAMMA; L, phi |- OwnerInv(s', M, Q - o) and o is discharged
```

The ordinary [return loop](../../../src/eval/machine.rs#L1930) pops a frame
before the pending-disposal and owner-count checks. The propositions above
must therefore carry the same popped owner as the transition's temporary
ownership, rather than assert that it remains on the active frame stack. An
early failure can drop that moved frame and is terminal; it does not establish
a successful release, an action start or a reusable owner. A worker's
preflight checks occur before its pop and are supplied by that excluded
context's own interface. The [cell return](../../../src/eval/machine.rs#L3469)
and [cleanup start and finish](../../../src/eval/machine.rs#L3372) show the
checks whose underflow, duplicate-start and non-Unit alternatives these
propositions address. Disposal, preparation, work and capacity failures remain
separate.

### Derive authentication from the same access

The cell's ordinary type, an effect-row member and a may-target set do not
establish that its actual handle matches the selected activation. Introduce
`HandleFact(h, R, P, a)` for a particular actual handle `h` produced for the
fresh activation `a`, and `InstanceFact(I, R, P, a)` for its exact sealed
provider instance after the same lexical instantiation. The successful
`J-Cell-Acquire` case supplies both for its bound access and installed owner.
The ordinary value contract preserves `HandleFact` when that same handle is
copied or passed; it does not create another owner. An opaque function or
module may return or pass an access only under its certified relationship to
its inputs. If that relationship is absent, callers cannot invent it from
the return type.

A generic builtin `write` has an actual operand pair. The ordinary value
producer must establish that the value at the request point resolves to the
two fields `(h, v)` and that the alias/location representation is usable in
that state. The `read` operand must establish the actual `h`. These facts can
come from the certified value and binding judgments, or a conditional contract
at an opaque boundary. A proof about a pair at an earlier state is insufficient
if an intervening outside operation can invalidate its backing. Work or
allocation required to resolve the operand is a separate failure case.

```sequent
family cell-authentication:
  J-Cell-Handle-Copy :=
    GAMMA; L, phi |- HandleFact(h, R, P, a) in state s
    GAMMA; L, phi |- the established ordinary value transition copies h to h' and preserves its representation
    ===>
    GAMMA; L, phi |- HandleFact(h', R, P, a) in the resulting state

  J-Cell-Request-Authentication :=
    GAMMA; L, phi |- OwnerInv(s, M, Q) and cell_owner(s, a, root, P, I)
    GAMMA; L, phi |- the certified request r uses the sealed cell operation at I and InstanceFact(I, R, P, a)
    GAMMA; L, phi |- r's actual read handle or resolved write-pair handle is h and HandleFact(h, R, P, a)
    GAMMA; L, phi |- the operand representation is usable and has the operation's required shape in s
    GAMMA; L, phi |- exact nearest selection for this same r and s selects the builtin owner a
    ===>
    GAMMA; L, phi |- authenticated_handle(r, a, P) and no malformed operation/handle/shape failure for this r
```

For a copied handle and its original owner, the equality follows from the
actual acquisition and the ordinary copy contract, not from choosing a member
of a set. The request contract must also retain the operation identity and the
complete instantiated `R,P` arguments from its saved lexical context; the
selected cell's instance is the same `I`. The
[nearest-boundary judgment](first-slice-nearest-boundary-judgments.md#candidate-composition-rules)
supplies the actual selected boundary, including any nearer source-handler
interception. If the source handler wins, its clause contract applies instead
and this builtin conclusion is not used. The
[runtime search](../../../src/eval/machine.rs#L4440) and
[generic interpreter](../../../src/eval/machine.rs#L4902) distinguish exact
instance selection from the later handle and pair checks. The result excludes
only those malformed operation, identity, handle and shape branches; it does
not establish sufficient work, trace reservation, valid independent backing,
safe replacement dependencies or successful disposal.

For example, two nested `Cell.Cell<_, P>` scopes can have the same payload
type but different activations `a` and `b`. A checked helper receiving the
outer handle must preserve its `HandleFact` and lexical instance when it
requests the outer cell; the nearer `b` owner does not acquire authority over
that handle. If a hypothetical unchecked request paired `a`'s instance with
`b`'s handle, the selected cell could reject it. The correlated certificate
rules out that pairing; a common payload type does not.

These rules still require the proposed certificate producer to establish the
initial count/placement invariant, sound ordinary value representations,
freshness and identity preservation through every applicable opaque boundary,
and complete guarded selection and owner-transfer coverage. In particular,
they do not yet prove that today's analysis produces these interfaces, that
all alias-resolution or instantiation failures are excluded, or that all
malformed control throughout the program is impossible. Their system-level
preservation and progress arguments belong to the soundness proof, not a
new verification run over each checked fragment.

## Producers, consumers and unresolved work

| Established producer | New consumer and applicability | Remaining work |
| --- | --- | --- |
| Initializer and conditional body judgments; sealed API declaration and selection | R1–R3 check a fresh scope, exact authority, row, actual initializer case and activation. | Represent conditional facts, authenticate evidence and preserve Type/Row specialization without rechecking bodies. Clarify the two specification discrepancies above. |
| Actual value, call, evidence and request judgments | R4 checks each returned value or crossed payload against its actual owner and recipient. | Define sound completeness and unknown handling across opaque boundaries, including imports, metadata and backing. |
| Control selection, actual cell targets, correlated roots and birth facts | R3/R5 check builtin access, every target/replacement and snapshots; source interception follows its own clause. | Prove coverage for joins, recursive activations, conditional predecessors and writes in clauses or restored control. |
| Capture, outside completion, close and action contracts | R6 transfers or closes only owned activations and preserves other obligations. | Establish their composition and effect rows under the separate discard and cleanup rules. |

Current [resource elaboration](../../../src/elaborate.rs#L14218) and [Core
validation](../../../src/core/validate.rs#L14413) authenticate types, rows and
authority. The current [value
analysis](../../../src/core/capture/value.rs#L6184) and [control
analysis](../../../src/core/capture/control.rs#L6470) also reconstruct result,
payload, contents and retention relationships; they are not yet these reusable
judgments. Source checking, imported summaries and independent validation can
have different subjects or assumptions. No current check is shown removable
merely by this record, and shared analyses also serve excluded scopes.

The rules expose obligations but do not settle finite or checkable
representation, recursive and unknown cases, reuse across the slice's opaque
boundaries, or correspondence between the cases and the established constituent
judgments. Sound coverage, substitution, preservation of owner and contents
correlations, and execution correspondence require separate proof. Capacity,
acquisition preparation and disposal failures still occur. The agreed
[failure admission rule](first-slice-failure-judgments.md#agreed-admission-rule-for-the-first-slice)
requires their internal cases to be ruled out for the no-error conclusion;
the necessary guards and evidence remain to be completed. No rule here proves
termination.
