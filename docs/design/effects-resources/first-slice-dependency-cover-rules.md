# First Slice: Dependency Cover Rules

This record develops the cover interface used by the [candidate cell resource
rules](first-slice-resource-rules.md#cases-and-assumptions) and the
[resource trace](first-slice-resource-trace.md). It proposes rules for
introducing, composing, specializing and consuming resource-dependency facts.
They are not current Ash syntax, implemented certificates, or a soundness
proof. The [specification](../../../spec/README.md) defines current Ash;
[generic cells](../../../spec/static-semantics.md#generic-cell-foundation)
and [scoped resource dependencies](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
state the relevant behavior.

Ordinary value construction, function application, method evidence and their
checking are outside this slice. Their established contracts supply the
boundary facts named below. A new resource or control composition uses those
facts and proves its own premises; it does not inspect or reverify a certified
value, function body, selected method or other constituent. A missing boundary
contract is an obligation, not an empty dependency set. Nothing here authorizes
removing the current graph or independent Core validation.

## Meaning and subject

Write `Cover(v, S, D)` under `GAMMA; L, phi` when an established fact guarantees
that every actual dependency of **this value** `v` on an owner in domain `S`
is in `D`. `D` is an upper bound, not necessarily the exact dependency set.
`S` and `D` contain owner *activations* or sound symbolic descriptions of
them, not just lexical acquisition sites. `phi` identifies the correlated
entry, path, value, state and local witnesses for the case. It may describe
many executions; the guarantee must hold for all of them. `L` contains only
facts established stable at this point. The subject can be a symbolic port
whose value is supplied by that same case; it is not a claim that the port
returns or that a particular case executes.

`actual_dep(v, d)` below is a proposition about the actual value and owner in
the current correlated case. It is not an instruction to traverse a value or
an inference from membership in an overapproximated dependency set.

The cover counts the applicable retained handles, actual callable captures,
selected evidence and indexed operation metadata. Unused environment entries,
unselected fields and uncalled methods are not automatically dependencies of
the selected value. This is a cell-resource domain: allocation regions,
backing and other excluded owners need their own established domain and
crossing facts. `Int` alone is not a proof about its allocation backing.

An interface for a certified constituent must preserve the subject and
contract identity, scope, entry and exit indices, guard, domain, and relevant
lexical instantiation. Hidden activation witnesses remain local to their case;
an outer conclusion may use them only through a valid scoped interface. Joining
independent possible values and states does not prove an exact combination.
The [normal-return cover](first-slice-normal-return-judgments.md#what-a-return-case-must-say)
gives the corresponding value and post-state correlation.

The schemas below may consume facts with outstanding obligations. An
unindexed premise denotes a fact established under the stated context and
guard; it does not turn an unresolved obligation into an established fact.
Where an indexed conditional fact is used, its obligations must accompany
the conclusion under the same subjects, guards and witness scopes. In
particular, the common cover composition and transport rules below make that
carry explicit. Leaving a case packages its local witnesses by the applicable
scoped-export rule; it does not erase their obligations or recheck the value.

## Introduction and weakening

The following rules introduce covers for two specific established value facts.
They concern resource owners only, not every possible kind of backing. `known`
requires the actual value and activation from the same covered case.

```sequent
family primitive-dependency-covers:
  J-Cover-Unit :=
    GAMMA; L, phi |- known(v = ())
    ===>
    GAMMA; L, phi |- Cover(v, S, {})

  J-Cover-Cell-Access :=
    GAMMA; L, phi |- acquired_access(v, a)
    GAMMA; L, phi |- cell_access_contract(v, a) establishes no other cell-owner dependency, including metadata
    ===>
    GAMMA; L, phi |- Cover(v, S, intersection(S, {a}))
```

The cell API contract used here states that this particular opaque access has
no cell-owner dependency other than `a`, including applicable metadata. It
also states that the access is non-owning; non-ownership alone would not prove
the dependency bound. The rule does not infer an activation
from a handle's ordinary type. The owner must be selected by the established
acquisition fact. An ordinary copied integer can supply an empty *cell-owner*
cover through its applicable value contract; that does not discharge a backing
region obligation.

For opaque values, define a boundary fact
`Sources(v, S, members, intrinsic)` to mean that, for this particular subject
and case, every dependency of `v` in `S` is either in `intrinsic` or a
dependency in `S` of one of `members`. The ordinary value or evidence judgment
must establish this fact, including selected fields, actual captures and
metadata. `members` is not derived by examining a certified implementation.
This gives a nontrivial composition rule from already established covers:

```sequent
J-Cover-From-Sources :=
  GAMMA; L, phi |- Sources(v, S, [v_1, ..., v_n], intrinsic) [O_sources]
  for each i, GAMMA; L, phi |- Cover(v_i, S, D_i) [O_i]
  D = intrinsic union D_1 union ... union D_n
  O_cover carries O_sources and each O_i under their original subjects, guards and witness scopes
  ===>
  GAMMA; L, phi |- Cover(v, S, D) [O_cover]
```

For example, an established aggregate-value contract can supply its actual
retained components as sources; a closure contract can supply its retained
captures and indexed metadata. These are different from the result of calling
that closure. If a source is unknown, the composition must use a sound cover
for it or remain unproved. In particular, a function's result does not acquire
all of its callable's captures merely because the function was invoked. The
boundary contract for its *actual result* decides which sources matter. The
rule does not prescribe how ordinary value judgments produce `Sources`.

An established equality of actual value subjects transports a cover; it does
not infer equality from matching ordinary types or a shared address alone.
Here equality includes the same retained captures and relevant lexical
instantiation and metadata in the same case. An established projection or
pattern-selection judgment can identify the selected value in that sense.
The following eliminations do not reopen an aggregate or replay a pattern:

```sequent
family dependency-subject-transport:
  J-Cover-Same-Value :=
    GAMMA; L, phi |- actual_value(v) = actual_value(w) [O_equal]
    GAMMA; L, phi |- Cover(v, S, D) [O_cover]
    O_result carries O_equal and O_cover under their original subjects, guards and witness scopes
    ===>
    GAMMA; L, phi |- Cover(w, S, D) [O_result]

  J-Cover-Selected-Field :=
    GAMMA; L, phi |- certified_selection(container, field, selected) [O_selection]
    GAMMA; L, phi |- actual_value(result) = actual_value(selected) [O_equal]
    GAMMA; L, phi |- Cover(selected, S, D) [O_cover]
    O_result carries O_selection, O_equal and O_cover under their original subjects, guards and witness scopes
    ===>
    GAMMA; L, phi |- Cover(result, S, D) [O_result]
```

The selection fact comes from the established ordinary aggregate or pattern
contract. It identifies the particular selected field; it does not transfer
the dependencies of unrelated fields. A call result requires the separately
certified result relationship below, even if its callable has a cover.

Covers may safely be weakened or restricted to a smaller domain. If no better
bound is available, the domain itself is a sound top cover for a value already
established in this case. A top cover is not proof that the value exists or
returns, and generally cannot establish independence from an owner in `S`.

```sequent
family cover-weakening:
  J-Cover-Weaken :=
    GAMMA; L, phi |- Cover(v, S, D) [O_cover]
    GAMMA; L, phi |- S_small subset-of S and D intersect S_small subset-of D_large [O_subset]
    O_result carries O_cover and O_subset under their original subjects, guards and witness scopes
    ===>
    GAMMA; L, phi |- Cover(v, S_small, D_large) [O_result]

  J-Cover-Top :=
    GAMMA; L, phi |- produced_value(v) [O_value]
    ===>
    GAMMA; L, phi |- Cover(v, S, S) [O_value]
```

A symbolic domain need not be enumerable. Its interpretation must cover the
actual owners at the specified point; an unmentioned hidden owner is not
excluded by choosing an incomplete domain. A top cover does not prove that an
unknown call returns or that an unresolved request has no payload. Resource
failure, non-return and unknown control remain governed by their own contracts.

## Producer contracts for a new value

A producer of a new value publishes the actual-value relationship at the
point where ordinary construction is checked. The consumer uses that
relationship and the covers of its inputs; it does not reopen the producer.
The following contracts are conditional on the existing ordinary type,
evidence, value and normal-completion judgments. `Sources` ranges over the
same complete cell-owner domain `S` and includes the full resource-indexed
metadata of the constructed value. Each premise and conclusion is guarded by
the same actual construction case.

```sequent
family new-value-source-contracts:
  J-Sources-Scalar :=
    GAMMA; L, phi |- v is a completed primitive value whose certified value contract excludes every cell-owner dependency
    v is not a resource access, retained key or other owner-indexed value
    ===>
    GAMMA; L, phi |- Sources(v, S, [], {})

  J-Sources-Alias :=
    GAMMA; L, phi |- ordinary binding returns the same actual value v as input u
    ===>
    GAMMA; L, phi |- Sources(v, S, [u], {})

  J-Sources-Aggregate :=
    GAMMA; L, phi |- checked construction produces v with actual retained fields [u_1, ..., u_n]
    GAMMA; L, phi |- I covers every additional cell-owner dependency of v's construction and indexed metadata
    ===>
    GAMMA; L, phi |- Sources(v, S, [u_1, ..., u_n], I)

  J-Sources-Closure :=
    GAMMA; L, phi |- checked closure creation produces v with actual retained captures [u_1, ..., u_n]
    GAMMA; L, phi |- I covers every additional cell-owner dependency of its selected evidence and indexed metadata
    ===>
    GAMMA; L, phi |- Sources(v, S, [u_1, ..., u_n], I)
```

The scalar rule applies only to primitive forms with the stated certified
cell-owner independence; scalar representation or absent type metadata alone
does not establish it. Resource accesses, retained keys and other values that
identify an owner use their own contracts, including `J-Cover-Cell-Access`.
Their non-owning representation does not make them dependency-free.

The aggregate contract covers the complete constructed aggregate; selecting a
field uses the selected field's own contract, not the union for unrelated
fields. `I` is a proved upper bound, not an assumption that the ordinary type
is independent. Closure captures mean values actually retained by the callable,
not every binding in its implementation environment. A closure's result is
not a capture of the closure merely because it is called. Direct access uses
`J-Cover-Cell-Access`; an implementation-selected method and operation
metadata require their own checked actual-value contracts. These rules do not
traverse already certified values.

For a new call composition, the callable producer supplies a normal-result
case family and, for each case, its actual `Sources` relationship, including
argument, selected evidence, capture, metadata and substitution relationships
that really can contribute. The caller composes that family using
`J-Cover-Call-Result`, `J-Cover-Join` and
`J-Cover-Specialize-With-Inputs`. A separately certified function, recursive
group, method, imported helper or native boundary supplies those facts as an
opaque contract, including unknown and non-return cases; the caller does not
inspect or recheck its body. A missing relationship remains an obligation or
a top cover. This is a candidate producer/consumer interface, not a claim
that existing callable summaries publish it.

## Correlated alternatives and specialization

A choice's established case cover must include every relevant execution and
provide the actual selected value `v` in that execution. Let `phi_i` include
all local witnesses and substitutions needed for case `i`; `case_cover` is an
established control or return cover, not an enumeration assumed complete because
no other case was observed. The output bound `D` must be in the outer scope.

```sequent
J-Cover-Join :=
  GAMMA; L, phi |- case_cover(subject, [phi_1, ..., phi_n])
  for each case i, GAMMA; L, phi, phi_i |- Cover(value(subject), S, D_i)
  for each case i, GAMMA; L, phi, phi_i |- D_i subset-of D
  subject, value(subject), S and D are well scoped outside every phi_i
  each case's domain denotes the same outer S
  ===>
  GAMMA; L, phi |- Cover(value(subject), S, D)
```

Each premise holds for all executions represented by its case. An infeasible
case may be removed only by established infeasibility; an unknown case must
supply its own sound bound or leave the conclusion unproved. This rule permits
a coarser upper bound; it does not assert that a root from one case and an
activation or returned value from another occurred together. An unbounded case
family needs an established outer upper bound; the rule does not assert finite
representation or a terminating solver.

Instantiation must preserve the contract's own subject, guards, owner mapping
and scoping. The following rule uses an **established substitution interface**
for this contract, including type/row substitution and the actual lexical
activation mapping. `image(theta, S)` describes only the mapped domain; it is
not automatically every owner in the caller's context.

```sequent
J-Cover-Specialize :=
  GAMMA; L, phi |- Cover(v, S, D)
  GAMMA; L, phi |- applicable_substitution(theta, v, S, D)
  the certified cover contract is preserved by theta under phi_theta
  ===>
  GAMMA_theta; L_theta, phi_theta |- Cover(theta(v), image(theta, S), image(theta, D))
```

The preservation premise is an obligation of the supplied interface, not a
new proof obtained by reopening its producer. It must account for hidden
witness scope and actual activation identity. Different symbolic parameters may
coincide after specialization: no injectivity is assumed. In particular,
`a not-in D` before substitution cannot by itself prove `theta(a)` absent
from `image(theta, D)`. Test absence again in the instantiated cover. Other
caller owners require their own covers or a larger sound domain.

One way to establish the instantiated bound without assuming that it equals
the original bound is to use a certified substitution dependency relation.
For the *actual* substituted value `v_theta`, let that relation establish that
every dependency in caller domain `S_theta` is either the image of an actual
dependency of `v` in `S`, or a member of `E_theta`. The latter accounts for
dependencies introduced or supplied by the particular instantiation. It must
be a sound upper bound, not a list of dependencies observed in one execution.
This yields the following introduction, even when symbolic owners coincide:

```sequent
J-Cover-Specialize-With-Inputs :=
  GAMMA; L, phi |- Cover(v, S, D)
  GAMMA; L, phi |- the actual substituted value is v_theta under theta and phi_theta
  under L_theta and phi_theta, theta's instantiation of the original cover assumptions L and phi holds
  the original and substituted subjects and owner mapping refer to the same covered invocation
  for every d_theta in S_theta, under phi_theta and actual_dep(v_theta, d_theta),
    d_theta is in E_theta or there is a d in S with actual_dep(v, d) and d_theta = theta(d)
  image(theta, D) union E_theta is well scoped at the caller
  ===>
  GAMMA_theta; L_theta, phi_theta |- Cover(v_theta, S_theta, image(theta, D) union E_theta)
```

The dependency relation is an input from the ordinary substitution or call
interface, under its stated lexical and activation assumptions; this rule
does not inspect the original body. If that interface proves no added
dependencies and maps exactly the original domain, the rule gives the
specialized bound above. If it supplies only an unknown added component, use a
sound top bound for that component or leave the desired exclusion unproved.
The rule does not assert that today's summaries supply this relation.

## Results, payloads and replies

A function, imported helper or selected evidence method may provide an
established behavioral contract whose **normal-return case** relates its
actual output to argument, callable, evidence and indexed-metadata sources.
The producer must account for the actual selected method and substitutions;
its ordinary function type does not establish the relationship. Under that
case, `Sources` and the preceding composition rule supply a cover for the
actual result. The following rule exposes that use. `case_f` and all covers
share the same invocation, selected evidence and return case.

```sequent
J-Cover-Call-Result :=
  GAMMA; L, phi |- certified_call_case(call, case_f, v)
  GAMMA; L, phi, case_f |- Sources(v, S, members, intrinsic)
  for each member_i in members, GAMMA; L, phi, case_f |- Cover(member_i, S, D_i)
  D = intrinsic union all D_i
  ===>
  GAMMA; L, phi, case_f |- Cover(v, S, D)
```

`certified_call_case` is an input from the existing callable and selected
evidence interfaces, including their assumptions and return coverage. It is
not permission to rerun the call or rederive its body. To cover all possible
results, compose the applicable cases with `J-Cover-Join`, including unknown
cases. The new-value producers above cover the stated constructors. Call case
coverage, selected evidence and substitution preservation remain inputs from
their ordinary boundary contracts; this record does not derive those contracts
by inspecting an existing body.

The [perform rule](first-slice-request-sequencing-judgments.md#candidate-rule-introduce-a-request)
first evaluates its operand. Its established normal-return case supplies the
actual payload `p`, not a value guessed from `P` or its row. An operation
request's selected interpreter supplies its actual reply `q`; for a source
handler resumed with an operand, that operand's actual normal-result cover is
the reply cover. The reply is supplied to the selected residual computation,
whose eventual return may be a different value. The following transport rules
need certified equality of actual subjects; same ordinary types do not suffice.

```sequent
family request-cover-transport:
  J-Cover-Payload :=
    GAMMA; L, phi |- operand_return_case(request, p)
    GAMMA; L, phi |- Cover(p, S, D)
    ===>
    GAMMA; L, phi |- request_payload_cover(request, p, S, D)

  J-Cover-Source-Reply :=
    GAMMA; L, phi |- selected_source_resume_case(request, resume_operand, q)
    GAMMA; L, phi |- Cover(q, S, D)
    ===>
    GAMMA; L, phi |- request_reply_cover(request, q, S, D)
```

Selection and resume contracts must establish that `q` is the particular
normal result of the actual resume operand for that selected activation. An
operand request alone does not supply a reply: its residual must first return
normally. Divergence, abandonment or failure before normal return supplies no
reply case. Other interpreters need their own reply contract;
a result type alone supplies no `Cover`. Payload crossing is a separate
obligation, as are any reply lifetime and crossing premises imposed by the
restored or surviving context. Conditional selection must cover source, cell,
native and outward cases as applicable, not just the convenient one.

## Cell roots, snapshots and updates

A cell-state contract relates a selected live activation `a` at state `sigma`
to its actual root `v`. It retains the corresponding `Cover(v, S, D)` and
birth enclosure for that same activation. Successful acquisition introduces
the initializer's actual result as the root after the separate retention and
preparation premises. The following rule transfers its already established
cover; it does not examine the initializer again:

```sequent
J-Cover-Acquired-Root :=
  GAMMA; L, phi |- successful_acquisition(a, v, sigma_after)
  GAMMA; L, phi |- Cover(v, S, D)
  ===>
  GAMMA; L, phi |- root_cover(sigma_after, a, v, S, D)
```

An exact builtin read selects and authenticates `a`, prepares the reply and
returns its current root. A successful builtin write replaces that root only
after its separate retention and preparation checks. Those current-state
relations yield the following cover facts:

```sequent
family cell-cover-flow:
  J-Cover-Builtin-Read :=
    GAMMA; L, phi |- selected_builtin_read(request, a, sigma, v)
    GAMMA; L, phi |- root_cover(sigma, a, v, S, D)
    reply preparation succeeds
    ===>
    GAMMA; L, phi |- request_reply_cover(request, v, S, D)

  J-Cover-Builtin-Write :=
    GAMMA; L, phi |- selected_builtin_write(request, a, sigma, v, sigma_after)
    GAMMA; L, phi |- Cover(v, S, D)
    GAMMA; L, phi |- retained_safely(v, a)
    reply and replacement preparation succeeds
    ===>
    GAMMA; L, phi |- root_cover(sigma_after, a, v, S, D)
```

Every applicable target and root case must be covered independently, with
its own actual handle, selected boundary and complete instantiated authority.
The selected source-handler branch uses `J-Cover-Source-Reply`, not the cell's
current root; an intercepted write does not itself replace that root. Writes
that a clause or resumed computation actually performs have their own ordered
state transitions. The current specification says that a later builtin
replacement changes neither an earlier read's snapshot nor its retained
dependencies. The general account must show that this replacement supplies
the applicable stability premise below; other transitions need their own
preservation evidence. The snapshot does not freeze mutable cells reachable
through that value. Failed preparation does not produce a successful write
case; internal failure after replacement has its own behavior.
[Cell execution](../../../spec/dynamic-semantics.md#scoped-cell-execution)
defines the current steps.

The following frame and snapshot rules make the state distinction explicit.
`same_dependencies` is an established ordinary-value stability fact for the
actual subject and domains across the indicated transition; it does not prove
that an owner remains live. A mutable cell reachable through the value can
change its own contents, so no rule below treats those contents as frozen.

```sequent
family cell-cover-preservation:
  J-Cover-Other-Root :=
    GAMMA; L, phi |- root_cover(sigma, a, v, S, D)
    GAMMA; L, phi |- successful_builtin_write(sigma, b, replacement, sigma_after)
    a and b are distinct actual activations and a remains live
    GAMMA; L, phi |- same_dependencies(v, S, sigma, sigma_after)
    ===>
    GAMMA; L, phi |- root_cover(sigma_after, a, v, S, D)

  J-Cover-Snapshot :=
    GAMMA; L, phi |- selected_builtin_read(request, a, sigma, v)
    GAMMA; L, phi |- root_cover(sigma, a, v, S, D)
    reply preparation succeeds
    GAMMA; L, phi |- snapshot is the actual returned value v
    GAMMA; L, phi |- same_dependencies(snapshot, S, sigma, sigma_after)
    ===>
    GAMMA; L, phi |- Cover(snapshot, S, D) at sigma_after
```

The builtin write changes only its actual target root; this frame rule does
not apply to an intercepted write or an opaque intervening computation without
an appropriate state contract. Snapshot stability preserves the snapshot's
value dependencies, not the liveness of those dependencies or the current
root of a cell later written. These rules compose the already established
value and transition facts; they do not recalculate a previous read or open a
stored value. If a transition's effect on a symbolic domain or value is
unknown, its stability premise remains an obligation.

## Independence, retention and predecessor facts

For a value crossing or returning past activation `a`, the resource rule needs
independence from that *particular* owner. This consequence uses a sound cover
without rechecking the value:

```sequent
J-Cover-Independent :=
  GAMMA; L, phi |- Cover(v, S, D)
  GAMMA; L, phi |- a is in S
  GAMMA; L, phi |- a is not in D
  ===>
  GAMMA; L, phi |- independent(v, a)
```

`a not in D` is a proved exclusion under the same case and instantiation, not
failure to find `a` in incomplete information. It does not establish absence
of any other owner. Payload and result crossing additionally need the actual
crossed boundary and recipient; the trusted interpreter exception is only for
the owner's own admitted interpreter. Preserve dependencies on owners that
remain live. See [resource crossing rules](first-slice-resource-rules.md#r4-actual-result-and-payload-crossing).

The per-owner elimination composes into a return or payload boundary only after
the relevant actual value and boundary cases have been covered. `crossed` is a
certified control-selection fact, not a set guessed from the effect row. The
first rule also retains the ordinary type, row, scheme and evidence escape
checks; a value cover cannot replace them. The second rule treats only the
actual owner's trusted interpreter as the exception to independence.

```sequent
family covered-resource-crossings:
  J-Cover-Body-Exit :=
    GAMMA; L, phi |- normal_body_case(body, a, v)
    GAMMA; L, phi |- Cover(v, S, D) and a is in S and a is not in D
    the result type, outward row, schemes and retained evidence do not expose a's local identity
    all other applicable boundary obligations hold
    ===>
    GAMMA; L, phi |- result_crossing(v, a) is admitted

  J-Cover-Request-Exit :=
    GAMMA; L, phi |- actual_request_case(request, payload, recipient)
    GAMMA; L, phi |- request_payload_cover(request, payload, S, D)
    GAMMA; L, phi |- crossed(request, recipient) = Owners
    for each a in Owners, either recipient is a's admitted trusted interpreter, or a is in S and a is not in D
    all other applicable boundary obligations hold
    ===>
    GAMMA; L, phi |- payload_crossing(request, payload, recipient) is admitted
```

Each condition is checked for the same actual result or request case and its
activation. A covering set of possibilities requires the elimination for
every feasible result, selected recipient and crossed-owner case. An
unknown owner or missing exclusion remains an obligation; failure to find it
in a partial set is not admission. The check for an inner owner does not erase
a dependency on a still-live outer owner. Actual dependence on a closing or
nontrusted crossed owner is a violation; lack of a proof of independence is
not by itself proof that a particular dependency occurs.

For initialization and builtin replacement, let `ResourceDomain(S)` establish
that `S` covers all resource-owner dependencies relevant to this value and
operation. `birth(a)` is the actual acquisition's strict enclosure, fixed at
birth. If all possible retained owners are known within that enclosure, the
following sufficient rule establishes the retention premise:

```sequent
J-Cover-Retain-In-Birth :=
  GAMMA; L, phi |- ResourceDomain(v, S)
  GAMMA; L, phi |- Cover(v, S, D)
  GAMMA; L, phi |- D subset-of birth(a)
  ===>
  GAMMA; L, phi |- retained_safely(v, a)
```

A covering domain, complete cover and subset proof are all required. In
particular, an unknown source cannot be treated as independent by omission,
and a later clearing write does not validate an earlier replacement. This rule
is sufficient, not yet an account of every case admitted by the current
analysis. An external backing domain needs its own obligations.

The current [retention check](../../../src/core/capture/value.rs#L5981) also
uses immutable pre-birth predecessor inputs with separately established
validity and structural-birth premises. The following **conditional** candidate
captures a sufficient semantic form without turning an overapproximation's
membership into proof that a dependency actually occurs. `d` is a fresh
symbolic owner in the relevant domain. The dependency
implications and owner-enclosure facts must come from certified relationships
under the same guard, not from a shared type, an unequal owner or a graph replay.

```sequent
family predecessor-enclosure:
  J-Predecessor-Enclosure :=
    GAMMA; L, phi |- frozen_prebirth_predecessor(p, a) at position j
    GAMMA; L, phi |- position j strictly encloses the acquisition of a
    GAMMA; L, phi, actual_dep(p, d) |- the owner d encloses position j
    GAMMA; L, phi |- birth(a) records the strict enclosing owners at acquisition
    ===>
    GAMMA; L, phi, actual_dep(p, d) |- d is in birth(a)

  J-Predecessor-Birth-Implication :=
    GAMMA; L, phi |- frozen_prebirth_predecessor(p, a)
    GAMMA; L, phi |- predecessor_validity_and_structural_birth(p, a)
    GAMMA; L, phi, actual_dep(v, d) |- actual_dep(p, d)
    GAMMA; L, phi, actual_dep(p, d) |- d is in birth(a)
    ===>
    GAMMA; L, phi, actual_dep(v, d) |- d is in birth(a)
```

The owner-enclosure premise must come from the predecessor's established
validity and owner-scope interface; ordinary validity at one unrelated point
alone does not supply it. The last two premises of
`J-Predecessor-Birth-Implication` are implications, not assertions that `d` occurs.
The established predecessor interface must justify them for the particular
value, activation, point and substitutions; its immutable pre-birth identity,
ordinary validity, actual structural nesting and focus exclusion are required.
The following rules derive the needed implication from certified source and
owner-scope facts. In particular, the current implementation's membership in an abstract
predecessor dependency set does **not** alone prove `actual_dep(p, d)`. The
candidate below uses such proved implications to handle overapproximated owners
outside the directly known birth set:

Let `scope_valid(p,j)` be an established ordinary-value boundary fact that
every actual resource dependency retained by this particular predecessor
encloses the actual position `j`. This is stronger than merely knowing that
`p` was constructed earlier or has a well-formed type. A newly formed
acquisition supplies the frozen predecessor, its pre-birth position and the
strict structural nesting relationship. The ordinary value interface supplies
`scope_valid` under the same activation and guard; neither input is derived by
revisiting `p`. At a later use position `t`, `same_dependencies(p,j,t)` must
establish that this is the same immutable predecessor value with the same
resource dependencies and lexical metadata as at `j`. It does not freeze the
contents of cells referenced by that value. The following introduction gives
one per-owner implication:

```sequent
J-Predecessor-From-Scope :=
  GAMMA; L, phi |- frozen_prebirth_predecessor(p, a) at position j
  GAMMA; L, phi |- scope_valid(p, j)
  GAMMA; L, phi |- same_dependencies(p, j, t) for this use at t
  GAMMA; L, phi |- j strictly encloses the acquisition of actual activation a
  GAMMA; L, phi |- birth(a) records the strict enclosing owners at acquisition
  ===>
  GAMMA; L, phi, actual_dep(p, d) |- d is in birth(a)
```

### Produce scope validity and the immediate pre-birth relationship

The following are sufficient producers for two concrete input cases. They do
not give every opaque input a scope-validity fact. `Enclosing(j,A)` states
that `A` is exactly the set of actual resource activations whose scopes
strictly enclose this particular entry point in each execution of the guard.
It is a control fact, not a list of all live owners. `ResourceDomain(v,S)` includes
every resource dependency relevant to `v`, including metadata, in the same
guarded case.

```sequent
family scope-validity-producers:
  J-Scope-Valid-From-Cover :=
    GAMMA; L, phi |- ResourceDomain(v,S) and Cover(v,S,D) at j
    GAMMA; L, phi |- Enclosing(j,A) and D intersect S subset-of A
    ===>
    GAMMA; L, phi |- scope_valid(v,j)

  J-Scope-Valid-Enclosing-Access :=
    GAMMA; L, phi |- acquired_access(v,d) for this actual activation
    GAMMA; L, phi |- cell_access_contract(v,d) establishes no other cell-owner dependency, including metadata
    GAMMA; L, phi |- ResourceDomain(v,S) and Enclosing(j,A) and d is in A
    ===>
    GAMMA; L, phi |- scope_valid(v,j)

  J-Scope-Valid-Unit :=
    GAMMA; L, phi |- known(v = ()) and ResourceDomain(v,S) at j
    ===>
    GAMMA; L, phi |- scope_valid(v,j)
```

The first rule eliminates a *complete* existing cover against actual
enclosure; it does not infer that every owner in a may-set is used. The
access and unit cases instantiate that rule with `J-Cover-Cell-Access` and
`J-Cover-Unit`. A retained access to an outer cell is valid when that exact
outer activation encloses `j`. An access to a live but non-enclosing owner
does not satisfy this producer merely because its handle exists. A top cover
is usable here only when its whole relevant domain is proved enclosing; an
unknown value's type alone does not produce that proof.

For one successful generic acquisition, `j` is the pre-publication point
after the initializer's actual normal return, and `t_body` is the immediately
entered body point. `E_scope` is the saved preceding lexical environment;
`E_body` is its extension by this acquisition. A binding `b` for `p` must
already be visible in `E_scope` and remain the same binding after extension.
In particular, an initializer-local value does not acquire that status
automatically. The transition must preserve the input's own retained
dependencies and metadata; extending the ambient instantiation is not, by
itself, proof of preservation for every opaque value.

```sequent
family cell-prebirth-producers:
  J-Cell-Input-At-Birth :=
    GAMMA; L, phi |- at j the saved E_scope binds b to the actual value p
    GAMMA; L, phi |- scope_valid(p,j) and Enclosing(j,A)
    GAMMA; L, phi |- the same generic acquisition succeeds from j with fresh a and enters t_body
    GAMMA; L, phi |- acquisition_birth(a,j,A) and birth(a) = A
    GAMMA; L, phi |- E_body preserves b's binding to p and p's retained dependencies and metadata through this transition
    ===>
    GAMMA; L, phi |- frozen_prebirth_predecessor(p,a) at j and same_dependencies(p,j,t_body) and j strictly encloses the acquisition of this a

  J-Same-Dependencies-By-Transition :=
    GAMMA; L, phi |- same_dependencies(p,j,t_1)
    GAMMA; L, phi |- the certified transition from t_1 to t_2 preserves this same p's retained resource dependencies and metadata
    ===>
    GAMMA; L, phi |- same_dependencies(p,j,t_2)
```

The successful [`E-Generic-Acquire`](../../../spec/dynamic-semantics.md#scoped-cell-execution)
step installs the fresh cell boundary around the body while retaining the
saved environment. The evaluator's
[`acquire_resource`](../../../src/eval/machine.rs#L4210) prepares the
instantiation and handle, publishes one boundary, and enters the body after
successful preflight. These steps support the control relationship above;
the environment-binding and value-metadata preservation premises still need
their ordinary-value contracts. `frozen_prebirth_predecessor` is the proposed
semantic fact for this case, not a claim that the current graph's frozen atom
is a complete runtime proof. The recorded `birth(a)` is fixed even if later
control is captured or restored.

`J-Same-Dependencies-By-Transition` composes a preservation fact supplied
by the actual transition. A builtin write to a different cell can preserve an
immutable access value without preserving that cell's contents; no general
rule assumes all opaque transitions, captured controls, or mutable referenced
objects preserve a value's dependency metadata. For a path with intermediate
requests, replies or multiple transitions, their certified preservation
contracts must compose in order to reach the later use. If the path or its
binding and metadata are unknown, the preservation premise stays an
obligation. No initializer, prior value or certified constituent is rechecked.

### An opaque pre-birth input returned from the cell body

An important instance is a value `p` already supplied at the point where a
cell is acquired, then returned unchanged by its body. Its ordinary type may
be polymorphic; no particular data representation is needed. The checker of
the enclosing boundary supplies a validity contract for that **actual input**.
The cell composition introduces a fresh owner and uses the contract; it does
not check the enclosing function or inspect the value. This derivation is
conditional on that contract and on the actual result being the same value.

The current value graph can seed a symbolic function parameter with
[`Atom::Unknown`](../../../src/core/capture/value.rs#L2772), propagate it
through a [variable alias](../../../src/core/capture/value.rs#L6633), and
then [drop the completeness flag](../../../src/core/capture/value.rs#L7294)
when computing resource candidates. The [audit's concrete trace](first-slice-verification-audit.md#unknown-value-at-a-resource-result)
explains why an empty projected list does not establish independence. The
[specification](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
requires the normal body result to be independent of the closing acquisition
and preserves dependencies on still-live outer acquisitions. The following
rules propose how to obtain that result without turning the unknown atom into
an empty cover.

`same_dependencies(p,j,t)` identifies the same input and its dependency
metadata at the pre-birth position `j` and later body-result position `t`.
`scope_valid(p,j)` has the stronger, established meaning above: every actual
resource owner on which that input depends encloses `j`. The acquisition
contract records the actual strict enclosing owners as `birth(a)` and ensures
the fresh `a` is not one of them. These are guarded facts about the same
execution and dynamic activation; a source location or the fact that `p` was
created earlier is insufficient.

```sequent
family prebirth-input-result:
  J-Prebirth-Input-Independent :=
    GAMMA; L, phi |- frozen_prebirth_predecessor(p, a) at position j
    GAMMA; L, phi |- scope_valid(p, j) and same_dependencies(p, j, t)
    GAMMA; L, phi |- j strictly encloses acquisition of this actual a
    GAMMA; L, phi |- birth(a) records that acquisition's strict enclosing owners
    GAMMA; L, phi |- a is not in birth(a)
    ===>
    GAMMA; L, phi |- independent(p, a) at t

  J-Cover-Extend-Fresh-Owner :=
    GAMMA; L, phi |- Cover(p, S_without_a, D) at t
    GAMMA; L, phi |- independent(p, a) at t
    GAMMA; L, phi |- S = S_without_a union {a} and a is not in S_without_a
    ===>
    GAMMA; L, phi |- Cover(p, S, D intersect S_without_a) at t

  J-Return-Prebirth-Input :=
    GAMMA; L, phi |- normal_body_case(body, a, v) at t
    GAMMA; L, phi |- actual_value(v) = actual_value(p) at t
    GAMMA; L, phi |- Cover(p, S_without_a, D) at t
    GAMMA; L, phi |- J-Prebirth-Input-Independent's premises hold for this p, a and t
    GAMMA; L, phi |- S = S_without_a union {a} and a is not in S_without_a
    the result type, outward row, schemes and retained evidence do not expose a's local identity
    all other applicable boundary obligations hold
    ===>
    GAMMA; L, phi |- result_crossing(v, a) is admitted
```

The first rule follows `J-Predecessor-From-Scope`: an assumed actual dependency
on `a` would put `a` in its own strict birth set, contradicting freshness. The
second combines that exclusion with the input's complete cover on the rest of
the stated domain; it does not claim that `D` is exact. The final rule
transports the resulting cover through the established actual-value equality
and applies `J-Cover-Body-Exit`. If no more precise input cover exists,
`J-Cover-Top` supplies `D = S_without_a` for the established input. This still
preserves possible outer dependencies while excluding only the new `a`.

The frozen predecessor and scope-validity contracts must be produced at the
appropriate boundary and transported through any intervening control. A
certificate for an unknown or later-produced value does not automatically
supply them. In particular, a body that constructs a wrapper, reads a mutable
root, calls an opaque computation, or returns a different value needs its own
certified source, snapshot or call-result relationship; identity cannot be
assumed from the result type. Non-return, request and failure cases remain in
their existing behavior covers. The implementation-to-contract completeness
and scope-validity correspondence, including contexts and recursive
activations, remains to be proved before any legacy check is removed.

For a result assembled from several certified sources, the next rule combines
any number of such predecessor implications with covers for the other
sources. The `Sources` relation accounts for *all* actual resource dependencies
of the result within the complete resource domain. `I` contains intrinsic
dependencies; `v_i` are the remaining sources. The condition `D_i intersect S`
avoids imposing a birth constraint on irrelevant owners outside the domain.
Every predecessor and ordinary source remains correlated with the actual
result, birth and guard. The per-`d` conclusion is universal over the symbolic
owner; it does not assert any dependency is present.

```sequent
J-Predecessor-Sources-Birth :=
  GAMMA; L, phi |- ResourceDomain(v, S)
  GAMMA; L, phi |- Sources(v, S, [p_1, ..., p_m, v_1, ..., v_n], I)
  for each predecessor p_j, GAMMA; L, phi, actual_dep(p_j, d) |- d is in birth(a)
  GAMMA; L, phi |- I intersect S subset-of birth(a)
  for each other source v_i, GAMMA; L, phi |- Cover(v_i, S, D_i) and D_i intersect S subset-of birth(a)
  ===>
  GAMMA; L, phi, actual_dep(v, d) |- d is in birth(a)
```

To use this result with `J-Cover-Retain-Conditional`, obtain `Cover(v,S,D)`
from the certified source covers, or use the top cover `D = S` when no tighter
bound is established. The latter remains sound: the new implication, rather
than an absent set member, establishes the birth condition for each actual
dependency. This composes wrappers, selected fields and call results only when
their ordinary boundary contracts supply the corresponding actual `Sources`
relationship. It also supports a mix of predecessors and direct enclosing
dependencies; a younger or incomparable actual source cannot satisfy the
birth premise. A later write cannot change the frozen birth relation.

```sequent
J-Cover-Retain-Conditional :=
  GAMMA; L, phi |- ResourceDomain(v, S)
  GAMMA; L, phi |- Cover(v, S, D)
  for each d in D, GAMMA; L, phi, actual_dep(v, d) |- d is in birth(a)
  ===>
  GAMMA; L, phi |- retained_safely(v, a)
```

All applicable cases must satisfy the implication. This rule cannot discharge
an unknown case without a sound cover and implication, nor establish that a
younger or incomparable actual owner encloses `a`. Whether the sufficient
predecessor interface matches every current accepted program, and how its
proof composes without reanalysis, remain open correspondence questions.

One access or acquisition can have several possible targets, values and
interpreter selections. The next elimination combines the case-specific
retention proofs into the new composition's admission; it does not select one
convenient target. The cover must include every applicable successful
acquisition and builtin replacement, with its own activation, value and birth.
Source-intercepted requests contribute their clause behavior rather than a
builtin replacement; any writes actually performed by that clause or resumed
control appear in their own covered cases. Unknown cases need a sound
conditional proof or prevent the unconditional conclusion.

```sequent
J-Retention-All-Cases :=
  GAMMA; L, phi |- case_cover(composition, Cases)
  for each case phi_i in Cases and every successful acquisition or builtin replacement (a_i, v_i) it represents,
    GAMMA; L, phi, phi_i |- retained_safely(v_i, a_i)
  all other cases preserve their established behavior and applicable boundary obligations
  ordinary type, row, evidence and structural continuation checks hold
  ===>
  GAMMA; L, phi |- retention_admitted(composition)
```

The conclusion concerns retention at these operations only. It does not prove
result or payload independence, completion, capacity or preparation success.
An infeasible case may be omitted only when its infeasibility is established;
source-site equality cannot merge recursive activations or their birth facts.

## Focused predecessor: producer and consumer correspondence

The current focused analysis is more specific than the semantic sufficient
rules above. [`focused`](../../../src/core/capture/value.rs#L4355) freezes
previous slots and their atom sets, keeps the initializer's original value,
and creates a fresh focus marker. [`cell_predecessors`](../../../src/core/capture/value.rs#L5233)
collects existing free-input ports at the original resource context, excluding
the resource subtree; it does not create a missing port. The control analysis
records the actual initializer and each possible builtin replacement with the
enclosing and predecessor facts at birth. It intersects those facts when a
symbolic occurrence recurs, and focuses the retention check on each fresh
designated marker ([initialization](../../../src/core/capture/control.rs#L6470),
[replacement](../../../src/core/capture/control.rs#L6551),
[focused check](../../../src/core/capture/control.rs#L6644)).

For a closed root dependency atom, the current
[`cell_retention`](../../../src/core/capture/value.rs#L5981) accepts if the
atom is in the recorded enclosing set, or if it occurs in at least one
frozen predecessor's dependency set and is not the focus marker. The frozen
port must be terminal and have an original context. These sets are abstract
may-information. In particular, [`dependencies`](../../../src/core/capture/value.rs#L7293)
uses the resource list and discards the completeness flag returned by the
underlying traversal. This observation describes the current query; it does
not by itself prove that an unknown reachable dependency is safe or that the
whole current analysis accepts an unsafe program.

The proposed producer carries two different facts. `Prebirth(p,a,j)` names
the same immutable input value and actual acquisition case; it records its
validity at the strictly enclosing position `j`. `same_dependencies(p,j,t)`
establishes the same value, its retained resource dependencies and relevant
lexical metadata from `j` to this use at `t`; it is a separate stable-value
contract and does not freeze mutable cells reachable through access values.
`BirthSafe(v,a,S)` means
that every actual dependency of `v` in the complete resource domain `S`
strictly encloses this actual activation `a`. The following rules construct
the facts when a new resource scope and value are composed:

```sequent
family prebirth-producer-contracts:
  J-Prebirth-Input :=
    GAMMA; L, phi |- p is an actual existing input at acquisition position j
    GAMMA; L, phi |- p is immutable through this acquisition and scope_valid(p,j)
    GAMMA; L, phi |- j strictly encloses the actual acquisition a
    ===>
    GAMMA; L, phi |- Prebirth(p,a,j)

  J-Prebirth-Source :=
    GAMMA; L, phi |- Prebirth(p,a,j)
    GAMMA; L, phi |- same_dependencies(p,j,t) for this source use at t
    GAMMA; L, phi |- ResourceDomain(v,S) and Sources(v,S,[p],I)
    GAMMA; L, phi |- I intersect S subset-of birth(a)
    ===>
    GAMMA; L, phi |- BirthSafe(v,a,S)

  J-BirthSafe-Sources :=
    GAMMA; L, phi |- ResourceDomain(v,S) and Sources(v,S,[u_1, ..., u_n],I)
    GAMMA; L, phi |- I intersect S subset-of birth(a)
    for each i, GAMMA; L, phi |- BirthSafe(u_i,a,S)
    ===>
    GAMMA; L, phi |- BirthSafe(v,a,S)

  J-BirthSafe-From-Cover :=
    GAMMA; L, phi |- ResourceDomain(v,S) and Cover(v,S,D)
    GAMMA; L, phi |- D intersect S subset-of birth(a)
    ===>
    GAMMA; L, phi |- BirthSafe(v,a,S)

  J-BirthSafe-Retain :=
    GAMMA; L, phi |- ResourceDomain(v,S) and BirthSafe(v,a,S)
    ===>
    GAMMA; L, phi |- retained_safely(v,a)
```

`J-Prebirth-Source` follows from `J-Predecessor-From-Scope` and the complete
`Sources` relationship: every actual dependency of the result is either a
proved birth-safe intrinsic or an actual dependency of that same predecessor.
`J-BirthSafe-Sources` composes any already established safe sources, including
several predecessors and direct enclosing handles. Instantiation preserves
the actual activation and scope facts, and rechecks exclusions after owner
parameters coincide. An abstract predecessor port is not itself `Prebirth`:
the ordinary value interface and structural control case must provide its
validity, position and the particular value. A scope or call boundary which
cannot publish these facts leaves the corresponding conditional obligation.

At a join, the producer retains guarded `BirthSafe(v_i,a_i,S_i)` for each
covered actual value, target and birth case. It may publish one outer fact
only when the target, value and domain have valid outer identities and every
case establishes the same fact. An unknown case requires its own proof;
otherwise `J-Retention-All-Cases` cannot admit it. This preserves the current
intent of intersecting birth information, without replacing distinct runtime
activations by a lexical source site. Normal reads preserve a snapshot's
already certified cover; a successful replacement publishes a new root cover
for that selected activation and state. Intercepted writes use their actual
clause behavior, and every later builtin write has its own retention check.

The distinction from may-set overlap is necessary. Suppose `p` may be either
a closure capturing `d` or an independent closure, while the current root
`v` actually captures `d` in the latter case. Both abstract sets can contain
the atom for `d`, but `actual_dep(p,d)` is false in this case. Thus overlap
cannot establish `actual_dep(v,d) implies actual_dep(p,d)` and cannot produce
`J-Prebirth-Source` without an additional correlated source contract. This is
a counterexample to that proposed inference, not a claimed accepted Ash
program or a proof of a bug in the current analyzer.

### A birth-safe upper bound without actual predecessor membership

There is another way to use an upper bound: prove that **every owner it can
denote** encloses the target's birth. This does not require the predecessor to
actually retain the owner. It does require more than membership in today's
predecessor atom set.

In a guarded case, write `Class(alpha, t)` for the set of actual owner
activations represented by a symbolic owner class `alpha` at the use point
`t`. Its interpretation is indexed by the execution and the class's scoped
owner bindings. A class may be a singleton or a union. `ClassBirth(alpha,
a, t)` states that, in every execution represented by this case, **every**
member of that class is in the recorded `birth(a)`. This is a historical birth
fact, not a claim that those owners are still live at `t`. Current scope,
crossing and authority requirements are separate.

`ClassCover(v,S,M,t)` is a complete upper bound: every actual dependency of
`v` in the complete domain `S` belongs to at least one `Class(alpha,t)` for
`alpha` in `M`. It does not assert that every class member is an actual
dependency, or that `v` exists on a non-returning path. The producer of `v`
establishes the cover when `v` is checked and carries it across the boundary.
The consumer does not reopen `v` or reconstruct its sources.

The following candidate rules produce and use this stronger fact. `A` is
the strict enclosing-owner set recorded for **this actual acquisition**,
not the owners that happen to be live later. A scoped exact owner binding
names the same actual activation throughout the indicated interval, in each
represented execution; different executions need not choose the same
activation. The ordinary control and acquisition contracts establish these
premises, including the selected path and any captured or restored boundary.

```sequent
family class-bound-producers:
  J-Acquisition-Birth :=
    GAMMA; L, phi |- initializer has returned value v at pre-acquisition point j
    GAMMA; L, phi |- strict_enclosing_owners(j, A)
    acquisition preparation succeeds and introduces fresh actual activation a
    ===>
    GAMMA; L, phi |- acquisition_birth(a, j, A) and A = birth(a)

  J-ClassCover-Access :=
    GAMMA; L, phi |- acquired_access(v, d)
    GAMMA; L, phi |- cell_access_contract(v, d) establishes no other cell-owner dependency, including metadata
    GAMMA; L, phi |- d is in Class(alpha, t)
    ===>
    GAMMA; L, phi |- ClassCover(v, S, {alpha}, t)

  J-ClassCover-Sources :=
    GAMMA; L, phi |- Sources(v, S, [v_1, ..., v_n], I)
    for each i, GAMMA; L, phi |- ClassCover(v_i, S, M_i, t)
    GAMMA; L, phi |- every member of I intersect S belongs to a class in M_0 at t
    M = M_0 union M_1 union ... union M_n
    ===>
    GAMMA; L, phi |- ClassCover(v, S, M, t)

  J-ClassCover-Frame :=
    GAMMA; L, phi |- ClassCover(v, S, M, t)
    GAMMA; L, phi |- same_dependencies(v, S, t, t_after)
    S has the same interpretation at t and t_after
    for each alpha in M, Class(alpha, t) subset-of Class(alpha, t_after)
    ===>
    GAMMA; L, phi |- ClassCover(v, S, M, t_after)
```

`strict_enclosing_owners(j,A)` describes the selected control case and its
actual structurally enclosing owners, rather than all currently live owners.
The successful acquisition step binds a fresh `a` and records that fixed
relation; failed preparation introduces no successful birth. The class-cover
source rule uses the already certified construction relation and covers for
its actual retained inputs, including a cover for intrinsic metadata. It
supports aggregates and closures through their existing `Sources` contracts;
an opaque function or selected evidence supplies its own result contract.
Read snapshots use the particular root's class cover at the read point, and a
successful replacement installs the replacement's class cover for the
selected activation. `J-ClassCover-Frame` transports the established bound
when the value dependencies, domain and class interpretations satisfy its
premises; it does not assume that a mutable cell reachable through `v` is
unchanged. These transfers use the same value and transition premises as the
[cell cover rules](#cell-roots-snapshots-and-updates); they do not recheck an
initializer, a previous root or a function body. Case joins
retain every guarded cover unless their subjects, domains and class bindings
can be soundly abstracted at the outer boundary.

```sequent
family birth-safe-owner-classes:
  J-ClassBirth-Exact-Owner :=
    GAMMA; L, phi |- acquisition_birth(a, j, A) and A = birth(a)
    GAMMA; L, phi |- scoped_exact_owner(alpha, d, j, t)
    GAMMA; L, phi |- d is in A
    ===>
    GAMMA; L, phi |- ClassBirth(alpha, a, t)

  J-ClassBirth-Guarded-Union :=
    GAMMA; L, phi |- cases phi_1, ..., phi_n cover this use of alpha
    for each feasible phi_i, GAMMA; L, phi, phi_i |- ClassBirth(alpha_i, a, t)
    under each phi_i, Class(alpha, t) is a subset of Class(alpha_i, t)
    the target a, its birth and the class binders are valid in the conclusion scope
    ===>
    GAMMA; L, phi |- ClassBirth(alpha, a, t)

  J-ClassBirth-Retention :=
    GAMMA; L, phi |- ResourceDomain(v, S) and ClassCover(v, S, M, t)
    for each alpha in M, GAMMA; L, phi |- ClassBirth(alpha, a, t)
    ===>
    GAMMA; L, phi |- retained_safely(v, a)
```

`scoped_exact_owner(alpha,d,j,t)` supplies the universal class-membership
claim, not just a type name or a syntactic acquisition site: for each
represented execution and every `d'`, membership of `d'` in the class at
`t` implies `d' = d` for that execution. An acquired enclosing access can
provide such a binding when its established lexical instantiation and control
contract select that exact activation at birth and preserve the binding until
the use. A captured activation remains identified by its original binding;
restoration cannot add a new enclosing owner to an earlier `birth(a)`.
Recursive executions at one source site have distinct activation bindings.
No singleton follows merely from a fresh-looking type variable, an abstract
graph atom, or equality of acquisition sites. A class containing several
possible owners needs the guarded union rule or another independently
established all-members bound.

For example, if `outer` is the exact owner selected by an established enclosing
access when a child is acquired, the acquisition contract records `outer` in
the child's birth. A singleton class for that same access is therefore safe
for the child, even on a branch where a predecessor value does not capture
`outer`. A root may then retain `outer` if its complete class cover contains
only classes proved safe. In contrast, a class which might also denote a
younger activation created after that birth has no such proof; sharing its
abstract label with a predecessor cannot establish safe retention.

The next rule makes the possible correspondence with the current predecessor
branch explicit. It accepts overlap only after establishing an all-world bound
for each reused class and a complete root cover. `P` is the union of the
predecessor classes made available by the producer, not evidence that any
particular predecessor actually contains a dependency.

```sequent
J-Predecessor-Class-Bound :=
  GAMMA; L, phi |- ResourceDomain(v, S) and ClassCover(v, S, M, t)
  GAMMA; L, phi |- birth_safe_classes(a, t, E)
  GAMMA; L, phi |- certified_predecessor_classes_at_birth(a, j, P)
  M subset-of E union P
  for each alpha in P used by M, GAMMA; L, phi |- ClassBirth(alpha, a, t)
  ===>
  GAMMA; L, phi |- retained_safely(v, a)
```

`birth_safe_classes(a,t,E)` abbreviates the same `ClassBirth` proposition for
every member of `E`; it is not an unchecked enclosing-set lookup. Its producer
can use exact enclosing-owner bindings and guarded joins above. Each
predecessor class in `P` needs its own all-world proof, or a stronger
producer-supplied safe set can be used directly without mentioning a
predecessor. This rule is a specialization of `J-ClassBirth-Retention` and
performs no second analysis. When substitution makes two owner parameters
coincide, their class denotations are interpreted under the same actual
substitution and guard; all class-safety and cover premises remain required.
An unresolved class, unproved coverage or unscoped existential is an
obligation and cannot grant unconditional retention.

This provides a concrete producer and consumer for class bounds, but it does
not establish that today's atoms already have these denotations or that all
currently accepted predecessor cases provide the required class certificates.
In particular, the focused query freezes atom membership; it does not by that
fact alone prove that every actual activation represented by an atom remains
the same enclosing activation through recursion, joins and restoration. The
current query also drops traversal completeness, while `ClassCover` requires
it. A transition would need either certified class covers and class-birth
facts at each boundary, or the separately justified actual-source path above.

The exact remaining correspondence lemma is: for each feasible focused
retention case and each *actual* root dependency `d` represented by an atom
`alpha` outside the recorded enclosing set, if the current check accepts
`alpha` through a frozen predecessor and `alpha` is not the focus marker,
then this same actual `d` is in `birth(a)`. The proof must relate the
abstract atom's creation context to the actual owner in that case, establish
the predecessor's applicable validity and structural birth, and account for
any root dependencies omitted by incomplete traversal. Mere membership in a
predecessor may-set proves none of these correlations. Alternatively, the
producer can certify a set whose members are known to enclose this birth in
*every* represented case, and prove each actual root dependency belongs to
that set. Neither alternative follows from the current query alone.

### From the existing atom test to a reusable judgment

The implementation gives a more precise boundary for that lemma. The
[`dependencies_with_completeness`](../../../src/core/capture/value.rs#L7303)
walk reports `complete = false` for an unknown atom, an empty reachable slot,
or a missing required field or owner slot. A region view has its own
domain-sensitive completeness treatment. `dependencies` returns only the
resource atoms and drops that flag. In addition to `cell_retention`, the
current [`check_payload`](../../../src/core/capture/value.rs#L6122) and
[`check_resources`](../../../src/core/capture/value.rs#L6184) use that
projection. By contrast,
[`check_retained_support`](../../../src/core/capture/value.rs#L5429) asks for
the flag and rejects an incomplete applicable input. These are observations
about particular queries, not a conclusion that the whole checker accepts an
unsafe source program. Other control, focus, summary and ordinary checks also
apply. Nor is a `complete = true` bit by itself a proof that the finite graph
faithfully covers all actual runtime dependencies: that is a correspondence
property of the producers and their composition.

The coordinates also have a narrower meaning than a dynamic owner identity.
An atom records a resource expression and an analysis creation context. The
context [lookup](../../../src/core/capture/value.rs#L3090) folds repeated
invocations to a previous context, and [interning](../../../src/core/capture/value.rs#L3144)
projects some nested call and dispatch discrimination. Distinct recursive
executions can therefore require an interpretation relating one symbolic
coordinate to more than one actual activation. Focused reconstruction copies
the existing atom sets into terminal slots with frozen coordinates, retains
the initializer's original port, and creates a new focus marker. That fixes
which abstract input is used; it does not by itself make the copied set exact,
prove an atom occurs in a particular runtime predecessor, or supply a unique
activation for every folded context. The
[origin search](../../../src/core/capture/value.rs#L5515) locates an available
causal source for a diagnostic after a resource atom has been found. Its span
is not an owner identity or a proof of the missing enclosure relationship.

For a migration adapter, `AtomCover(v,S,R,rep)` means that the result `R`
of an **already performed** focused query is accompanied by a certified
interpretation `rep` under which every actual dependency of this particular
`v` in complete domain `S` is represented by some atom in `R`. `rep` is
case- and activation-indexed and can map one atom to several possible actual
owners. This is a proposed interface and proof obligation, not a claim that
the existing `dependencies` result or its Boolean flag supplies it. The
adapter must use the query result already established at that boundary; it
must not rerun a focused query when a user composes the fragment.

For one successfully checked focused root, write `E` for the recorded
enclosing atom set, `P` for the union of the accepted frozen-predecessor
dependency atoms, and `focus` for its designated fresh marker. The current
local predicate checks each atom `alpha` in its returned root list against
`alpha in E` **or** `alpha in P and alpha != focus`. In particular, the
focus test is reached only on the predecessor branch; proving that a focus
marker cannot be accepted by the enclosing branch is a separate structural
obligation. Let `Class(alpha,t)` denote the set of owners represented by that
atom in the current case and use the `ClassBirth` facts defined above.

```sequent
J-Focused-Result-To-Retention :=
  GAMMA; L, phi |- ResourceDomain(v,S) and AtomCover(v,S,R,rep)
  GAMMA; L, phi |- the already established focused result for this v and a admits every alpha in R by the recorded E, P and focus test
  for each alpha in R and actual d, rep(alpha,d) implies d is in Class(alpha,t)
  for each alpha in R admitted through E, GAMMA; L, phi |- ClassBirth(alpha,a,t)
  for each alpha in R admitted through P, GAMMA; L, phi |- ClassBirth(alpha,a,t)
  ===>
  GAMMA; L, phi |- retained_safely(v,a)
```

The rule consumes the old result **and** a complete semantic atom cover and
all-world birth facts. It does not derive either extra fact from membership in
a may-set. `AtomCover` gives `ClassCover(v,S,R,t)` using the stated
representation relation; `J-ClassBirth-Retention` then supplies the
conclusion. A predecessor-derived actual-source implication may establish
the same safety using `J-Predecessor-Sources-Birth` instead, without proving
all members of a coarse atom class safe. In both cases the same actual target,
value, birth, guard, substitutions and activation must be retained. A
diagnostic's source span and a shared lexical site are insufficient.

This exposes two separate obligations for a claimed match to current admission:

1. **Coverage.** For each actual dependency relevant to each applicable
   initialization, replacement, return or payload crossing, show that the
   producer's published interface represents that dependency in the same
   case. A graph's incomplete traversal cannot establish it by omission;
   even its complete flag still needs the system correspondence argument.
2. **Predecessor enclosure.** For each actual dependency represented by a
   root atom admitted by the predecessor branch, show the same actual owner
   is in that particular target's birth. Account for folded contexts and
   substitutions that can coincide. A frozen may-overlap alone is not the
   source-to-predecessor implication or an all-members class proof.

These obligations can be proved separately for a restricted certified case;
neither is an instruction to repeat the current query. Preserving existing
admission additionally requires showing that each currently admitted case can
be expressed and discharged with the new interfaces, including its
conditional opaque inputs. Exact equality of the two acceptance sets would
also require the reverse inclusion; semantic safety alone does not supply it.
Until the required correspondence and the other consumers are justified,
this record does not identify a current verification pass as removable.

### Conservative fallback and a complete local derivation

When an opaque value has no sufficiently precise dependency certificate, the
existing `J-Cover-Top` supplies `Cover(v,S,S)` for an already produced value
and a complete relevant domain `S`. This is safe but usually insufficient for
retention: if `S` includes the target itself or a younger owner, `S subset-of
birth(a)` is not established. The checker must then retain the scoped
obligation that this actual value's relevant dependencies enclose this actual
birth, or reject the unconditional composition. It must not read the opaque
body, substitute an empty set, or turn a missing proof into an assertion that
an escape actually occurs. A later boundary can discharge the obligation from
an established more precise value/source contract under the same guard and
activation. Existential owner witnesses must remain scoped until that use;
a whole-program no-error conclusion cannot leave the obligation unresolved.

The fallback does not force every generic payload to be opaque. Consider an
already acquired outer generic cell `a` with opaque payload type `T`; its
access `outer` has the API's established single-owner cover. A new child cell
`b` stores values of type `Cell.Cell<A,T>` and is initialized with `outer`.
Assume the certified control case establishes that this same actual `a`
strictly encloses the birth of `b`. The following is the whole retention
derivation for this covered case:

```sequent
J-Example-Enclosing-Cell-Access :=
  GAMMA; L, phi |- acquired_access(outer,a) and the cell access contract excludes other cell-owner dependencies, including metadata
  GAMMA; L, phi |- successful child acquisition creates b with a in birth(b)
  GAMMA; L, phi |- ResourceDomain(outer,S) and D = S intersect {a}
  ===>
  GAMMA; L, phi |- retained_safely(outer,b)
```

`J-Cover-Cell-Access` establishes `Cover(outer,S,D)`, and
`J-BirthSafe-From-Cover` followed by `J-BirthSafe-Retain` establishes the
displayed result. If a selected builtin read of `b` later returns that same
root and an authenticated builtin write stores that same result back into
`b`, the read and write reuse the established root/value cover and the same
birth fact. Their new selection, state, retention, preparation and failure
premises still apply. They do not recheck the original outer value, reopen
`T`, or assume an intercepted operation was builtin. This one case does not
prove that the outer initializer was valid, that every possible target is
safe, or that the whole program cannot fail.

The before/after boundary is therefore explicit. Today the focused retention
query checks returned atom membership against the recorded enclosing and
predecessor sets; payload and return consumers perform their own applicable
queries. The candidate producer publishes the complete guarded value, source,
birth and selected-state facts once; acquisition, read, write and crossing
consume those facts and prove only their new relationships. Unknown or
unproved correspondences remain obligations. Existing verification continues
until the relevant producer and **every** affected consumer have an
established disposition; a composition must not rerun a constituent's
already certified analysis merely to cross that boundary.

Before any future replacement of the graph query, each value producer must
publish complete guarded covers and source relationships; each acquisition
must publish its actual birth and prebirth interfaces; each mutation and
selection must preserve case-correlated state; and each consumer must retain
all applicable cases and obligations. Current graph checks and independent
Core validation continue unchanged. The proposal supplies sufficient
compositional admission for the cases above; it does not yet establish that
every case accepted by today's predecessor branch has such a certificate.

## Worked retention and snapshot cases

In the [recursive acquisition case](../../../tests/resource_scope_typing.rs#L1703),
one invocation creates a cell and a closure `next` that captures its handle;
the recursive invocation uses `next` as its initializer. Let `outer` be the
first actual activation and `child` the second, even though both execute one
lexical acquisition site. At the child's pre-birth position, the certified
argument contract identifies the actual initializer as `next`, and the
certified closure contract supplies `outer` as its actual source. A valid
pre-birth scope fact establishes that `outer` encloses that position; the
child's actual birth occurs inside it. `J-Predecessor-From-Scope` establishes
the enclosure implication, and `J-Predecessor-Sources-Birth` transfers it
through any certified wrapper that retains only that predecessor and otherwise
birth-safe sources. This is conditional on those contracts and their common
activation and guard, not a proof that today's imported summaries expose them.

The opposite direction is different. An outer activation cannot retain a
closure capturing its younger child: the child is not in the outer
activation's birth enclosure, and the predecessor rule supplies no contrary
fact. The [self-retention and younger-cycle cases](../../../tests/resource_scope_typing.rs#L1761)
also reject an invalid write followed by a clearing write. A missing exclusion
alone is not proof of an actual younger capture, but it cannot establish safe
retention either.

In the [snapshot case](../../../tests/resource_scope_typing.rs#L1614), an
earlier read of an independent root supplies an independent closure snapshot.
The write installs a different closure retaining an outer cell; the earlier
snapshot keeps its own value and cover, while a later builtin read obtains the
new root's cover. The two closures have the same ordinary type. A source
handler's intercepted read instead uses the actual reply cover, as illustrated
by the [handler reply case](../../../tests/resource_scope_typing.rs#L1818).
These existing tests were inspected, not run for this record; they illustrate
the premises but do not prove the candidate judgments or their completeness.

## Current producers and remaining obligations

| Current path | Result to preserve and candidate consumer |
| --- | --- |
| [Value dependency traversal](../../../src/core/capture/value.rs#L7303) and [resource check](../../../src/core/capture/value.rs#L6184) | Actual value and capture paths, owner atoms and completeness feed result and escape checks. The proposed cover interface must preserve subject, domain, case and completeness; this table does not show that a particular graph query can be removed. |
| [Cell initialization](../../../src/core/capture/control.rs#L6470), [access](../../../src/core/capture/control.rs#L6551) and [read link](../../../src/core/capture/value.rs#L5972) | Record target, birth, possible roots and read/write relationships. The new acquisition, read and write rules consume correlated root and cover facts. |
| [Retention predicate](../../../src/core/capture/value.rs#L5981) | Checks birth enclosure and the bounded predecessor path. Derive and justify the predecessor interface before claiming equivalent admission. |
| [Crossed payload collection](../../../src/core/capture/control.rs#L7587) and [payload checking](../../../src/core/capture/value.rs#L6122) | Identify actual request payload and crossed resource owners. Selection, cover and trusted-recipient premises remain separate. |
| [Linked Core validation](../../../src/core/validate.rs#L13857) | Reconstructs applicable relationships under its gate. It remains required until each applicable consumer and proof boundary has a justified disposition. |

The rules give introductions, transformations, predecessor implications and
consumers conditional on their stated certified inputs. The remaining
obstruction is concrete: current summaries are not shown to provide complete
`Sources` and call/evidence cases, pre-birth `scope_valid` and structural
nesting for the same activation, dependency-stable state transitions, or the
substitution dependency relation needed at each opaque boundary. An
overapproximate predecessor set alone cannot supply an actual-dependency
implication, and an unknown cover cannot prove absence. Until those facts are
available, the new rules cannot grant unconditional retention or crossing in
the affected cases. Their representation and derivation, scoped abstraction
with coincident parameters, and coverage of recursive and unknown behavior
remain open; no constituent is rechecked to manufacture them.

Separate system-level proofs must justify those interfaces, coverage,
correspondence to the current predecessor check and execution under the stated
assumptions. The current graph and independent validation remain in force. No
judgment here proves termination, successful resource preparation or disposal,
or the full first-slice correctness guarantee.
