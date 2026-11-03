# Effects and Resources: Judgment and Composition Requirements

This record belongs to [DN-0061](../DN-0061-effects-and-resources-first-slice.md).
It takes the facts in the [facts catalogue](first-slice-facts-and-obligations.md)
and identifies what the slice's type-system judgments and composition rules
must express. It is a candidate design boundary, not current Ash semantics or
a complete calculus. The [specification](../../../spec/README.md) remains the
source for current rules.

The [verification audit](first-slice-verification-audit.md) traces current
checks to the rule premises they suggest and identifies unresolved coverage.
The [request and capture judgment record](first-slice-request-capture-judgments.md)
develops those premises for the first composition under consideration.

The aim is to check a new composition from the types and certified judgments
of its constituents. The composition is a new fragment; its constituents are
opaque and are not verified again. Rules may establish new conclusions from
their premises. An unproved premise remains an obligation rather than becoming
true because no contradiction was found.

Map these rules from the intended operational behavior: identify the facts
each step requires, introduces, discharges and preserves, then determine the
type judgments that account for them. A rule may introduce some facts while
eliminating others. The [worked audit trace](first-slice-verification-audit.md#worked-trace-request-and-resume)
shows this method for a request and resume; it does not claim the calculus is
complete.

## Judgment boundary

As a schematic description, write `GAMMA |- fragment : C` for a judgment that
the fragment has a computation type `C` under assumptions `GAMMA`. This is
metanotation, not proposed Ash syntax or a choice of Core representation.
Its type-system account must make the following information available to the
composition rules where relevant:

1. The value or answer type, exact effect requirements and applicable type and
   row parameters and constraints.
2. Facts about values and their actual resource or backing dependencies, kept
   distinct from the computation's possible requests and control behavior.
3. The requirements and guarantees of control that may be captured, including
   permitted continuation use, owned and outside completion obligations, and
   requirements of closing owned control.
4. The premises under which these facts hold. A judgment checked under an
   assumption remains conditional on that assumption.

These are requirements on the type system, not a decision that `C` is a tuple,
that every fact belongs in an effect row, or that source programmers must write
every annotation. Surface information may be inferred. Typed Core must carry
the complete resulting types. A successfully typechecked Core program or
fragment is certified; a consumer uses that certification without running
verification over the verified subject again. Certificate representation is
not selected here.

### Mechanisms, legacy and instances

The slice distinguishes three roles when mapping current behavior and checks
to the larger type system. A component can have more than one role:

1. **Language mechanisms** define how types, effects, handlers, resources,
   interfaces and their control boundaries can be formed and composed. This
   slice concerns the effect and resource interactions; it treats the other
   mechanisms through their established interfaces. Their current semantics
   remains authoritative. The intended type and proposition rules must
   express the applicable mechanism and its interactions.
2. **Legacy** includes existing verification and reconstruction paths
   targeted for replacement and constructs or implementations explicitly
   identified as legacy.
   A check is a candidate for replacement only where the new type-system
   judgment supplies the same required fact for the same subject and all its
   affected consumers. Until that correspondence is established, the
   uncovered check remains in the ledger. Shared analyses may have additional
   consumers outside this slice. The proposed removal of the legacy integer
   cell is a separate semantic change; its current semantics still applies
   until that change is adopted.
3. **Declared instances and implementations** use the mechanisms: for
   example, an effect and its operation requirements, a particular handler,
   or a resource and its operations. Their contracts state the facts specific
   to those declarations, and a checked implementation supplies evidence
   that it satisfies its contract. The common rules apply that evidence to a
   new composition. A particular declaration or its runtime implementation
   is not legacy merely because its behavior is concrete or built in.

Instances drive the hard design questions. Trace their specified operations
and actual implementations to identify which data, control and completion
facts must cross each boundary. Use those facts to identify and justify any
missing **general** type, proposition or authority form and its introduction
and elimination rules; then relate the declared instance contract back to
the operational semantics and implementation. This is direct design and
correspondence work, not a separate experiment or a request for a dedicated
checker for each instance. If a common rule cannot yet express or establish a
required fact, retain that gap and its affected consumers in the ledger.

An existing builtin can have special language or verification treatment
because Ash lacked a way to express its contract when it was introduced. Do
not presume that this privilege or a dedicated checker is a permanent
requirement. For an in-slice builtin, trace the specific privilege, the facts
it currently establishes and the declared behavior and external boundaries it
implements. Determine whether the missing facts and authority can be expressed
by general type-system forms and common rules, and record the correspondence
and disposition of each affected check. This may remove a special language or
verification path; it does not by itself establish that the builtin's actual
runtime or external behavior can be removed. Any changed behavior or replaced
implementation needs its own specified correspondence or semantic change and
evidence. The concrete implementation remains evidence for this design, not
an assumption that either its present privilege or its present code must be
permanent.

This classification does not turn a runtime operation into a type-level
proof or require reimplementing its behavior. It also does not make every
existing typechecking rule obsolete: the audit must identify the particular
verification work being replaced and the evidence that replaces it. A
successfully certified fragment and its contract are reused; a new
composition checks only its own relationships. The integer-cell proposal is
not a reason to classify the generic cell or other concrete instances as
legacy.

### Candidate Core judgment form

For this slice, the proposed complete Core computation judgment has the
following components:

```text
Comp(A, epsilon; requires R; behavior B; obligations O)
```

`A` is the ordinary result type and `epsilon` the existing effect row. `R`
is a proposition over the permitted boundary inputs and entry state; `B` is
the proposition or type-level contract covering the computation's applicable
results, requests, delimited control, resource transitions and failures.
`O` contains the still-unproved propositions needed by this particular
judgment. This notation names the information the Core judgment carries; it
does not prescribe source syntax, a tuple representation or a new runtime
value. Ordinary effect rows retain their existing meaning. Behavioral facts
are additional type-system facts rather than assumed consequences of a row.

The proposition language must be able to state scoped conjunction,
implication, equality and inequality, and quantification over the symbolic
values, states, owners and cases used by these rules. A proof of a proposition
may be established by the applicable typing rule or supplied as already
certified evidence. An unknown proposition is not a proof; where no rule or
evidence establishes it, the judgment remains conditional or fails at a use
that requires it. The rules do not require a complete decision procedure for
arbitrary propositions. Surface inference may construct these facts without
requiring them to be written; the resulting Core judgment must retain them.

Persistent propositions may be reused. One-shot capability authority is
tracked with its own usage state and cannot be duplicated merely because the
proposition describing it is reusable. Case-local witnesses cannot escape
their scope, and assumptions about an entry state do not automatically apply
after a transition. A fragment's outstanding requirements and obligations
remain attached when its judgment is reused; successful checking of a closed
program requires the applicable requirements and no-error obligations to be
established under the stated external assumptions.

For a polymorphic judgment, instantiation must preserve the facts, scope and
constraints established under its parameters. In particular, it must not
assume that distinct type parameters remain distinct after instantiation, or
that an abstract value has no resource dependencies. A call or handler can
check a new relationship between certified inputs and its own context; it
does not recover missing facts by inspecting an opaque constituent.

### Candidate propositions and evidence

The preceding requirements need a small logical interface. This subsection
specifies candidate judgments, not Ash syntax, a runtime proof engine or a
choice of solver. It is sufficient to state the rule families developed for
this slice; the adequacy and decidable implementation of particular predicates
remain to be established. The existing type, kind, row and instantiation
judgments remain authoritative for their domains.

Use the following sorts in the metatheory. A binder ranges only over its
declared sort and scope; a dynamic witness is symbolic at checking time.

| Sort | Examples of what it identifies |
| --- | --- |
| Static | Well-kinded types, rows and instance expressions; authenticated operations, binders and exact certified subjects. |
| Value | A symbolic value of an established ordinary type, with any separately certified representation and dependency facts. |
| World | An entry, intermediate, failure or post-state, including the applicable control and resource projections. |
| Failure observation | An actual failure world or the no-post-state marker for a terminal outcome with no resulting machine state. |
| Owner | A dynamic handler activation, cell activation or cleanup obligation, distinguished from its static site and from other executions. |
| Case | A request, reply, selection or transition witness with its scoped values, worlds, owners and guard. |

Kinds and sorts are not interchangeable. In particular, an effect instance
expression is instantiated in a correlated runtime context; it is not the
same object as a dynamic owner. A case-local value or owner is not a global
constant merely because its source site is known. World-indexed facts describe
that world: an entry fact is not silently transported to a post-state.

Write `GAMMA |- p : P` for reusable evidence `p` of a persistent proposition
`P` under persistent assumptions. Atomic propositions include the specific
well-sorted facts introduced by the slice rules: exact identity and equality,
row and dependency relations, case coverage, transition relationships,
owner phase and position, and failure or no-error conditions. Each atom needs
its own justified producer; naming it does not prove it. Equality is sorted,
and substitution is capture-avoiding and subject to the relation's stated
scope. Inequality is a proposition to establish, not the result of failing to
prove equality. Natural-number comparisons used by capacity rules require
their own sound arithmetic evidence.

For persistent evidence the following introduction and elimination rules are
inherited from ordinary intuitionistic natural deduction. They do not examine
a certified program fragment:

| Proposition | Introduction | Elimination |
| --- | --- | --- |
| `P and Q` | Establish evidence for both under the same assumptions. | Project either component. |
| `P or Q` | Establish one indicated alternative. | Establish the same conclusion separately from `P` and from `Q`, then discharge those branch assumptions. |
| `P implies Q` | Establish `Q` under an additional persistent assumption `P`, then discharge that assumption. | Apply the evidence to evidence of `P`. |
| `x = y` | Use reflexivity or a justified equality producer for terms of the same sort. | Substitute in a well-scoped proposition or use symmetry and transitivity. |
| `forall x:S. P` | Establish `P` for a fresh arbitrary `x:S` independent of undischarged assumptions and obligations. | Instantiate with an admissible term of sort `S`. |
| `exists x:S. P` | Supply a witness of sort `S` and evidence of its `P`. | Open a fresh witness in a local derivation; neither it nor assumptions depending on it may escape the conclusion or retained obligations. |
| `false` | Establish a contradiction by a justified rule. | Close the corresponding impossible branch. |

Negation is implication to `false`. Disjunction elimination checks both
alternatives as alternatives of one composition; it does not execute both or
duplicate an owner. A guarded case split requires evidence that the guards
cover all applicable cases and uses the same bound witness throughout each
branch. If coverage or a branch is unknown, the corresponding guarded
obligation remains. The quantifier rules do not turn a claim about one dynamic
activation into a claim about all activations, and existential elimination
does not let a fresh owner escape as an unconditional outside fact. A result
that genuinely needs such a witness must retain an appropriately scoped
existential interface and its obligations.

Authority is tracked in a separate context `DELTA`, not as a persistent
proposition. The current ordinary continuation instance is one-shot.
Write `GAMMA; DELTA |- construct : J [O] ; DELTA'` for a constructor that
establishes its judgment and transforms the available capabilities according
to its own rule. Acquisition or source selection introduces a fresh actual
authority only on its successful case; resume, discard or finish consumes or
moves the applicable authority according to that case's rule. Other
capabilities are preserved only where their contracts establish preservation.
The persistent proposition that an owner is live at a particular world can be
referenced repeatedly, but it does not introduce, copy or restore that
authority. A subsequent operation needs the appropriate current capability
and world-indexed facts. Alternative branches have compatible capability
accounting at their join; sequential uses cannot both consume the same
one-shot authority. These rules describe current one-shot behavior without
deciding the separate rules future multishot or discardable continuations
will require.

An evidence reference identifies the exact proved proposition, subject,
instantiation, assumptions and outstanding guarded obligations. A new use
checks its substitution and context and applies the evidence; it does not
recheck the proof or the verified fragment. Derived evidence may itself be
conditional, and all its undischarged assumptions and obligations remain
attached. An outstanding obligation is not evidence for itself, including
through a cyclic chain. Recursion or an unbounded case family requires a
separately justified induction, guarded finite-prefix argument or other sound
recursive rule with its assumptions explicit.

This logical interface does not establish that arbitrary formulas are
decidable, that every needed behavior can be inferred, or that an absence of
a detected contradiction is sufficient for correctness. A complete
implementation design must select admissible proposition forms, evidence
representation, solver and inference boundaries, and the treatment of
unproved obligations. System-level proofs must establish substitution,
capability preservation, coverage and the narrow no-error consequence of the
whole rule system. Those proofs are not performed by the compiler for each
program.

### Missing forms for declared contracts

The common judgments above still need a way to obtain the particular facts
they apply. The following is the minimum *expressive requirement identified
by this slice*, not proposed source syntax or a claim that each form must be
a separate language construct. A form may be inferred on the surface if the
complete result is retained in typed Core.

| Required form or relationship | What the slice needs to express |
| --- | --- |
| Declaration-bound contract | Attach authenticated, scoped propositions and obligations to an effect operation, handler, resource operation or lifecycle boundary. An effect operation's request/reply requirements are distinct from a particular handler's implementation and its certified behavior. |
| Parameterized contract | Bind existing type, kind, row and identity parameters in the contract; instantiate all dependent facts and obligations together. Actual dynamic values and fresh activations remain symbolic case witnesses, not static type identities. |
| Effect-parameter interface requirement | State an interface requirement on an effect's parameters, and preserve the instantiated requirement and applicable evidence or scoped obligation at each boundary that needs it. A checked implementation is reused; declaring or naming a requirement is not proof that it is satisfied. |
| Guarded transition | Relate the same actual input, authority and entry facts to correlated result, state, dependencies, effects and ownership disposition. Describe applicable success, request, failure, non-return and unknown cases, including the states or observations they actually reach. A declaration need not have state or an operation merely because another declaration does. |
| Control and completion | Express a captured segment's owner, permitted use and reply interface; preservation or transfer through control movement; and the declared normal, abandoned or effectful completion obligations. A later request's residual is scoped to its actual delimiter and witnesses. |
| Conditional evidence and laws | State premises, consequences and any laws needed by a declared contract, with equality, case splits, quantification and scoped witnesses as above. A law is a proposition requiring evidence under its assumptions, not a claim that every resource or operation satisfies the same law. |
| Contract satisfaction | Relate a particular checked implementation or trusted boundary to its declared contract and preserve that evidence at its opaque boundary. A declaration alone does not establish that an implementation or handler satisfies it. |
| Mutable value | Express that a particular mutable subject can hold and update a value of ordinary type `T`, with the applicable access, state-transition and resource-lifetime facts. A row mentioning a state effect does not by itself establish those facts or permission to access that subject. |

The current [effect rules](../../../spec/static-semantics.md#effects) admit
effect parameters and operation signatures and already track an exact row
instance; they do not by themselves express these behavioral contracts.
They also do not let an effect declaration require interface evidence for its
parameters. For example, a future `Failure<E>` contract may require `Error<E>`;
formation and use must obtain applicable evidence or retain the requirement as
a scoped obligation. The effect and interface are general mechanisms, and
`Error<CloseProblem>` is an instance of the latter. A generic boundary may
accept `Error<E>` as an explicit assumption; it cannot claim that assumption
was proved. Instantiation must carry the requirement and evidence under the
same parameters and scope without reselecting an already established
implementation. The precise formation, evidence scope, Core representation
and correspondence remain to be specified for rows, operations, handlers,
imports and public interfaces; this is not current Ash syntax. The bound does
not by itself change the existing exact effect identity or make handler
selection a wildcard. How scoped evidence and its dependencies interact with
each use must be specified without assuming evidence is part of that identity.
Current [cell rules](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
and [cleanup rules](../../../spec/static-semantics.md#scoped-cleanup-actions)
establish additional specialized semantic and analysis facts. They are
evidence to express and connect through the shared contract interface, not
permission to assume a general resource-declaration feature already exists.
The [Core effect forms](../../../spec/elaboration.md#effect-core-lowering)
retain existing typed structure; a proposal must specify which resulting
contract facts and evidence Core additionally carries.

Ash can express state changes through its current specialized cell operations,
but it does not yet provide a general source declaration or type-system form
for a mutable variable. The [ordinary value semantics](../../../spec/dynamic-semantics.md)
does not make internal locations source-visible mutable identities; the
[current cell execution](../../../spec/dynamic-semantics.md#scoped-cell-execution)
instead owns and updates a special slot. The intended cell is a mutable
variable holding `T`, with storage allocation, disposal and lifetime supplied
by its resource rather than by an additional cell owner. This is a design
target and an expressibility gap, not a claim about current Ash.

The general form must relate the ordinary value type `T`, the actual mutable
subject and permitted accesses, its state operations and effect requirements,
and the resource contract that supplies the storage and its lifetime. It must
express the applicable dependency, control and failure obligations for the
same cases, including how a previously returned value relates to a later
update. A particular aliasing, borrowing, sharing or mutation model remains a
design question; the missing form does not decide one. A checked producer
establishes the applicable contract and evidence once, and later compositions
reuse those facts while checking only their new access and context premises.
If the needed mutability, lifetime or preservation fact cannot be expressed or
proved, retain the gap and its legacy consumers rather than adding a separate
cell-specific verifier.

One generic contract application rule must instantiate the authenticated
contract for the exact declared subject, establish or retain its premises
for the same scoped case, and compose its conclusions with the existing
constituent judgments. Operation introduction does not select an interpreter:
an actual selected handler's separately certified contract supplies its
behavior, subject to the operation's requirements. Capability transitions
use the applicable authority state; reusable proof evidence does not create
another capability. The conclusion retains every unresolved guarded
obligation and all covered outcomes. It must not recheck a verified
declaration, handler or operand merely because the contract crosses a new
boundary.

These are language and typed-interface gaps where Ash cannot yet state or
retain the required relationship. Distinct work remains even after the forms
exist: selecting a checkable proposition fragment, inferring or obtaining
evidence, deciding which guards are provable, certifying implementation
correspondence and proving the system's coverage and no-error theorem. A
solver's failure to prove a proposition is an outstanding obligation, not a
new semantic rule or evidence that its negation holds. No inference mechanism
or particular logical encoding is selected here.

### Decision: mutability as a type-system property

Mutability is a property the general type system must be able to express and
track for the applicable subject or access. It is considered alongside the
ordinary value type `T`, location or resource relationship, permitted usage,
dependencies and other relevant properties. This decision does not choose
whether the property is attached to a binding, type, access or another
interface, nor does it add a separate resource or a mutable-subject calculus.
It is not automatically a property of the payload type `T`. A subject here is
a scoped type-system referent, not necessarily a source-visible address or a
runtime object.

The common property and contract judgments must relate mutability to the
same actual subject and its applicable access authority, state operations and
resource lifetime. The storage-providing resource supplies its allocation,
disposal and lifetime facts; mutability does not introduce a second owner or
lifecycle. The property is independent of any particular storage, resource or
effect protocol; a use composes whichever location, lifetime, permission and
state facts its contract requires. An effect protocol can describe operations,
but does not by itself establish the mutability property. An effect row
describes requirements, but by itself does not prove permission to update or
that an intercepted request changed state.
Guarded operation contracts describe actual results, state changes,
dependencies, failures and remaining obligations. A read result's ordinary
type does not decide whether access copies, borrows or moves it, or freeze
mutable state reachable through it.

The following generic schemas apply to **any** well-formed type-system
property; they are not specialized mutation checks. `P` names an admitted
property of the exact typed subject, and `mode` is its established evidence
and authority discipline. `Carry_prop` preserves all undischarged premises,
subject identities, guards and scoped witnesses. A general introduction must
have its own justified premises; writing a property is not proof of it.

```sequent
family shared-property-use:
  J-Property-Introduce :=
    GAMMA; DELTA_in |- certified(subject, J_subject) [O_subject]
    the applicable general property introduction is admitted for this subject, context and P and produces evidence e with discipline mode, the same case-indexed DELTA_out and undischarged obligations O_intro and O_new
    O_prop = Carry_prop(O_subject, O_intro, O_new)
    ===>
    GAMMA; DELTA_in |- property(subject, P, e, mode) [O_prop] ; DELTA_out

  J-Property-Apply :=
    GAMMA; DELTA_in |- established property(subject, P, e, mode) [O_prop]
    the new use requires P of this same subject under its applicable context and state, or retains O_fit
    the applicable general use rule applies e respecting mode and the authority and preservation contracts, producing the same J_result and case-indexed DELTA_out and retaining O_use and O_new
    O_result = Carry_prop(O_prop, O_fit, O_use, O_new)
    ===>
    GAMMA; DELTA_in |- the new use has result J_result [O_result] ; DELTA_out
```

The introduction and application each check only the new relationship.
Already established evidence is reused without rechecking its subject or
proof. Evidence is reusable only under its own discipline; a fact about a
one-shot authority does not duplicate that authority. Across a state or
control transition the property is available only if the applicable contract
preserves it. `DELTA_out` and the conclusion are the actual case-indexed
results of the respective general rule, with their unresolved obligations
retained; unknown cases do not prove permission or preservation.

Surface syntax and inference, property attachment, access and alias
permissions, initialization policies, and the representation and
interpretation of state operations remain to be designed. Future multishot
and discardable continuations require their own authority rules. Current Ash
supplies mutation through the specialized generic-cell builtin; it does not
yet provide this general mutability property. The existing independent cell
owner and its behavior remain current until a semantic change is proposed and
retained. The [gap ledger](first-slice-rule-resolution.md#design-and-implementation-gap-ledger)
records the evidence and affected legacy consumers. This decision is not an
implementation or a proof of system soundness.

### Compose properties of the same subject

The logical conjunction rule above applies to persistent propositions. It
does not by itself combine properties whose evidence or authority has a
different usage discipline. The following common schema composes established
properties of one subject without assuming that all properties or their
evidence are persistent. `Bundle` is a type-system interface, not a selected
runtime representation. Its components may include an ordinary type and
properties such as mutability, location or permitted usage. The subject `s`
and any case witnesses are scoped under the same guard `phi(c)`; an enclosing
interface must bind them when that case is left.

```sequent
J-Compose-Properties :=
  for each i, SIGMA contains the certified property(subject_i,P_i,e_i,mode_i) with its assumptions, guarded cases and obligations O_i
  under the same applicable case c, phi(c) and context, the certified subject and state relationships identify each subject_i with the same subject s, or retain scoped obligations O_subject_i(c)
  each property's instantiated assumptions and guard hold for that same case, or retain scoped obligations O_fit_i(c)
  the common authority rules jointly fit the evidence and actual DELTA to all applicable mode_i and preservation contracts, without inventing or duplicating authority or dropping an obligation; otherwise retain scoped O_authority(c)
  the common property rules determine Bundle(s,(P_i,e_i,mode_i)), its combined usage interface mode_bundle and the same case-indexed DELTA_out as the conclusion, retaining new obligations O_new
  O_bundle = Carry_bundle(each O_i, each guarded O_subject_i and O_fit_i, O_authority, O_new), preserving every original subject, guard and witness scope
  ===>
  SIGMA; GAMMA; DELTA, phi(c) |- Bundle(s,(P_i,e_i,mode_i)) : mode_bundle [O_bundle] ; DELTA_out
```

The subject relationships require the same actual value or access and the
relevant state facts, not merely the same ordinary type or source spelling.
Properties established in different worlds can be combined only when their
certified transition or stability relationships justify the facts at the
common case. Guarded alternatives remain correlated; combining facts from
incompatible cases is not evidence of a reachable combined case.

Joint authority fit is stronger than showing each use possible in isolation.
For example, two properties can refer to one one-shot authority without
creating two authorities or granting two uses. Any unexposed authority or
completion obligation is carried, scoped or discharged only as its own
protocol permits. The resulting interface permits each component to be used
only under its retained discipline; projecting one component does not make
another use of the same one-shot authority available. Distinct authorities
retain their own disciplines. A permitted shared authority follows its own
contract. An unproved subject match, compatibility or authority fit remains
an obligation, not an unconditional bundle.

This composition reuses the certified property evidence and checks only the
new correlations and compatibility. It does not recheck the subject, rerun
the producer's proof or introduce a mutation-specific checker. The
representable bundle and discipline, their inference and the system-level
substitution and soundness results remain to be specified.

### Specialize property-bearing evidence

`J-Use-Certified` below already permits a well-scoped instantiation of an
established judgment and carries its conditions and obligations. Property
evidence needs the following explicit specialization of that **same** use
rule: the property, its subject and its usage discipline must be substituted
together. This is a general rule for any property; mutability, location and
linearity are examples, not separate specialization algorithms.

```sequent
J-Specialize-Property :=
  SIGMA(q) = certified(GAMMA_q; DELTA_q |- property(subject,P,e,mode) [O_q]) with its original guarded case and witness scopes
  sigma is a well-kinded, capture-avoiding instantiation that respects rigid identities and the certificate's binders
  the new context establishes the instantiated GAMMA_q premises and actual subject correspondence, or retains their same-scoped obligations O_fit
  the instantiated authority interface matches the actual capabilities under mode[sigma], without duplicating or inventing authority, or retains O_authority
  the common substitution rule transports subject, P, e, mode and O_q under the same sigma and scopes its local witnesses
  the new instantiation and context checks retain their undischarged proof obligations as O_new
  O_use = Carry_use(O_q[sigma], O_fit, O_authority, O_new), preserving the original guards, subjects and binders
  ===>
  SIGMA; GAMMA; DELTA |- use(q,sigma) : property(subject[sigma],P[sigma],e[sigma],mode[sigma]) [O_use]
```

`O_new` contains any undischarged proof obligations introduced by this new
instantiation and context fit. The rule retains them; it does not assume they
are satisfied. `e[sigma]` denotes use of the same certified evidence at the
admitted instantiation, not a new proof of the subject or an extra runtime
capability. `DELTA_q` is the certificate's formal authority interface; the
actual `DELTA` must supply a matching authority under the instantiated mode.
Applying the evidence subsequently follows that discipline.
An unresolved property, capability match or subject correspondence leaves the
use conditional and cannot justify a closed no-error conclusion.

Distinct formal type or row parameters may instantiate to the same argument.
An inequality needed by the certified contract must be established for the
actual instantiation or remain an obligation; distinct spelling is not that
evidence. Conversely, the established freshness of two *dynamic* owner
activations is a case fact and is not erased merely because their static
types or sites coincide. If two formal inputs refer to one actual capability,
the instantiated usage policy must permit that relationship; an exclusive or
one-shot authority cannot be copied to satisfy two inputs. A policy that
permits sharing follows its own certified rules.

Substitution also preserves each world's and guard's correlation to its own
case. A property at entry is not automatically a property after a write,
capture or other state transition; that use additionally needs the applicable
established preservation or transition fact. Local existential witnesses
remain bound or are transported by an explicit scoped interface. The rule
does not select an aliasing or borrowing model, prove a solver complete, or
repeat checking of the certified subject. The scope, substitution and
authority-preservation theorem for this rule remains system-level work.

### Introduce and apply declared contracts

The following schemas make the shared use of those forms explicit. They are
candidate type-system rules, not new source syntax or a rule for a particular
operation. `K` is the authenticated contract of the exact declaration;
`sigma` substitutes its admitted parameters and `O` records undischarged
obligations with their subjects, guards and local binders. The evidence and
capability contexts are those defined above. A proof with unresolved
obligations remains conditional, and no premise may be discharged by assuming
its own conclusion, directly or through a cycle.

First, relate one exact checked implementation to its declared contract.
`implements(J_impl,K)` is the required behavior inclusion and premise
relationship for **all** cases admitted by `K`: it includes the actual
results, requests, state and dependency transitions, applicable authority
dispositions, non-return, failure and unknown cases. It is proved by the
applicable common judgments over the implementation's already established
judgment; it is not inferred from a matching ordinary type or an effect row.
`DELTA_impl` names the implementation's scoped formal capability interface;
the satisfaction certificate records its requirements and does not itself
own or export a runtime capability.

#### Derive behavioral refinement from guarded cases

The following common introduction supplies `implements(J_impl,K)` from
already certified behavior. Let `Pre_K` and `Pre_impl` be the contract's and
implementation certificate's complete entry assumptions, including their
applicable authority interfaces. `Cases_impl` is a complete guarded upper
cover of the exact implementation; `Cases_K` is the declared allowed behavior
under the corresponding contract entry. A covering case can represent several
outcomes and does not assert that any one outcome occurs. All comparisons
refer to the same actual subject and correlated entry, values, worlds, dynamic
owners, authority and local witnesses, under the admitted instantiation.

```sequent
J-Behavioral-Refinement :=
  GAMMA; DELTA_impl, Pre_impl |- certified(exact_implementation, J_impl) with complete guarded cover Cases_impl [O_impl]
  GAMMA |- authenticated_contract(declaration, K) with Pre_K and allowed guarded behavior Cases_K [O_K]
  under every admitted contract entry and authority, Pre_K establishes the corresponding Pre_impl and implementation authority premises, or retains their scoped obligations O_entry
  for every applicable implementation case, its guard and represented outcomes are covered by applicable K cases with the same correlated inputs, observations, authority dispositions and scoped witnesses, or retain their scoped inclusion obligations O_cases
  for each covered request, K permits that request and every reply and surrounding-control behavior admitted by the applicable K interface fits the implementation's corresponding residual assumptions; each residual refines the matching K residual under the same request and actual reply, or retains its scoped obligations O_residual
  the coverage and refinement evidence is non-circular and covers all admitted finite prefixes; applicable infinite behavior and nonreturn requirements have separately justified coverage
  O_refine carries O_impl, O_K, O_entry, O_cases, O_residual and all other undischarged proof obligations; the formal DELTA_impl interface and runtime entry and case witnesses are bound under their own scopes and guards, and unconditional structural obligations retain their original scope
  ===>
  GAMMA |- implements(J_impl,K) [O_refine]
```

The entry implication goes from the contract's permitted inputs to the
implementation's requirements: an implementation cannot demand an extra
precondition or capability from a caller unless the contract supplies it.
The implementation and case obligations are instantiated for every admitted
contract entry and packaged under their formal authority, entry and case
binders when the conclusion leaves those local contexts. They cannot escape as free witnesses;
an unconditional structural obligation is not made conditional on runtime
reachability merely by this packaging.
The case comparison includes normal return, request, state and dependency
changes, failure and applicable disposal, nonreturn and unknown behavior.
A possible implementation case can be omitted only if its guard is proved
infeasible under the same contract entry. An unknown implementation outcome
needs a sufficiently broad allowed case or remains an obligation; an absent
listed outcome is not evidence of impossibility. Output and failure
observations, including no-post-state, retain their actual correlations.

The request premise compares reply acceptance in the caller-safe direction:
every reply admitted by the contract must fit the implementation residual,
not merely replies the implementation happens to prefer. Capture, resume,
discard and other authority changes are compared using their declared case
dispositions, so reusable evidence does not create another capability. A
future multishot contract needs evidence for each admitted reentry and its
actual state and authority; this rule grants no copying permission. Recursive
evidence requires a justified well-founded or guarded finite-prefix argument,
not a cycle assuming this conclusion. Finite-prefix safety alone does not prove
an eventual-return or other liveness promise.

This introduction compares established interfaces and checks the new
relationship; it does not revisit the implementation's code or reprove its
certificate. All unresolved conditions remain attached to the resulting
refinement. The exact representation and proof procedures for case inclusion,
reply fit and recursive coverage remain design work; the schema does not
claim that current Core can express or discharge them.

```sequent
J-Contract-Satisfaction :=
  GAMMA |- authenticated_contract(declaration, K) [O_K]
  GAMMA; DELTA_impl |- certified(exact_implementation, J_impl) [O_impl]
  the implementation's scoped entry assumptions and capability interface match those required by K, or retain their precise obligations O_entry
  GAMMA |- implements(J_impl,K) using the certified cases and applicable common evidence rules [O_fit]
  O_sat = Carry_sat(O_K, O_impl, O_entry, O_fit), preserving subjects, case guards, binders and all undischarged proof assumptions
  ===>
  GAMMA |- satisfies(exact_implementation, declaration, K) [O_sat]
```

This introduction checks the new conformance relationship, not the already
certified implementation again. If that same relationship is already
certified, reuse its evidence rather than establishing it again. Source and
Core are distinct subjects: a
Core implementation can use this evidence only through an established
correspondence for the exact constructed Core and its obligations, or by its
own first applicable certification. A conditional satisfaction certificate
cannot be used as an unconditional implementation guarantee.

For an operation use, the declared contract governs the new request or
transition. Its established operand is evaluated once; `ApplyOp` composes
its covered cases and instantiates `K` on each actual normal operand result.
It carries operand requests, failures, non-return and unknowns without
inventing an operation execution on those paths. The operation's row
projection is computed by the applicable shared row rules.

```sequent
J-Apply-Operation-Contract :=
  GAMMA |- authenticated_contract(operation, K_op) [O_K] and sigma is a well-scoped admitted instantiation
  GAMMA; DELTA |- certified(operand, J_arg) [O_arg]
  for each covered normal operand case, its same actual value, state, dependencies and authority satisfy K_op[sigma]'s entry propositions, or retain the scoped obligations O_entry
  the common operation and capability-transition judgments construct B_op = ApplyOp(J_arg,K_op[sigma]) with the same result C, row epsilon and case-indexed authority disposition DELTA_out as the conclusion, retaining unresolved obligations O_new
  O_call = Carry_call(O_K[sigma], O_arg, O_entry, O_new), preserving each original subject, guard and witness scope
  ===>
  GAMMA; DELTA |- apply_contract(operation, operand, sigma) : C ! epsilon ; B_op [O_call] ; DELTA_out
```

This rule does not select a handler, prove a reply or instantiate a handler's
implementation guarantee from the effect declaration. It also does not
duplicate a capability by reusing persistent evidence. `DELTA_out` is the
case-indexed authority disposition established by the applicable transition;
an unestablished disposition remains an obligation.

An actual handler has its **own** certified behavior interface `K_handler`.
Its separately established satisfaction evidence relates that same
implementation to the effect declaration's requirements `K_effect`; the two
contracts are not assumed identical. A new handler composition applies the
handler interface only to cases where the
established nearest-boundary and crossing rules select that handler. Cases
that pass the boundary, are intercepted elsewhere, fail, do not return or
remain unknown are preserved under their own guards. The selected contract
receives the same actual request, capture and fresh dynamic owner; its reply,
resume, discard and completion behavior follow its certified interface and
the common authority rules. The handler's output row is obtained by the
applicable common row and least-row judgments, including clause effects.

```sequent
J-Apply-Handler-Contract :=
  GAMMA; DELTA |- certified(body, J_body) [O_body]
  GAMMA |- certified(exact_handler, J_handler) [O_handler] and K_handler is the scoped behavior interface of that same J_handler
  GAMMA |- satisfies(exact_handler, declaration, K_effect) [O_sat] and the satisfaction evidence relates this same K_handler to K_effect
  the common selection and crossing judgments cover the body's applicable request cases under the actual identities, contexts and guards, or retain O_select
  for each selected case, declaration and K_effect are the exact targeted effect and the same operation's requirements under that case's admitted instantiation
  for each selected case, K_handler's scoped premises fit the same request, capture, owner and entry state, or retain O_entry
  the common handler, continuation and row judgments construct B_handle = Handle(J_body,K_handler) with the same result C, row epsilon and case-indexed authority disposition DELTA_out as the conclusion, retaining O_new
  O_handle = Carry_handle(O_body, O_handler, O_sat, O_select, O_entry, O_new), preserving each original subject, guard and witness scope
  ===>
  GAMMA; DELTA |- handle_contract(body, exact_handler) : C ! epsilon ; B_handle [O_handle] ; DELTA_out
```

The `for each` premises instantiate one certified conditional interface at
the correlated symbolic cases; they do not verify a handler or operand once
per case. Missing selection, residual, satisfaction or behavior coverage is
an obligation or covering unknown. In particular, an unknown case cannot
establish a closed no-error result. The [current handler semantics](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
and [static rules](../../../spec/static-semantics.md#effects) are the source
for the operational correspondence these candidate schemas must eventually
prove. Any existing specialized verification not yet covered by a shared
rule and established contract remains in the slice's ledger; naming a schema
does not establish its replacement.

### Apply an authority protocol

Authority can move when a request captures control, a reply restores it, an
owner completes or an admitted discard closes owned control. These are not
all the same transition. Let the established contract `K` describe the
permitted transition, input authority, scoped facts and possible outcomes
for its particular subject. Its authority policy is part of the contract;
the generic rule does not impose one-shot behavior on every declaration or
infer duplication or discard permission from a reusable proposition.

`DeltaCase(c)` is the authority disposition for the **same** covered case
`c`: it records the destination context for a continuing case, or the actual
terminal or non-return disposition when there is no next ordinary context.
For an unknown case it is a covering unknown, not an asserted exact
disposition.
`Post(c)` records that case's correlated world, subject, capabilities,
dependencies and remaining completion facts as applicable. For a fatal
failure with no observable post-state it uses the established no-post-state
failure observation, not a fabricated world. `Carry_auth`
retains each undischarged contract, input, transition and proof obligation
with its subject, guard and scoped witnesses.

```sequent
J-Authority-Transition :=
  GAMMA |- authenticated_contract(subject, K) [O_K] and sigma is an admitted scoped instantiation
  GAMMA; DELTA_in, phi |- action is the same subject's actual covered transition under K[sigma]
  the certified input facts and DELTA_in satisfy that transition's declared premises, or retain their scoped obligations O_entry
  K[sigma] supplies a complete guarded transition cover B with Post(c) and DeltaCase(c) for each applicable continuing, terminal, non-return and unknown case
  the common capability and proposition judgments check this new transition and its case relationships, retaining O_transition
  O_out = Carry_auth(O_K[sigma], O_entry, O_transition), including any other undischarged input and proof obligations
  ===>
  GAMMA; DELTA_in, phi |- transition(subject, action) : B [O_out] ; DeltaCase
```

The rule instantiates one certified protocol; it does not perform the
transition or assume that a covered case occurs. Its conclusion is
conditional where an entry, case or postcondition obligation remains. For a
capture or restore, the same actual segment, owners, phases and outside
obligations are carried or otherwise disposed of exactly as that protocol
states. A claim that a segment was copied requires the applicable contract's
authority and dependency conditions for the copies; neither the reusable
description of a segment nor a source location creates a second authority.
For a close, successful completion, failure, pending disposal and non-return
retain their own outcomes. Unknown behavior cannot prove an owner completed.

For a new sequential composition, apply the second certified interface only
to cases that actually reach its entry, with the first case's own world,
authority disposition, values and obligations. Other outcomes remain in the
composition's cover. The following schema uses the existing sequencing
judgments; `SeqCases` is their case composition, not a second scan of either
constituent.

```sequent
J-Authority-Compose :=
  GAMMA; DELTA_in |- certified(first, J_first) [O_first] with complete guarded cases and authority dispositions
  GAMMA |- certified_conditional(second, J_second) [O_second] for its declared entry and authority interface
  for each covered first case c that enters second, Post(c) and DeltaCase(c) establish its same-case entry and authority premises, or retain scoped O_fit(c)
  the common sequencing rules give B_seq = SeqCases(J_first,J_second), including first requests and residuals, non-return, failures and unknowns
  the common authority rules determine DeltaSeq(c) for each resulting case without merging distinct owners or duplicating one-shot authority
  those new sequencing and authority checks retain their undischarged proof obligations as O_new, with their original guards and witnesses
  O_seq = Carry_seq(O_first, O_second, each guarded O_fit(c), O_new), preserving every original subject, guard and witness scope
  ===>
  GAMMA; DELTA_in |- compose(first,second) : B_seq [O_seq] ; DeltaSeq
```

Alternative cases are checked as alternatives, not executed together. A
control-flow join may publish only the capability and fact interface justified
for every case it represents, with any unresolved differences retained as
case distinctions or obligations. In particular, a path that fails, is
abandoned or does not return does not enter the second fragment merely to
make authority states agree. A capture followed by restoration uses the
already established capture and restore contracts for that actual activation;
the composition checks their new connection and does not verify the captured
fragment again.

The current [ordinary continuation rules](../../../spec/static-semantics.md#effects)
and [capture and resume semantics](../../../spec/dynamic-semantics.md#effect-handlers-and-completion)
are the one-shot instance for this slice: the applicable structural and
runtime consumption conditions still hold. Future multishot or discardable
continuations require their own declared protocols and system-level
justification; this schema neither implements nor assumes those policies.
The shape and checkability of protocol declarations, case-indexed authority
and their substitution and soundness proofs remain open.

### Join guarded alternatives

An alternative composition needs a producer for its joined property and
authority interface, not only a statement that branches should agree. Let
the already certified selector supply guarded cases for the actual choice,
and let each branch have its own conditional certified behavior and scoped
obligations. `Normal_i` covers normal results of branch `i` with the same
actual selector case, result, post-state, authority disposition and local
witnesses. `P_join` may refer to that correlated result; it does not identify
different branch-local values or fresh owners. `Delta_join` is a common
authority interface, possibly retaining guarded alternatives or scoped
existential witnesses rather than equating different dynamic owners.

```sequent
J-Alternative-Join :=
  GAMMA; DELTA_in |- the certified selector and branch interfaces cover all applicable choices and outcomes, or retain a covering unknown [O_inputs]
  for each covered choice i, the same selector case establishes the corresponding certified branch's entry and authority premises, or retains scoped O_entry_i
  for each covered normal result c of each branch, its established postconditions entail P_join(c) and its authority disposition admits Delta_join(c), or retain scoped O_join_i(c)
  each such authority fit accounts for all applicable authorities and completion obligations: any not exposed by Delta_join(c) are carried or scoped, or have been consumed, transferred, discharged or forgotten only as their own declared policy permits; otherwise retain scoped O_authority_i(c)
  every unknown case that may reach the join is covered by the same P_join and Delta_join guarantees, or retains its scoped obligation O_unknown
  the common case and sequencing judgments construct B_alt with all selector, branch, request/residual, failure, non-return and unknown outcomes and preserve their completion and outside obligations
  every applicable ordinary and structural usage rule is established for each required syntactic branch independently of behavioral reachability
  O_alt carries O_inputs, each guarded O_entry_i, O_join_i and O_authority_i, O_unknown, and the new case, coverage and proof obligations under their original scopes
  ===>
  GAMMA; DELTA_in |- the new alternative has behavior B_alt [O_alt] and, on its normal join cases, P_join with authority interface Delta_join
```

The join eliminates the selected case distinction only for facts and
authority supported by every applicable normal outcome. A terminal failure
or non-return has its own completion, disposal and outside obligations; it
does not reach the normal join. A request or abandonment follows its certified
residual or handler case, which may later return or not. If a branch's normal
outcomes, unknown behavior or entry fit are insufficiently known, a covering
unknown or scoped obligation remains; it cannot supply an unconditional
joined fact. An established empty normal-return cover yields no actual join
case and does not prove termination or completion.

An authority fit is not unrestricted subcontext projection: it cannot silently
drop a required completion or duplicate an affine or linear capability. A
policy that permits discarding an authority can establish that disposition
under its own conditions; this rule does not impose one policy on all cases.

Ordinary branch typing and the current structural `U-Match` check are separate
from this behavioral cover. In particular, an unreachable behavioral case does
not remove a syntactic arm from the one-shot usage rule. Other authority
policies use their own declared structural rules. The same case-indexed
certificate is reused when the joined result is consumed; this rule does not
verify the selector or branches again. Scope, coverage and authority-join
preservation remain system-level proof obligations.

### Use an established judgment

The following rule makes reuse explicit. `SIGMA` is the environment of
judgments already established for the relevant subjects; it is metanotation,
not a decision to build a registry. A reference `q` identifies one such
subject and its judgment, including its premises and any outstanding
obligations `O`. `sigma` is an admitted capture-avoiding instantiation of the
judgment's parameters. The use preserves its conditions, scopes, subject
relationships and obligations. `O_need` contains the instantiated premises
that this context does not yet establish, with their guards and scopes. It checks the new instantiation and context
relationships; it does not check the referenced fragment or its proof again.

```sequent
J-Use-Certified :=
  SIGMA(q) = certified(subject, GAMMA_q |- J [O])
  sigma is well kinded and respects the certified parameter and scope constraints
  the new context establishes the premises GAMMA_q[sigma] or retains each missing premise in O_need
  the new use respects the consumption discipline of each actual capability
  ===>
  SIGMA; GAMMA |- use(q, sigma) : J[sigma] [O[sigma] union O_need]
```

The certificate is reusable information, not a second runtime capability.
Using it twice does not duplicate a one-shot owner: the applicable composition
and usage rules still account for that owner's actual state. Conversely,
distinct abstract type parameters are not assumed unequal merely to make a
composition succeed. `O[sigma] union O_need` remains conditional until the appropriate
proof is established; a reference does not turn it into a fact. A conditional
or untrusted claim is not admitted to `SIGMA` as an unconditional certified
judgment. System-level substitution and soundness results must justify the
rule separately from each program's type checking.

### Carry and discharge an obligation at its use

A checked fragment can expose an obligation whose facts become available only
when it is composed with its context. To use such a fragment without checking
it again, the type-level interface must preserve the obligation's subject,
guard, bound witnesses, assumptions and proposition together. Write
`o = (subject, bind z, phi, P)` for the requirement that every admissible
case of that subject satisfying `phi` establishes `P` for the **same** `z`.
This refines the guarded pairs used by
[`C-Require` and `C-Discharge`](first-slice-behavior-coverage-rules.md#guarded-cases-and-obligations);
it does not require a particular registry or runtime representation.

The judgment that carries `o` remains conditional. An enclosing composition
can establish the requirement for its own actual case, but cannot rewrite the
original certificate as unconditional for every other context. The proof may
reuse previously established facts and the producer's certified interface;
it does not inspect the subject. `z` can include an activation, value, entry
and later state, or type and row parameters. A fact about one such tuple is
not automatically a fact about a different tuple. Write
`guarded(z, phi, O_proof)` for those proof obligations retained under the
same binder and guard, including their own additional guards and scopes.

```sequent
family scoped-obligation-use:
  J-Obligation-At-Use :=
    SIGMA(q) = certified(subject, GAMMA_q |- J [O union {o}])
    sigma is an admitted capture-avoiding instantiation and GAMMA establishes the instantiated outer assumptions
    o[sigma] = (subject[sigma], bind z, phi, P) with z well scoped at this use
    GAMMA; L, entry, phi |- P [O_proof] for every admissible z of this same instantiated subject
    the proof uses its premises under the applicable capability discipline
    O_proof does not depend on discharging this occurrence of o, directly or through a cycle
    ===>
    SIGMA; GAMMA |- use(q, sigma) : J[sigma] [O[sigma] union guarded(z, phi, O_proof)]

  J-Obligation-By-Cases :=
    SIGMA; GAMMA |- use(q, sigma) : J [O union {(subject, bind z, phi, P)}]
    n >= 1 and each g_i is well scoped under z
    GAMMA; L, entry, phi |- g_1 or ... or g_n [O_cover] for every admissible z
    for every i, GAMMA; L, entry, phi, g_i |- P [O_i] for the same subject and z
    O_cover and each O_i do not depend on discharging this occurrence, directly or through a cycle
    ===>
    SIGMA; GAMMA |- use(q, sigma) : J [O union guarded(z, phi, O_cover) union union_i guarded(z, phi and g_i, O_i)]
```

Each case in `J-Obligation-By-Cases` includes its own correlated witnesses and
facts; a proof for one case cannot be paired with a different case's value or
owner. Infeasibility is one way to establish a branch, but an undecided guard
must remain covered. For example, if a cleanup request may select either an
inner handler or an outer one, compatibility must be established for both
feasible selections. A fact for the inner handler does not discharge the
outer case.

The evidence used at one composition may itself be conditional on other
obligations; those obligations remain attached to the result with their own
guards and scopes. An obligation cannot be discharged by assuming itself,
including through a cycle of other outstanding obligations; recursive
evidence needs its own justified rule. Persistent
propositions can be referenced again when their subjects and assumptions
match. A proposition about a one-shot capability is not another copy of the
capability: actual consumption remains in the linear usage and owner
judgments. The rules do not merge obligations for distinct activations merely
because their written propositions look alike. Instantiation carries any
remaining obligations and their binders forward; it cannot leave a local
owner or case witness free outside its scope.

For a closed program, all applicable in-slice obligations, including the
no-internal-error obligations, must be discharged under the permitted external
assumptions. A conditional judgment is useful at an open boundary but does not
by itself establish the closed no-error result. These rules specify how an
established obligation can be transported and discharged; the individual
rule families still have to provide sufficient facts and coverage to do so.

### Infer a conditional source judgment

Surface inference may fill in type, property and contract information that a
program does not write. The following common schema describes its result; it
does not choose surface syntax, a constraint solver or a completeness claim.
`J_meta` is a proposed source judgment with scoped inference variables, and
`C_gen` records the constraints and evidence obligations introduced by the
new source composition. The judgment includes its applicable case-indexed
authority disposition, not only its value type and effect row. Generation
uses the applicable general introduction, elimination and composition rules
and reuses any certified children; it does
not infer a behavioral contract merely from an ordinary type or effect row.

```sequent
J-Surface-Inference-Result :=
  GAMMA; DELTA |- generate(source, certified_children) = J_meta, C_gen [O_children]
  the system-justified generation correspondence establishes that the generated constraints and evidence entail this same J_meta for this source and context, covering all applicable ordinary, structural, property, behavioral and authority premises
  sigma is a well-scoped, kind-correct substitution for the inference variables it resolves, preserving guards, subject identities and local binders
  sigma consistently specializes GAMMA, DELTA, the child interfaces, their assumptions and obligations, and the resulting authority disposition
  established evidence E in the specialized context, with its inherited obligations O_evidence, discharges the identified constraints C_proved[sigma] without assuming the same discharge or resulting judgment, directly or through a cycle
  every other generated constraint is retained after sigma as a well-scoped obligation O_unsolved, with its subject, assumptions, guards and witnesses
  gen soundly generalizes eligible remaining metavariables under the applicable rules and contexts into fresh explicit parameters; all ineligible metavariables needed for the Core judgment are solved
  gen applies the same capture-avoiding replacement and parameter binders to J_meta[sigma], retained constraints, assumptions, authority interfaces, evidence and dependent obligations
  (J_result, O_result) = gen(J_meta[sigma], Carry(O_children[sigma], O_evidence, O_unsolved, new evidence and composition obligations)) as one package with the same parameter binders and instantiation throughout, retaining each original scope and guard
  no unsolved inference metavariable is relabeled as a resolved Core type, instantiation or established fact
  ===>
  GAMMA[sigma]; DELTA[sigma] |- source : J_result [O_result]
```

The generation correspondence is justified once for the system; it is not a
separate soundness proof for each use. The discharge premises need justified
general rules and evidence; naming a constraint or finding no contradiction
does not prove it. Evidence may itself have other conditional obligations,
provided they are carried in `O_result` without a discharge cycle.
Solver refusal or inability to prove a constraint leaves it unresolved, not
false or automatically satisfied. A well-scoped unresolved behavioral
obligation may remain at an open boundary. If an unresolved type, kind or
other metavariable cannot be bound in a permitted interface or represented
in typed Core through sound generalization, inference cannot publish a
completed Core judgment for it. Generalization must satisfy the applicable
rules; merely binding or renaming an unsolved metavariable does not establish
it as a parameter. An explicit proposition or constraint can remain an
obligation where the interface admits it, but it is not a hole requiring Core
to infer a missing type, kind, instantiation or constituent contract.
Ordinary typing and structural usage requirements apply even to a behavior
that has no normal return.

The result is conditional on all its retained obligations. A later
composition can discharge an applicable obligation using new contextual
facts without rechecking the source or certified children. A closed no-error
result still needs every applicable obligation discharged under its permitted
external assumptions. This schema does not assert that all properties can be
inferred, that a solver is complete, or that Ash currently represents these
new contracts and evidence.

### Carry a checked source judgment into Core

Source inference and Core certification concern related but different
subjects. An established source judgment cannot simply be relabeled as a
judgment about an arbitrary Core node. Conversely, generating a Core node
does not require rechecking a source constituent whose judgment is already
established. The proposed elaboration must construct the new Core judgment
from the source judgment and certified judgments for the Core children, using
the applicable correspondence for the constructor it introduces.

The target Core interface states the result of surface inference explicitly,
so checking a Core composition need not infer types, implicit resource or
control relationships, proof evidence or missing substitutions from its
constituents. A composition checks its own supplied relationships and uses
certified evidence under its original assumptions and authority discipline;
it does not recheck the certified subjects. References to evidence are
permitted where they identify the actual judgment, subject, scope and premises.
An open obligation remains explicitly represented and conditional. This is a
design target, not a claim that current Core or these candidate rules already
provide such an interface.

Explicit does not mean enumerating a future runtime continuation or activation
at compile time. The interface can bind a symbolic context, resource, owner or
case, and the new composition instantiates the applicable relationship without
opening an opaque fragment. Runtime selection supplies its actual instances.
The required Core forms and their system-level correspondence remain to be
specified; this account selects neither a proof representation nor runtime
control encoding.

Write `lower(e, Gamma, J) = (n, J_core, map)` for one successful elaboration.
`map` relates the source binders, instance expressions, local owner binders,
case witnesses and obligations to the actual Core node and its scope. For a
runtime activation or value witness, this is a scoped relational schema, not
an assertion that its future dynamic identity is known or stored at compile
time. It is specific to this elaboration, not evidence inferred from a matching
ordinary type. For each in-slice form, a system-level elaboration correspondence must
justify the applicable constructor rule and the preservation of observable
behavior and stated obligations. That justification is a property of the
rules and elaborator, established separately; compilation does not prove it
again for each program.

```sequent
J-Lower-Certified-Composition :=
  GAMMA |- source_form(e_1, ..., e_n) : J_source [O_source]
  each J_i and GAMMA_i is the corresponding certified child judgment of that same source derivation
  for every child i, lower(e_i, GAMMA_i, J_i) = (n_i, J_core_i, map_i) with its certified Core judgment and outstanding obligations
  each map_i relates that exact source child judgment to J_core_i under the same applicable substitutions and scoped assumptions
  the applicable in-slice lowering rule constructs exactly node n from those n_i and the established source evidence
  the new Core constructor's type, row, scope, ownership and behavior premises hold using J_core_i and the mapped source facts
  map is well scoped and retains every applicable source and child assumption and obligation, including guarded witnesses
  J_core and O_core are the constructor rule's resulting judgment and mapped outstanding obligations
  ===>
  GAMMA_core |- n : J_core [O_core]
```

`O_core` contains the mapped outstanding obligations and any new obligations
of this Core composition. The conclusion certifies the exact constructed node
under those conditions; it cannot certify a different node merely because the
nodes have the same type. The rule checks the newly introduced constructor
and its relationships. It reuses child certificates and does not replay
either a certified source child or a certified Core child. If the required
correspondence or a mapped fact is unavailable, it remains an obligation or
the construction cannot claim certification. A separately supplied Core node
without a suitable certificate needs its own first applicable checking; this
rule does not authenticate it by association with source text.

For example, lowering a certified `perform E.op operand` constructs the Core
`Request` from the certified lowered operand. The new constructor retains the
same effect-instance expression and operation and the operand's actual type
and row. Its runtime request frame saves the applicable lexical instantiation
before evaluating that operand; the static node is not that runtime snapshot.
The request rule composes the operand's existing behavior, dependency and
failure facts with the new request-frame facts. If the operand requests an
effect itself, its residual retains that pending frame; it is not replaced by
the outer request or checked again. The Core judgment also retains the row
union and any unresolved crossing or failure obligations. The
[current Core form](../../../spec/elaboration.md#effect-core-lowering) is the
operational correspondence to be justified; this example does not assert
that current Core carries the proposed behavioral certificate.

More specifically, the request constructor can instantiate the general
composition rule as follows. `J_operand` is the operand evidence used by this
same source `perform`, and `map_operand` is the corresponding child
elaboration. `I` is the symbolic instance expression, not a fixed runtime
instantiation. In the Core node below, `I` denotes that expression after the
constructor's binder and substitution map, and `GAMMA_core` is the mapped
scope; the two entry environments must be related by the same correspondence.
The relation `Corr_request` is the system-level correspondence
for this constructor, including the mapping of source and Core entry states,
the saved instantiation, request and reply cases, and their scoped witnesses.

```sequent
J-Lower-Perform :=
  GAMMA |- perform I.op operand : J_source [O_source] using certified J_operand
  lower(operand, GAMMA_operand, J_operand) = (n_operand, J_operand_core, map_operand) for the same scoped operand and substitutions
  the authenticated operation contract and the operand's Core type, row and behavior satisfy the new Request constructor's premises
  n is the Core Request(I, op, n_operand), with its exact resulting type, row, origin and scope
  the certified request-frame rule supplies the new normal, request, failure, non-return and unknown cases under their actual guards
  Corr_request relates those Core cases and obligations to the source perform cases under map_operand and the constructor's scope map
  O_core retains the mapped source and child obligations and every new request-construction obligation
  ===>
  GAMMA_core |- n : J_request_core [O_core]
```

The constructed `J_request_core` includes the actual `J-Perform-Behavior`
composition over the lowered operand interface, with the same certified
normal-return compatibility and request-frame conditions. `Corr_request` does
not claim that source and Core take identical machine steps, or that the
compiler checks every execution. Its once-per-system justification must
relate the relevant observations and boundary facts. If the request-frame
failure or behavior interface remains unknown, the corresponding Core
obligation remains; successful lowering does not make it empty. The rule
does not select the request's eventual handler.

Current Ash specifies independent linked Core validation and reconstructs
some capture and resource relationships. The construction rule above is the
proposed end-to-end replacement for the in-slice constituent work, not a
description of the present pipeline or permission to remove that validation
now. Its correspondence and all affected consumers must first be established.

## Shape of a composition rule

The following is a schematic interface for a rule, not an implementation or a
sufficient calculus. Each constituent judgment is already certified under its
own assumptions. The new composition has context `GAMMA`; the constructor's
specific rule determines which additional premises and conclusion type apply.
It also introduces any constructor-local binders and assumptions needed to
match a constituent's certified judgment.

```sequent
J-Compose :=
  for each constituent_i, certified(GAMMA_i |- fragment_i : C_i)
  for each constituent_i, local_i = constructor_context_i(GAMMA)
  each local_i establishes the required instantiated premises from GAMMA_i
  the constructor's new composition premises hold under GAMMA, local_i and C_i
  the constructor's rule discharges its local assumptions and determines C
  ===>
  GAMMA |- constructor(fragment_1, ..., fragment_n) : C
```

The composition uses the certified judgments and checks its own premises; it
does not verify the constituents again. Each `local_i` extends `GAMMA` with
only the binders and assumptions provided for that constituent by the
constructor. For example, a handler supplies its clause's pattern bindings and
capability, and a cell scope supplies its body's fresh owner and provider.
The rule must discharge or preserve assumptions according to their scope; it
cannot export a local assumption as an unconditional fact. An open `GAMMA` may
itself contain assumptions, so the conclusion remains conditional on them. A
closed use must establish the relevant premises; an undischarged assumption is
not permission to proceed as though it were proved. Current Ash rejects
relevant unproved resource escape, retention or abandonment. This schema does
not change those rules or establish that any particular type representation is
sufficient.

## Required judgments and compositions

F01–F23 below refer to the facts catalogue; E1–E10 and R1–R10 refer to the
[current rule catalogue](first-slice-catalogue-and-map.md#rule-catalogue). The
columns state what a rule must account for, not fully specified inference
rules. The semantic meaning and sufficient type-level form of each relationship
remain to be defined and justified.

| Composition | Certified inputs and premises | Required conclusion or obligation |
| --- | --- | --- |
| Effect instance and row, E1–E3 | Effect declaration identity, parameter kinds and operation signatures; type/row arguments and their equality and lacks facts. | Establish a well-formed exact instance or computation row. Preserve applicable facts under instantiation; union, weakening and exact removal must satisfy their premises. An unknown tail does not prove membership or absence. F01–F03. |
| Request, E4 | Operation contract `P -> Q` at the exact instance; an operand judgment with type `P`, its effects and relevant value dependencies; a defined row union. | Produce a computation of result type `Q` with the operand requirements and requested instance. Its type-system account must retain the request and relevant payload facts for later composition. Static typing does not choose the runtime interpreter. F01–F04, F12, F15. |
| Handler, E5–E6 | A certified body whose row contains the exact target; exactly one irrefutable clause for every operation, with its pattern checked against that operation's instantiated input type and its body checked at the shared answer type under its introduced continuation capability; and the context facts needed by the control rules. | Produce that answer type and the least output row containing the body remainder and direct clause effects; discharge only the handled exact body requirement. The control account must support the separately specified nearest exact runtime selection; static typing does not select the runtime boundary, and a clause's direct request bypasses the removed handler. F05, F07–F11. |
| Continuation use, E7 and E9 | An available capability with operation-result input type, handler-answer type and output row; a certified operand of the input type whose effects fit the output row and whose usage leaves the capability available; usage facts for the clause paths. | Resume consumes the capability after its operand, yields the handler answer and accounts for restoration. Each normally completing clause path must consume its capability exactly once; sequencing and branches compose usage, and the specified barriers prevent escape. This does not prove termination. F07–F08, F10. |
| Discard and close, E8 and E10 | An available ordinary-clause capability not associated with a private Store root; facts about its recursively owned control and resources, outside and running completion, closing actions and their actual interpreter requirements. | Consume the capability and establish that closing the owned control preserves required outside and running completion and compatible interpretation. Produce `Unit` and the least residual close row under the current rules. On successful close, discharge the owned obligations. Unproved closability remains an obligation; it is not permission to discard or a guarantee of termination. F10–F12, F19–F22. |
| Cell scope, R2–R3 | A certified initializer checked in the preceding scope, with fixed payload type `T`, relevant value dependencies and effects; the generic-cell API and its authenticated provider and operations; a body checked with the fresh scope identity and authority. | Establish the scope's answer type and the initializer row union the body row after removing only its exact cell effect. Account for ownership, initialization and scope completion; prove the closing identity does not escape through the result, outward row or evidence, and dependent results or evidence do not escape. F13–F16, F18. |
| Cell access and retained value, R3–R5 | Established handle and provider authority; each possible target activation; dependencies of the particular payload or, for a read, facts supplied by the established cell-state relationship or selected handler-reply contract. | Preserve `T` and the particular returned value or snapshot's dependencies. Require retained owners of every actual initializer or builtin replacement to strictly enclose each possible target. An intercepted read uses its handler's actual reply; an intercepted write does not itself replace the builtin slot. Missing relevant facts remain obligations. F14–F17. |
| Cleanup, R7–R10 | The action and body judgments, action's latent effects and dependencies, and the owner and interpretation facts applicable at closing. | Establish the scope result and effects, its invocation and completion obligations, and their preservation through capture and resumption. Closing must account for the action's structural interpreter requirements and effects; a running action or unfinished close cannot be skipped. F20–F22. |
| Scoped completion and boundaries, R4–R6 and R10 | The particular result, payload, capture and owner relationships; any established facts from outside the slice, including backing dependencies. | Preserve outside obligations and facts, discharge only the owners closed by the rule, and reject or retain an explicit obligation where independence or completion is unproved. A payload type alone does not prove resource independence. F11, F15, F19, F23. |

For a handler clause, “checked under the introduced capability” can itself be a
conditional judgment: the clause is checked under the capability's stated
assumptions, then the handler composition must establish or retain the premises
needed for the particular captured context. The rule must not inspect the
verified clause or body again to recover those facts.
The current structural usage check composes every syntactic branch and its
outgoing state even when behavioral facts prove no normal return there; the
normal-path wording in the table is its execution consequence, not permission
to skip the structural rule.

For a cell scope, the current implementation distinguishes a structurally
present cell effect, a `Missing` exact-removal result and an ambiguous open
tail. `Missing` is not by itself a proof of semantic absence for unresolved
parameterized instances; the [resource rules](first-slice-resource-rules.md#resolve-the-scopes-type-and-row-premises)
record the correspondence question. The
[resource trace](first-slice-resource-trace.md#r1--legacy-scope) records that
the specification's resource-scope wording does not explicitly settle all
three cases; the candidate rule must not assume ordinary handler admission
applies unchanged.

For cleanup, the action owner progresses from armed to running to finished.
Capture and resume preserve its phase and saved normal result; an admitted
close starts an armed action at most once and completes owned work in structural
order if execution succeeds. At each closing position, the account must
preserve lexical instantiation and the nearest applicable interpreter, including
action-local, retained and surviving contexts. A removed nearest source or
generated handler cannot be replaced by an outer same-instance handler. The
discard row accounts for action-local and still-enclosing retained builtin cell
interpretation; surviving source handlers discharge residual effects at their
own boundaries.

Operation payloads and results are checked against each resource owner they
cross; the owner's own trusted interpreter is an admitted recipient. Facts
about backing storage and external assumptions can cross the slice independently
of resource ownership. The slice preserves those facts without defining region
semantics or classifying internal capacity and work failures as external events.

Cell contents, read snapshots, captured segments and completion phases refer to
particular subjects and contexts. The type-system account must relate those
subjects without treating a fact about an earlier snapshot as a fact about a
later replacement, or treating a lexical resource identity as one runtime
activation. The design must state the relationship; the table does not claim
that an entire changing runtime state is a fixed certificate.

## What already exists and what is missing

Current Ash already has computation and value types, exact effect instances and
rows, type/row instantiation, handler result typing, cell/provider types and
structural one-shot checking. These are inputs to the candidate, not machinery
to reimplement. See [effect typing](../../../spec/static-semantics.md#effects),
[rows](../../../spec/static-semantics.md#computation-types-and-effect-rows)
and [generic cells](../../../spec/static-semantics.md#generic-cell-foundation).

Current callable summaries and control/resource analyses establish additional
relationships, including possible requests, stored dependencies, owned
captures, cleanup interpretation and completion. They are not yet a general
type-language contract exposing every fact needed for opaque composition.
The next design work must determine how those relationships are stated and
composed in types, propositions or other judgments within the type system,
and how much surface inference can establish. It must not assume absence of a
dependency or owner merely because the existing ordinary type does not name it.

Current Core carries types, rows and structural metadata, but current linked
validation can reconstruct control and resource relationships from assembled
Core. The certified-constituent rule above is the intended result of the
slice, not a claim that the present implementation already meets it.

## Conditions for a sufficient account

The rules must be strong enough that successful type checking establishes the
in-scope facts needed for the narrow correctness guarantee in
[DN-0060](../DN-0060-typed-data-and-control-roadmap.md#program-checking-and-correctness),
under the judgment's stated boundary premises. Matching existing checks or
finding no contradiction among the facts currently expressed is not sufficient
if an in-scope execution error remains possible. A whole-program guarantee
also requires the applicable rules outside this slice and its boundary
premises to hold. Separately established system-level proofs must justify this
consequence of the rules against the operational semantics.

The judgments and rules are not complete until they explain, using certified
premises and without rechecking verified constituents:

- Exact effect matching when polymorphic parameters can coincide, and row
  composition when an open tail's membership or absence is not established.
- Two values of the same ordinary type where one is independent of a closing
  resource and the other retains it; the same distinction through a callable
  or operation payload.
- An owned nested capture versus an outside or already running completion
  owner, including a resume-only case where unknown discard safety is irrelevant.
- Cleanup whose nearest required interpreter was removed, even when an outer
  handler has the same effect instance; and the correct residual effects after
  close.
- A cell snapshot before a later replacement and distinct activations of a
  repeated lexical acquisition, without relying on a particular payload type.

For each, identify what its premises establish, what the new composition must
check, which obligations remain conditional or cause rejection, and what the
specified successful transition preserves. These are requirements on the rules,
not a separate experiment project or proof that the current implementation is
correct. System-level soundness and correctness remain separate proofs of the
rules against their specified behavior and premises.
