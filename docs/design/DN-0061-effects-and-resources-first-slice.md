# DN-0061: Effects and Resources as the First Typed Slice

- ID: `DN-0061`
- Status: exploring
- Related: [DN-0059](DN-0059-compositional-contracts-and-evidence.md),
  [DN-0060](DN-0060-typed-data-and-control-roadmap.md),
  [CP-0031](../proposals/CP-0031-remove-legacy-integer-cell.md),
  [CP-0032](../proposals/CP-0032-row-indexed-handler-contexts.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md).

## Selection and question

The first slice of the method in
[DN-0060](DN-0060-typed-data-and-control-roadmap.md) covers the language rules
for effects, handlers, captured continuations and scoped resources. Its purpose
is to determine how their control and resource facts can be expressed and
composed in the type system.

What must a judgment express about a computation and its surrounding context
so that type-system rules can check effect handling, capture, resumption,
discard and resource completion by composing established facts?

The slice is a set of semantic rules and their interactions, not a single
program or compiler pass. It covers both permitted and rejected compositions.
This note selects the subject and boundaries. The
[current rule catalogue and implementation map](effects-resources/first-slice-catalogue-and-map.md)
records the starting rules, paths, shared analyses and gaps. The
[facts and obligations catalogue](effects-resources/first-slice-facts-and-obligations.md)
identifies the established and required relationships and their current
representations. Candidate replacement judgments and their remaining
before/after dispositions are developed in the linked records. The
[judgment and composition requirements](effects-resources/first-slice-judgment-requirements.md)
set out what those rules must express for this slice without selecting a
concrete type syntax or proof representation. The
[verification audit](effects-resources/first-slice-verification-audit.md)
traces current checks to candidate rule premises and records the work still
needed before replacing them with type checking. Its
[trace index](effects-resources/first-slice-verification-audit.md#trace-index)
links every rule family to its operational and implementation trace.
The candidate rules are developed in the
[effect and completion](effects-resources/first-slice-effect-completion-rules.md),
[resource](effects-resources/first-slice-resource-rules.md), and
[cleanup and owned-close](effects-resources/first-slice-close-rules.md) records.
The [sequencing cases](effects-resources/first-slice-sequencing-cases.md)
explain how an established initializer and remainder compose. These records
mark remaining premises and gaps; they do not claim the rules are complete.
The [rule resolution status](effects-resources/first-slice-rule-resolution.md)
connects every catalogue family to its candidate rules and remaining gaps.
The [failure admission rule](effects-resources/first-slice-failure-judgments.md#agreed-admission-rule-for-the-first-slice)
is agreed for this slice: a closed program must discharge its internal-failure
obligations to obtain the no-error conclusion. Other design and evidence
questions remain open.
This note does not define current semantics or authorize product implementation.

The immediate work is to identify the facts this slice can establish and the
rules its compositions must satisfy. The type system must be able to express
those facts and rules. Type checking establishes judgments by applying the rules
and checking their premises. An outstanding obligation leaves the dependent
judgment conditional until it is discharged; merely finding no explicit
conflicting declaration does not prove that obligation. System-level proofs,
established separately, justify what those rules guarantee about execution.

The work distinguishes three categories:

1. Language mechanisms such as resources, effects, types and interfaces,
   expressed or implemented through general type-system forms and rules.
2. Legacy constructs, machinery and checks whose disposition must be traced
   as the general rules take over, including existing verification that
   establishes or reconstructs facts.
3. Particular instances and implementations of the first category, with
   their declared contracts and behavior checked using those general rules.

An instance's implementation is not legacy merely because it is concrete.
An in-slice implementation is checked against its contract once, and its
users reuse the resulting facts. An excluded implementation instead supplies
an established boundary fact or an explicit assumption or obligation.
Correspondence between the language rules and their runtime implementation is
a separate system-level question. Legacy checks remain in place until their
particular consumers are covered; other slices may still use shared machinery.

Builtins are a special case in current Ash: they were introduced when the
language lacked capabilities needed to express particular behavior. For each
in-slice builtin, trace what the language, checker and runtime currently treat
specially and identify the missing general forms or rules. Record the needed
design and implementation work instead of assuming that builtin status or a
dedicated verification path must remain. Separately account for how the
behavior is implemented and how that implementation satisfies its contract;
expressing a contract does not itself execute the operation or prove runtime
correspondence.

Instances and their implementations are the source of the difficult design
questions. Analyze their intended operational behavior and the checks that
touch it to discover which facts must be declared, established, preserved and
composed. If the general type system cannot express or derive a required fact,
record that gap with the instance and operational rule that expose it; use
the evidence to design the needed general form or rule and justify its scope.
Then state how the instance's contract uses that form and how the affected
legacy check can be replaced. This is an analysis and design method, not a
separate experiment or an instance-specific verifier.

## Rules inside the slice

The slice includes the following rule families and their interactions:

- **Effects and rows:** effect and operation instances, operation requests,
  computation requirements, effect-row formation and composition, and the
  exact handling or forwarding of an instance. Include parameterized types
  and rows where the rules apply; preserve their identities and constraints
  through instantiation.
- **Handlers and captured control:** handler entry and normal return, nearest
  matching interpretation, movement of the captured context into the selected
  clause, and composition of the clause with surrounding control.
- **Continuation use:** the input and answer relationships of captured
  control; its owner and permitted use; one-shot consumption by `resume` or
  `discard` in ordinary clauses; restoration, abandonment and completion;
  and obligations owned inside or remaining outside the capture. Include
  nested captures and the effect requirements of closing where these rules
  interact.
- **Scoped resources:** acquisition, access, ownership, scoped completion and
  release, including resource dependencies carried by values and captured
  control. State common composition rules against the applicable resource
  contract, rather than assuming that all resources behave like a cell. The
  current audit includes both integer and generic cell scopes and scoped
  cleanup actions as concrete cases. Generic cells carry abstract payloads;
  cleanup can have effects and can itself require completion. Cover their
  permitted and rejected interactions with requests, resumption and discard.
- **Composition and preservation:** the premises and conclusions that let
  these rules combine judgments of their operands, bodies, clauses and
  contexts. State what each rule preserves, changes or discharges, and how its
  result and assumptions survive the source-to-Core path.

These are families to catalogue, not a claim that the existing specification
contains a complete or correct set of rules for every interaction. The audit
must identify their exact scope, premises, conclusions and operational steps,
including relevant rules currently stated only in prose.

A resource's declaration or established boundary contract determines its
own access, state, operation, ownership and completion facts. A common rule
may use a property only when that contract establishes it. In particular,
the generic cell's root, read/write operations, duplicable handle, sealed
provider, exact effect and retention constraints are facts of the cell case;
they are not definitions of resource ownership in general. Cleanup supplies
its own completion and action facts. The intended type-checking design uses
the same general rules for these declared contracts and their propositions;
it does not introduce an effect-, handler-, or resource-specific verification
rule merely because a declaration has its own operations. Cell read/write
semantics and the existing
runtime's preparation and failure behavior remain concrete facts to express in
the contract and justify against its implementation. Shared rules and
established contracts are composed without reopening their implementations.
Develop the generic judgments and their introduction, elimination and
composition rules first. When the audit finds a specialized verification,
map it to those judgments if they already express its requirement. If they
cannot yet express or discharge it, record the exact requirement and source in
the [rule ledger](effects-resources/first-slice-rule-resolution.md): a missing
general form or rule is a design gap, while a specified general rule awaiting
implementation is an implementation gap. An unresolved mapping is not evidence
that a specialized checker is necessary or that a general rule is sufficient.

Retained-control Stores and their private `retain` clauses, lexical regions,
registrations, native and network resources are outside this slice. Facts and
obligations from them may cross its boundary where relevant; such facts must be
established, explicitly assumed or recorded as open obligations. Their own
rules are left for later work. Implicit root allocation and its environmental
premises still apply to the complete path.

The current generic cell is evidence for the facts to recover, not a required
permanent resource foundation. The intended direction is a variable of type
`T` with **mutability as a property tracked by the type system**, alongside
the applicable location and usage properties. General type and proposition
rules and any applicable effect rules express its permitted operations;
mutability alone does not determine a particular state-effect protocol or
introduce another resource or owned object. Allocation, storage lifetime,
disposal and resource completion belong to the applicable resource contract,
such as a region or arena; the variable does not introduce a second cell-specific
owner or resource protocol. Its actual dependencies and access obligations
still need the appropriate general facts. The slice must reuse established
resource, control and completion evidence rather than reconstruct a
cell-specific equivalent.

Current Ash does not have a general form for expressing this mutability
property; the generic cell's builtin API supplies its present mutable behavior.
How the property attaches to a binding, value or access, the surface syntax
or inference that supplies it, its type and effect judgments, and composition
with resource facts are design gaps. Their resolution must not assume a
particular surface syntax, aliasing discipline or capability representation
without specifying and justifying it.

The current builtin instead gives each cell a separate scoped owner. That
separate-owner design is a **legacy candidate**, not already-removed current
semantics. The comparison must account for scope and access lifetime,
interception, retention, snapshots, capture, release, failure and all affected
consumers, and identify any semantic change and outstanding obligation. It
must not assume that the current region interface alone already provides
mutable reads, replacement or snapshot behavior, or that the two designs are
equivalent. Region and arena implementation remain outside this slice; only
their established boundary facts are used here.

## Opaque boundaries

Declarations establish typed boundaries throughout the language: functions,
modules, interfaces, effects, resources and other declared entities expose the
facts and requirements their users need while hiding their implementation
details. A function's users rely on its established type and associated
judgments; a module exposes its facts through its interface. Effect, resource
and interface declarations similarly supply contracts for their uses. Where a
declaration has an implementation, checking must establish that it satisfies
the applicable contract. A declaration of a requirement is not by itself a
proof that an implementation satisfies it.

These boundaries follow the same principle: establish each applicable judgment
once and apply composition rules to it without rechecking the implementation.
The type-system judgment must express the facts and requirements needed to
check permitted compositions, including relevant effects, control, resource and
completion facts.

These judgments may include inferred types, propositions or evidence; this note
does not select their representation or require every fact to be written by the
programmer. They need not expose implementation details that users do not need.
The same principle applies to both effects and resources: an operation's
declared type-level contract states its applicable behavior and obligations,
and the general request, handler, ownership and composition rules consume
those facts. An effect-specific or resource-specific verification rule is not
required merely because a particular declaration has different operations.
An effect row retains its existing role as a summary of effect requirements;
it does not by itself express every behavioral proposition. An operation
contract states what its interpreters must satisfy; a handler's own checked
contract can establish more specific facts. A caller may use those additional
facts only in a composition where the applicable handler is established; the
effect name alone does not select that handler or determine its replies.

### Proposed handler context

For the interface-based handler design, a handler's clause uses the effect
implementations available at that handler's installation. The binding is fixed
for that installation, rather than selected again when a clause is invoked or
a continuation is resumed. How the required context is supplied remains to
be derived. An implementation introduced inside a clause has its own nested
scope. The operation's continuation is supplied separately at each request,
with its applicable use, scope and completion contract. The interface and handler do
not capture that continuation: it is a function value supplied as an operation
argument. It carries the captured computation and its environment. Any
ordinary lexical dependencies of a handler implementation are separate from
that function and follow the same rules as other implementation dependencies.

This is a proposed semantic change, not a description of current Ash. Current
[request and resume rules](../../spec/dynamic-semantics.md#effect-handlers-and-completion)
select from the active control and restore the captured handler into the
resuming clause's context. Thus an enclosing effect implementation can differ
on a later invocation of the same handler. For example, if an outer `Ask`
returns `1`, and a handler's first clause installs an `Ask` returning `100`
around a resume, current Ash can give a subsequent clause `100`; fixing that
clause's outer `Ask` at the original installation instead gives it `1`.
The existing catalogue and audit trace the current behavior until the accepted
handler-context change is implemented.

The design should use the same closure, scope and interface-evidence rules as
other functions. The required effect context may be symbolic at compile time
and supplied by the actual installation; this does not require the compiler to
predict a concrete enclosing handler. Typed Core must retain the required
evidence and its scoped dependencies or obligations, and compositions reuse
their established contracts. The proposal does not yet settle all continuation,
resource-completion, effect-row or ordinary-function rules, or show that the
resulting account covers the slice.

The [local implementation review](effects-resources/first-slice-rule-resolution.md#local-implementations-handler-boundaries-and-continuations)
records the current scoped-evidence restrictions, candidate changes, and the
boundary and continuation gaps against the effect rule catalogue.
The [effect-to-interface account](effects-resources/first-slice-rule-resolution.md#effect-to-interface-elaboration-and-function-properties)
derives a tested example and records the proposed general rules for function
use, escape, lifetime and completion.
The [effect-interface elaboration proposal](effects-resources/effect-interface-elaboration-proposal.md)
and [CP-0032](../proposals/CP-0032-row-indexed-handler-contexts.md) are accepted
as one effects package. Implementation is pending. This acceptance covers the
effects elaboration and its stated type-system dependencies; resource and
cleanup design beyond its stated bridge remains exploratory.

An effect declaration must be able to state interface requirements on its
parameters. For example, the proposed `Failure<E>` effect can require
`Error<E>`; a particular `Failure<CloseProblem>` instance then needs the
applicable `Error<CloseProblem>` evidence. A generic use carries the same
requirement or established evidence at its boundary. This is a general
declaration facility, not a failure-specific checker. Typed Core must retain
the instantiated requirement and its applicable evidence or scoped obligation;
later compositions reuse that evidence rather than checking its implementation
again. The required source and Core forms, evidence scope and correspondence
are design work. Current Ash effect declarations do not express this bound,
and the example does not select syntax or establish a bottom type.
Resource contracts can need the same general parameter requirements; the
common rules must support them without introducing a separate resource-bound
checker. A resource's prerequisite evidence is distinct from evidence its
successful acquisition introduces for the body. Current Ash does not have a
general source resource-declaration facility; the [resource review](effects-resources/first-slice-resource-rules.md#resource-parameters-and-interface-requirements)
records the current scope and the remaining gap.

Where current Ash cannot declare, infer or carry a required contract or prove
that an implementation satisfies it, record that missing capability and the
fact it must express. Resolving it may require a new general proposition,
law, type form or checking rule. Its need comes from the contract and
composition being checked, not from the name of one particular effect or
resource. Any proposed form and its semantics require the normal change
proposal before implementation.
When a composition requires a fact not established at the boundary, the need
remains an explicit obligation; it cannot be inferred from an unexamined body
or silently treated as proved. Dependent conclusions retain any explicit
assumptions.

The surface and Core have different responsibilities. Surface declarations
may leave types and other required information to inference, and the language
may later increase what can be inferred. Typed Core must carry the complete
types resulting from checking and inference, including the type-system facts
needed by this slice. Source annotations are not required merely to make those
types explicit in Core. Carrying a type or an established judgment across a
boundary must not re-establish it. The current Core's existing types and rows
do not yet express every control and resource fact targeted here.

The design target is that checking typed Core needs no inference to recover
that information: the Core interface explicitly supplies its types, relevant
control and resource facts, assumptions, evidence and outstanding obligations.
Surface elaboration may infer them. Core checking still checks the new
composition's rules, including scoped substitution, equality and applicable
evidence; explicit information is not automatically true. It reuses certified
constituents instead of inferring or checking their facts again. A representation
may attach information or refer to established scoped evidence; this target
does not choose a certificate format or require copying proofs into each use.
The representation and rules must make those new checks tractable; making an
input explicit alone does not establish that evidence or equality checking is
simple.

Explicit Core information can be symbolic. A caller's future handler, an
activation created at runtime or an enclosing resource need not be known at
compile time: a complete interface can bind or parameterize over them and
state the applicable relationships. The runtime still selects its actual
handler and activation. Open obligations remain explicitly scoped and make
dependent conclusions conditional; they are not unresolved inference variables
presented as established facts. A closed no-error conclusion must discharge its
applicable obligations under the permitted assumptions. How to express and
check these interfaces without repeating work remains design and correspondence
work, including reconciliation with AD-0007's independent validation.

Questions about surface inference are also a way to discover Core gaps. For
each fact inference would supply, first identify the Core form or established
interface that states it, its scope and its consumers. If Core cannot express
or carry that fact, record the representation and rule gap before choosing
how to infer it. Surface convenience must not depend on silently reconstructing
missing information from a certified Core fragment. This does not require the
source program to spell out the fact or select an inference algorithm.

Successful Core type checking must establish a certification of the checked
Core program or fragment and its stated premises. Later consumers reuse that
result without running verification over that verified program or fragment
again. A composition is a new fragment: check the composition using the
certifications of its previously verified constituent fragments, without
verifying those constituents again. This requirement does not select a
certificate format or a registry implementation.

Ordinary data-type rules and general function definition and application
typing are outside the slice. A value, computation, function or context from
outside it is opaque: the fragment consumes its established judgment and
preserves or transforms its facts only as the applicable composition rule
specifies. It does not inspect the outside implementation to re-establish
them. Missing facts remain explicit obligations; an assumption is not a proof,
and a conclusion depending on it remains conditional.

Treat values and computations polymorphically wherever their structure is not
needed by an in-scope rule. A type parameter does not imply that a particular
value has no resource dependencies. A value's established dependencies and
other relevant facts must remain available even when its concrete type or
implementation is opaque. The fragment must not reconstruct the value merely
to recover them.

Function calls can occur at this boundary. Their effect rows describe effect
requirements, but a row alone is not yet shown to express all relevant
control, resource or completion facts. The catalogue must identify what the
fragment needs from an already checked call and what happens when that
information is unavailable. A caller composes the callee's established
judgment with its own context; it does not check the function body again.

The generic-cell API's `read` and `write` methods are themselves function
applications using sealed provider evidence. Their established contracts,
identities and evidence cross the boundary; the slice must account for their
resource and effect behavior without bringing general function-application
typing into scope. Captured control can also contain outside frames, including
call frames. The slice must preserve and compose their supplied facts and
obligations, not assume the frames have no effect on safety.

The present design concerns these language rules and typed boundaries.
Linking, whole-program optimization and other phases may later have explicit
rules for opening modules, but their designs are not needed to define this
boundary. The eventual delivery must still cover the source-to-typed-Core path
and reconcile the current Core-validation decision; those implementation and
assurance questions do not change the opacity of module users here.

The slice does not select a concrete proposition language, source annotation,
proof representation, registry implementation or runtime control encoding.
Propositions, laws or new forms are introduced only if the catalogue and
design show what they must express. Delimited-control accounts, including
shift/reset and CPS, are comparisons for the logical rules; they do not by
themselves define Ash behavior.

## Current starting points

The [effect rules](../../spec/static-semantics.md#effects) specify exact
requests and handlers, structural one-shot completion and checked discard.
The [generic-cell rules](../../spec/static-semantics.md#generic-cell-foundation)
specify a fixed payload type for each acquisition, stored dependencies,
snapshots and scope completion. They distinguish the cell's current contents
from earlier read snapshots and require retained resource owners to strictly
enclose the target activation. Capture and resumption must preserve the actual
activation and its ownership relationships. The
[cleanup rules](../../spec/static-semantics.md#scoped-cleanup-actions) specify
the action's effects and the required completion of a running action or close.
The
[dynamic handler rules](../../spec/dynamic-semantics.md#effect-handlers-and-completion)
and [cell execution rules](../../spec/dynamic-semantics.md#scoped-cell-execution)
describe capture, restoration and closing. The specification states intended
current behavior; the audit must check its completeness and correspondence
with the implementation.

[Effect Core lowering](../../spec/elaboration.md#effect-core-lowering) retains
effect and resource operations, their types and rows. The linked
[validation boundary](../../spec/elaboration.md#validation-boundary) checks
control, resource dependencies and completion. Elaboration and validation call
the shared capture analysis with different inputs; this is a starting point
for the before/after map, not evidence that every check at both sites is the
same work. Imported module facts already retain some established results and
must be reused where their premises hold.

## Remove the legacy integer cell

As part of this slice, remove the separate legacy integer-cell facility and
use generic cells instantiated at `Int` for its uses. Migrate affected programs,
tests, fixtures and documentation to the generic API. Apply the generic
resource and control judgments rather than maintaining a second verification
path for integer cells. [CP-0031](../proposals/CP-0031-remove-legacy-integer-cell.md)
records the proposed semantic transition and required evidence. Until the
complete change is retained, the current specification and the before map
continue to describe both facilities.

That proposal uses the currently available generic cell for this migration;
it does not establish its separate owner as the intended final resource or
storage model. The comparison above must determine how its behavior can be
expressed by a mutable variable and general resource, state and effect
contracts, what changes observably, and whether that later change requires a
separate semantic proposal. CP-0031 remains proposed; this direction does not
implement or silently amend it.

## Required development and completion

Apply the repeatable cycle in DN-0060 to these rules. Catalogue every existing
rule, check and analysis that touches the slice, its inputs, outputs, producer
and all consumers. Trace the applicable source, module, elaboration, linked
Core and execution paths. For each consumer, record whether the established
judgment is reused, a legacy check is replaced, redundant work is removed or
shared analysis remains necessary outside the slice.

For every in-scope obligation, the resulting type-system rules and evidence
must establish the fact or compose it from established premises. Together with
established facts or explicitly stated assumptions at its boundaries, these
rules must be sufficient to rule out the slice's contribution to execution
errors under DN-0060's narrow correctness guarantee. A checked slice judgment
alone does not assert correctness of the enclosing program: its assumptions and
the other applicable program rules must also be satisfied. A boundary
fact must identify its subject, premises, source and consumer; an outstanding
obligation must remain visible until established or explicitly assumed under
the applicable trust policy. Do not repeat inference, proof discovery or proof
checking for an established fact. Check new composition obligations using the
established facts of the constituents. An index of proofs and obligations may
be used if needed, with the reason for every entry and its consumers.

The initial effects-to-interfaces delivery has one accepted verification gap:
ordinary function typing cannot yet fully check one-shot use of generated
continuations. General usage properties remain future work. A Core certificate
from that delivery must not claim this missing fact or an unconditional
correctness guarantee that depends on it. This is an exception for that
delivery, not a change to the slice's eventual verification goal or the current
language's structural checks. The [effects proposal](effects-resources/effect-interface-elaboration-proposal.md#current-behavior-and-intended-change)
records the scope of the gap.

The result must cover the real source-to-typed-Core path and replace mandatory
in-scope reconstruction for its consumers. Shared verification remains for
other consumers until they have a valid disposition. Reconcile this no-repeat
requirement with [AD-0007](../decisions/AD-0007-typed-core-dialects.md)'s
independent Core validation before claiming completion; neither requirement is
silently waived.

Check the operational failure paths against the intended guarantee in
DN-0060: an accepted program can run without raising an error under stated
environmental assumptions, barring external events. Identify internalized
external events and Ash's response separately from failures that the rules
must make unreachable. Propose changes to failure semantics where needed.
System-level soundness and correctness proofs justify the rules against the
specified behavior; they are separate from per-program type checking.

Multi-shot and broader discardable continuations are future requirements.
They must challenge the chosen judgments without being treated as implemented
or assigning them semantics in this slice. In particular, permission to resume,
discard or duplicate control, and ownership of its resources, are distinct
questions.
