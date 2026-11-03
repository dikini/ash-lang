# DN-0060: A Roadmap Concept for Typed Data and Control

- ID: `DN-0060`
- Status: exploring
- Related: [DN-0059](DN-0059-compositional-contracts-and-evidence.md),
  [DN-0001](DN-0001-reboot-foundations.md),
  [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md),
  [DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md),
  [DN-0034](DN-0034-one-shot-kernel-soundness-and-practicality.md),
  [DN-0055](DN-0055-algebra-of-regions-lifetimes-and-ownership.md),
  [DN-0056](DN-0056-scoped-continuation-retention-and-library-scheduling.md).

> This note sets out the proposed method and implementation requirements for
> the direction in DN-0059 and DN-0060. Once the method has converged, an
> architectural decision should record its non-language requirements. The
> type-system design remains open; individual fragment selections are recorded
> separately. This note does not itself define current language semantics or
> authorize product implementation.

## Question

How can Ash express and check the relationships among types, data, control,
effects and resources in one compositional static system, so that later
components can use established results without reconstructing the programs
that established them?

[DN-0059](DN-0059-compositional-contracts-and-evidence.md) states this
direction in terms of contracts and evidence. This note sets the method for
the work: map the intended semantics and current implementation,
select and deliver a sequence of connected language fragments, and extend the
type and logic rules while replacing existing analysis as its consumers are
covered. The method determines the fragments and their order; this note does not
select them. [DN-0061](DN-0061-effects-and-resources-first-slice.md) records the
first selection separately. The method's implementation requirements apply to
work on both notes and must be carried into the relevant proposals, decisions
and tasks.

The method here differs from DN-0059's E1/E2-first investigation sequence.
Its examples remain important evidence and challenges for this roadmap. This
note does not supersede DN-0059 or change the authority of either artifact.

## Direction

The goal is to move most, if possible all, verification of types, kinds,
modules, control, effects, continuations and resources into an expanded type
system. Types, kinds, effects, constraints, propositions and evidence should
work together to describe and justify the behavior that a component requires
or provides. Every verification obligation inside a selected fragment must
be established by that system. Existing analyses may infer judgments or
evidence where useful, without repeating work already performed. Mandatory
behavioral reconstruction can be retired where established facts and their
composition suffice.

The working hypothesis is that program constructs and control composition can
be understood through logical rules, including introduction and elimination
where a suitable connective and interpretation exist. A typing derivation
then establishes a program judgment; propositions and proofs can establish
additional laws about its behavior. The connection must be demonstrated for
Ash's actual operations. A construct is not an introduction or elimination
form merely because it resembles one in another calculus.

This direction does not require all properties to be encoded in an effect
row, all evidence to be written by programmers, or a particular proof theory
to be selected now. Nor does it make every executable Ash expression a proof
of an arbitrary proposition. The design must specify the logical fragment,
its treatment of recursion and effects, and the interpretation that makes its
claims sound.

## Program checking and correctness

The target is that an accepted program can run without raising an error, under
the stated assumptions about its environment and barring external events that
violate those assumptions. This narrow guarantee does not say that the program
terminates or computes the result its author intended. An expected failure
represented explicitly as a typed result or value is an outcome of the program;
it is distinct from raising an execution error. The semantics must also state
whether and when a source-level error effect counts as raising an error. The
exact observations and assumptions belong in the relevant semantics and
correctness claims.

Compilation and type checking establish that a particular program satisfies
the applicable rules under their premises. Those rules and premises must be
sufficient for that successful check to establish the narrow correctness
guarantee for the program, not merely the absence of contradictions the
current checker happens to detect. Separately established system-level
soundness and correctness proofs justify this consequence of satisfying the
rules against the relevant specification. These are proofs of the system,
not proofs the compiler repeats for every program. The assurance also needs a
justified connection between the specified rules and the implementation;
tests provide evidence about that connection but do not prove it universally.

Current Ash is not yet claimed to meet this target. The
[dynamic semantics](../../spec/dynamic-semantics.md#observation) report both
malformed control and capacity exhaustion as internal runtime failures. Some
failures can reflect external limits or events encountered by the runtime. For
each such case, distinguish the external event or assumption from Ash's
specified response, including cleanup and reporting. An internal failure is
not automatically an external event: invalid control, for example, must be
ruled out under the stated premises or treated as a gap in the rules, their
implementation or their correspondence. Audit the current failure semantics
against the target and revise them through a semantic proposal where needed.

## Current foundation

The [specification](../../spec/README.md) states intended current Ash. Its
[static semantics](../../spec/static-semantics.md) define types, kinds,
interfaces, effect rows and admission rules. Its
[dynamic semantics](../../spec/dynamic-semantics.md) define execution,
including handler selection, captured control, restoration and closing.
Authority is not evidence that the specification is complete or that every
implementation conforms to it. The map below must check both questions.

Ash already composes checked information. Imported schemes and selected
interface evidence cross module boundaries; linking retains defining checks
and checks the new connections without selecting the same evidence again.
Private control summaries also permit imports without dependency source
bodies. See [module linking](../../spec/elaboration.md#module-linking-and-entry-generation)
and [control summaries](../../spec/elaboration.md#effect-core-lowering).

Other obligations still require reconstruction. Linked Core validation
derives capture, resource, cleanup and completion requirements from the
assembled program. The elaborator and validator use a shared capture-analysis
engine with different inputs and responsibilities. This identifies a
replacement opportunity, not proof that all work at those stages is identical
or unnecessary. See [Core validation](../../spec/elaboration.md#validation-boundary).
The current [elaboration call](../../src/elaborate.rs) and
[validator call](../../src/core/validate.rs) supply starting points for tracing
the shared [capture engine](../../src/core/capture.rs).
[AD-0007](../decisions/AD-0007-typed-core-dialects.md) currently requires an
independent validation boundary; a later replacement must preserve its
assurance and follow the decision process.

Current effect rows describe unordered sets of exact effect-instance
requirements. They do not alone describe the captured continuation, its
permitted use or its closing obligations. Ash currently checks one-shot
continuation consumption, including checked `discard`. Source propositions
and proofs are not implemented. See [effect rows](../../spec/static-semantics.md#computation-types-and-effect-rows),
[effect rules](../../spec/static-semantics.md#effects) and the
[trajectory](../trajectory.md).

## Properties of a fragment

Select each fragment from current Ash semantics and justify it against the
coverage and dependency map. A fragment is a bounded part of the language and
its intended behavior, not a compiler pass, a new dialect or a disposable
implementation. This note does not prescribe a particular first, second or
later fragment.

Every selected fragment must have:

- **A coherent semantic scope.** Name its source constructs, interactions,
  intended operational steps, observations and exclusions. Select a complete
  interaction rather than an isolated rule or implementation helper.
- **Useful coverage.** Be small enough to specify, prove and deliver, while
  exercising multiple related obligations. The first selection must be rich
  enough to establish a meaningful connection among types, data and control.
  Later selections must state which uncovered relationships they add.
- **A complete path.** Identify the real source entry, checking and
  elaboration, the typed Core result and its consuming validation path, and
  the intended execution behavior. Include module composition or other
  boundaries when the selected interaction crosses them.
- **A defined proof boundary.** List facts established inside the fragment,
  facts supplied from previously covered work or elsewhere, outstanding
  obligations, and their subjects, premises and consumers.
- **A replacement target.** Identify the existing analyses and verification
  that establish its facts, their other consumers, and what in-scope work the
  new judgments and evidence must replace.
- **A relationship to later work.** Identify unresolved dependencies,
  interactions and future control requirements that challenge the fragment,
  without assigning semantics to features outside its scope.

Each fragment's delivery must be complete from source through typed Core. For
every in-scope construct and interaction, account for name and kind formation,
typing, effect and control admission, elaboration, linking and typed Core
validation as they apply. The new derivations and evidence must establish every
in-scope verification obligation, including obligations discovered during the
audit, using already established facts where applicable. All such obligations
must be established by the type system, including its judgments, propositions
and evidence. Establish each new fact once for its subject and premises, then
carry and compose the result; do not repeat inference, proof discovery or
proof checking for the unchanged fact. The path must not retain mandatory
reconstruction of those facts as a fallback. Existing analysis may remain as
an inference or diagnostic tool where it is no longer required to establish
those facts again.

The design target is an inference-free typed Core interface: surface checking
and elaboration may infer information, but the resulting Core makes the types,
instantiations, applicable behavioral facts, evidence, assumptions and open
obligations explicit. A Core checker checks the new composition using those
interfaces and established constituent certifications. Symbolic parameters and
runtime witnesses remain explicitly scoped; they are not guesses at future
runtime values. An outstanding obligation remains conditional, and an unsolved
inference variable cannot stand in for a completed Core annotation. This target
does not itself change current Core validation or select an evidence format.

Every rewrite, including elaboration to Core, must preserve enough source
provenance to report meaningful errors against the original program. Diagnostics
must identify the relevant source construct and, where useful, the declaration
or contract that supplies the conflicting requirement. Generated names and
forms must not obscure the actionable source cause. Preserve provenance across
successive rewrites and checked boundaries; use established interfaces and
their recorded origins instead of reopening or rechecking opaque bodies to
explain a composition error. Each fragment must verify this requirement for
its rewrites, including errors detected after elaboration.

Do not remove a shared analyzer while other fragments still use it. An isolated
rule, helper or passing component test is not fragment completion: the actual
source-to-Core consumer must use the established results. Execution checks then
compare the accepted Core's behavior with the intended operational semantics.

### Boundary of the fragment

Each fragment must name facts established outside it, such as imported
declaration identities, effect signatures or resource-operation contracts.
For each one, record its subject, statement, source of evidence, premises and
consumer. The fragment may rely on an accepted, already established fact under
the applicable trust policy, or record a fact as an outstanding obligation to
be established. It must not silently assume an unproved obligation is proven.
An explicitly accepted axiom remains an assumption in dependent results.

Open derivations may be checked under recorded obligations. For an admitted
program, an obligation must be discharged by established evidence or remain
an explicit assumption under the applicable trust policy. An assumption is
not a proof: any guarantee depending on it remains conditional. The boundary
must identify which case applies, how the fact remains valid through linking
and specialization, and what invalidates it. This supports separate checking
without requiring the fragment to prove the entire language first.

## Delimited control as a logical account

Shift/reset and related delimited-control calculi are important comparisons
for this work. They make the delimiter, captured evaluation context and
composition with the surrounding computation explicit. CPS can express the
same kind of control and remains useful for reasoning and comparison. Neither
choice requires Ash to expose new source syntax or use a particular runtime
representation.

When a fragment includes captured control, describe the relevant delimiter and
captured frames as a context with a hole. Relate the account to its in-scope
Ash transitions, such as request selection, capture, clause execution,
resumption and discard. Determine which input and answer types, effect and
interpreter requirements, resource support, allowed uses and completion
obligations its context judgment needs. Determine which of these are type
constituents, constraints or propositions through the rules, not by assuming
every one belongs in the existing row.

Compare `shift`/`reset`, `shift0`/`reset0` and related accounts where their
different delimiter and reinstatement behavior matters. A translation or
analogy does not establish equivalence: Ash selects the nearest handler for an
exact instance, runs its clause outside that handler and reinstalls captured
control on resume. `discard` consumes and closes owned control; its cleanup
may have effects. [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md#sequencing-is-already-ambient-in-ash)
already relates Ash sequencing to delimited continuations and states what a
CPS equation leaves open.

For each construct, ask what judgment it introduces, consumes or transforms;
how that rule composes with its surrounding context; and which operational
transition justifies it. Function introduction and application provide a
starting point. The logical account of operation requests, handler entry,
resumption and closing remains to be derived. In particular, effectful
discard is not automatically unrestricted logical weakening.

Each derivation should connect the responsibilities in its selected path.
For a fragment involving a call and captured control, for example, compose a
checked callee judgment with the caller's context and account for the permitted
use and completion of that context. Reuse the same callee judgment at another
call site without deriving its body again. The exact rules depend on the
selected fragment; this is a design requirement, not an Ash typing rule.

## Map the semantics and the implementation

The map has two connected views. It is an evidence index for the roadmap, not
a second normative specification.

**Semantic slices** follow a complete interaction, rather than a compiler file
or a single syntax form. For each slice record:

1. The intended operational steps, observations and stated scope.
2. The static premises and guarantees that make those steps admissible.
3. The corresponding source checking, elaboration, Core and evaluator paths.
4. Existing positive, negative and interaction evidence, including transformed
   or malformed Core where relevant.
5. The proposed typed or propositional judgment, its composition rules and
   the argument connecting it to the intended steps.

Keep a plain-language explanation alongside the derivation. Use concrete
examples where they clarify how a rule introduces, discharges or preserves
facts, and how a new context reuses an established judgment. Where useful,
contrast an accepted and a rejected composition. Identify assumptions and
label candidate rules and unverified examples so the explanation can also
support future documentation without becoming a second source of semantics.

Include specification prose and implicit premises, not just displayed rules.
Record missing specification, unexamined correspondence, an observed conflict
and bounded supporting evidence separately. Tests can expose discrepancies and
support particular cases; they do not prove general correspondence. Where the
specification and implementation disagree, investigate whether the intended
rule is incomplete or incorrect, or the implementation fails it. Do not
promote the implementation or a test accident into semantic authority.

**Shared analyses and facts** are indexed independently of slices. Record
each analysis once, the fact it establishes, its premises and subject, all
producers and consumers, and the boundaries at which the fact is reused,
reconstructed or becomes invalid. Link each slice to the relevant entries.
For every proposed replacement, record before and after for each consumer.
Keep a shared check until all its consumers have a valid replacement or an
explicit reason to retain it. This prevents one slice from removing work that
another still needs.

For every verification rule or check that touches a slice, the before record
must identify:

- The specified rule or implementation-only check, its location, triggering
  subject and boundary.
- Its inputs and premises, including outside evidence and assumptions, and its
  outputs: established judgments or facts, retained data and diagnostics.
- Its producer and every consumer, including consumers outside the slice.
- The operational behavior it supports, the evidence of correspondence, and
  any missing rule, ambiguity or observed conflict.
- Whether the work reuses an established result, reconstructs it, or checks a
  new composition obligation.

The after record identifies the applicable type-system rule and evidence,
how the result reaches each consumer, and the disposition of the old check:
reuse, replacement, removal as redundant, or retention for another consumer.
For every remaining legacy consumer, record the reason and condition for later
retirement. Link shared analyses to one record rather than maintaining
independent copies in each slice.

For example, the capture engine contributes to resource dependencies and
cleanup as well as discard admission. Mapping only the discard path would not
justify retiring that shared analysis. Separately identify repeated discovery,
checking supplied evidence and checks for genuinely new composition or a
changed subject; their costs and assurance roles differ.

## Propositions, evidence and reuse

Develop propositions and laws alongside the fragments, using the same
account of subjects, scope and evidence as the type judgments. A proposition
states a relationship; a law applies it to identified entities; a proof
establishes it under its premises. An explicit assumption can be useful before
an internal proof exists, but must remain visible in dependent conclusions.
Tests may challenge a law; passing tests do not prove it. See
[DN-0001](DN-0001-reboot-foundations.md#14-propositions-laws-and-proofs) and
[DN-0059](DN-0059-compositional-contracts-and-evidence.md#propositions-laws-and-their-justification).

For example, a declared associativity assumption for an identified operation,
domain and equality could support a checked four-operand reassociation. The
conclusion remains conditional until the premise is proved. This example does
not select a fragment or claim that arbitrary effectful operations are
associative, or that their behavior is determined by an unordered effect row.

For a checked result, record what it establishes, its subject and premises,
and which checking or semantic basis gives it meaning. A consumer should
instantiate and compose that result rather than rediscover its derivation.
The design must distinguish this reuse from checking a supplied proof at an
actual trust boundary, and from compilation or cache reuse. A representation
or compiler-stage boundary alone is not a reason to check the same proof
again. Successful Core type checking certifies the checked program or fragment;
later consumers must not run verification over that verified subject again. A
composition is a new fragment: check its composition rules using the established
certifications of its constituent fragments, without verifying those constituents
again. A component need not expose its implementation to clients that use its
established public contract.

For each fragment, the map must count where each fact is discovered,
checked and consumed from source through typed Core. Where a genuine trust
boundary appears to require repeated checking, record the conflict and its
reason, and resolve it before claiming completion. Do not presume an exception
or permission to reconstruct the producer. The design must reconcile no
repeated work with the independent validation guarantee in AD-0007. Checking
identities or composing a genuinely new obligation is distinct from proving
the same fact again. The fragment is not complete if verification has merely
moved into a repeated evidence-generation or checking step.

### Indexing proofs and obligations

If needed to retain and reuse these results, maintain a registry or database
of proofs and obligations and index the relevant code with them. It must allow
the checker to find an existing result and its dependencies rather than repeat
the work that established it. Determine the required operations and lifetime
before choosing an in-memory index, attached Core records, persistent storage
or a combination. If used, later fragments must reuse and extend the index
where its contracts apply rather than reconstruct its entries.

Each entry needs an identifiable subject and statement, its premises and
dependencies, its scope and checking basis, and its status: outstanding,
explicitly assumed or established by checked evidence. It must also say why
it is in the registry: which declaration, typing rule or other obligation
introduced it, what requirement or guarantee it supports, and which code or
other facts consume it. Record all reasons when a result serves more than one
consumer, so its continuing purpose remains inspectable. Tests and attestations
may be recorded with their own meanings.

The code index associates source constructs and their lowered Core subjects
with the relevant entries, including where linking, specialization or
transformation changes that association. It must distinguish reusing an
established result from finding an unresolved obligation or an assumption,
and show why each association is needed.

Record which changes preserve an association and which require its evidence
to be reassessed. A registry entry is not itself proof: evidence must have an
accepted origin and remain valid for its actual subject and premises. The
registry must not authorize a use merely because a claim is indexed under a
matching name. Its creation, lookup and maintenance are part of the complete
path's work and must not conceal repeated analysis.

The rules must also state which assumptions may authorize an operational
permission or an optimization. An unproved assertion must not silently become
an unconditional safety guarantee. Dynamic facts and external behavior may
still require runtime checks or explicit premises.

## Repeatable path forward

This is the proposed delivery method for implementing the direction in
DN-0059 and DN-0060. It develops and delivers successive connected fragments;
it does not select an implementation schedule or authorize product work, and
does not call for disposable prototypes or separate experiment projects.

Begin with a coverage and dependency index of current semantic constructs,
judgments, transitions, analyses and their consumers. This index can begin at
coarse granularity and be refined as fragments are selected; a complete audit
of the language is not a prerequisite for choosing the first fragment. Include
known interactions and open correspondence questions so a narrow selection does
not erase its dependencies on the rest of Ash.

Repeat the following cycle for each fragment:

1. **Select and bound.** Use the coverage and dependency index to identify a
   connected interaction that satisfies the fragment properties. State why it
   is the next useful selection, what it adds, its exclusions, entry and exit
   boundaries, and which established results or open obligations it needs. The
   first fragment must connect types, data and control. Each later fragment
   builds on established results and addresses uncovered obligations or their
   consumers.
2. **Analyze data and control.** Describe the selected data, computations,
   control contexts and their interactions, including the effects, resources,
   observations and completion obligations that fall within the boundary.
   Trace their intended operational steps and identify how they compose with
   facts and obligations from outside the fragment.
3. **Catalogue the existing verification.** Identify every rule, check and
   analysis that touches the fragment, including its inputs, premises, outputs,
   producers and consumers. Follow the actual source-to-Core and execution
   paths. Record shared consumers outside the fragment and distinguish reuse,
   repeated establishment and genuinely new obligations.
4. **Check the operational semantics and correspondence.** Compare the
   intended steps with the existing static rules and their implementation.
   Record evidence, missing or ambiguous specification, implementation
   disagreements and uncovered obligations. Trace failure paths against the
   target guarantee: identify what the rules must rule out, external events
   and assumptions, and Ash's required response. Where the failure semantics
   need to change, propose the change. Resolve a semantic gap through the
   appropriate design or proposal before making a local implementation choice.
5. **Determine the necessary forms.** Establish what existing types, kinds,
   constraints, effects and evidence can already express. Identify and justify
   any missing forms or judgments, such as delimited-control forms,
   propositions or laws. Compare alternatives against the intended semantics;
   a logical or mathematical form does not by itself require new source syntax.
6. **Define the type-system rules and replacement.** Add or rephrase the
   required judgments and their introduction, elimination and composition
   rules so that type checking establishes every in-scope obligation. Connect
   each rule to the operational behavior it justifies. Name boundary facts as
   established evidence, explicit assumptions or outstanding obligations.
   Reuse results from earlier fragments where their premises hold. Record the
   before/after disposition of each old check and every consumer: reuse an
   existing type judgment, replace a legacy check, remove redundant work, or
   retain shared analysis for consumers outside the fragment. State the
   conditions for retiring any retained analysis.
7. **Implement the forms and all rules.** After the applicable proposal,
   decision and task process authorizes product work, implement any necessary
   new forms and every in-scope rule through actual source checking,
   elaboration, linking where applicable and typed Core validation. Carry and
   compose the evidence on that path. Replace the corresponding legacy
   verification for covered consumers; retain shared machinery while other
   consumers require it. Form and rule implementation may proceed together
   where they depend on one another.
8. **Verify the result.** Establish the applicable system-level soundness and
   correctness claims against the intended operational semantics, including
   preservation through elaboration to typed Core, under recorded premises.
   State what is proved separately from compilation and what implementation
   correspondence checks support. Check valid and invalid cases, stale or
   forged evidence where relevant, and execution. Demonstrate replacement of
   in-scope mandatory reconstruction and no repeated work for unchanged facts;
   account for evidence production, transport and consumption across the path.
   Independent validation remains as required by its governing decision unless
   that decision changes. A helper, model or isolated check is not completion.
9. **Update and select again.** Record the retained result, each shared
   analysis's remaining consumers, discharged and outstanding obligations,
   interactions, and any new semantic gaps. Use that record to select the
   next fragment and repeat the cycle. Reconsider an earlier result if new
   evidence disproves it or its premises do not hold; do not re-establish an
   unchanged result merely because the scope has grown.

The first cycle establishes a usable base. The second and third compose that
base with new relationships and replace the corresponding additional checks;
the same method applies to later cycles. Their contents and order follow from
the map, dependencies and useful coverage, not a sequence selected in this
note. A coverage goal is complete only when its required consumers and boundary
obligations are addressed; record any remainder rather than counting isolated
proofs or partial replacements as completion.

At each cycle distinguish intended semantics, a formal property of a stated
model, and correspondence with the implementation. The existing
[one-shot formalization](direct-effects/one-shot/README.md) supplies bounded
evidence under its premises; it does not establish general Core
correspondence. A sound abstract account is not enough if it describes different
handler selection, cleanup or observable execution.

## Future control requirements

Multi-shot and broader discardable continuations are intended directions, not
current general Ash facilities. They must pressure fragment selection and
judgment design from the start without assigning them semantics prematurely.
Distinguish repetition, abandonment, escape, suspension and concurrent use. Repeating a
continuation does not automatically duplicate its resources or close authority;
shared state and independent branches can have different observations.

The roadmap must later define which segment is repeated, what is shared or
fresh, which owner closes each branch, how effectful cleanup runs and what
failures leave available. Current checked `discard` is evidence about a
specific owned-closing operation, not a complete design for those future
facilities. [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md#continuation-extensions-and-sequencing-laws)
records these independent dimensions.

## Research references

The following results inform the design; none establishes Ash semantics or
implementation correctness:

- Kiselyov and Shan, [A Substructural Type System for Delimited Continuations](https://okmij.org/ftp/continuations/delim-control-logic.pdf):
  types for expressions and evaluation contexts related to small-step control.
- Tov and Pucella, [A Theory of Substructural Types and Control](https://users.cs.northwestern.edu/~jesse/pubs/substructural-control/):
  control effects and substructural use, including shift/reset.
- Piróg, Polesiuk and Sieczkowski,
  [Typed Equivalence of Effect Handlers and Delimited Control](https://maciejpirog.github.io/papers/typed-equivalence-fscd2019.pdf):
  typed relationships for particular deep and shallow handler calculi.
- Zyuzin and Nanevski, [Contextual Modal Types for Algebraic Effects and Handlers](https://arxiv.org/abs/2103.02976):
  effects as contextual modal types with logical introduction and elimination.
- Tang and Lindley, [Rows and Capabilities as Modal Effects](https://www.research.ed.ac.uk/en/publications/rows-and-capabilities-as-modal-effects/):
  a 2026 comparison framework for particular row and capability systems.
- Tang and others, [Soundly Handling Linearity](https://arxiv.org/abs/2307.09383):
  control-flow linearity, captured resources and qualified-type inference.
- Mathiasen, Timany and Birkedal, [Yarrow](https://arxiv.org/abs/2607.15876):
  a 2026 preprint on a mechanized program logic for regions and one-shot and
  multi-shot handlers; its type system is future work.

## Open questions

1. Which existing judgments and evidence already compose sufficiently, and
   which analyses establish relationships the current type system cannot state?
2. Which delimited-control accounts describe the relevant Ash fragments, and
   what additional rules are necessary for selection, ownership and closing?
3. Which logical introduction, elimination and structural rules describe its
   data, functions, computations and captured contexts?
4. Which relationships belong in types, effects, context judgments or
   propositions, and what subjects and kinds can those relationships name?
5. How do written and inferred judgments share a meaning, and how much useful
   information can be inferred without reconstructing producer behavior?
6. How are evidence and assumptions preserved through calls, modules,
   specialization, linking and transformations?
7. What must replace each consumer of the existing analysis, and what independent
   checking remains necessary at an actual trust boundary?
8. How can the foundation admit the intended future control policies without
   silently deciding their resource, state or cleanup semantics?
