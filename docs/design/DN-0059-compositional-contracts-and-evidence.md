# DN-0059: Compositional Contracts and Evidence

- ID: `DN-0059`
- Status: exploring
- Related: [DN-0001](DN-0001-reboot-foundations.md), [DN-0032](DN-0032-algebra-of-scoped-resource-composition.md), [DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md), [DN-0034](DN-0034-one-shot-kernel-soundness-and-practicality.md), [DN-0055](DN-0055-algebra-of-regions-lifetimes-and-ownership.md), [DN-0056](DN-0056-scoped-continuation-retention-and-library-scheduling.md), [DN-0057](DN-0057-checked-ffi-module-boundaries.md), [issue #193](https://github.com/dikini/ash-lang/issues/193).

> This design note is informative. It does not define current Ash, accept an architecture or authorize product implementation.

The implementation baseline is [954c174bb37d5444d2491ec01dc3e495ea6117a1](https://github.com/dikini/ash-lang/commit/954c174bb37d5444d2491ec01dc3e495ea6117a1), after M4 integration. This exploration develops requirements, candidate boundaries and an investigation sequence.

## Question

What must Ash express at program boundaries so that behavioral obligations can be checked compositionally, with progressively less reconstruction of the implementations behind those boundaries?

Which relationships can existing types, interfaces, kinds and constraints express? Which require additional machinery? How can declarations, explicit assumptions and checked evidence establish those relationships while supporting practical programs and improving inference?

## Motivation

Ash’s development must balance four goals:

- **Practical Ash:** programs can communicate, manage resources and interface with the outside world.
- **Richly typed Ash:** types describe the boundaries and behavioral contracts those programs require.
- **Correct Ash:** the intended semantics are adequately specified, their claimed formal properties are established, and the implementation corresponds to them.
- **Verified Ash:** programs can be shown to satisfy specified properties under explicit assumptions.

These goals advance at different rates. Useful facilities may require guarantees that the current type system cannot yet express directly. Formal results may cover a bounded model before correspondence with the implementation is established. Program verification may rely on assumptions about libraries, native code or the environment.

Each development stage must state exactly what it establishes and what remains assumed or unverified.

### The current analysis as a stepping stone

Ash already separates surface syntax from typed, annotated Core. Top-level annotations and bidirectional checking provide a foundation for checking boundaries while inferring many inner forms.

Additional compiler analysis establishes relationships that ordinary types and effect rows do not yet express sufficiently: retained dependencies, resource lifetimes, captured control, interpreter compatibility and outstanding completion obligations.

This analysis enables practical programs while enforcing guarantees that would otherwise be unavailable. It is a necessary surrogate for a more explicit contract system and a source of evidence about what that system must express.

As facilities compose, reconstructing these relationships requires increasingly extensive reasoning across values, calls and control contexts. The resulting concern is both practical and semantic: maintenance becomes harder, checking costs can grow, and the connection between a declared boundary and its enforced guarantees becomes less direct.

The intended direction is **successive replacement of implicit reasoning with explicit, compositional contracts**.

### Types and composition

Types are central because they describe boundaries and the behavior components may require or promise. Interfaces already express some relationships. Additional kinds, constraints or judgments may be needed for effects, resources, usage and other properties.

Composition is equally central. Contracts must support the construction of larger programs from smaller components, including composition through handlers and continuations. A contract that describes an isolated component but cannot justify its use in a surrounding context is insufficient.

The target is the smallest contract sufficient for safe composition. More detailed facts may remain private evidence. Consumers should rely on established contracts without reconstructing implementation details irrelevant to their obligations.

### Declarations assumptions and evidence

Not every useful property must initially have a machine proof.

Ash should be able to express requirements and axiomatic laws as language-level statements. An explicit assumption can participate in later declarations and proofs, even when its justification is external or unavailable to the compiler.

A checked derivation establishes its conclusion under its premises. Assumed premises must remain identifiable through subsequent composition; testing or indirect use does not silently turn them into proved facts.

This provides a practical progression from expressible requirements and assumptions toward stronger evidence without changing the statements downstream reasoning uses.

Future signed artifacts may let consumers accept authenticated statements from trusted authorities without repeating their verification. This possibility strengthens the need for precise claims, subjects, dependencies and assumptions.

### Inference and practical development

Explicit contracts must support an improving inference path. Ash’s existing annotated boundaries and bidirectional checking are the starting point.

Simple relationships should be inferred first, with progressively more useful forms becoming inferable. Explicit annotations or evidence should provide a path where inference is insufficient but the checking rules can establish the obligation.

The transition must preserve practical development. Its success is measured by obligations becoming explicit and reusable, composition requiring less behavioral reconstruction, and guarantees acquiring a clearer semantic and implementation basis.

## Context

### Existing foundations and their limits

Ash already has typed Core, constrained schemes, exact effect rows, module summaries and independent linked validation. Effect rows record outstanding interpretation requirements. Interface constraints select evidence for relationships among admitted type-level arguments. Neither currently supplies a general language of capture, usage or proof contracts.

The restrictions are concrete. Effect-row variables cannot currently be ordinary interface arguments. The specification also excludes source capture annotations and capture-polymorphic function types. Extending the existing relational machinery requires examining its subjects, formation rules and evidence, rather than adding only a convenient interface name. [Kinds and schemes](https://github.com/dikini/ash-lang/blob/954c174b/spec/static-semantics.md#L196-L220), [capture rules](https://github.com/dikini/ash-lang/blob/954c174b/spec/static-semantics.md#L1210-L1245).

Module checking infers private summaries containing possible calls, requests, handlers and completion control. Imported calls specialize those summaries without requiring dependency source bodies. Separate source checking is therefore already possible. The remaining question is how much behavior consumers must reconstruct from the retained summaries. [Summary contract](https://github.com/dikini/ash-lang/blob/954c174b/spec/elaboration.md#L432-L439).

### What the current analysis supplies

| Relationship | Relevant distinction |
| --- | --- |
| Stored dependencies | Retaining live resource access differs from retaining an independent snapshot |
| Control interaction | A helper can capture caller obligations through an effect request without storing resource-dependent values |
| Continuation ownership | Moving or consuming a capture differs from duplicating ordinary access values |
| Cleanup compatibility | A matching effect row does not establish that the required interpreter survives abandonment |
| Completion | Producing a result does not establish that required suffixes and cleanup have completed |
| Observation validity | A genuine state observation can cease to justify an action after intervening state changes |

These relationships interact, but are not interchangeable. They explain why an ordinary function domain, result and outward row can be insufficient to check a use. [Static semantics](https://github.com/dikini/ash-lang/blob/954c174b/spec/static-semantics.md), [capture engine](https://github.com/dikini/ash-lang/blob/954c174b/src/core/capture.rs).

### Typed Core and independent reconstruction

Linked Core validation derives capture, dependency and cleanup obligations from actual control. Imported summaries and elaborator permissions do not replace this derivation. A transformation that preserves ordinary types can still invalidate a dependency, completion relationship or cleanup interpretation. [Validation requirements](https://github.com/dikini/ash-lang/blob/954c174b/spec/elaboration.md#L850-L878).

The validator invokes the shared capture-analysis engine. Its independence is from the elaborator’s claimed result; it is not a separate proof-checking implementation. This protects against stale permissions but also identifies the replacement opportunity: some guarantees lack sufficient explicit contracts and evidence at the Core boundary. [Validator entry](https://github.com/dikini/ash-lang/blob/954c174b/src/core/validate.rs#L13820-L13890).

### Evidence from practical composition

M4 puts the codec and Work/Ack protocol in ordinary Ash. The host provides transport and carrier behavior, while generic ownership and completion rules govern local resources. The accepted worker decision supersedes protocol-specific compiler checking. This demonstrates library expression of behavior; it does not establish protocol honesty, liveness, per-message processing or native correctness. [AD-0017](https://github.com/dikini/ash-lang/blob/954c174b/docs/decisions/AD-0017-pinned-worker-host-and-transport.md), [library scope](https://github.com/dikini/ash-lang/blob/954c174b/libraries/README.md).

At this baseline, the combined retained-control, binding and Network example uses the source-native interpreter with trusted Rust callbacks. Generated native images do not support Network operations. Separate generated-host C and SQLite canaries establish their own supported paths, not a combined Network image. [Execution scope](https://github.com/dikini/ash-lang/blob/954c174b/libraries/README.md).

[Issue #190](https://github.com/dikini/ash-lang/issues/190) reports that a combined program exhausts final-elaboration work when importing a fuller native-binding module containing an unused discard-bearing path, whereas a focused binding compiles. The reported contextual cleanup analysis discovered at least 58,810 states before exhaustion. The issue records that the exact relocated reproduction command had not been rerun.

This is evidence of pressure, not a diagnosis. Missing contracts, excessive contextual reconstruction, overly broad roots and implementation inefficiency remain distinct explanations. Improving boundary contracts and repairing an algorithmic inefficiency are compatible activities.

### Existing formal evidence

The one-shot formalization establishes substantial results for stated annotated models, including preservation and bounded execution results under explicit premises. It does not establish complete correspondence with the current compiler or multi-shot behavior. Those proof boundaries must remain intact when results are reused. [Proof status](https://github.com/dikini/ash-lang/blob/954c174b/docs/design/direct-effects/one-shot/README.md#current-proof-status).

## Constraints

### Explicit and sufficient contracts

A contract must have a meaning independent of the algorithm that discovers it. Its subjects, parameters, scope and assumptions must be identifiable.

A consumer must be able to check the relevant composition from the contract and accepted evidence. Replacing an implementation with another satisfying the contract must preserve the consumer’s established obligations. Identical results or traces follow only where the contract promises such equivalence.

The contract should expose sufficient information while permitting irrelevant internal changes. A renamed internal graph is not automatically an adequate public boundary.

### Composition and usage

Candidates must explain composition through the forms they support: calls, higher-order functions, aggregates, branches, recursion, handlers and continuations. A bounded candidate may support only a fragment, provided its exclusions are explicit.

Usage multiplicity, uniqueness, access permissions and completion ownership must remain distinguishable. An affine permission does not establish unique access; a unique reference does not by itself establish safe abandonment; a duplicable handle does not duplicate close authority. The eventual rules may connect these properties, but must justify those connections.

### Inference and justification

Written and inferred contracts must have the same meaning. Inference failure must distinguish an inexpressible relationship, missing evidence, a violated obligation and an ambiguous policy choice. An annotation can repair missing inferred information only where the language can express and check the required relationship.

Claims must distinguish outstanding requirements, accepted assumptions, checked derivations and testing evidence. The design must state which justifications may discharge each obligation, including any operational permission that depends on trust.

### Evidence integrity and practicality

Evidence must remain associated with its subject through linking, specialization, transformation and loading, or be re-established. Runtime state facts need preservation conditions in addition to static implementation evidence.

Candidates must be evaluated on useful programs, including existing positive and negative cases. Conservative intermediate restrictions are possible, but their practical and annotation costs must be explicit.

### Evaluation criteria

| Criterion | Question |
| --- | --- |
| Sufficiency | Can the consumer establish its obligation from the contract and accepted evidence? |
| Abstraction | Which implementation details may change without invalidating consumer reasoning? |
| Compositionality | Where is contextual reconstruction still necessary? |
| Expressiveness | Which relational, usage and state properties can be stated? |
| Inference | Which annotations can be omitted now, and what enables improvement? |
| Assurance | What is checked, proved, assumed or enforced at runtime? |
| Practical cost | What happens to checking work, evidence size, diagnostics and programmer effort? |
| Replacement | Which existing reconstruction becomes unnecessary? |

## Bounded investigation examples

The investigation uses six example families. Existing tests establish current observations; they do not prove a replacement sound. E1 and E2 are the first detailed study. E3 challenges its treatment of surrounding control; E4–E6 test interpretation, state and justification.

### E1 Independent snapshots and retained access

A closure created inside cell scope R may retain an independent snapshot or retain access to R. Only the latter requires R afterward. Reading a cell preserves the returned value’s dependencies; it is not an independent deep copy. A closure may also depend on its own backing storage.

The boundary question is whether the escaping value requires R and whether its other support remains valid. A value’s creation inside R does not make every resulting value depend on R. [Opaque-wrapper examples](https://github.com/dikini/ash-lang/blob/954c174b/tests/resource_scope_typing.rs#L291-L310), [dependency rules](https://github.com/dikini/ash-lang/blob/954c174b/spec/static-semantics.md#L1545-L1577).

### E2 Higher-order transport

Pass independent and dependent values through opaque containers, projections, callable wrappers and callback invocation. The helper must be checked under an abstract contract; clients should use that contract.

The required relationships differ. Projection selects component support. Wrapping retains the original callable and introduces any new captures and backing. Callback invocation must describe the returned value’s support separately from support needed to run the callback. Current tests distinguish callbacks that both use dependent access but return different closures. [Callback results](https://github.com/dikini/ash-lang/blob/954c174b/tests/resource_scope_typing.rs#L665-L678), [imported projections](https://github.com/dikini/ash-lang/blob/954c174b/tests/resource_scope_typing.rs#L711-L726).

### E3 Interaction with caller control

A helper retaining no resource-dependent values performs an effect. One surrounding handler confines capture to a closable segment; another captures live caller obligations. Admission depends on the actual cut and permitted clause actions, not solely on the helper’s stored captures. [Direct and helper requests](https://github.com/dikini/ash-lang/blob/954c174b/tests/effect_typing.rs#L235-L279).

### E4 Cleanup after abandonment

Cleanup performs an operation whose selected interpreter may be removed by abandonment. An outer interpreter for the same effect instance need not preserve the required interpretation. Compare surviving and removed interpreter arrangements. [Cleanup override example](https://github.com/dikini/ash-lang/blob/954c174b/tests/cleanup_interactions.rs#L155-L192).

### E5 Stale state observations

Observe that a Store is quiescent, introduce retained work, then attempt release using the old observation. Contrast this with a genuine current observation whose validity is preserved. An ordinary Boolean is not release authority. [Stale fixture](https://github.com/dikini/ash-lang/blob/954c174b/tests/fixtures/retained-drain/stale.ash), [rejection cases](https://github.com/dikini/ash-lang/blob/954c174b/tests/retained_control.rs#L184-L225).

### E6 Derivation from an axiomatic law

A hypothetical library exports a binary operation with an axiomatic associativity law. A client derives equality between four-input parenthesizations. Compare an assumed law, a later proof of the same statement and an implementation change that invalidates former evidence.

The law must identify the operation, quantified domain and equality being claimed. For effectful operations, it must identify the relevant observations. This is a proposed example, not implemented Ash functionality.

## Retained support across value boundaries

### Contract content for E1 and E2

For this study, required support means the owners or backing whose validity a value’s retained representation and access require. It is a dependency description, not an ownership grant.

Candidates must account for primitive and resource access values, field support, closure captures, construction backing, projection and boundary crossing. A conservative upper bound may suffice. Exact equality is not always needed, but retaining unrelated owners can reject useful compositions.

Opaque transport must preserve payload dependencies separately from container backing where extraction permits that separation. If extraction depends on container backing, the result must retain that requirement. The private representation determines what the producer must establish; the public contract determines what consumers may rely on.

A callable boundary may need to distinguish its stored environment, invocation requirements and normally returned results. A callback can require R while executing and return an independent value. Another callback with similar invocation requirements can return access dependent on R. Fresh result allocation may depend on the caller’s selected context rather than the stored environment.

### Candidate representations

| Candidate | Benefit to investigate | Main question |
| --- | --- | --- |
| Support-qualified types | Generic abstraction can preserve support distinctions carried in types | How are bounds quantified, inferred and hidden across opaque boundaries? |
| Relational constraints | Signatures relate inputs, environment, invocation and results | Which static subjects and composition rules are admitted? |
| Propositional contracts | Richer relationships can have assumed or proved justification | How do statements connect to operational typing obligations? |

These may form layers rather than competing architectures. Types can carry distinctions; constraints can relate them; propositions can justify additional relationships.

A relation over only the current ordinary arrow type cannot distinguish two callable values with that same type and different support. The additional distinction must occur somewhere: a qualified type, static identity, explicit evidence or contextual judgment. Adding new kinds identifies admissible subjects; it does not alone establish any relationship among them.

### Structural propagation and explicit relationships

Some generic operations may preserve richer information through ordinary type abstraction. Packing and unpacking could transport a support-qualified payload without a special law for every helper. Whether this follows must be established by the typing rules, including allocation and opacity; it cannot be inferred from the visual shape of a polymorphic signature alone.

Other helpers need explicit relationships. Projection requires selecting the relevant component. Callback invocation requires using the callback’s result contract. These boundaries test whether sufficient information survives without exposing implementation control graphs.

Producer checking establishes the contract or records its accepted premise. Call-site composition instantiates it. Boundary checking establishes that the resulting support remains valid. The intended replacement removes producer-body reconstruction from the latter two steps.

## Continuation interaction across call boundaries

### Contract content for E3

A stored-support contract cannot account for all effects on a caller. Performing an operation can capture pending caller computation, scope owners and unfinished clauses. The obligations therefore depend on both the callee’s interaction and the context supplied by the caller.

A candidate must distinguish at least three contributions: the operation’s interaction contract, the selected handler clause’s use of its continuation, and the captured context’s admissible uses. An effect’s outward presence or absence does not determine all three.

For example, placing the selected handler outside a resource scope can put that resource owner inside the captured segment. Placing the selected handler inside the resource scope leaves the owner outside that segment. Both arrangements still require completion checking, but they present different obligations to abandonment or splitting. Moving the handler across the scope therefore requires justification rather than ordinary syntactic rearrangement.

The boundary need not describe every frame publicly. It must express enough about possible capture and continuation use for the caller and handler to establish compatibility. A helper can remain abstract over a compatible context rather than naming each caller owner.

### Composition requirements

The candidate must explain how pending work contributes requirements when sequencing pushes a context, how a request cuts that context at an exact handler, and how resumption reconnects it. It must also account for work remaining in the clause after resumption.

Handler clauses execute outside the selected handler in current Ash. Requests made by a clause can capture a different segment, including live obligations of another clause. Reusable handler code differs from an already live one-shot capability: repeated installation need not duplicate a live capability, whereas copying a segment containing that capability would. [Current handler rules](https://github.com/dikini/ash-lang/blob/954c174b/spec/static-semantics.md#L1068-L1245), [candidate mixed-control examples in DN-0033](https://github.com/dikini/ash-lang/blob/954c174b/docs/design/DN-0033-direct-effects-and-continuation-capabilities.md#worked-mixed-handler-derivations).

The investigation should compare a context-typing judgment, qualified interaction constraints and proposition-backed compatibility. These are ways to express the missing relation, not reasons to introduce computation wrappers, selectable bind operations or conversion between computation models.

### Replacement boundary

Success would let a caller compose a checked helper interaction contract with a checked context contract. If the consumer still follows the helper’s possible bodies and reconstructs every capture route, the replacement is incomplete for that obligation.

Contract abstraction may lose precision. A fixed conservative continuation-use bound might reject a helper accepted by body-sensitive analysis. The study must record this cost and determine whether a richer relation, specialization or explicit evidence offers a useful improvement.

## Cleanup interpretation and completion

### Contract content for E4

Cleanup has several obligations: whether an action is eligible to start, whether its invocation has begun, what remains before it completes, what support must remain live and which interpreters its requests require.

An ordinary callback type and effect row describe only part of this contract. Closing occurs at a particular structural position. Some interpreters have already been removed, others remain, and a running completion must not be skipped. A completed callback result cannot stand in for unfinished close work.

Candidates should compare interpreter requirements that abstract over a supplied compatible interpretation, requirements tied to a particular installation, and contextual relations that preserve selection under closing. Exact identity may be necessary in some cases but may overexpose implementation detail in others. The sufficient relation must be derived from the semantic obligation.

### Closing as a checked transition

The expected contract describes what authority is consumed, which actions must run, what support remains live during them and what is established on normal completion. Failure behavior must be stated separately. A claim about normal return does not promise termination or successful cleanup after every internal or native failure.

A candidate succeeds when consumers can justify closing from the contract and their surviving context without rediscovering all transitive callback behavior. Producer checking or evidence must still establish the callback’s declared requirements.

This study should use E4’s removed-override example before generalizing to all cleanup. Preserve current protection against substituting an outer same-instance interpreter for the required removed interpretation.

## State observations and transition contracts

### Contract content for E5

A genuine Store observation relates a particular live Store’s state to its result. A later operation may preserve that relation or invalidate it. The contract must describe the subject, provenance and permitted intervening changes.

Three candidate treatments merit comparison: explicit state evidence passed through operations, relational preconditions and postconditions, and scoped facts whose validity is checked across preserving operations. None is selected here. Each must explain aliases, branches, recursion and unknown callees.

Stable implementation claims and current-state facts have different lifetimes. A static theorem may state that a successful probe has a particular meaning. Applying that theorem still requires the actual authenticated observation and its state conditions. Signing the theorem does not preserve a fact after the state changes.

### Normal return and release

A library drain can potentially promise that, if it returns normally, specified work has completed. This does not promise eventual return, fairness or that an empty queue implies quiescence. Generic Store ownership and actual transport settlement remain separate obligations.

Success would let release consume an established current completion fact or a suitable normal-return contract. It would remove the need to reconstruct a particular drain implementation at every use while retaining checks on operations that may create work afterward.

## Propositions laws and their justification

### Statements and subjects

The foundational distinction is useful: a proposition is a semantic relation or predicate; a law is a required instance for identified entities; a proof establishes a law under stated premises. This study adds an explicit account of requirement and justification status. General source law and proof facilities remain a future direction. [DN-0001 sections 14 to 16](https://github.com/dikini/ash-lang/blob/954c174b/docs/design/DN-0001-reboot-foundations.md#14-propositions-laws-and-proofs).

Statements need meaningful subjects. Depending on the claim, these may include types, effect instances, resource identities, particular implementations or static refinements of values. A symbol name alone does not identify an unchanged implementation. Whether subjects require additional kinds, explicit static entities or other mechanisms is open.

### Requirement and evidence status

| Status | Meaning |
| --- | --- |
| Outstanding requirement | A property must be established before the use that requires it |
| Axiomatic assumption | The property is explicitly accepted as a premise |
| Checked derivation | The conclusion follows from recorded premises under the checking rules |
| Tested property | No counterexample was found in the stated test scope |
| Accepted attestation | A trusted signer authenticates a specified claim about specified artifacts and evidence |

These statuses can coexist. A checked derivation can depend on axioms; an assumed law can also be tested. An attestation can certify proof checking without vouching for every premise, or separately attest to acceptance of a premise.

An outstanding requirement must not silently become an accepted assumption. The policy governing when an axiom can discharge an obligation must be explicit. In particular, functional-correctness reasoning, operational safety admission and optimizer permissions need not have identical trust policies. This note leaves their exact policies open.

### E6 as a complete evidence example

Let a library name an operation and assume associativity under a specified equality. A client proves equivalence of two four-input parenthesizations by repeated use of that assumption and the admitted equality rules. The client derivation checks, but retains the associativity premise.

For a hypothetical total binary value operation, the assumed equation is “combine(combine(a, b), c) = combine(a, combine(b, c))” for all values in its domain. A client can derive:

1. combine(combine(combine(a, b), c), d)
2. = combine(combine(a, b), combine(c, d))
3. = combine(a, combine(b, combine(c, d)))

The first step instantiates associativity at combine(a, b), c and d; the second instantiates it at a, b and combine(c, d). Equality transitivity connects the endpoints. No commutativity is assumed, and argument order is preserved. The conclusion remains conditional on the named associativity premise and the example’s total-operation and equality basis. This is mathematical explanation, not proposed proof syntax.

If the library later establishes the same law by a checked proof, consumers can retain the same statement while the evidence dependency is strengthened. If the operation changes, its associated evidence must be reassessed. Testing may refute the assumption or increase practical confidence; passing tests do not discharge it.

For effectful operations, equality must specify observations such as results, ordering, failure, divergence and completion events as relevant. An unordered effect row does not establish equivalence under reassociation or exchange. A law quantifying only total value operations cannot silently apply to arbitrary effectful computations.

### Connection to checking

A small proof checker does not automatically understand how any arbitrary theorem grants an operational permission. The design needs a defined bridge between statements and the judgments or transformations that consume them. That bridge may consist of a selected family of foundational relations and general composition rules, without making every user proposition compiler-specific.

Contradictory accepted assumptions can invalidate the usefulness of derived guarantees. Recording the trust basis is necessary but is not a proof of its consistency. The initial stage can remain useful with explicit assumptions while keeping its conditional claims clear.

### A useful stage before proof checking

Statements and axiomatic declarations can arrive before any internal proof language. They can document requirements, connect later law declarations to their premises, support external reasoning and guide testing. At that stage, a declared consequence is not a checked derivation merely because its premises are recorded; its justification must remain assumed or outstanding as appropriate.

A later bounded proof fragment can check steps such as the associativity example. More general proof construction and evidence synthesis can follow. This preserves the value of explicit laws without making a full prover a prerequisite for contract development.

## Candidate directions

The working candidate separates four responsibilities.

1. **Types and static subjects** distinguish values, effects, resources, support and usage information as required by the supported fragment.
2. **Composition rules and constraints** relate those subjects across program boundaries and operations.
3. **Propositions and evidence** state additional properties, track assumptions and justify permitted uses.
4. **Core operations and runtime contracts** supply the actual transitions whose behavior is described and checked.

This is a division of responsibilities, not a commitment to four new subsystems. Existing Ash machinery may implement several roles. The investigation should add machinery only where a concrete obligation cannot be expressed or checked sufficiently.

Libraries own algorithms, protocol choices, scheduling policy and compositions of established facilities. The foundation owns the meaning of the judgments and evidence that authorize use. Structural evidence can be inferred; program-specific evidence can be written or assumed under an explicit policy. Runtime operations continue to enforce dynamic conditions and native assumptions remain at their actual boundary.

Keep the underlying checking judgments independent of a particular inference strategy. Initially the existing analyzer may produce some annotations or evidence, but it must be demonstrated that its facts can be represented adequately. It is not already a general certificate generator.

## Consequences for multi-shot admissibility

Multi-shot control is a demanding consumer of these contracts, not the first replacement milestone.

Admission must relate the chosen repetition policy, captured support, interpreter context, use permissions and completion obligations. Result type and outward effects alone cannot supply this relation. Copying a non-owning key or access handle grants no additional ownership.

| Policy | Obligation to express |
| --- | --- |
| Classical purity | A declared observational contract that may permit allocation, divergence or failure |
| Effectful repetition | Specified repeated interactions and ordering with valid support and ownership |
| Strict property whitelist | Each relevant behavior satisfies the selected predicates under stated assumptions |

Current source arrows include the private default allocation requirement even when written with an empty row. That convention cannot serve as an allocation-free contract. Internal resource exhaustion and declared allocation refusal also have different behavior. [Allocation defaults](https://github.com/dikini/ash-lang/blob/954c174b/spec/static-semantics.md#L317-L331), [failure boundary](https://github.com/dikini/ash-lang/blob/954c174b/spec/dynamic-semantics.md#L125-L147).

A library may select sequential shared state or independent snapshots, and inference may establish their prerequisites. It must not silently choose between their different observable meanings. Similarly, sequential duplication does not authorize concurrent execution or nondeterministic reordering. Such uses require their own sharing, synchronization and observational contracts.

An explicit split into separately owned one-shot branches is a possible bounded experiment. Its semantics must define what repeats, what is shared, who closes each branch and what failure leaves available. It is an alternative to compare, not an accepted Core addition. A live one-shot capability inside the segment remains restricted unless a valid split relation accounts for it.

## Signed artifacts and foreign assumptions

An attestation should bind the claim to its subject artifact, semantic and checking basis, dependency contracts and assumptions. Consumers can verify evidence themselves or accept an authorized attestation under their trust policy. Signatures authenticate attestations; acceptance of correctness is a separate decision.

Verification reuse and compilation reuse are related but different. Avoiding proof checking requires accepted evidence. Avoiding recompilation additionally requires a compatible compiled artifact, target and linkage contract. The eventual packaging design must specify how dependency substitution and semantic-version changes affect both.

Designing signing infrastructure is unnecessary for the first contract experiment. Preserving stable claim identities and explicit assumptions is useful now. The precise hashing, signing, cache and revocation mechanisms remain separate work.

FFI contracts must distinguish Ash representation validity, supported access, native lifetime, external behavior and containment. A verified wrapper cannot establish arbitrary native correctness from a declaration. Runtime checks, explicit native premises and stronger external evidence can coexist. [DN-0057](https://github.com/dikini/ash-lang/blob/954c174b/docs/design/DN-0057-checked-ffi-module-boundaries.md).

The same principle applies to M4. Transport-origin authentication does not prove honest acknowledgements or application processing. Worker return, protocol success and backing settlement remain distinct facts. Ordinary protocol libraries should be able to state and establish their properties without a protocol-specific compiler checker.

## Successive replacement sequence

These are ordered investigations with bounded exit criteria, not an accepted implementation schedule. Practical development and focused repairs may proceed while the contract work advances.

### First establish the obligation map

For E1–E6, record the producer, consumer, semantic obligation, current reconstruction, candidate sufficient statement, assumptions, invalidating changes and the reconstruction that could be removed. Keep this map connected to existing examples rather than introducing a separate evidence framework.

Exit when one chosen boundary has an explicit claim and a defensible explanation of why consumers need no additional producer information. Treat the cause of issue #190 as a separate diagnosis until evidence connects it to that boundary.

### Compare explicit E1 and E2 contracts

Write the same opaque-transport and callback-result contracts using the qualified-type, relational and propositional candidates. Keep backing and result support separate. Show a producer check, an abstract higher-order helper check and a client boundary check for positive and negative cases.

Exit when at least one candidate explains the cases, its annotation requirements and exactly what behavioral reconstruction it removes. If none does, identify whether the gap is expressiveness, evidence or unavoidable contextual dependence. Do not choose syntax to conceal that gap.

### Add statements and explicit assumptions

In parallel with the chosen obligation, work through E6’s statement formation, assumption use, derived claim and subject change. Establish how an outstanding requirement differs from an accepted premise and how dependency information is preserved.

The first exit requires meaningful, well-formed statements, explicit acceptance of axioms and inspectable dependencies. An internal proof checker is not required for this stage. As a bounded derivation mechanism becomes available, check E6’s client derivation while preserving its unproved premise. General proof machinery and signed artifact implementation can follow independently.

### Connect the bounded contract to Core checking

Define the supported Core annotations and checking judgments for the selected relation. Compare reconstruction, local evidence checking and accepted attestations without assuming that all must be implemented at once.

Where useful, retain the current analyzer as a temporary producer or comparison oracle. The old implementation is regression evidence, not the definition of correctness. Classify disagreements against the intended semantics and explicit contracts.

Exit when malformed or stale evidence is rejected, the supported examples check through the new boundary, and the old reconstruction is no longer mandatory for the selected obligation. A prototype remains experimental until the repository’s semantic-change and delivery process retains it.

### Improve inference within the established rules

Begin with local construction, direct captures, projections and expected contracts. Progress to constraint propagation through ordinary calls, polymorphic support relationships and checked recursive bounds. More precise recursive inference or evidence synthesis follows demonstrated needs.

Every inferred result must have the same meaning as its explicit counterpart. At each step record newly inferable forms and the remaining annotation escape hatch. Failure must distinguish insufficient inference from a rejected obligation.

Exit criteria concern useful removed annotations and predictable behavior under the same contracts, not a universal inference-completeness claim.

### Extend through E3 E4 and E5

Challenge the value-contract boundary with caller control, cleanup interpretation and state preservation. Add only the relations required to explain these cases. Connect any formal results to their actual fragment and separately assess implementation correspondence.

Exit for each extension when the producer and consumer responsibilities are explicit and a named part of existing reconstruction becomes unnecessary. A new generic interaction rule should replace repeated special cases rather than merely move them into a solver.

### Retire replaced analysis and investigate broader consumers

Remove mandatory reconstruction only after all consumers of the selected fact use the established boundary. Retain valuable inference and diagnostics where appropriate. The target is simpler acceptance obligations, not deletion of useful tooling.

Then investigate library-defined multi-shot policies, richer resource protocols and signed evidence reuse against the same contract foundation. Changes to usage, lifetime and scheduling remain distinct semantic steps.

## Evidence and experiments

Each bounded experiment needs a compact account of its supported fragment, semantic claim, evidence premises and corresponding implementation checks. A formal model, a checked Core judgment, a passing runtime test and an accepted native assumption establish different parts of the result.

A disposable prototype, if needed, must test one named candidate against the relevant E1–E6 cases and evaluation criteria. Discard its implementation if it fails the boundary or merely relocates the required reconstruction. Retain useful findings, counterexamples and bounded formal evidence in this note or linked evidence. Any implementation kept solely for comparison remains experimental; product adoption requires the separate semantic-change and delivery process.

Reuse existing positive and negative examples and add focused cases for malformed annotations, invalid evidence, transformed subjects and lost assumptions. Compare explicit and inferred versions where both are supported. Test capture identity, generic specialization and implementation substitution where relevant to the particular obligation.

Measure the cost of the complete acceptance route: producer work, repeated consumer work, evidence size, annotation burden and diagnostics. Distinguish discovery from checking and cold consumption from reuse. Faster inference is useful even when it does not change the mandatory boundary; a smaller checker is useful even when evidence construction remains expensive.

For each stage, report the four Ash goals separately. State which practical programs are supported, which contracts are expressible, which formal and correspondence results exist, and which program properties follow under which assumptions. Stronger evidence in one dimension must not be presented as completion of another.

## Alternatives and tradeoffs

Continuing to improve the existing analyzer remains practical for immediate programs and targeted inefficiencies. Its risk is further dependence on behavioral reconstruction. A comprehensive new calculus could unify obligations, but risks delaying practical feedback and accumulating unused machinery. Beginning with the largest performance problem could deliver relief, but risks confusing an algorithm repair with a contract-design requirement.

The working preference is a bounded producer–consumer study, challenged early by adjacent cases. Its main risk is overfitting. E3–E5 provide the required pressure against an E1–E2 solution that accounts only for stored values.

Some acceptance may become more conservative. Record those cases and their practical importance rather than promising both identical precision and immediate simplification. Conversely, a richer contract language can move complexity into annotations, constraint solving or proofs. Evaluate that total cost before retaining a design.

Runtime enforcement remains appropriate for dynamic facts. Explicit assumptions remain appropriate where a useful conditional guarantee is intended. The investigation must make their boundaries composable instead of treating static proof as the only acceptable realization.

## Open questions

1. Which support distinctions belong in value types, and which remain contextual judgments?
2. Which static subjects must interfaces and other relations admit, and what kind or quantification extensions are necessary?
3. Which relationships follow from generic abstraction, and which require explicit contracts?
4. How are fresh and hidden support, allocation context and normal-result dependencies represented?
5. Which usage permissions are intrinsic and which can be justified by general evidence under an explicit trust policy?
6. What context contract is sufficient for effect requests and continuation composition without exposing the complete frame graph?
7. What interpretation relationship is sufficient during cleanup without needlessly exposing provider identity?
8. How do state observations gain, preserve and lose authority through aliases, calls and recursion?
9. Which axioms may discharge functional, safety and optimization obligations, and how are the resulting guarantees distinguished?
10. What is the smallest useful proposition and evidence-checking fragment?
11. What implementation, semantic and dependency identities must reusable evidence bind?
12. Which current acceptance cases justify additional expressiveness rather than conservative rejection or specialization?

## Immediate next investigation

The next bounded study is E1 and E2 under an explicit top-level contract. Produce side-by-side candidate statements for opaque transport and callback results, one producer derivation and one client composition for each, and a precise list of reconstruction they eliminate. Include the counterexample where invoking a dependent callback returns an independent value, and account for backing independently of cell access.

Use E3 to test the candidate’s limit before generalizing it to continuation admission. Work through E6 alongside the study so that assumptions and derivations have a defined status from the beginning.

A retained outcome is either a justified contract candidate for a semantic proposal or a documented reason it is insufficient. The investigation succeeds by making the missing obligation and its boundary explicit, even if its first candidate is rejected.
