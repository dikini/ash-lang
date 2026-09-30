# DN-0001: Ash Reboot Foundations

- ID: `DN-0001`
- Status: exploring
- Related: [AD-0004: Small-Step Semantic Method](../decisions/AD-0004-small-step-semantic-method.md), [DN-0002: Core Representation](DN-0002-core-representation.md), [DN-0003: Parser Architecture](DN-0003-parser-architecture.md)

> This design note is informative. It records reboot principles, constraints, and open directions; it is not the Ash specification and does not accept the speculative designs it discusses.

## Purpose

This note captures the current design intent for the Ash language reboot.

It is not the Ash specification. It does not define future language semantics. It records the development principles, architectural constraints, and open design directions that should guide the initial reboot work.

The previous Ash repository at `dikini/ash` should be treated as a historical archive and source of prior experiments, not as authority for the reboot.

---

## 1. Reboot principle

The reboot starts from a small, coherent, pure functional Ash and grows in stages.

The aim is not to preserve the accumulated feature inventory of historical Ash. The aim is to preserve what was learned from it while rebuilding the language through a simpler development process.

Mainline should always describe and implement a coherent language.

A feature should not exist in the current specification merely because it is intended, designed, or partially implemented.

The canonical specification describes what Ash currently is.

---

## 2. Project artifacts

The reboot should keep a small number of artifact classes with sharply different roles.

### Specification

The specification describes current implemented Ash.

It answers:

> What is Ash now?

Properties:

- normative;
- describes `main`;
- contains only implemented language/runtime behaviour;
- does not contain future feature inventories;
- changes together with implementation.

The specification may be split into independent files or sections, but they form one logical specification.

### Change proposal

A change proposal describes a proposed transition from the current specification to a new specification state.

It answers:

> What will Ash become if this change is accepted and implemented?

It should state:

- current behaviour;
- proposed behaviour;
- semantic delta;
- affected specification sections;
- resulting specification truth;
- interactions;
- non-goals;
- required evidence.

A change proposal is prospective specification text.

It does not become current Ash until implementation, tests, and the corresponding specification update merge.

### Task

A task is an implementation planning and execution record.

It answers:

> What work must be done to realize an accepted change or architectural decision?

Tasks record:

- dependencies;
- implementation work;
- progress;
- verification;
- discoveries;
- deviations requiring proposal/design reconsideration.

Tasks do not define language semantics.

If implementation discovers that the proposed semantics are wrong, the proposal should change rather than allowing the task to invent new semantics locally.

### Design note

A design note records exploration.

It answers questions such as:

> What options are we considering?
> What pressures should influence the current design?
> What remains uncertain?

Design notes may contain:

- research;
- alternatives;
- experiments;
- tradeoffs;
- speculative future ideas;
- architectural pressure on immediate work.

They are informative, not normative.

### Architectural decision

Some decisions are important but are not language changes.

Examples include:

- parser architecture;
- Core representation;
- compiler pass organization;
- repository workflow.

These should be captured as short architectural decisions after exploration converges.

A typical flow is:

```text
research
→ design note
→ architectural decision
→ task
```

Language changes instead follow:

```text
research
→ design note
→ change proposal
→ task(s)
→ implementation + tests + specification update
```

---

## 3. Current tree versus history

The repository working tree should contain only current, valid artifacts.

Superseded, rejected, and historical documents should normally be removed from the current tree.

Git history preserves historical evidence.

Important lifetime states may be marked with tags.

The intended temporal model is:

```text
working tree
    current project state

git history
    how the project evolved

tags
    important named states
```

The historical Ash repository should remain external historical evidence. Its documents should not be copied wholesale into the reboot repository.

A useful rule is:

> If deleting a historical document from the current tree does not reduce understanding of current Ash, it belongs in history rather than in the current tree.

---

## 4. Repository as project context

The repository should be sufficient to understand the project without depending on GitHub, GitLab, Linear, or another external system.

External systems may provide views, collaboration, scheduling, issues, or pull requests, but they are not the semantic source of project state.

If external systems disappeared, the repository should still answer:

- What is Ash?
- Why is it designed this way?
- What is changing?
- What work is active?
- What future directions currently matter?
- What assumptions and unresolved questions exist?

The repository is not intended to become a full project-management system or knowledge-management system.

It should support project management and knowledge management only to the degree needed to understand and evolve Ash.

---

## 5. Context reconstruction

A central goal of the development system is context reconstruction.

A contributor or agent should not need to understand the entire project before making a correct local decision.

The system should make it cheap to answer:

```text
What is true now?
Why is it true?
What is changing?
What remains uncertain?
What evidence supports this?
```

Different agents need different views over the same project state.

### Design work

Needs:

- current specification;
- relevant design notes;
- architectural decisions;
- alternatives;
- future architectural pressure.

### Implementation work

Needs:

- current specification;
- accepted change proposal;
- relevant decisions;
- active task;
- tests and invariants.

### QA

Needs:

- specification obligations;
- proposal acceptance criteria;
- positive and negative cases;
- invariants.

### Documentation/specification work

Needs:

- current specification;
- semantic delta from proposals;
- decisions affecting wording or structure.

### Planning

Needs:

- trajectory;
- dependencies;
- active proposals;
- task state.

The goal is:

> Reconstruct the minimum sufficient context for the question being answered.

The system should not require agents to read large numbers of unrelated documents.

---

## 6. Development trajectory

Development should be represented as a dependency graph rather than one large sequential roadmap.

Orthogonal capabilities may be developed in parallel and integrated when their dependencies and interaction points are ready.

Planning detail should decrease with distance.

Near-term work should be detailed and implementation-ready.

Further work should preserve:

- intent;
- dependencies;
- major interactions;
- architectural pressure;
- large risks.

Far-future work may contain speculative detail, but it remains explicitly speculative.

A useful maturity progression is:

```text
idea
→ speculative
→ outlined
→ designed
→ specified
→ implementation
```

Dependency readiness and design maturity are separate concerns.

A feature may be technically unblocked while still being too poorly understood to implement.

Future nodes should be detailed enough to prevent large architectural mistakes, but not detailed enough to pretend that unresolved decisions have been made.

Useful future notes should state:

```text
Current work MUST:
...

Current work MUST NOT:
...

Current work NEED NOT:
...
```

This allows future thinking to influence immediate architecture without turning future ideas into current requirements.

---

## 7. Initial language trajectory

The reboot should begin with a pure functional language.

The initial nucleus should be deliberately small and coherent.

Likely early capabilities include:

- primitive values;
- immutable bindings;
- functions and calls;
- recursion;
- algebraic data types;
- pattern matching;
- basic parametric polymorphism.

Effects, providers, processes, propositions, laws, proofs, and optimizer search should not be required for the first usable implementation.

The initial implementation exists partly to test the parser, type system, and Core architecture while the language is still small enough to change cheaply.

Infrastructure may merge before being exposed in surface syntax.

User-visible language semantics should not merge in an intentionally incomplete form.

A useful rule is:

> Infrastructure may be incomplete while unreachable; accepted language semantics may not be knowingly temporary.

---

## 8. Parser and grammar

The specification and parser architecture must remain separate concerns.

### Grammar

The language grammar should describe the accepted language independently of parser implementation.

EBNF is the likely normative notation for grammar.

The grammar should define:

- lexical structure;
- syntax;
- precedence;
- associativity;
- ambiguity rules.

### Parser architecture

Parser extensibility is an implementation concern.

The parser should be designed so future syntax can be added without repeatedly restructuring unrelated parser code.

Possible approaches should be researched before committing to a parser architecture.

Relevant questions include:

- modularity;
- grammar growth;
- precedence handling;
- ambiguity;
- diagnostics;
- error recovery;
- source spans;
- tooling support.

A suitable flow is:

```text
parser research
→ design discussion
→ design note
→ architectural decision
→ implementation task
```

The specification should not expose parser extension points.

---

## 9. Semantic specification discipline

The reboot should define a consistent semantic notation rather than mixing semantic styles opportunistically.

Using big-step semantics for some constructs and small-step semantics for others risks creating two normative semantic systems that can drift.

Ash is expected to include effects, handlers, explicit continuations, concurrency, cancellation, and runtime state.

[AD-0004](../decisions/AD-0004-small-step-semantic-method.md) selects
small-step operational semantics as the primary normative method.

Derived explanatory or big-step views may still be useful, but they should not become competing sources of truth.

Concrete language behavior remains to be accepted through semantic proposals
and recorded in the specification; the method decision does not define it.

The chosen semantics should be as complete as practical rather than selectively formal only around difficult features.

---

## 10. Core IR

Core is an immediate architectural concern because several expected future capabilities depend strongly on its shape.

The current direction is a Freer-like semantic model for effectful computation:

```text
Pure a
Impure op continuation
```

This is a semantic shape, not yet a commitment to a literal textbook Freer Monad encoding in the implementation language.

Important Core constraints include:

- Core is typed.
- Pure Ash fits naturally.
- Effects extend Core without requiring a monolithic recursive expression type to grow for every effect family.
- Continuations are explicit compiler data, not host-language closures.
- The representation supports reliable traversal and rewriting.
- The representation has a clean relationship with a separate CPS IR.
- Core remains checkable after transformations.
- The concrete representation should be selected through implementation experiments rather than abstraction preference alone.

Candidate encodings may include:

- direct first-order Freer-like representation;
- value/computation split;
- explicit bind/step representation;
- explicit continuation graph variants.

The initial Core work should compare concrete representations using actual compiler operations rather than only theoretical criteria.

Useful test cases include:

- pure evaluation;
- beta reduction;
- ADTs and match;
- effect operation;
- handler;
- Core → CPS;
- CPS → Core;
- opaque CPS fragment;
- typed rewriting.

---

## 11. Core and CPS as complementary representations

Core and CPS should be separate IRs.

They are expected to make different compiler transformations natural.

A transformation may be possible in both representations while being significantly simpler and safer in one.

This motivates a longer-term model where optimization can move between representations rather than following a permanently linear pipeline.

Conceptually:

```text
Core
  → Core transform
  → CPS
  → CPS transform
  → Core
  → ...
```

Optimization may eventually become graph search over:

```text
representation
+
program state
+
legal transformations
```

Representation changes are themselves transformations.

This is not an immediate optimizer requirement. It is architectural pressure on Core/CPS design.

Current work should avoid assuming that Core → CPS is permanently irreversible.

---

## 12. Opaque CPS regions in Core

A CPS → Core transformation can be total by allowing CPS fragments that cannot be reconstructed structurally as normal Core to appear as opaque Core regions.

Conceptually:

```text
OpaqueCps {
    fragment,
    typed interface
}
```

Core cannot inspect CPS structure inside such a region.

It may reason only through statically established interface facts.

Depending on those facts, Core may be able to:

- retain the region;
- move it;
- compose around it;
- lower it back to CPS.

This allows structuredness to vary rather than requiring every CPS program to reconstruct perfectly into high-level Core.

The detailed representation remains speculative.

---

## 13. Compiler transforms and correctness

Different graph representations require different rewrite rules.

The project should not force one universal rewrite formulation if representation-specific rules are simpler and easier to implement correctly.

A principle worth preserving is:

> Prefer changing representation over implementing an unnatural transformation in the wrong representation.

Transform correctness should rely on statically established facts.

Search or scheduling may be heuristic, but admissibility should remain checkable.

A useful long-term division is:

```text
search
    heuristic

transform applicability
    statically checked

resulting IR
    revalidated
```

Future ML-guided optimization, if explored, should rank or propose legal transformations rather than becoming part of the trusted semantic core.

---

## 14. Propositions, laws, and proofs

This is a future language direction, not an immediate requirement.

The current conceptual distinction is:

### Proposition

A proposition is a general, type-level semantic relation or predicate.

Examples:

```text
Idempotent(F)
Commutes(F, G)
Associative(Op)
```

Propositions should eventually be expressible in Ash rather than limited to a built-in compiler catalogue.

### Law

A law is a required instance of a proposition for specific program entities.

For example:

```text
Idempotent(normalize)
```

The word `law` is intentionally stronger from the user perspective: it states something that the program is required to obey.

### Proof

A proof establishes a law statically.

The intended development trajectory is:

```text
no laws
→ propositions + law declarations
→ propositions + laws + proofs
```

The intermediate stage remains useful long-term.

An unproved law is an explicit assumption.

It can be observed by tooling and used for:

- QA;
- external analysis;
- generative property testing;
- tracking production assumptions.

An assumed law does not become a compiler optimization fact merely because it has survived testing.

---

## 15. Generative testing of laws

A law is a single semantic obligation.

Testing and proof are different ways of interrogating it.

For example, an assumed idempotence law may generate attempts to falsify:

```text
forall x:
    f(f(x)) == f(x)
```

One counterexample refutes the law.

Large numbers of passing generated cases do not prove it.

The distinction between unproved, tested, and proven must remain explicit.

The intended principle is:

> The law is the obligation; testing attempts to falsify it; proof establishes it.

### Search and exploration

The future testing direction is to explore inputs and executions that make
plausible faults observable. QuickCheck-style generation is one starting point.
AFL-style coverage feedback could guide exploration, but coverage is only one
signal. Even complete coverage under a chosen metric does not establish that a
trace exposing a fault has been executed. Values, operation ordering, and state
relationships can differ while exercising the same branches.

Candidate feedback includes code coverage, boundary values, new state
transitions, and domain-specific classifications. A case may remain useful even
when it adds no code coverage. Passing results mean no counterexample was found
within the recorded search and budget; they do not discharge the law or authorize
compiler optimization.

### Library composition and supporting capabilities

Generators and search strategies appear to be library concerns. The architectural
pressure is to support their definition and composition without committing to
language syntax, a library API, or a particular search algorithm.

A useful conceptual distinction is between constructing candidates and deciding
which candidates to explore next. Composition could include:

- constructing larger values from smaller generators, including choices that
  depend on previously generated values or model state;
- combining fresh generation, mutation of retained cases, boundary exploration,
  and bounded enumeration;
- allocating effort among strategies using observations from earlier runs.

Adaptive exploration needs to retain state and consume execution feedback.
Controllable, replayable generation choices could let a search strategy reuse a
generator while changing how it explores those choices. Automatically derived
generators could supply defaults, with libraries adding domain knowledge. These
are capabilities to investigate, not a selected representation or protocol.

Compiler or runtime support may be needed to collect observations; the policy
using them can remain in a library. For tests of Ash programs, investigate
coverage associated with Ash/Core execution sites: host coverage of the evaluator
can emphasize interpreter machinery rather than distinguish branches in the
tested program. Testing the evaluator itself has a different coverage target.

### Evaluation pressures and open questions

- Type-correct generation does not ensure semantic preconditions. Compare
  construction of valid inputs with rejection and feedback-guided search; keep
  discarded cases distinct from successful checks.
- Preserve fresh exploration alongside adaptive search. Coverage can plateau
  while relevant values and executions remain unexplored.
- Replay must account for adaptive search history. Retained concrete cases or
  generation choices may be needed beyond an initial random seed.
- Shrinking should preserve the failure and its preconditions, without requiring
  all coverage discovered during exploration to remain.
- Effectful laws need explicit initial conditions and observations for comparing
  executions. Search cannot supply a missing definition of equivalence.
- Compare fault discovery under equal wall-clock budgets, including observation
  overhead, rather than judging strategies by coverage alone. Historical
  regressions and deliberately seeded faults could provide evidence, while their
  selection may bias the comparison.

No implementation or experiment is selected here. A later experiment should
compare ordinary generation with guided alternatives on representative laws,
including sparse preconditions, branch-heavy behavior, and algebraic properties
where coverage provides little guidance.

### Research references

- Lampropoulos, Hicks, and Pierce,
  [Coverage Guided, Property Based Testing](https://lemonidas.github.io/pdf/FuzzChick.pdf)
  (2019): FuzzChick combines QuickChick with coverage feedback and type-aware
  mutation. Its abstract-machine experiments show improved fault discovery for
  sparse preconditions; carefully tuned handwritten generators can still do
  better. This supports investigating guided search, not a general performance
  claim for Ash.
- Padhye et al.,
  [Semantic Fuzzing with Zest](https://people.eecs.berkeley.edu/~ksen/papers/zest.pdf)
  (2019): Zest mutates the parameters underlying QuickCheck-style generators and
  uses coverage and input validity as feedback. Its structured Java benchmarks
  provide an alternative to direct typed-value mutation. Neither approach is
  selected for Ash.

---

## 16. Compiler use of laws

The trusted compiler optimization path should use only facts established by Ash's static semantics.

Eventually, proven laws may supply compiler facts.

Assumed but unproved laws should not authorize normal correctness-critical optimization.

The compiler should not need to hardcode the logical expression defining every proposition.

Propositions are type-level Ash expressions that the compiler can interpret or normalize statically.

Transforms should consume the fact that a required proposition has been established.

Conceptually:

```text
facts ⊢ RequiredProposition(entity)
```

rather than:

```text
if proposition_name == "idempotent" ...
```

The compiler may understand only a selected subset of proposition identities for transforms.

User-defined propositions may still exist without optimizer meaning.

---

## 17. Future compiler scripting

A distant possibility is allowing transforms to be written in Ash or distributed in libraries.

Conceptually:

```text
transform collapse_nested_call<F>
where Idempotent(F)
```

This is explicitly downstream.

It should not influence immediate language complexity beyond avoiding architecture that makes safe, typed transform APIs impossible.

Future transforms should operate through checked IR interfaces and should be revalidated by the compiler.

---

## 18. Documentation and communication style

Writing quality is part of engineering quality.

Project documents should prefer plain, direct language.

Principles include:

- avoid unnecessary jargon;
- prefer short words where they are equally precise;
- prefer active voice;
- remove words that add no information;
- avoid fashionable abstractions and architecture-by-adjective;
- distinguish facts, decisions, and ideas explicitly;
- keep explanation proportional to commitment;
- avoid overexplaining;
- avoid overdesigning.

Technical vocabulary is appropriate where it names a stable concept.

Words such as:

- bounded;
- robust;
- extensible;
- scalable;
- explicit;
- principled;
- modular;
- compositional;

should normally be followed by the concrete property they claim.

Instead of:

> Core is extensible.

Prefer:

> Adding an effect family does not require adding a new recursive Core expression form.

A useful general rule is:

> Prefer nouns and verbs over adjectives.

Orwell's writing rules are a useful influence, not a rigid formal standard.

---

## 19. Tooling the development discipline

The process should not rely on contributors manually maintaining large amounts of metadata.

At the same time, process tooling must not become another major project.

The initial system should be small.

Possible progression:

### Stage 0

Plain repository structure and templates.

### Stage 1

Validation tooling:

- stable artifact IDs;
- unique IDs;
- valid references;
- required sections;
- artifact status validation.

### Stage 2

Derived artifact/reference graph.

### Stage 3

History and context queries.

Examples:

```text
What options have we considered for Core representation?

Why did we choose this parser architecture?

What proposal introduced this semantic rule?

What future features depend on this decision?
```

### Stage 4

Agent-oriented context assembly.

Tooling should be local and repository-based.

No external database should be required.

The graph should be derivable from repository content and git history.

---

## 20. Design archaeology

The history system should preserve choices, not merely changes.

A useful historical query is:

> What options have we considered for X, and why?

The answer should reconstruct:

- alternatives;
- experiments;
- decisions;
- reasons for rejection;
- current direction;
- relevant specification state.

Current artifacts should contain only current knowledge.

Historical reasoning remains recoverable through git history, tags, logs, and artifact references.

---

## 21. Agent support

The repository should support new and experienced human contributors as well as design, implementation, QA, documentation, and planning agents.

Agents should not be expected to remember Ash.

They should reconstruct the context needed for the task.

The project succeeds when an agent can find:

```text
What exists?
Why?
What is changing?
What do I need to do?
What remains uncertain?
```

without reading large amounts of irrelevant material.

The primary purpose of development artifacts is therefore:

> context reconstruction for future contributors and agents.

---

## 22. Immediate reboot work

Before substantial language implementation, establish:

1. repository purpose and historical relationship;
2. development and artifact model;
3. specification methodology;
4. writing/communication guidelines;
5. initial trajectory;
6. Core representation research/design note;
7. parser architecture research/design note;
8. tiny current specification;
9. first implementation tasks.

Do not migrate the historical Ash documentation wholesale.

Use it as reference when a current decision needs historical evidence.

The first implementation should remain intentionally small enough that parser, type-system, and Core architecture can be corrected cheaply.

---

## 23. Guiding test

For process:

> Can a contributor reconstruct the minimum sufficient context for a decision quickly and verify where that context came from?

For specification:

> Does the canonical spec describe exactly the Ash that exists on `main`?

For design:

> Does future thinking prevent obvious mistakes without forcing speculative implementation today?

For implementation:

> Are accepted language constructs complete through their current semantic and execution route?

For writing:

> Does every sentence reduce uncertainty?

These are the main constraints for the reboot.
