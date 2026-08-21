# DN-0016: First Mini-Ash Corpus Stratum

- ID: `DN-0016`
- Status: exploring
- Related: [DN-0002: Core Representation](DN-0002-core-representation.md), [DN-0003: Parser Architecture](DN-0003-parser-architecture.md), [DN-0005: Surface Function Definitions](DN-0005-surface-function-definitions.md), [DN-0006: Initial Type System](DN-0006-initial-type-system.md), [DN-0007: Data and Pattern Typing](DN-0007-data-and-pattern-typing.md), [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md), [DN-0015: Mini-Ash Phase](DN-0015-mini-ash-phase.md)

> This design note is informative. It governs a provisional evaluation corpus
> and bounded experiments. It does not define current Ash, accept syntax or
> semantics, or accept a parser, Core, typing, or evaluation architecture.

## Question

What shared evidence should the first Mini-Ash corpus stratum provide before Ash
accepts and retains a monomorphic pure-functional increment?

## Context

[DN-0015](DN-0015-mini-ash-phase.md) directs Mini-Ash research through a growing
corpus rather than an immediate retained walking skeleton. The first stratum
combines primitive values, variables, immutable bindings, monomorphic functions,
and applications because together they expose scope, evaluation order,
typed representation, source provenance, and diagnostics.

The corpus is split into [linked evidence documents](mini-ash/first-stratum/)
rather than placing grammar, typing, dynamics, diagnostics, and representation
discussion in one note. Stable case IDs connect the documents. A case remains
provisional until an accepted change proposal selects it as evidence for an
implemented semantic increment.

## Constraints

- The corpus must distinguish language questions from implementation questions.
- Each case must connect source, static facts, dynamic behavior, and diagnostics
  without treating any one candidate representation as authoritative.
- Equational and inline operational definitions remain distinct surface
  mechanisms with different definitional strengths. Equivalent cases may lower
  to the same or similar callable Core without erasing clause, match, body,
  provenance, diagnostic, or tooling differences prematurely.
- Definition and application grouping follow the function type. Successive
  equational patterns and applications follow nested arrows; an operational
  comma-separated parameter tuple and its application follow one product
  domain.
- Provisional grammar uses `ebnf` fences, and provisional typing and operational
  rules use `sequent` fences when they are inference rules. Prose must explain
  every formal fence.
- The retained first-stratum boundary excludes recursion, algebraic data types,
  general pattern matching, polymorphism, effects, modules, mutation, and I/O.
  Boolean-pattern and parameter-grouping probes may cross that boundary only to
  expose the defining relationship between equation clauses, explicit matches,
  nested arrows, and product-domain operational functions.
- Functions and any evaluation state remain inspectable data. Retained designs
  must not represent Ash functions or continuations as Rust closures.
- A typed representation candidate must state and validate scope, type, and
  source-provenance invariants before evaluation.
- Adding a corpus form should exercise feature-local parser, representation,
  typing, and evaluation components rather than require unrelated central
  rewrites.

## Candidate directions

### Shared corpus with selective probes

The leading direction defines common programs, rules, traces, errors, and
representation pressure before implementing component probes. Written analysis
settles a question when it exposes a clear difference. Code is reserved for
Rust encoding, composition, recovery, traversal, validation, or evaluation
behavior that remains uncertain.

### Competing vertical interpreters

Multiple disposable end-to-end interpreters would expose boundary costs early,
but they would duplicate work and make a difference harder to attribute to one
component. A thin vertical trace may test an interface, but a full competing
interpreter is not the default experiment.

### Semantics and Core before surface syntax

Constructing terms directly would isolate typed representation and evaluation,
but it would postpone parser and diagnostic pressure. Independent Core probes
may construct inputs directly, while the shared corpus continues to carry
provisional source and source-located failures.

## Evidence package

The [first-stratum index](mini-ash/first-stratum/) owns case identity and links
the evidence slices:

- [programs](mini-ash/first-stratum/programs.md) define representative valid and
  rejected inputs;
- [grammar](mini-ash/first-stratum/grammar.md) records one provisional surface
  grammar and unresolved alternatives;
- [typing](mini-ash/first-stratum/typing.md) records provisional declarative
  judgments and expected case outcomes;
- [dynamics](mini-ash/first-stratum/dynamics.md) records provisional small-step
  rules and representative traces;
- [diagnostics](mini-ash/first-stratum/diagnostics.md) records source spans,
  structured reasons, recovery expectations, and rendered-message criteria;
- [representations](mini-ash/first-stratum/representations.md) records invariants
  and concrete pressure on candidate boundaries.

These documents form one comparison corpus. None has independent semantic or
architectural authority.

## Evidence and experiments

Each component experiment must name one question, the case IDs it uses, the
candidates it compares, the distinguishing criteria, and its disposal
condition. Parser, representation, typechecker, evaluator, and transformation
probes may proceed independently when they do not share an unresolved choice.

The comparison records:

- which invariants types express and validators check;
- whether grammar and compiler changes remain local when a case adds one form;
- precedence, ambiguity, recovery, span, and source-provenance behavior;
- ownership, traversal, rewriting, and validation mechanics in Rust;
- typechecking and evaluation complexity;
- diagnostic structure, rendered clarity, and cascade control;
- agreement between direct evaluation and the provisional reduction traces;
- downstream extension seams and redesign risks without implementing future
  features.

Prototype code is disposable. Record measurements, counterexamples, and
conclusions in the governing design note, then remove the code. Retaining a
component requires an accepted architectural decision and an implementation
task. Retaining language behavior additionally requires an accepted change
proposal whose implementation, tests, executable path, and specification update
land together.

## Tracked experiment program

This table tracks current research progress. `Ready` means that the governing
question, corpus cases, comparison criteria, and retention boundary are
sufficient to begin. `Pending` means that an earlier comparison must finish
first. A status does not accept syntax, semantics, or architecture.

| Work | Status | Evidence scope | Completion condition |
| --- | --- | --- | --- |
| Corpus consistency review | Complete | Every `V`, `X`, `P`, `R`, `T`, and `I` case across all evidence slices | No blocking disagreement remains among syntax, scope, typing, dynamics, diagnostics, and representation obligations. |
| [Specification method](mini-ash/first-stratum/comparisons/specification-method.md) | Complete | First-stratum small-step rules and traces, plus downstream runtime-state pressure | The written comparison favors small-step semantics as the one primary normative method and identifies the decision boundary without accepting it. |
| [Core representation](mini-ash/first-stratum/comparisons/core-representation.md) | Complete | `V-001` through `V-008`, `X-001`, `X-003`, and `I-001` through `I-004` | The three named encodings are compared on types, validation, traversal, transformation, provenance, ownership, and downstream extension pressure. |
| [Resolution, typechecker, and elaboration](mini-ash/first-stratum/comparisons/static-semantics-organization.md) | Complete | `V-001` through `V-008`, `R-001`, `R-002`, `T-001` through `T-004`, and `X-001` through `X-003` | Candidate rule boundaries and data flow are compared on binder identity, scope, expected typing, grouping, patterns, structured failures, and provenance. |
| [Evaluator](mini-ash/first-stratum/comparisons/evaluator-architecture.md) | Complete | `V-001` through `V-008`, `X-001`, and `X-003` | A direct evaluator and an explicit first-order machine are compared against the reduction rules, traces, lexical capture, inspectability, and host-stack risk. |
| [Parser architecture](mini-ash/first-stratum/comparisons/parser-architecture.md) | Complete | The provisional grammar, every valid source presentation, and `P-001` through `P-003` | At least two composable organizations are compared on locality, precedence, ambiguity, recovery, spans, diagnostics, and tooling pressure. |
| [Component convergence](mini-ash/first-stratum/comparisons/component-convergence.md) | Complete | Completed component comparisons | The evidence identifies which choices require architectural decisions and records unresolved alternatives without selecting them implicitly. |
| [Architectural decisions](../decisions/README.md) | Complete | The completed convergence record and five decision boundaries | AD-0004 through AD-0008 accept only the converged non-language choices and keep the listed syntax, semantics, and concrete implementation mechanisms unresolved. |
| [First semantic proposal](../proposals/CP-0001-first-mini-ash-nucleus.md) | Accepted | Accepted specification method, component decisions, and `V-001` through `V-008` | CP-0001 defines the authorized semantic transition and evidence required for implementation without describing current Ash. |
| [First implementation task](../tasks/TASK-0006-implement-first-mini-ash-nucleus.md) | Active | Accepted CP-0001 and AD-0004 through AD-0008 | TASK-0006 implements the executable, tests, specification, and documentation as one retained increment. |

The completed consistency review found no blocking disagreement in the named
cases. Grouping parentheses erase consistently before typing and dynamics,
X-003 has the product typing and reduction rules needed to derive its result,
and every rejected case has a compatible stage and diagnostic obligation. The
grammar admits a few uncased generalizations, including anonymous
multi-parameter functions and products above arity two. Parser experiments may
observe those forms, but only named cases carry static or dynamic expectations;
the grammar must be narrowed or the extra forms specified before a semantic
proposal relies on them.

The railroad and sequent renderers still need the conformance updates recorded
by [AD-0003](../decisions/AD-0003-formal-notation-fences.md). Those external
tool updates do not change the canonical Markdown or block component research.

## Convergence gates

1. Review the corpus for agreement among programs, grammar, typing, dynamics,
   diagnostics, and representation pressure. This gate is complete.
2. Compare component candidates against only the cases needed to answer each
   question. This gate is complete.
3. Accept the specification method and converged component architectures in
   separate decisions. This gate is complete through AD-0004 to AD-0008.
4. Propose and accept the first user-visible semantic increment. This gate is
   complete through CP-0001.
5. Implement the accepted increment as a retained single-file executable. This
   gate is active through TASK-0006.

## Open questions

- Which concrete Rust encoding composes typed Core fragments while retaining
  exhaustive validation and useful traversal?
- Which concrete event and tree types implement AD-0005 without deciding trivia
  or layout prematurely?
- How should AD-0008's frame transitions compose by Core feature without one
  monolithic transition function?
