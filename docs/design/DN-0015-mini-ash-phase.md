# DN-0015: Mini-Ash Phase

- ID: `DN-0015`
- Status: exploring
- Related: [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md), [DN-0002: Core Representation](DN-0002-core-representation.md), [DN-0003: Parser Architecture](DN-0003-parser-architecture.md), [DN-0005: Surface Function Definitions](DN-0005-surface-function-definitions.md), [DN-0006: Initial Type System](DN-0006-initial-type-system.md), [DN-0007: Data and Pattern Typing](DN-0007-data-and-pattern-typing.md), [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md), [DN-0009: Effects, Handlers, and Continuations](DN-0009-effects-handlers-and-continuations.md), [DN-0013: Session and Resource Protocol Stress Tests](DN-0013-session-and-resource-protocol-stress-tests.md), [DN-0014: Finite Kinds and Promotion](DN-0014-finite-kinds-and-promotion.md), [DN-0017: Resource Management and Storage Policy](DN-0017-resource-management-and-storage-policy.md), [DN-0018: Runtime-Established Static Evidence](DN-0018-runtime-established-static-evidence.md)

> This design note is informative. It does not define current Ash, accept
> Mini-Ash semantics, or accept a parser, Core, typing, or evaluation
> architecture.

## Question

How should Ash use a growing pure-functional corpus to evaluate syntax,
semantics, representations, typing, parsing, diagnostics, transformations, and
evaluation before retaining the first working Mini-Ash interpreter?

## Context

Current Ash has no implemented language semantics. The intended phase result is
not a disposable prototype: it is a retained single-file interpreter for a
coherent pure-functional subset, with normative specification and tests.
Component experiments performed before decisions remain disposable evidence.

The initial feature pressure is:

- primitive values;
- immutable bindings;
- functions and applications;
- recursion;
- algebraic data types;
- pattern matching;
- basic rank-1 parametric polymorphism.

This list starts the evaluation corpus rather than fixing one release proposal.
Experiments may add features when another case is needed to judge complexity,
composition, extension, diagnostics, or a component boundary. The design notes
on effects, continuations, identities, lifetimes, modules, resolution, hooks,
protocols, multiplicity, finite kinds, CPS, propositions, and proofs provide a
useful but incomplete snapshot of later pressure. They do not promise a future
feature inventory.

The suggested rules in current design notes carry strong design evidence even
though they remain informative. A comparison should begin from the relevant
suggested rules. It should introduce an alternative to answer a named concern
and should record contrary evidence before departing from a suggestion.

## Constraints

### Retain complete semantic increments

Mini-Ash should land through several coherent proposals rather than one large
language proposal. Each retained user-visible increment updates syntax, static
semantics, dynamic semantics, implementation, positive and negative tests, and
the normative specification together.

Every sufficiently complete semantic increment should produce an executable
path from one source file through parsing, elaboration and typechecking, typed
representation validation, and evaluation. Mini-Ash need not support modules.
The executable should reject invalid programs before evaluation, render
source-located diagnostics, return a nonzero status for failure, and run every
valid program specified by the increment.

An increment may retain richer internal machinery when later pressure justifies
it. Unreachable machinery needs named invariants and tests, but it remains
implementation infrastructure rather than current Ash semantics and stays out
of the normative specification.

### Use small-step operational semantics

The leading phase direction is one primary small-step account of operational
behavior. Explanatory views may derive from it but should not become a competing
normative semantics. The specification method requires an accepted decision
before substantial normative semantics are written.

The retained evaluator must behave consistently with the accepted small-step
rules. An experimental evaluator may compare an approach, but it cannot silently
become a second semantic authority.

### Keep representations typed and inspectable

Every retained semantic representation should state and validate its typing and
structural invariants. A representation boundary is justified only when the
conversion establishes named facts and makes a consumer simpler enough to
warrant another form.

Candidate pipelines may use surface, resolved, typed, elaborated,
pattern-preserving, or lowered representations. The phase does not assume that
the parser produces Core, that parser and typechecker share one representation,
or that one AST-to-Core boundary is permanent.

The strong Core hypothesis is Freer-like in spirit: pure results and future
operation families should remain separate from the recursive computation
structure, and adding an operation family should not require extending one
monolithic recursive sum and every unrelated consumer. Mini-Ash need not
manufacture an `Impure` form before it has effectful operations.

If a retained Mini-Ash representation uses continuations, they should be
explicit inspectable data rather than Rust closures. A closure-based
implementation may serve as a disposable baseline. Retaining one would require
evidence that typing, validation, traversal, transformation, and downstream
continuation pressure remain satisfiable, followed by revision of the current
Core constraint.

CPS conversion belongs primarily to later effect work. If Mini-Ash requires
continuations, a candidate should provide at least a theoretical CPS account.
Otherwise it should record the relevant extension seam and redesign risks
without implementing CPS prematurely.

Later effect experiments should use a non-escaping one-shot handler as the
primary continuation case, then add discard, escape, and repeated resumption as
separate pressures. Continuation modes may eventually appear as type indices,
but usage, capture, lifetime, and handler replayability remain distinct checking
obligations. This ordering does not add handlers, continuation typing, or CPS to
the Mini-Ash deliverable. It asks Mini-Ash representation candidates to preserve
an explicit, typed extension seam and to record any redesign that the later
control rules would require.

### Make composition observable

“Composable” and “extensible” name comparison properties, not conclusions.
Candidates should demonstrate that:

- adding a grammar construct changes a bounded grammar component without
  restructuring unrelated parsing code;
- adding a language construct or downstream operation family does not require
  expanding one central dispatch function or monolithic recursive
  representation throughout the compiler;
- representation passes have explicit input, output, and validation contracts;
- typechecking, evaluation, and transformations consume the representation that
  expresses the invariants they require;
- feature-specific components compose without hiding precedence, ambiguity,
  typing, evaluation-order, or diagnostic behavior.

A generated parser, parser combinators, and a modular hand-written parser remain
possible. A single hand-written function that accumulates every grammar form is
not the preferred baseline.

### Design diagnostics with the language

Each corpus stratum should contain representative mistakes and the intended
diagnostics. Elm provides a guide for plain explanation and focused correction;
Rust provides a guide for precise spans, related locations, and structured
supporting context.

A diagnostic should identify the problem in user terms, select a precise primary
span, label interacting locations when relevant, show expected and found forms,
retain useful context without exposing internal IR vocabulary, and suggest a
correction only when the compiler can justify it. Recovery should limit
cascading errors.

Representations and lowerings must preserve enough source provenance and
semantic context to produce these errors. A candidate that computes the correct
result but loses the information required for useful diagnostics fails the
comparison.

### Account for future pressure without implementing it

For each downstream feature:

- define and test a mechanism precisely when Mini-Ash already needs it;
- document an extension seam and preserved invariants when the feature can be
  added without changing current behavior;
- record the redesign risk when the feature would change a fundamental
  representation or interface;
- use a theoretical derivation or worked example when it distinguishes
  candidates;
- build a disposable probe only when the interaction remains uncertain.

A simple Mini-Ash candidate should not lose merely because it does not already
implement effects, advanced typing, multiplicities, identities, protocols, CPS,
or proofs. Mini-Ash needs a coherent typed subset; later typing may be much more
expressive.

## Candidate directions

### Corpus-led staged convergence

The leading direction has three layers:

1. A growing evaluation corpus supplies valid programs, rejected programs,
   provisional grammar fragments, typing cases, small-step rules, evaluation
   traces, source spans, diagnostics, and candidate representations.
2. Component research evaluates parser, representation, typechecker, evaluator,
   and transformation designs against shared corpus slices. Written comparison
   is sufficient when it decides the question; bounded prototypes supply missing
   evidence.
3. Accepted component decisions authorize several retained semantic proposals
   that cumulatively produce Mini-Ash.

A provisional product decomposition is:

1. primitive values, variables, immutable bindings, monomorphic functions, and
   applications;
2. recursive definitions;
3. algebraic data types, constructors, and pattern matching;
4. rank-1 parametric polymorphism.

Research may change these boundaries when two features require one coherent
semantic account.

### Whole-subset proposal

One proposal could define all Mini-Ash behavior before implementation. It would
centralize interactions but create a large review and evidence boundary. A
change to one component could reopen the whole proposal.

### Immediate retained walking skeleton

A very small executable could become product code before the growing corpus has
exercised recursion, data, patterns, polymorphism, and later pressure. It would
provide early end-to-end feedback but risk making lightly tested parser and
representation boundaries current architecture.

## Evidence and experiments

### Corpus strata

Grow the corpus through:

1. [primitive values, variables, immutable bindings, functions, and
   applications](DN-0016-first-mini-ash-corpus.md);
2. recursive definitions and applications;
3. algebraic data types and constructor values;
4. pattern bindings, matching, and coverage failures;
5. basic rank-1 polymorphism with explicit typed operations.

Each stratum should add representative valid programs, rejected syntax and
typing cases, provisional grammar, typing judgments, small-step rules,
evaluation traces, source spans and diagnostics, and candidate representation
forms.

### Comparison criteria

Record for each candidate:

- which invariants its types express and its validators check;
- the number and locality of unrelated changes required by a new corpus feature;
- grammar composition, precedence, ambiguity, recovery, and span behavior;
- representation size, ownership constraints, traversal, and transformation
  mechanics;
- typechecking and evaluation complexity;
- source-provenance preservation and diagnostic quality;
- failure modes and rejected invalid states;
- downstream extension seams and known redesign risks.

### Prototype boundary

An experiment must name one component question, its corpus slice, comparison
criteria, and the condition under which code is discarded. It need not implement
the end-to-end interpreter. Parser, evaluator, transformer, representation, and
typechecker probes may be independent when their question permits it.

Experimental code is discarded after its evidence is recorded. Code becomes
retained product implementation only through an accepted decision or proposal
and an active task; an experiment does not grow into product architecture by
accident.

### Product evidence

A retained increment requires:

- accepted syntax, typing, and small-step behavior;
- typed representation contracts and validation;
- parser, typechecker or elaborator, and evaluator behavior;
- positive, negative, diagnostic, validation, and executable integration tests;
- agreement between the evaluator and operational rules;
- a normative specification update;
- a single-file executable for the programs the increment specifies.

## Open questions

- What exact surface program structure and entry point should the first
  executable accept?
- Which initial feature boundaries form coherent semantic proposals?
- Which representation stages are justified by distinct invariants and
  consumers?
- Which parser organizations merit comparison against the growing corpus?
- What concrete Rust encoding provides feature-local Core extension while
  retaining useful exhaustive reasoning?
- Which Mini-Ash typing and elaboration rules should be accepted from the strong
  suggestions in DN-0006 through DN-0008?
- Which richer internal mechanisms are justified before their surface exposure?
- Which downstream pressures can be settled by analysis, and which require a
  disposable probe?
