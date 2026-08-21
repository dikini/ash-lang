# AD-0004: Small-Step Semantic Method

- ID: `AD-0004`
- Status: accepted
- Related: [AD-0008: Explicit Evaluator Machine](AD-0008-explicit-evaluator-machine.md), [DN-0001: Ash Reboot Foundations](../design/DN-0001-reboot-foundations.md), [DN-0016: First Mini-Ash Corpus Stratum](../design/DN-0016-first-mini-ash-corpus.md), [first-stratum specification-method comparison](../design/mini-ash/first-stratum/comparisons/specification-method.md)

## Decision

Ash uses one small-step operational account as the primary normative method for
dynamic semantics.

When Ash has dynamic semantics to specify, the relation describes one
transition between expressions or runtime configurations. Runtime state such as
stores, handlers, suspended control, or scheduler data extends the
configuration rather than introducing a second primary semantic method.

Big-step judgments, result summaries, representative traces, executable
evaluators, and mechanized models may explain or validate behavior. They remain
derived or non-normative views and must not define behavior absent from the
small-step account. Evaluator implementation details such as allocation,
ownership, host-stack use, and diagnostic rendering are not language semantics.

This decision selects a specification method, not any Ash syntax or behavior.
Each language change still requires a change proposal, implementation, tests,
and specification update through the semantic workflow.

## Context

The first Mini-Ash corpus compared small-step rules, big-step judgments, and an
evaluator-as-specification approach. All three could state final results for
terminating pure expressions. The distinction appeared in strict left-to-right
evaluation, nested application, intermediate tuple behavior, divergence
pressure, and future suspended or interleaved control.

Small-step rules expose evaluation order and intermediate control without
choosing a direct evaluator or abstract machine. A big-step primary account
would need auxiliary control-sensitive relations as the language gains
divergence, handlers, suspension, or concurrency. An evaluator primary account
would turn one implementation's control and storage choices into semantic
authority.

The comparison found that the extra verbosity of small-step rules can be
managed through rule families, verbal explanations, and selected traces. Those
explanatory forms do not need independent normative status.

## Consequences

- Normative dynamic-semantics sections use one-step transitions and define any
  multi-step or result relation from them.
- Formal rules use the repository's `sequent` notation and have matching verbal
  explanations.
- Evaluation order, stuck states, divergence, and runtime configuration changes
  have one semantic owner.
- Retained evaluators and abstract machines are checked against the applicable
  transition rules rather than treated as semantic oracles.
- Explanatory big-step judgments and traces must be labeled as derived or
  non-normative.
- Future effects, handlers, concurrency, cancellation, and runtime state extend
  the transition configuration and do not trigger a switch of primary method.
- This decision does not choose congruence rules versus evaluation contexts,
  concrete syntax, observations, integer behavior, a proof framework, or an
  evaluator architecture.

## Verification

For every implemented semantic increment with dynamic behavior:

- the specification states the applicable one-step relation and values or
  terminal configurations;
- representative programs derive their required results through zero or more
  transitions;
- evaluation-order tests distinguish the intended transition sequence;
- retained evaluators agree with the required results and observable traces;
- derived explanations do not introduce behavior missing from the small-step
  account;
- later runtime state extends a named configuration with transition rules
  rather than creating another normative evaluation relation;
- documentation review checks each formal rule's notation, prose explanation,
  and authority label.
