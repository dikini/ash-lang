# First-stratum specification-method comparison

> This comparison is informative evidence governed by
> [DN-0016](../../../DN-0016-first-mini-ash-corpus.md). It does not accept a
> specification method or define current Ash semantics.

## Question

Can small-step operational semantics serve as Ash's one primary normative
account of dynamic behavior, while big-step explanations and executable
evaluators remain derived views rather than competing authorities?

## Scope and method

This written comparison uses the first-stratum reduction rules and traces. It
also checks whether each candidate leaves a direct path to later runtime state,
effects, explicit continuations, concurrency, and cancellation without
implementing those features. No prototype is required because the differences
are visible in the specification forms and their authority boundaries.

The comparison considers three candidates:

1. small-step rules are primary, while big-step explanations and evaluators
   must agree with their reflexive-transitive closure;
2. big-step rules are primary, with separate auxiliary accounts where
   evaluation order or intermediate control matters;
3. one retained evaluator or abstract machine defines behavior directly, and
   prose or rules explain that implementation.

## Criteria

A candidate should:

- give one complete account rather than split authority by construct;
- state strict left-to-right evaluation and intermediate control precisely;
- distinguish elaboration from runtime reduction;
- remain independent of the direct-evaluator or explicit-machine choice;
- support executable agreement tests without making tests semantic authority;
- extend to configurations containing stores, handlers, suspended control, or
  scheduler state;
- permit shorter derived explanations when they do not introduce new behavior;
- keep source diagnostics and provenance separate from runtime semantics.

## Corpus evidence

### Small-step as the primary account

The existing relation exposes each distinction needed by the corpus:

- `V-001` separates syntactic precedence from runtime reduction;
- `V-003` makes strict binding and resolved shadowing visible one step at a
  time;
- `V-008` exposes function-before-argument evaluation across nested
  applications;
- `X-001` separates definition elaboration, coverage checking, scrutinee
  evaluation, and arm selection;
- `X-003` exposes tuple element order and generated product destructuring.

The same relation can later range over configurations rather than expressions
alone. Adding a store, handler stack, scheduler state, or suspended continuation
changes the configuration and transition rules without requiring a second
meaning of evaluation.

Small-step rules are more verbose than a result-only relation. The first corpus
already offsets that cost by grouping related rules into families and providing
representative traces. A specification need not print every possible trace;
rules define the steps and selected traces explain them.

### Big-step as the primary account

A big-step judgment can state the final results of the terminating pure cases
compactly. It can serve as a useful derived explanation for examples such as
`V-002` or `V-006`.

As the primary account, it would need auxiliary structures to expose the order
tested by `V-008`, the intermediate product behavior in `X-003`, divergence once
recursion enters, and later suspension or interleaving. Those additions either
reconstruct a transition system inside the judgment or create a second
normative account for control-sensitive constructs. The smaller presentation
therefore does not remain smaller under the known pressure.

### An evaluator as the primary account

An executable evaluator makes behavior testable and avoids duplicating an
algorithm in prose. The corpus, however, deliberately compares a structured
direct evaluator with an explicit first-order machine. Making either candidate
normative before that comparison would turn an implementation choice into
language semantics.

Evaluator code also contains allocation, ownership, traversal, and diagnostic
mechanisms that are not observable Ash behavior. Treating the code as the
specification would make later refactoring a semantic review even when the
reduction relation and program results remain unchanged.

## Comparison

| Criterion | Small-step primary | Big-step primary | Evaluator primary |
| --- | --- | --- | --- |
| One semantic authority | Yes, if derived views are explicitly non-normative | At risk when control-sensitive constructs need a second account | Yes, but tied to one implementation |
| First-stratum results | Directly derivable | Directly derivable | Directly executable |
| Evaluation order | Explicit in congruence and calculation rules | Requires order in premises or auxiliary judgments | Explicit only through implementation control flow |
| Intermediate control | Explicit | Usually hidden | Representation-dependent |
| Divergence and suspension pressure | Natural transition behavior | Requires additional treatment | Depends on the chosen evaluator |
| Evaluator comparison | Both evaluators can be checked against one relation | Both can be checked for terminating results, with weaker trace comparison | One candidate becomes privileged before comparison |
| Explanatory brevity | Derived traces or result summaries remain available | Strongest property | Source code is concise only for implementers |
| Architecture independence | Preserved | Preserved until auxiliary control machinery is required | Not preserved |

## Conclusion

The evidence favors small-step operational semantics as the primary normative
method. Big-step judgments, result summaries, traces, and evaluator descriptions
may remain useful explanatory or validation views, but they should be derived
from or checked against the small-step account and must not define additional
behavior.

This evidence led to
[AD-0004](../../../../decisions/AD-0004-small-step-semantic-method.md). The
comparison did not itself accept that decision and remains informative.

## Accepted outcome

AD-0004 accepts these points:

- one small-step account is the primary normative dynamic semantics;
- the account covers ordinary and control-sensitive constructs rather than
  switching methods by feature;
- explanatory big-step views and traces are non-normative derivations;
- retained evaluators must agree with the applicable reduction rules;
- future runtime state extends the transition configuration rather than
  introducing another semantic authority.

The decision does not choose concrete Ash syntax, the first semantic increment,
an evaluator architecture, a proof framework, integer behavior, or the exact
rule organization for features not yet proposed.

## Remaining questions

- Should future specifications use direct congruence rules, evaluation
  contexts, or a checked presentation derived from one of them?
- Which observations beyond termination and returned values become public Ash
  behavior in later increments?
- Which mechanized checks, if any, are worth adding after the first retained
  semantics exists?

These questions affect presentation and later evidence. They do not require a
second primary semantic method.

## Retention boundary

This comparison uses written evidence only. It creates no experimental code to
retain or discard. Any later executable semantics checker requires separate
authorization and must not become semantic authority merely because it can run.
