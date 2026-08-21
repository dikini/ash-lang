# AD-0008: Explicit Evaluator Machine

- ID: `AD-0008`
- Status: accepted
- Related: [AD-0004: Small-Step Semantic Method](AD-0004-small-step-semantic-method.md), [AD-0007: Typed Core Dialects](AD-0007-typed-core-dialects.md), [DN-0016: First Mini-Ash Corpus Stratum](../design/DN-0016-first-mini-ash-corpus.md), [first-stratum evaluator comparison](../design/mini-ash/first-stratum/comparisons/evaluator-architecture.md)

## Decision

The retained Mini-Ash evaluator is an explicit first-order machine over
validated typed Core.

The machine runs through an explicit control loop. Its current evaluation
contexts are typed frame data rather than Rust activation records or closures.
Its lexical function values contain inspectable Ash code identity or body data
and captured Ash environments. Application transitions make function,
argument, body, caller-environment, and captured-environment boundaries
explicit so the machine can implement the applicable accepted semantics
without relying on the host call stack.

Machine transitions return structured internal or runtime failures rather than
using Rust panics or stack overflow as Ash behavior. Optional traces observe
control transitions without becoming semantic authority.

Ordinary evaluation frames are not surface or Core effect continuations. This
decision does not make them capturable, resumable, duplicable, or discardable by
Ash programs and does not decide continuation multiplicity. Later effect and
handler work must identify any continuation boundary and its typing explicitly.

The concrete composition of frame handlers, Core code identity, environment
storage, and resource accounting remains implementation work. Transition
ownership must remain reviewable as Core features are added, but this decision
does not select a Rust composition mechanism.

## Context

The first corpus compared a direct host-recursive evaluator with a loop-driven
machine over the same typed expressions. Both agreed on values and complete
left-to-right entry-event sequences for the valid and cross-stratum cases. Both
used inspectable closure data.

The direct evaluator was about half the evaluator-module size in the disposable
probe and closely followed expression recursion. Its Rust call depth grew with
source-expression depth. A 2,000-level well-typed addition tree overflowed the
test thread's host stack and aborted the process instead of returning a
structured failure.

The machine completed that case with one Rust loop and 2,000 explicit frames.
Its frame variants also made function-before-argument, left-before-right,
binding, tuple, and match control inspectable. Current host-stack independence
and evaluation-order evidence justify the machinery without relying only on
future effects.

## Consequences

- Evaluation depth grows in explicit machine storage rather than Rust call
  depth.
- Each Core feature that evaluates must define its control transitions and any
  frame data needed to suspend surrounding work.
- Lexical capture, code, environments, and current control remain inspectable
  compiler/runtime data.
- The evaluator consumes only independently validated Core dialects.
- Machine behavior is tested against AD-0004's small-step rules and does not
  define language semantics itself.
- A direct recursive evaluator may remain a disposable differential oracle but
  is not a required second retained execution path.
- Resource exhaustion needs an explicit structured policy when implementation
  evidence makes one necessary.
- This decision does not accept effects, handlers, CPS, continuation
  multiplicity, concurrency, cancellation, integer behavior, an environment
  allocator, or stable Core node identities.

## Verification

Evaluator implementation and later feature work must provide:

- agreement with every applicable valid corpus result and representative
  small-step trace;
- explicit evaluation-order tests for each form whose order is defined by the
  applicable accepted language specification;
- lexical-capture and higher-order-function tests over inspectable closure data;
- deep valid input that exercises explicit frame growth without proportional
  Rust call-stack growth;
- structured failures for invalid validated-input assumptions and runtime
  resource failures that the implementation claims to handle;
- no Rust closure as the sole representation of Ash functions, environments, or
  language control;
- reviewable transition ownership as Core features are added;
- differential tests for any independently retained evaluator expected to
  implement the same Core behavior.
