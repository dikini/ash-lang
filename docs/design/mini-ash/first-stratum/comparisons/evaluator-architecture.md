# First-stratum evaluator-architecture comparison

> This comparison is informative evidence governed by
> [DN-0016](../../../DN-0016-first-mini-ash-corpus.md). It does not accept an
> evaluator architecture or define current Ash semantics.

## Question

Does the first pure evaluator benefit enough from explicit first-order control
and environment data to justify more machinery than a host-recursive evaluator?

## Scope and method

A disposable Rust probe implemented two evaluators over the same validated,
typed, resolved expression data:

1. a direct evaluator that recurses through Rust calls;
2. a loop-driven machine with explicit control, Ash environments, values, and
   typed evaluation frames.

Both candidates covered `V-001` through `V-008`, both `X-001` presentations,
and both `X-003` grouping shapes. The cross-stratum cases existed only to test
Boolean match, tuple evaluation, product destructuring, and nested curried
application. The probe did not implement parsing, typechecking, effects,
handlers, recursion, concurrency, or CPS.

Each evaluator recorded expression-entry events. The tests compared final
values and the complete event sequence for every case, then checked the
specific left-to-right sequences required by the representative `V-001`,
`V-008`, and `X-003` traces in [dynamics.md](../dynamics.md).

## Shared runtime data

Both candidates represented a lexical function value as inspectable Ash data:

```text
Closure {
    binder
    body
    environment: [(BinderId, Value)]
}
```

Application evaluated the function in the caller environment, then the
argument in the caller environment, then evaluated the body in the captured
environment extended by the parameter binding. Neither candidate used a Rust
closure for Ash code, capture, or control.

The probe used checked `i64` arithmetic and returned a structured host-overflow
failure. That choice kept the experiment from inheriting debug-versus-release
overflow behavior; it does not decide Ash's integer model, range, or overflow
semantics.

## Direct recursive evaluator

The direct candidate followed the typed expression structure. Its application
case was conceptually:

```text
closure = evaluate(function, caller_environment)
argument = evaluate(argument, caller_environment)
evaluate(closure.body, closure.environment + binding)
```

This form aligned closely with the prose meaning of lexical evaluation and was
the smaller implementation. Excluding shared expression, corpus, and test
code, the probe's direct-evaluator module occupied 155 lines.

Its language control lived partly in Rust activation records. Instrumentation
showed a 512-level nested addition reaching 513 host calls. A 2,000-level
well-typed addition tree overflowed the test thread's Rust stack and aborted the
process with `SIGABRT`; it could not return a structured evaluator failure.
The exact failure depth depends on host and build details. That dependence is
the finding: a source-program property reached an unreported host limit.

Adding a checked recursion limit could replace the abort with a failure, but it
would introduce a limit whose status and diagnostic would need separate design.
Trampolining the evaluator would instead reconstruct explicit control similar
to the machine candidate.

## Explicit first-order machine

The machine candidate used this control shape:

```text
Machine {
    control: Evaluate(term, environment) | Return(value)
    frames: [Frame]
}
```

Its frame family included the current evaluation contexts:

```text
AddLeft(right, environment)
AddRight(left_value)
MultiplyLeft(right, environment)
MultiplyRight(left_value)
EqualLeft(right, environment)
EqualRight(left_value)
Let(binder, body, environment)
ApplyFunction(argument, environment)
ApplyArgument(binder, body, captured_environment)
TupleLeft(right, environment)
TupleRight(left_value)
LetTuple(left_binder, right_binder, body, environment)
MatchBool(true_body, false_body, environment)
```

Every loop transition either decomposed one expression, returned one value to
the top frame, or completed evaluation. The frame variants made the
function-before-argument and left-before-right rules inspectable without
reconstructing them from Rust call order.

The machine module occupied 319 probe lines, a little more than twice the direct
module. Much of the difference was explicit frame declaration and return-path
dispatch. On the 512-level case it used one Rust loop and 512 frames. It also
completed the 2,000-level case that aborted the recursive candidate, again with
one Rust loop and 2,000 explicit frames.

These measurements compare control shape, not speed or production code size.
The probe cloned simple vector environments and reference-counted terms for
convenience. It did not measure allocation, sharing, or optimized environment
representations.

## Corpus comparison

| Pressure | Direct recursive evaluator | Explicit first-order machine |
| --- | --- | --- |
| `V-001` primitive order | Rust call order follows the rule | `AddLeft` and multiplication frames expose the order |
| `V-002` presentation convergence | Both elaborated terms return `42` | Both elaborated terms return `42` |
| `V-003` shadowing | Distinct binder identities and nested environments work | Distinct binder identities and nested environments work |
| `V-004` lexical capture | Inspectable closure environment works | Inspectable closure environment works |
| `V-005` higher-order application | Caller and captured environments remain distinct | `ApplyFunction` and `ApplyArgument` store the distinction |
| `V-008` nested application | Correct sequence is visible only through instrumentation or call inspection | Control and frame state expose the sequence directly |
| `X-001` Boolean match | Direct branch after recursive scrutinee evaluation | `MatchBool` frame records the suspended arms and environment |
| `X-003` product order | Recursive tuple calls evaluate left then right | Two tuple frames record left-to-right progress |
| Invalid runtime shape | Structured errors are possible after validation | Structured errors are possible after validation |
| Deep typed input | Host stack depth grows with expression depth and overflow aborted the probe | Explicit frame storage grows while Rust loop depth stays constant |
| Current implementation size | Smaller | About twice the evaluator-module lines in the probe |
| Later control pressure | Requires conversion or a separate runtime form | Already represents ordinary evaluation contexts as data |

The event comparison proves agreement for the named cases, not general
equivalence between the two algorithms. The small-step rules remain the
semantic comparison source; neither evaluator becomes authoritative because it
can execute them.

## Conclusion

The evidence favors an explicit first-order machine for the retained Mini-Ash
evaluator. The current justification is host-stack independence and inspectable
evaluation order, not future effects by reputation. The extra frame machinery
directly represents evaluation contexts already required by the pure
small-step rules.

The machine's frames are internal evaluator control. This comparison does not
place continuations in surface Ash or typed Core, make them capturable, or
decide one-shot versus multi-shot handler continuations. Later effect work must
still determine which machine state becomes an Ash continuation and how its
kind is tracked.

A direct recursive evaluator remains a useful disposable comparison oracle. A
retained implementation should avoid maintaining two independent evaluators
unless differential testing supplies enough value to justify duplicate rule
implementations.

## Accepted outcome

[AD-0008](../../../../decisions/AD-0008-explicit-evaluator-machine.md) accepts
these properties:

- the retained evaluator represents current evaluation contexts as explicit
  first-order frame data;
- lexical closures contain inspectable code and Ash environments;
- the evaluator runs through an explicit control loop rather than relying on
  Rust recursion for language evaluation depth;
- frame transitions follow the applicable small-step evaluation order;
- invalid typed input and runtime resource failures return structured failures
  rather than panic;
- evaluator tracing observes control transitions without becoming semantic
  authority.

The decision does not accept effect or handler semantics, continuation
multiplicity, CPS structure, concurrency, cancellation, integer behavior,
resource limits, or a concrete environment-allocation strategy.

## Remaining questions

- Should the machine hold recursive Core references, stable node identities, or
  another code identity?
- Which machine states and origins should an optional diagnostic trace expose?
- What runtime resource exhaustion can be reported portably without defining
  accidental language semantics?
- Can frame handlers compose by Core feature family without one monolithic
  transition function?
- Which later effect experiment first requires distinguishing ordinary
  evaluation frames from capturable continuation data?

The parser and component-convergence comparisons can proceed without resolving
these implementation questions.

## Retention boundary

The evaluator probe lived under ignored build output and is disposable. Its
five tests, format check, and warning-denying Clippy check passed after the
comparison. This document retains the candidate shapes, corpus agreement,
module-size observations, stack-failure counterexample, and decision boundary;
the probe is not product implementation or language authority.
