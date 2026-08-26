# DN-0020: Ash Dialect Milestones

- ID: `DN-0020`
- Status: exploring
- Related: [DN-0022: Passive Static Modules](DN-0022-passive-static-modules.md), [DN-0023: Interfaces and Implementations](DN-0023-interfaces-and-implementations.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [DN-0006: Initial Type System](DN-0006-initial-type-system.md), [DN-0011: Modules, Providers, and Resolution](DN-0011-modules-providers-and-resolution.md), [DN-0015: Mini-Ash Phase](DN-0015-mini-ash-phase.md), [DN-0019: Primitive Feature Composition](DN-0019-primitive-feature-composition.md), the [Mini-Ash closure report](mini-ash/closure.md), the [passive-module evidence](modular-ash/evidence.md), the [interface implementation evidence](modular-ash/interfaces-evidence.md), the [core-and-library audit](modular-ash/core-library-evidence.md), and the [Modular Ash closure report](modular-ash/closure.md)

> This design note is informative. It records implemented dialect increments
> and future sequencing pressure, but it does not define current Ash or
> authorize roadmap work.

The Mini-Ash milestone and every bounded Modular Ash semantic or audit increment
are complete. Passive source modules, method-only interfaces, the separately
authorized core-versus-library audit, and the final simplification analysis
each retain their increment-local implementation, review, verification, and
evidence. The `mini-ash` Git tag, closure report, and integration evidence retain
the historical dialect. The
[current specification](../../spec/README.md) defines the implemented first
`lib-ash` increment on the completed Modular Ash base; its type-class-like
interfaces and `impl` are not module signatures. The final
cross-cutting independent reviews and root verification completed the lifecycle
gate after task and plan cleanup. The annotated `modular-ash` tag retains the
final closure commit. Those mechanics did not supply missing semantics, and
this note records the result but did not authorize that work.

## Question

How did the completed Mini-Ash milestone constrain the Modular Ash milestone,
and which later design questions remain outside that completed boundary?

## Context

Mini-Ash closed with a single-file, pure, rank-1 language and a simplification
analysis. The `mini-ash` tag at commit `d62d3ba` retains its implementation,
tests, specification, and evidence. The passive-module comparison built that
tag separately and confirmed representative unchanged observations. Current
source keeps no Mini-Ash grammar, driver, lowering, or selectable compiler
dialect.

[DN-0019](DN-0019-primitive-feature-composition.md) found that later work
should first try to elaborate a feature through existing forms or place
behavior in a library. Mini-Ash had no module or library boundary with which to
test that advice.

[DN-0011](DN-0011-modules-providers-and-resolution.md) explores passive static
modules together with later dynamic loading, providers, registration, and
unloading. Those later mechanisms should not enter the initial static-module
increment.

Ash interfaces and `impl` are type-class-like typed relationships, not module
signatures. Their completed increment followed passive modules so imports,
exports, visibility, and typed composition were established first.

## Constraints

### Retain Mini-Ash historically

The `mini-ash` tag is the runnable retained dialect. Current source has evolved
beyond Modular Ash rather than carrying historical grammars, drivers,
lowerings, or Core compatibility paths. Current artifacts may reference the tag
and build it for bounded comparison evidence.

This retention preserves the milestone without constraining later
core-to-library refactoring to keep Mini-Ash source runnable in the evolving
compiler.

### Lower only after the owning judgment

Static facts remain explicit through every judgment that consumes them. A
lowering may erase module or interface structure only after a target invariant
authenticates all relationships needed downstream. Language dialect evolution
does not require a one-to-one sequence of typed Core dialects.

### Add Modular Ash in bounded increments

The first increment added only passive static modules, imports, exports,
visibility, opacity, and typed composition. [DN-0022](DN-0022-passive-static-modules.md)
records the exploration that developed that boundary, and the
[passive-module evidence](modular-ash/evidence.md) records its implementation.

[DN-0023](DN-0023-interfaces-and-implementations.md) records the exploration
that led to implemented method-only Ash interfaces, `impl`, constraints,
satisfaction and rejection, and separate checking against real module
boundaries. The
[interface implementation evidence](modular-ash/interfaces-evidence.md)
retains the resulting corpus and compiler boundaries. Associated types remain
later comparison pressure rather than part of this increment.

The separately authorized
[core-and-library audit](modular-ash/core-library-evidence.md) used integer
equality to compare a retained Core primitive with an explicit source-library
interface. It recorded distinct admission, typing, diagnostic, Core, and
evaluation consequences instead of treating “move to a library” as a
source-layout change. The
[closure report](modular-ash/closure.md) retains that conclusion with the
module and interface evidence.

Dynamic loading, providers, effects, registration, unloading, and runtime
resolution remain later pressure.

### End each milestone with simplification analysis

Completion requires agreement among accepted semantics, specification,
implementation, tests, runnable behavior, evidence, and simplification. Each
milestone should examine:

- facts retained and released at compiler boundaries;
- constructs that lower to already validated forms;
- behavior that can move from the core language into libraries;
- resource budgets, ownership, and lifetime boundaries;
- unused mechanisms that can be removed; and
- invariants and exclusions carried into the next increment.

Semantic changes found by the audit return to proposal or design work. Cleanup
may remove implementation machinery only when current behavior and retained
evidence no longer depend on it.

## Candidate trajectory

The leading trajectory is:

1. Preserve completed Mini-Ash at the `mini-ash` tag with its closure evidence.
   This is complete.
2. Evolve current source through a passive-static-module proposal based on
   DN-0022. This is complete.
3. Design, specify, and implement interfaces and `impl` against the passive
   module boundary. This is complete.
4. Separately authorize and compare representative core primitives with library
   definitions. This is complete.
5. Close Modular Ash with its own simplification analysis and final
   `modular-ash` checkpoint. This is complete. Lifecycle cleanup removed the
   temporary task and plan, final cross-cutting independent reviews and root
   verification closed the gate, and the annotated tag retains the closure
   commit.

Keeping both Mini-Ash and Modular Ash runnable in the same current compiler
would add grammar selection, driver selection, compatibility lowering, and
cross-dialect maintenance. The historical tag supplies the required retained
baseline without those mechanisms.

Adding interfaces in the module increment would conflate name visibility,
opacity, constraint evidence, implementation selection, and associated-type
questions. Separate increments provide clearer rejection cases and allow the
module boundary to be tested before it supports automatic typed resolution.

## Evidence and experiments

The [passive-module evidence](modular-ash/evidence.md) records the cases and
boundaries named by [DN-0022](DN-0022-passive-static-modules.md), including
generated export summaries, hidden identities, opaque types, acyclic rooted
imports, and one linked Core program.

The [interface implementation evidence](modular-ash/interfaces-evidence.md)
records method-only declarations, explicit requirements, implicit evidence,
ambiguity, orphan and overlap policy, passive summaries, validation, Core
lowering, runtime observations, and the retained unspecialized trace. It leaves
associated types and specialization as future comparison pressure.

The paired [core-and-library audit](modular-ash/core-library-evidence.md)
retains direct integer equality and `Primitive::Equal`, and expresses an
explicit equality capability through `Equal<A>` and `Equal<Int>`. It records
the different admission, typing, diagnostics, Core representation, evaluation,
maintenance, resource, and lifetime paths. The
[Modular Ash closure report](modular-ash/closure.md) joins that result to the
passive-module and interface evidence at the final checkpoint.

Historical comparison evidence may build the `mini-ash` tag in an isolated
worktree. It should not copy the historical compiler into current source or
make routine current-tree verification depend on two implementations.

## Recorded conclusions and later pressure

The audit concludes that integer `==` and `Primitive::Equal` remain Core. An
explicit `Equal<Int>` source-library capability is useful without an operator
rewrite, implicit import, shipped prelude, interface-specific Core node, or
runtime interface machinery. The two paths keep distinct admission, typing,
diagnostic, Core, and trace behavior.

Associated types and specialization remain later library-design pressure.
They are not unresolved Modular Ash semantics, and this informative note does
not authorize their design or implementation.
