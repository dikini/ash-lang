# DN-0020: Ash Dialect Milestones

- ID: `DN-0020`
- Status: exploring
- Related: [DN-0022: Passive Static Modules](DN-0022-passive-static-modules.md), [DN-0023: Interfaces and Implementations](DN-0023-interfaces-and-implementations.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [DN-0006: Initial Type System](DN-0006-initial-type-system.md), [DN-0011: Modules, Providers, and Resolution](DN-0011-modules-providers-and-resolution.md), [DN-0015: Mini-Ash Phase](DN-0015-mini-ash-phase.md), [DN-0019: Primitive Feature Composition](DN-0019-primitive-feature-composition.md), the [Mini-Ash closure report](mini-ash/closure.md), the [passive-module evidence](modular-ash/evidence.md), and the [interface implementation evidence](modular-ash/interfaces-evidence.md)

> This design note is informative. It records implemented dialect increments
> and future sequencing pressure, but it does not define current Ash or
> authorize roadmap work.

The Mini-Ash milestone and passive-static-module increment are complete. The
method-only interface increment is implemented and specified while its final
review and task closure remain pending. The `mini-ash` Git tag, closure report,
and integration evidence retain the historical dialect. The
[current specification](../../spec/README.md) defines Modular Ash with passive
source modules and type-class-like interfaces and `impl`; these interfaces are
not module signatures. A separately authorized core-versus-library audit is the
next Modular Ash increment. This note does not begin that audit.

## Question

How should the completed Mini-Ash milestone constrain the Modular Ash
milestone, and which design questions belong to each Modular Ash increment?

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
signatures. Their implemented and specified increment followed passive modules
so imports, exports, visibility, and typed composition were established first.

## Constraints

### Retain Mini-Ash historically

The `mini-ash` tag is the runnable retained dialect. Current source has evolved
into Modular Ash rather than carrying two grammars, drivers, lowerings, or Core
compatibility paths. Current artifacts may reference the tag and build it for
bounded comparison evidence.

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

Modular Ash can now use representative cases to compare core forms with library
definitions. That audit requires separate authorization and should state the
typing, diagnostic, Core, and evaluation consequences rather than treating
“move to a library” as a source-layout change.

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
   module boundary. This is implemented and specified; final task closure
   remains pending.
4. Separately authorize and compare representative core primitives with library
   definitions. This is next and has not begun.
5. Close Modular Ash with its own simplification analysis and tag.

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

The core-versus-library audit should retain at least one representative
primitive in Core and express at least one representative operation through a
library interface. It should compare source admission, typing, diagnostics,
Core representation, evaluation, and maintenance sites.

Historical comparison evidence may build the `mini-ash` tag in an isolated
worktree. It should not copy the historical compiler into current source or
make routine current-tree verification depend on two implementations.

## Open questions

- Which current primitives become credible library candidates after interfaces
  exist?
- What bounded audit corpus can compare a retained Core primitive with a
  library-interface definition without silently changing diagnostics or
  evaluation?
- Which separately proposed associated-type or specialization semantics, if
  any, are justified by later library pressure?
