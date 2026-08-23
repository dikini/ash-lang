# DN-0020: Ash Dialect Milestones

- ID: `DN-0020`
- Status: exploring
- Related: [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [DN-0006: Initial Type System](DN-0006-initial-type-system.md), [DN-0011: Modules, Providers, and Resolution](DN-0011-modules-providers-and-resolution.md), [DN-0015: Mini-Ash Phase](DN-0015-mini-ash-phase.md), [DN-0019: Primitive Feature Composition](DN-0019-primitive-feature-composition.md), [data-and-pattern integration evidence](mini-ash/data-and-patterns/evidence.md)

> This design note is informative. It does not define current Ash, accept
> rank-1 polymorphism or module semantics, or accept an architecture.

The Mini-Ash side of this informative trajectory is complete. Its retained
[closure report](mini-ash/closure.md) and
[rank-1 integration evidence](mini-ash/rank-1-polymorphism/evidence.md) provide
the stable input to future Modular Ash design. The specification defines the
current language.

## Question

Which retained implementation dialects should follow the data-and-pattern
increment, and which design questions belong to each milestone?

## Context

Mini-Ash is a growing retained implementation dialect. Its planned semantic
increments cover the pure functional nucleus listed in
[DN-0015](DN-0015-mini-ash-phase.md), ending with rank-1 parametric
polymorphism. The monomorphic data-and-pattern increment landed in signed merge
`1e01622`. The [current specification](../../spec/README.md) defines its
semantics, and its retained
[integration evidence](mini-ash/data-and-patterns/evidence.md) records the
implementation pressure.

The final data review preserved the planned monomorphic boundary. It also made
expected-type propagation through matches, recursive-data initialization order,
result-heap ownership, syntax and coverage work budgets, and representation
release points explicit. These facts do not add polymorphism or modules. They
do belong in Mini-Ash closure analysis and constrain later changes to the
affected judgments and stage boundaries.

[DN-0019](DN-0019-primitive-feature-composition.md) found that a later feature
should first try to elaborate through existing forms or reside in a library.
Modules and interfaces create the first useful boundary for testing that
advice across a language rather than one primitive feature.

[DN-0011](DN-0011-modules-providers-and-resolution.md) explores both passive
static modules and later dynamic loading, providers, registration, and
unloading. Those pressures should not enter one initial module milestone.

## Constraints

### Retain distinct runnable dialects

Mini-Ash and Modular Ash should remain distinct Ash implementation dialects
and development milestones. Completing Modular Ash should not rename or
silently expand Mini-Ash. Each dialect should remain independently selectable
and testable against the language it admits.

Language dialects and typed Core dialects need not correspond one-to-one. A
language dialect may reuse a Core dialect when that Core preserves its required
facts, and one language dialect may use several Core dialects across justified
lowering boundaries.

### Finish Mini-Ash with rank-1 polymorphism

Rank-1 polymorphism belongs to Mini-Ash. Its future proposal should preserve
these intended boundaries unless new evidence reopens them:

- type declarations bind type-constructor parameters explicitly, as in
  `type Some<A> = Some A`;
- a global value name's type annotation implicitly quantifies its free type
  variables, as in `id : A -> A`;
- conservative local generalization may apply to anonymous-function bindings;
- recursive checking remains monomorphic; and
- unification remains first-order and preserves kinds.

The explicit binder in a type declaration and implicit quantification in a
value annotation express universal scope at different language levels. A
function declaration introduces a value name, so the rank-1 design should not
force the type-constructor convention onto it.

These points constrain future design; they are not current Ash semantics. The
proposal must define the exact judgments, local-generalization criterion,
diagnostics, representation, and operational erasure.

### Lower after the relevant judgments

Polymorphism facts should remain explicit through every judgment that needs
them. A lowering may erase or translate those facts when its target invariant
is independently validated and no later judgment depends on the distinction.

The landed match-checking rules provide a current example: a surrounding
expected type must reach every arm, including the first, before a later boundary
can omit that checking context.

The milestone does not yet choose explicit value-level type application,
dedicated Core type abstractions and applications, or an earlier erasure. That
choice belongs to rank-1 design evidence. Early lowering is useful only when it
simplifies consumers without making later judgments indirect or incomplete.

### Start Modular Ash at the static boundary

Modular Ash should begin after Mini-Ash and its closure analysis. Its first
design boundary is passive static modules, interfaces, imports, exports,
visibility, and typed composition. This boundary should make separate
compilation and interface checking concrete enough to evaluate what the core
language must retain.

Dynamic loading, providers, effects, registration, unloading, and runtime
resolution remain later pressure. Modular Ash should preserve relevant options
without implementing those mechanisms in its first increment.

### End each milestone with simplification analysis

Completion means more than passing the increment's semantic tests. Each
milestone should examine:

- which constructs and facts cross each compiler stage;
- which forms can lower to already validated forms;
- which behavior can move from the core language into libraries;
- which resource budgets bound each stage;
- which ownership and lifetime boundaries preserve reachable values;
- when representations can be released and which later form owns each retained
  fact;
- which mechanisms no accepted behavior uses;
- whether required maintenance sites are found by the compiler or one stable
  search;
- which representation, validation, or dispatch machinery can be removed; and
- which invariants and intentional exclusions the retained dialect carries
  forward.

Semantic changes found during this analysis still require the proposal and
specification workflow. Cleanup may remove unused implementation machinery only
when retained invariants and tests no longer depend on it.

## Candidate directions

### Two retained milestone dialects

The leading trajectory is:

1. Use the landed monomorphic data-and-pattern specification and integration
   evidence as the baseline for later Mini-Ash work.
2. Design, propose, and implement rank-1 polymorphism as the final Mini-Ash
   semantic increment.
3. Run the Mini-Ash simplification and cleanup analysis, then retain the
   resulting runnable dialect.
4. Design Modular Ash around passive static modules and interfaces.
5. Use those boundaries to compare core primitives with ordinary library
   definitions, then run the Modular Ash simplification and cleanup analysis.

This direction gives module design a stable small language to compose and gives
core-versus-library analysis a real interface boundary.

### Extend one moving Ash dialect

One implementation dialect could absorb every increment. This would reduce the
number of selectable configurations, but it would erase the milestone boundary
needed to compare complexity before and after modules. It would also make
Mini-Ash's closure analysis a transient repository state rather than retained
evidence.

### Add modules before Mini-Ash closes

Modules can compose a monomorphic language, so rank-1 polymorphism is not a
prerequisite for module semantics. Designing modules first would nevertheless
leave their treatment of exported rank-1 definitions unsettled and could
require the boundary to be designed twice. The leading trajectory therefore
uses module and interface cases as pressure during rank-1 design but retains
module semantics only after Mini-Ash closes. A bounded module probe remains
appropriate if rank-1 generalization or interface checking cannot be judged
without that evidence; the probe would not add modules to Mini-Ash.

## Evidence and experiments

The rank-1 proposal should test global implicit quantification, conservative
local generalization, monomorphic recursion, explicit type-constructor
parameters, kind errors, and cross-stage preservation of polymorphism facts.
It should compare lowering points by naming which later judgments consume each
fact and which target validator makes erasure safe.

Mini-Ash closure evidence should record the inventory and simplification checks
listed above against the complete dialect. It should identify the stable
language and Core dialect entry points that Modular Ash can reuse. The audit
should include the syntax and coverage work budgets, completed-heap ownership,
and representation release boundaries retained by the data-and-pattern
increment.

The first Modular Ash design should compare programs split across passive
modules, interface satisfaction and rejection, abstract and visible names,
import and export errors, and separate checking. Its core-versus-library audit
should show at least one representative primitive retained in the core and one
representative operation expressed through an interface or library, with the
typing, diagnostic, and evaluation consequences stated.

A milestone is ready to close when its accepted semantics, specification,
implementation, tests, runnable dialect, evidence report, and simplification
analysis agree. A later milestone may revise its own design in response to new
pressure, but it should not retroactively change the admitted language of a
retained earlier dialect.

## Open questions

- Which exact generalization judgment and representation should the rank-1
  proposal select?
- Does Mini-Ash need any explicit value-level type instantiation syntax, or can
  elaboration supply all rank-1 instantiations?
- Which Core dialect boundaries preserve polymorphism facts without coupling
  every language dialect to a unique Core dialect?
- Which module and interface semantics best support separate checking and the
  core-versus-library audit?
- Which current primitives become credible library candidates once Modular Ash
  has interfaces?
