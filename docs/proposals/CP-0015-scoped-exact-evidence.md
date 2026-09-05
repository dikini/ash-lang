# CP-0015: Scoped Exact Evidence

- ID: `CP-0015`
- Status: accepted
- Related: [DN-0026](../design/DN-0026-effect-ash-resource-first-milestones.md),
  [DN-0027](../design/DN-0027-effect-ash-program-design.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md)

> This proposal is not current Ash.

The user requests this slice, one pure-relation end-to-end case followed by
interaction coverage, autonomous bounded choices, subagents with at most high
reasoning, and no unnecessary mechanisms or process. This document records the
semantic choices accepted under that delegated authority on 2026-09-05 after
independent semantic (high) and implementation-boundary (medium) reviews.
Scope expansion returns to the user.

## Current behavior

The integration baseline `90f517d` combines module and local `newtype` with the
resume-required effect kernel. Local nominal identities are stable lexical
identities, not fresh runtime acquisitions. Their representations supply no
interface evidence. Identity-free closures may capture their erased values.

Constraint selection uses complete applications, with abstract requirements
before exact current-implementation evidence before concrete implementations.
Determined pending roots use one fixed eligibility snapshot and one mandatory
forward improvement pass; recursively generated prerequisites instead use
complete-goal selection without snapshot membership. Selected methods lower to
ordinary authenticated function values and applications. There is no lexical
source for independently supplied methods.

## Proposed behavior

### Sequential introduction

Add one private local declaration using the already-reserved `with` keyword.
The grammar below reuses interface applications and implementation equations.

```ebnf
local_evidence_declaration ::=
  "with" interface_application
  "{" line_end
  [ impl_equation { line_end impl_equation } [ line_end ] ]
  "}" ;
```

Admit it among sequential block declarations, not at module level or inside a
`let rec` group. It has no visibility modifier, head type parameters, or
`where` clause. Every interface argument is explicit, well-kinded, and contains
no inference variable. Existing enclosing rigid type parameters and local
nominals are permitted; there is no freshening or head-pattern matching.

At least one active local nominal identity must occur structurally in the
selection key: the complete application for an interface without an edge, or
its determinant arguments otherwise. An occurrence only in a dependent
argument is insufficient. An occurrence beneath a type constructor counts;
no outer-constructor orphan restriction applies. This ties introduction to
local identity without giving local code new evidence for an unrelated global
key. Module implementation coherence and orphan rules remain unchanged.

The declaration supplies each required method exactly once, using the existing
equation-grouping, pattern, coverage, and contextual method-checking rules.
Interface arguments instantiate interface parameters; interface method-local
parameters remain rigid during checking. Their declaration spellings do not
enter the supplied body's source type namespace; existing enclosing type names
retain their meanings, as for implementation equations. Existing higher-kinded parameters and
effect annotations retain their ordinary meaning. This does not add first-class
polymorphic source values.

Method bodies see the preceding term and evidence scopes, including ordinary
captured values and preceding recursive functions. The declaration does not
introduce ordinary method-name bindings or its own evidence into its method
bodies. It therefore grants no implicit self-selection or sibling-method
recursion. Each supplied method body is a resume barrier: using an enclosing
clause capability reports `effect.resume-capture`; with no enclosing clause,
`effect.resume-outside-clause` retains ownership. A handler declared inside
the method receives its own capability normally. All methods must check before
the source becomes available to the following block remainder.

### First complete case

This pure relation introduces behavior that no existing implementation supplies.
The complete example exercises constrained forwarding and must evaluate to
`42 : Int`. A paired test replaces `forward(saved)` with `read(saved)` to
exercise direct selection of the same supplied method.

```ash
interface Read<A, B> where A -> B {
    read : A -> B
}

forward<A, B> : A -> B where Read<A, B>
forward value = read(value)

main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    let saved = Token(41)
    with Read<Token, Int> {
        read ignored = match saved {
            Token(value) => value + 1
        }
    }
    forward(saved)
}
```

### Availability and precedence

One source has one module-qualified lexical identity and one checked complete
interface application. It is not a module implementation or abstract
requirement. Two simultaneously visible lexical sources for the same interface
may not have identity-equal selection keys: an identical complete application
is a duplicate; unequal dependent tuples conflict. Disjoint scopes may supply
different methods for the same identity. Nested distinct identities also remain
valid. There is no lexical candidate search, unification, or implicit rebinding.

Selection keeps the current complete-goal gate and uses this order:

1. identity-equal complete abstract requirement;
2. exact current implementation;
3. identity-equal complete lexical evidence at the occurrence's source scope;
4. ordinary concrete implementation selection.

Lexical evidence cannot be hijacked by a matching generic concrete
implementation. It cannot replace a definition's explicit abstract contract or
exact current-implementation evidence. Recursive concrete prerequisites use the
same source order and the original complete-goal and cycle rules.

### Improvement and delayed closure

Preserve ordinary unification, the fixed root snapshot, and the single forward
improvement pass. Use the same source precedence, with identity-equal key
lookup for lexical improvement. A lexical source supplies its complete dependent
tuple and participates in the existing mandatory transactional consistency
check. It never refines a determinant, unlocks an ineligible root, searches its
own prerequisites, records a selection during improvement, or repeats the pass.

Each occurrence retains its lexical source scope even if inference closes after
that source scope has been traversed. Do not close inference early merely to
avoid retaining scope, or accidentally use the final traversal scope for an
earlier occurrence. Generalization and existing inference timing are unchanged.

The existing root/prerequisite distinction remains intentional. If lexical
`R<N, Int>` determines the key `N`, a pending root `R<N, Bool>` conflicts during
improvement. A recursively generated complete prerequisite `R<N, Bool>` is not
that lexical source's goal and may use later complete evidence. It does not
gain a new key barrier or snapshot requirement.

### Closures and erasure

The evidence source is available only to occurrences within its lexical
remainder, including bodies defined there. New occurrences outside cannot select
it. A previously checked closure retains its recorded selection and captures
the ordinary supplied method functions when necessary; returning from the
evidence block does not revoke those functions.

An ordinary selected method may leave an inner evidence block as `N -> Int`
when `N` was introduced in an enclosing scope. At the enclosing nominal scope,
the existing outward-type, row, scheme, requirement, and inferred-binding checks
apply unchanged. An identity-free closure may cross that boundary while
retaining hidden representation values and selected method functions. No
lexical source is exported through an inferred requirement, scheme, summary,
import, or first-class evidence package.

The compiler checks canonical source identity, complete application, method
identity and declaration order, contextual type parameters, capture binders,
and actual lexical availability independently in linked and Core validation.
Validation authenticates the recorded selection; it never re-runs selection.
Transforms preserve these relationships and revalidate before execution.

Lower to ordinary method functions, local bindings, and applications. Source
selection carriers erase into that lowering; minimal immutable method-evidence
authentication facts may remain through Core validation and transforms, inert
at runtime. Selected method behavior and ordinary captures remain. No evidence
dictionary, runtime registry, dynamic
lookup, new runtime identity, or general Core authority framework is introduced.

## Semantic delta

Sequential `with` admits checked lexical methods for one exact local-identity
relationship. Lexical sources join selection and forward improvement between
exact-current and concrete sources. All other evidence, nominal, effect,
generalization, and runtime rules remain unchanged.

## Affected specification areas

- [Syntax](../../spec/syntax.md): block declaration grammar and exclusions.
- [Name resolution](../../spec/name-resolution.md): source identities,
  preceding method scopes, and contextual method-parameter ownership.
- [Static semantics](../../spec/static-semantics.md): admission, precedence,
  improvement, delayed scope ownership, diagnostics, and closure behavior.
- [Elaboration](../../spec/elaboration.md): distinct source and independent
  method/capture authentication through ordinary Core lowering.
- [Dynamic semantics](../../spec/dynamic-semantics.md): static erasure and
  ordinary captured method execution, with no new transition family.
- [Overview](../../spec/README.md): one executable pure relation example.

## Resulting specification truth

After complete integration into `main`, these rules and their tested examples
become normative. A proposal, product branch, or milestone integration branch
alone does not make them current Ash.

## Interactions

The existing budgets own new syntax, canonical facts, scope links, retained
applications, method bindings, selection nodes, and authentication work. Charge
proportional work before retention, publish atomically, and preserve retry and
iterative teardown. Concrete formulas belong to implementation evidence, not
new semantic limits. Programs without lexical evidence retain existing work
paths and runtime observations.

Acquisition may later introduce evidence through the same distinct lexical
source pattern. This proposal does not choose acquisition freshness or lifetime.
Supplying ordinary interface methods establishes no proof, resource, provider,
or handler authority; those future authorities cannot masquerade as this source.

## Non-goals

No local `impl` search, generic evidence heads, declared evidence prerequisites,
recursive evidence groups, active-key shadowing, representation-derived
relations, arbitrary global-key replacement, new solver pass, ownership system,
checked discard, resource acquisition, proof rule, existential package,
suspension, foreign interface, or dynamic dispatch.

## Required evidence

Retain these named obligations in the task and executable corpus:

- first pure-relation direct call and constrained forwarding observe `42`,
  including a supplied method that captures a preceding local nominal value;
- missing, duplicate, extra, ill-typed, and non-exhaustive method groups;
  contextual polymorphic methods and higher-kinded enclosing arguments;
- self-selection, implicit sibling recursion, forbidden head parameters,
  prerequisites, module/recursive placement, and resume capture rejection;
- missing local key, local identity only in a dependent, duplicate active
  complete goal, and equal-key unequal-dependent rejection; disjoint scopes
  and nested distinct identities succeed;
- direct and recursive selection distinguish lexical evidence from matching
  concrete methods; abstract and exact-current priority remain intact;
- mandatory dependent conflict, unknown determinant ambiguity, fixed-snapshot
  ineligibility, delayed inference after lexical exit, recursive lexical
  prerequisites, and the complete-goal asymmetry described above;
- selected methods may leave an inner evidence scope without exporting its
  evidence; identity-free closures execute after the nominal scope returns;
  wrong-identity and representation evidence never transfer;
- stable source diagnostics: `evidence.missing-local-key`,
  `evidence.duplicate`, `evidence.determination-conflict`,
  `evidence.missing-method`, `evidence.duplicate-method`, and
  `evidence.extra-method`; existing argument, kind, type, pattern, coverage,
  constraint-improvement, and resume reasons keep their existing owners;
- after resolution, arity, and kind admission, local-key admission precedes
  active-key duplicate/conflict checking, then complete method-membership
  checking, then method-body checking in the existing deterministic order;
  `evidence.missing-local-key` labels the new header; duplicate/conflicting
  sources label the new header and relate the earlier header; a missing method
  labels the header and relates the required interface method; a duplicate
  method labels the repeated group name and relates the earlier group name;
  an extra method labels that name and relates the interface declaration;
  malformed compiler facts are internal failures;
- linked and Core tampering cannot replace source owner, complete goal,
  method slot, parameter mapping, capture binder, or source scope; both
  transforms revalidate the original runtime observation;
- exact accounting, one-short atomic failure, retry, iterative deep disposal,
  unchanged production limits, and no lexical facts in summaries or imports;
- existing evidence, nominal, closure, effect, Core, CLI, resource, and
  executable-specification corpora pass; independent semantic and Rust/resource
  reviews close all Critical and Important findings before the full gate.
