# First Slice: Matching and Selection Coverage

This record refines the `accepts` and `passes` premises in the
[nearest-boundary rules](first-slice-nearest-boundary-judgments.md#candidate-composition-rules).
It proposes a source-handler instance comparison and a conservative selection
coverage judgment. These are candidate type-system rules, not current Ash
syntax, an implemented checker or a soundness proof. The
[specification](../../../spec/README.md) remains the authority for current
semantics.

The scope is deliberately narrow: it covers matching a request against an
ordinary source handler, then composing **established** boundary-match facts
into a covering set of nearest-selection outcomes. It does not define
function application, cell or native interpretation, discard safety or the
representation of arbitrary opaque control. Those rules provide or consume
boundary facts under their own premises.

## Before: checks and consumers

| Current path | Inputs and output | Intended disposition |
| --- | --- | --- |
| [Label specialization](../../../src/core/capture/control.rs#L2712) | A request or boundary label and its own lexical context yield a specialized label, retaining ambiguity when a relevant substitution is unproved. | Apply the certified declaration, instantiation and scope facts to the new comparison. Preserve the request and handler's separate substitutions and their assumptions. |
| [Label comparison](../../../src/core/capture/control.rs#L2813) | Two labels yield `(can_select, can_cross)`: exact equality can yield `(true, false)`, a definite difference `(false, true)`, and uncertainty `(true, true)`. An applicable known row-tail exclusion can rule out that tail's match. | Establish a typed bound on possible match outcomes. A bound is reusable under its stated subject and assumptions; neither a missing proof nor a different variable name is proof of inequality. |
| [Boundary selection](../../../src/core/capture/control.rs#L5966) | Per-boundary possibilities and the control graph produce possible selections, crossed prefixes and possible outward continuation; builtin cells and other boundaries have additional matching rules. | Compose already established boundary and suffix facts into a covering selection judgment. Do not reconstruct certified constituent control to recover those facts. |
| [Selected-case consumers](../../../src/core/capture/control.rs#L6156) | Possible source, cell, native, removed-handler and outward routes lead to their respective payload, capture, interpreter or escape checks. | Check each applicable new composition obligation using the covering judgment. A possible selection is not itself proof that its payload or close is safe. |

These paths share control analysis with other checks. The exact disposition of
each consumer and the current requirement for independent Core validation
remain open. The table does not show that a current check can be removed.

## Source instance facts

For a possible request `r` and a certified ordinary source-handler boundary
`b`, let `I_r` be the request's effect instance under the request's saved
lexical instantiation, and `I_b` the handler's instance under its own saved
instantiation. Their declarations, arguments, kinds and operation contracts
are already established by their applicable judgments. In particular, the
source handler's operation coverage and pattern premises are not rechecked by
this comparison.

Interpret `GAMMA, phi |- same(I_r, I_b)` as an established fact that, for
every applicable realization satisfying those assumptions, the instantiated
effect identities and all ordered arguments are equal. Interpret
`GAMMA, phi |- different(I_r, I_b)` as a fact that they differ in every such
realization. The subject includes the actual lexical instantiation and, where
relevant, the particular resource activation. Two executions at one source
site are not automatically the same activation. These relations are
metanotation; this record does not claim that current Ash exposes a general
type-level inequality proposition or can decide every comparison.

Distinct authenticated effect identities establish `different`; for the same
identity, an established unequal argument can do so. Equal identity and equal
complete instantiated arguments establish `same`. Names of distinct type
variables, unsolved unification or absence of an equality proof do not by
themselves establish `different`. See
[effect instances and rows](../../../spec/static-semantics.md#computation-types-and-effect-rows)
and [runtime handler selection](../../../spec/dynamic-semantics.md#effect-handlers-and-completion).

## Candidate match bounds

Write `match_bound(r, b, M)` for a judgment that the set `M` covers the
possible outcomes of comparing this request with this boundary under the
stated assumptions. For this record, `M` contains `accept`, `pass`, or both.
Coverage means that every applicable concrete encounter's actual outcome is in
`M`; membership does not assert that the outcome occurs. The encounter assumes
the applicable prior admission and preparation premises; internal failures are
not silently classified as `pass`.

The following candidate rules apply only to the authenticated source-handler
case. `source_pair(r, b, I_r, I_b)` supplies the established possible
request/boundary pairing and their separately instantiated, well-formed
instances. It includes the applicable declaration and handler contract, not a
fresh inspection of either implementation. Each conclusion remains
conditional on `GAMMA, phi`.

When the complete instances are established equal, only acceptance is needed
in the bound:

```sequent
M-Source-Same :=
  GAMMA, phi |- source_pair(r, b, I_r, I_b)
  GAMMA, phi |- same(I_r, I_b)
  ===>
  GAMMA, phi |- match_bound(r, b, {accept})
```

When the complete instances are established different, only passing is needed:

```sequent
M-Source-Different :=
  GAMMA, phi |- source_pair(r, b, I_r, I_b)
  GAMMA, phi |- different(I_r, I_b)
  ===>
  GAMMA, phi |- match_bound(r, b, {pass})
```

When the facts do not establish either relationship, retaining both outcomes
is a conservative candidate. This rule may also be used as a less precise
bound when more precise facts exist; it does not assert that both outcomes
actually occur:

```sequent
M-Source-Conservative :=
  GAMMA, phi |- source_pair(r, b, I_r, I_b)
  ===>
  GAMMA, phi |- match_bound(r, b, {accept, pass})
```

These rules require a justified account of instantiation and of `same` and
`different`. The conservative rule must not be interpreted as a way to prove
either an exact acceptance or exact passing judgment. Conditional exact cases
may instead be derived under equality and inequality assumptions if their
coverage is established. The implementation of such conditions is open.

An established row-tail lacks fact may rule out an instance for requests
arising from that tail; it does not eliminate an independently known member.
For an unknown request where no exact instance is available, the source-pair
premise above may itself remain conditional or unavailable. Carry an
appropriate unknown possibility or obligation; do not manufacture a known
request, a known handler or an empty result.

## Candidate coverage composition

Write `covers_selection(r, K, S)` for the judgment that `S` covers every
applicable completed search of `r` through the certified described context
`K`, including both selection and passage outward without a selected boundary.
An abstract outcome is `selected(b, prefix, outside)` or `outward(prefix)` as
in the nearest-boundary record. For every concrete outcome there must be an
abstract outcome that represents the same request and activation and
conservatively represents its selected boundary, crossed-control and outside
facts as applicable. An eventual rule must define this correspondence; matching
boundary names alone is insufficient. The set is an upper bound: a member need
not occur. It is not an exact `selects` judgment.

For `b :: K`, define `prepend(b, S)` to preserve each suffix outcome and its
outside context while adding `b` to its crossed prefix. The following
schematic rules use already established boundary and suffix judgments under
the same condition. `case(r, K)` identifies the possible request/context
pairing; `K` is the certified described suffix at the search position reached
after the prefix, for the same request, activation and control facts.

At the end of the described context, selection remains outward; an unknown
suffix cannot be treated as empty:

```sequent
C-Outside :=
  GAMMA, phi |- case(r, [])
  ===>
  GAMMA, phi |- covers_selection(r, [], {outward([])})
```

If the boundary can only accept, it covers the selection here; the rule does
not query the suffix. If it can only pass, reuse the suffix coverage and add
the crossed boundary:

```sequent
C-Accept :=
  GAMMA, phi |- case(r, b :: K)
  GAMMA, phi |- match_bound(r, b, {accept})
  ===>
  GAMMA, phi |- covers_selection(r, b :: K, {selected(b, [], K)})

C-Pass :=
  GAMMA, phi |- case(r, b :: K)
  GAMMA, phi |- match_bound(r, b, {pass})
  GAMMA, phi |- covers_selection(r, K, S)
  ===>
  GAMMA, phi |- covers_selection(r, b :: K, prepend(b, S))
```

If both outcomes remain possible, cover selection here and all covered suffix
outcomes reached by passing:

```sequent
C-Both :=
  GAMMA, phi |- case(r, b :: K)
  GAMMA, phi |- match_bound(r, b, {accept, pass})
  GAMMA, phi |- covers_selection(r, K, S)
  ===>
  GAMMA, phi |- covers_selection(r, b :: K, {selected(b, [], K)} union prepend(b, S))
```

The rules describe known boundary contracts, not inspection of an opaque
constituent. The suffix judgment is an established fact, potentially
parameterized over the request and assumptions; applying it must not rerun
the constituent's verification. If the required suffix fact is missing, the
composition remains conditional or unproved. A context whose hidden shape or
selected owner is unknown needs a covering unknown outcome or explicit
obligation; it cannot be replaced with a fabricated known boundary or `[]`.

The uniform-condition rules are a conservative starting point. A more
precise account can attach different conditions to acceptance, passing and
each suffix outcome. It must instantiate each contract in its own lexical
context, conjoin conditions when composing cases and retain their
correlations. Only a proved infeasible case can be eliminated. Coarsening may
add impossible outcomes and cause conservative rejection; it must not be used
to prove an unsafe composition safe. Every feasible encounter must be covered
by acceptance or passing; an empty bound is valid only for an established
infeasible case.

## Using coverage

For `E<T>.op` at an inner `E<U>` handler, an established `same` fact gives
`{accept}`; an established `different` fact gives `{pass}`. Without either,
`{accept, pass}` preserves both the inner selection and selections or outward
requests after passing it. It does not state that either happens for every
specialization. If conditions are represented, the equality and inequality
cases can retain the relationship between this comparison and later ones.

The typechecker must establish the relevant payload, capture, completion and
interpretation premises for **each covered case under its condition**, unless
that case is proved infeasible. Failure to establish feasibility is not proof
of infeasibility. If one symbolic case represents several concrete outcomes,
its obligations must cover all of them and their relevant metadata. A coarse
bound may therefore require a proof for an outcome that is in fact
unreachable. A may-selection is not an exact selection; failure to prove
acceptance does not establish passing. An unproved discard premise remains an
obligation or rejects that discard. If a capture is only resumed and all other
applicable premises hold, uncertainty about its discardability alone must not
reject that resume.

These candidate rules do not establish that Ash has the needed condition
language, a finite representation for recursive or unknown behavior, or a
terminating checker. The [imported generic test](../../../tests/effect_modules.rs#L133)
exercises related equal and different instantiations, but was not run here and
does not prove coverage. A system-level argument must relate the eventual
rules to all relevant specified executions. The current implementation and
Core validation remain in force.
