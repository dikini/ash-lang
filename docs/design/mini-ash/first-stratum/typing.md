# Provisional first-stratum typing

> These judgments are informative evidence governed by
> [DN-0016](../../DN-0016-first-mini-ash-corpus.md). They support comparison and
> do not define current Ash static semantics or accept a typechecker algorithm.

The retained-boundary type language contains `Int`, `Bool`, `Unit`, and
monomorphic function types `τ₁ -> τ₂`; X-003 additionally uses one probe-only
product type. A context `Γ` maps resolved binders to one monotype. The judgment
`Γ |- e ⇒ τ` synthesizes a type from an expression, while `Γ |- e ⇐ τ` checks an
expression against an expected type. This begins from the bidirectional
suggestion in [DN-0006](../../DN-0006-initial-type-system.md) rather than
inventing mandatory parameter annotations for anonymous functions.
Grouping parentheses have already been removed by surface elaboration before
these judgments apply. Their source origin remains available for diagnostics,
but they require no separate typing rule.

## Primitive values and variables

The following rules synthesize the three primitive types. A variable synthesizes
the monotype stored for its resolved binder in `Γ`. An expression that
synthesizes the expected type may also check against it; `τ₁ = τ₂` is structural
equality for this provisional monomorphic type algebra.

```sequent
family primitive-typing:
  T-Int :=
    ===>
    GAMMA |- n ⇒ Int

  T-Bool :=
    ===>
    GAMMA |- b ⇒ Bool

  T-Unit :=
    ===>
    GAMMA |- () ⇒ Unit

  T-Var :=
    x : tau in GAMMA
    ===>
    GAMMA |- x ⇒ tau

  T-Check-Inferred :=
    GAMMA |- expression ⇒ tau_1
    tau_1 = tau_2
    ===>
    GAMMA |- expression ⇐ tau_2
```

Here `n` ranges over integer literals, `b` over Boolean literals, and `x` over
resolved occurrences. The keyboard aliases keep the source typeable while the
renderer may display conventional Greek letters and turnstiles. In the formulas,
`⇒` and `⇐` label synthesis and checking; they are not inference separators.

## Functions and applications

An anonymous operational function checks against an expected domain and
codomain. This makes the parameter type available while checking the body. An
application synthesizes its function, checks its argument against the exposed
domain, and synthesizes the codomain.

```sequent
family functional-typing:
  T-Function-Check :=
    GAMMA, x : tau_1 |- body ⇐ tau_2
    ===>
    GAMMA |- fn(x) { body } ⇐ tau_1 -> tau_2

  T-Apply :=
    GAMMA |- function ⇒ tau_1 -> tau_2
    GAMMA |- argument ⇐ tau_1
    ===>
    GAMMA |- function argument ⇒ tau_2
```

V-004 gets the expected function type from its local annotation. V-005 gets the
global parameter type from the inline interface and gives its anonymous
application argument the function domain as an expected type. This stratum does
not require an unannotated anonymous function to synthesize a type.

## Blocks and bindings

Surface blocks elaborate their local lines to nested nonrecursive binding terms.
The first rule synthesizes an unannotated initializer before extending the
context. The second checks an annotated initializer against its written type.
In both rules, the initializer is checked outside the new binding's scope.

```sequent
family binding-typing:
  T-Let-Inferred :=
    GAMMA |- initializer ⇒ tau_1
    GAMMA, x : tau_1 |- body ⇒ tau_2
    ===>
    GAMMA |- let x = initializer; body ⇒ tau_2

  T-Let-Annotated :=
    GAMMA |- initializer ⇐ tau_1
    GAMMA, x : tau_1 |- body ⇒ tau_2
    ===>
    GAMMA |- let x : tau_1 = initializer; body ⇒ tau_2
```

The semicolon in these conclusions separates fields of the elaborated binding
term; it is not a claim about surface punctuation. V-003 resolves the second
initializer to the outer `value` and the remaining body to the inner `value`.

## Global interfaces and presentations

An equational definition and an inline operational definition may elaborate to
the same or similar callable structure after their definition-specific checks.
The equational interface supplies an expected type to its clauses. An inline
operational header supplies its domain and codomain exactly once. The rest of
the file sees either checked global at the resulting function type.

```sequent
family global-typing:
  T-Equational-Global :=
    elaborate-presentation(body) = function
    GAMMA |- function ⇐ tau
    GAMMA, name : tau |- rest ⇒ result_type
    ===>
    GAMMA |- name : tau; body; rest ⇒ result_type

  T-Inline-Operational-Global :=
    GAMMA, parameter : domain |- body ⇐ codomain
    GAMMA, name : domain -> codomain |- rest ⇒ result_type
    ===>
    GAMMA |- fn name(parameter : domain) -> codomain { body }; rest ⇒ result_type
```

For the base stratum, an equation head contains one irrefutable binder. The
declared domain determines its type and grouping. Presentation-specific source
provenance survives elaboration. Core need not gain separate equational and
inline operational function kinds merely because their surface checks,
diagnostics, and tooling strengths differ.

## Cross-stratum pattern pressure

X-001 and X-002 use the pattern-checking direction suggested by
[DN-0007](../../DN-0007-data-and-pattern-typing.md). The provisional judgment
`Γ |-pattern p : τ ⇒ Δ` checks pattern `p` against expected type `τ` and returns
the bindings `Δ`. A binder accepts its expected type, while the two Boolean
patterns introduce no bindings.

```sequent
family boolean-pattern-typing:
  P-Binder :=
    ===>
    GAMMA |-pattern x : tau ⇒ { x : tau }

  P-True :=
    ===>
    GAMMA |-pattern true : Bool ⇒ { }

  P-False :=
    ===>
    GAMMA |-pattern false : Bool ⇒ { }
```

The match rule checks the scrutinee, every pattern, and every arm body against a
shared result type. The same coverage operation must report the Boolean pattern
set as exhaustive. This rule is comparison pressure only; it does not place
matches in the first retained semantic increment.

```sequent
T-Boolean-Match :=
  GAMMA |- scrutinee ⇒ Bool
  for every i, GAMMA |-pattern pattern_i : Bool ⇒ bindings_i
  for every i, GAMMA, bindings_i |- body_i ⇐ tau
  coverage(Bool, patterns) = Exhaustive
  ===>
  GAMMA |- match scrutinee { pattern_i maps-to body_i } ⇒ tau
```

An equation group checks its heads with the same pattern judgment, checks all
right-hand sides against the declared codomain, and invokes the same coverage
operation. It then elaborates to a function whose body is a match. X-002 must
therefore report `false` as missing for both source definitions.

## Cross-stratum definition and application grouping

X-003 applies the type-directed grouping rule suggested by DN-0005 and DN-0006.
An equational pattern list consumes successive arrow domains and elaborates to
nested functions; juxtaposed applications consume those domains successively.
An inline operational comma-separated parameter list decomposes one product
domain and elaborates to one function over that product; its application
therefore supplies one tuple value.

```sequent
family two-parameter-definition-typing:
  T-Tuple-Two :=
    GAMMA |- left ⇒ domain_1
    GAMMA |- right ⇒ domain_2
    ===>
    GAMMA |- (left, right) ⇒ (domain_1, domain_2)

  T-Equational-Curried :=
    GAMMA, x : domain_1, y : domain_2 |- body ⇐ codomain
    ===>
    GAMMA |- name x y = body ⇐ domain_1 -> domain_2 -> codomain

  T-Inline-Operational-Product :=
    GAMMA, x : domain_1, y : domain_2 |- body ⇐ codomain
    ===>
    GAMMA |- fn name(x : domain_1, y : domain_2) -> codomain { body } ⇐ (domain_1, domain_2) -> codomain

  T-Let-Product-Two :=
    GAMMA |- initializer ⇒ (domain_1, domain_2)
    GAMMA, x : domain_1, y : domain_2 |- body ⇒ result_type
    ===>
    GAMMA |- let (x, y) = initializer; body ⇒ result_type
```

These rules do not give Core two function types. Core retains one
`Function(domain, codomain)` constructor: the equational type nests it, while
the operational type uses a product as its one domain. A tuple-domain equation
uses one tuple pattern instead of a multi-pattern curried head. The final rule
checks the product destructuring inserted when an operational parameter tuple
elaborates to a single semantic argument.

## Primitive operations

Addition and multiplication check both operands against `Int` and synthesize
`Int`. Equality in this corpus compares integers and synthesizes `Bool`; it is
not an overloaded or polymorphic operation.

```sequent
family primitive-operation-typing:
  T-Add :=
    GAMMA |- left ⇐ Int
    GAMMA |- right ⇐ Int
    ===>
    GAMMA |- left + right ⇒ Int

  T-Multiply :=
    GAMMA |- left ⇐ Int
    GAMMA |- right ⇐ Int
    ===>
    GAMMA |- left * right ⇒ Int

  T-Integer-Equal :=
    GAMMA |- left ⇐ Int
    GAMMA |- right ⇐ Int
    ===>
    GAMMA |- left == right ⇒ Bool
```

## Case obligations

| Cases | Expected type |
| --- | --- |
| `V-001` through `V-005`, `V-008` | `Int` |
| `V-006` | `Unit` |
| `V-007` | `Bool` |

The rejected cases distinguish four structured failures:

- `T-001` fails while checking an elaborated equation against its global
  interface;
- `T-002` fails while checking the left operand of integer addition;
- `T-003` fails because the applied expression cannot expose a function domain
  and codomain;
- `T-004` fails while checking an argument against the domain recorded by the
  global interface.

## Representation and algorithm pressure

A candidate typechecker should record one structured reason for each failed
rule application and retain the source origins required by
[diagnostics.md](diagnostics.md). Its output must make every binder's type and
every expression's result type inspectable and independently validatable.

This corpus does not exercise generalization, inference variables, kinds beyond
`Type`, or type application. Those enter later strata. A candidate may represent
their extension seams, but unreachable machinery needs named invariants and must
not make the monomorphic rules indirect or their diagnostics less specific.
