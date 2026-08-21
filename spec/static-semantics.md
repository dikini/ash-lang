# Static Semantics

Mini-Ash has four structural type forms: `Int`, `Bool`, `Unit`, and a unary
function type from a domain to a codomain. Surface `domain -> codomain` denotes
that function type. Two types are equal exactly when their structures are
equal.

The typing environment `GAMMA` maps resolved binder identities to monotypes.
The judgment `GAMMA |- expression ⇒ type` synthesizes a type, while
`GAMMA |- expression ⇐ type` checks an expression against an expected type.

## Primitive expressions

Literals and resolved variables synthesize types. Any expression that
synthesizes a structurally equal type checks against that expected type.

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

  T-Variable :=
    x : type in GAMMA
    ===>
    GAMMA |- x ⇒ type

  T-Check-Inferred :=
    GAMMA |- expression ⇒ type_1
    type_1 = type_2
    ===>
    GAMMA |- expression ⇐ type_2
```

Here `n` ranges over integer literals, `b` over Boolean literals, and `x` over
resolved occurrences. The equality premise in `T-Check-Inferred` is structural
type equality.

## Functions and application

An anonymous function checks only when an expected function type supplies its
parameter and result types. Application first synthesizes the function, then
checks the argument against its domain.

```sequent
family function-typing:
  T-Function-Check :=
    GAMMA, x : domain |- body ⇐ codomain
    ===>
    GAMMA |- fn(x) { body } ⇐ Function(domain, codomain)

  T-Apply :=
    GAMMA |- function ⇒ Function(domain, codomain)
    GAMMA |- argument ⇐ domain
    ===>
    GAMMA |- function argument ⇒ codomain
```

An anonymous function in a position that must synthesize has no applicable
rule and is rejected with `type.function-needs-context`. Mini-Ash does not infer
a parameter type for that case.

## Blocks

Block bindings are checked from left to right. An annotated initializer checks
against its annotation. An unannotated initializer must synthesize its binding
type. The new binder is available only in the remainder.

```sequent
family block-typing:
  T-Block-Result :=
    GAMMA |- result ⇒ result_type
    ===>
    GAMMA |- { result } ⇒ result_type

  T-Block-Let-Inferred :=
    GAMMA |- initializer ⇒ binding_type
    GAMMA, x : binding_type |- { remainder } ⇒ result_type
    ===>
    GAMMA |- { let x = initializer; remainder } ⇒ result_type

  T-Block-Let-Checked :=
    GAMMA |- initializer ⇐ binding_type
    GAMMA, x : binding_type |- { remainder } ⇒ result_type
    ===>
    GAMMA |- { let x : binding_type = initializer; remainder } ⇒ result_type
```

The semicolons in the two binding conclusions separate semantic fields. They do
not add semicolon punctuation to Ash source.

## Primitive operations

Addition and multiplication require two `Int` operands and synthesize `Int`.
Equality compares only integers in Mini-Ash and synthesizes `Bool`.

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

The rules reject an operand that does not check as `Int`. The executable test
`static_semantics_operand_example_has_its_documented_reason` checks that this
file is rejected with `type.operator-operand`:

```ash
true + 1
```

## Globals and programs

An equational interface must expose one function domain and codomain. Its
binder has the domain type while its body checks against the codomain. An
inline operational header supplies those same two types directly. Either form
contributes a function type only to the following program scope.

```sequent
family global-and-program-typing:
  T-Equational-Global :=
    GAMMA, parameter : domain |- body ⇐ codomain
    ===>
    GAMMA |-definition name : Function(domain, codomain); name parameter = body ⇒ name : Function(domain, codomain)

  T-Operational-Global :=
    GAMMA, parameter : domain |- body ⇐ codomain
    ===>
    GAMMA |-definition fn name(parameter : domain) -> codomain { body } ⇒ name : Function(domain, codomain)

  T-Program-Definition :=
    GAMMA |-definition definition ⇒ name : definition_type
    GAMMA, name : definition_type |-program remainder ⇒ result_type
    ===>
    GAMMA |-program definition; remainder ⇒ result_type

  T-Program-Result :=
    GAMMA |- result ⇒ result_type
    ===>
    GAMMA |-program result ⇒ result_type
```

The definition judgment returns the name and type added to the following
scope. The program rules process definitions sequentially and synthesize the
file type from its required result expression. Semicolons in these judgments
separate semantic fields and are not source punctuation. Resolution has already
ensured global-name freshness and equational name agreement.

There are no inference variables, generalization, polymorphism, overloading,
subtyping, implicit conversions, or recursive typing environments in Mini-Ash.
