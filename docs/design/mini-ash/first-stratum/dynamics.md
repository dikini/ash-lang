# Provisional first-stratum dynamics

> These rules are informative evidence governed by
> [DN-0016](../../DN-0016-first-mini-ash-corpus.md). They support comparison and
> do not define current Ash dynamic semantics or accept an evaluator design.

The provisional relation `e -> e'` takes one deterministic reduction step. The
values are integer and Boolean literals, `()`, and anonymous function values.
Inline operational and equational globals may elaborate to the same or similar
anonymous function form for the binder-only cases in this stratum. Block-local
bindings elaborate to nested nonrecursive binding terms. Both elaborations
retain source origins and definition-specific facts even when those facts have
no runtime action.

`substitute(e, x, v)` is capture-avoiding replacement of occurrences resolved
to binder `x` in expression `e` by value `v`. The written rules use substitution
to keep the semantic account independent of evaluator representation. A direct
evaluator may use explicit environments and function data, while an
explicit-machine candidate may use frames; both must produce the same results
and observable traces.

Grouping parentheses have already been removed by surface elaboration before
the reduction relation applies. Their delimiters remain in source provenance,
so a diagnostic can still label the grouping written by the user.

## Presentation elaboration

For binder-only definitions, the two surface forms can produce the same semantic
function value after their distinct surface checks:

```text
name : τ₁ -> τ₂        fn name(x : τ₁) -> τ₂ { body }
name x = body                      |
          \                        /
                fn(x) { body }
```

This diagram is explanatory text rather than an inference rule. A multi-clause
equational definition instead elaborates to a function whose body is a typed
match. The equivalent inline operational definition writes that match
explicitly. Pattern typing and coverage occur before both reach comparable Core.

Whole-program elaboration binds each checked global over the remainder of the
file in source order:

```text
definition₁
definition₂
result
  ⇝ let name₁ = function₁;
       let name₂ = function₂;
         result
```

Each generated initializer is outside its own binding's scope, while its body
contains the later definitions and result. Globals are therefore nonrecursive
and visible only to the source that follows them in this stratum. Generated
bindings and function values retain the interface, presentation, and source
origins from which they were elaborated.

For X-001, the equational clauses build the match that the inline operational
definition writes explicitly:

```text
negate : Bool -> Bool          fn negate(value : Bool) -> Bool {
negate true = false                match value {
negate false = true                   true  => false
               |                      false => true
               |                  }
               |              }
               v                      |
          fn(value) {                 |
              match value { <---------+
                  true  => false
                  false => true
              }
          }
```

The equation group carries implicit scrutinee construction; the inline body
carries an explicit source match. After shared pattern and coverage checks,
their typed match bodies can converge without losing their different origins.

X-003 follows the function type rather than attaching a separate arity to a
name. Its equational and inline operational definitions have these distinct
elaboration shapes:

```text
add : Int -> Int -> Int           fn add(left : Int, right : Int) -> Int
add left right = left + right
              |                                  |
              v                                  v
fn(left) { fn(right) {              fn(arguments : (Int, Int)) {
    left + right                         let (left, right) = arguments
} }                                      left + right
                                     }
```

The equational use supplies arguments through successive applications. The
operational use constructs one tuple value as its product-domain argument. Both
can calculate the same result, but their Core type and application structure
must remain distinct.
For this comparison only, a tuple of values is a value and its elements evaluate
strictly from left to right. The operational parameter list elaborates to one
tuple pattern over that value; general tuple dynamics remain outside the first
retained boundary.

The following probe-only rules make that claim executable for a two-component
product. The tuple steps its left component first, then its right component. An
inserted tuple binding substitutes both components only after they are values.

```sequent
family product-pressure-steps:
  E-Tuple-Left :=
    left -> left'
    ===>
    (left, right) -> (left', right)

  E-Tuple-Right :=
    right -> right'
    ===>
    (left_value, right) -> (left_value, right')

  E-Let-Tuple :=
    ===>
    let (x, y) = (left_value, right_value); body -> substitute(substitute(body, x, left_value), y, right_value)
```

Here `left_value` and `right_value` range over values, and `x` and `y` are
distinct resolved binders that are not in scope in the initializer. These rules
exist only to make X-003's product-domain comparison derivable; they do not add
general product data or pattern bindings to the retained boundary.

## Bindings

The initializer of an elaborated binding steps to a value before substitution
into its body. This makes bindings strict and nonrecursive.

```sequent
family binding-steps:
  E-Let-Step :=
    initializer -> initializer'
    ===>
    let x = initializer; body -> let x = initializer'; body

  E-Let-Value :=
    ===>
    let x = value; body -> substitute(body, x, value)
```

The semicolon separates fields of the semantic binding term and does not claim
surface punctuation. In `E-Let-Value`, `value` ranges only over the value forms
listed above. V-004 can therefore substitute the captured integer into the
function body before application; an environment-based evaluator must preserve
the same lexical fact explicitly.

## Applications

Application evaluates the function first and the argument second. Juxtaposition
associates to the left, so `f a b` means `(f a) b`. Once both sides are values,
application substitutes the argument for the function parameter.

```sequent
family application-steps:
  E-Apply-Function :=
    function -> function'
    ===>
    function argument -> function' argument

  E-Apply-Argument :=
    argument -> argument'
    ===>
    (fn(x) { body }) argument -> (fn(x) { body }) argument'

  E-Beta :=
    ===>
    (fn(x) { body }) value -> substitute(body, x, value)
```

The second rule applies only after the function expression is a function value.
A well-typed closed program cannot apply a non-function value; `T-003` is
rejected before evaluation.

## Cross-stratum Boolean matches

The X-001 probe steps the match scrutinee before selecting the arm whose Boolean
pattern equals the resulting value. Successful coverage checking ensures that
one arm is available; X-002 is rejected before evaluation.

```sequent
family boolean-match-steps:
  E-Match-Scrutinee :=
    scrutinee -> scrutinee'
    ===>
    match scrutinee { arms } -> match scrutinee' { arms }

  E-Match-Boolean :=
    selected-arm(boolean, arms) = body
    ===>
    match boolean { arms } -> body
```

These rules distinguish equation elaboration from runtime behavior. They are
pressure for the shared match machinery described by DN-0007, not part of the
first retained dynamic semantics.

## Primitive operations

Each primitive operation evaluates left to right. The calculation rules apply
only to literal operands and produce the corresponding mathematical integer or
Boolean result.

```sequent
family addition-steps:
  E-Add-Left :=
    left -> left'
    ===>
    left + right -> left' + right

  E-Add-Right :=
    right -> right'
    ===>
    n + right -> n + right'

  E-Add-Values :=
    n_3 is the integer sum of n_1 and n_2
    ===>
    n_1 + n_2 -> n_3

family multiplication-steps:
  E-Multiply-Left :=
    left -> left'
    ===>
    left * right -> left' * right

  E-Multiply-Right :=
    right -> right'
    ===>
    n * right -> n * right'

  E-Multiply-Values :=
    n_3 is the integer product of n_1 and n_2
    ===>
    n_1 * n_2 -> n_3

family equality-steps:
  E-Equal-Left :=
    left -> left'
    ===>
    left == right -> left' == right

  E-Equal-Right :=
    right -> right'
    ===>
    n == right -> n == right'

  E-Equal-Values :=
    b is true exactly when n_1 and n_2 are the same integer
    ===>
    n_1 == n_2 -> b
```

The integer model, overflow behavior, and literal range remain unresolved. A
prototype may use host integers only if it reports where host behavior appears
and does not present that behavior as Ash semantics.

## Representative traces

V-001 demonstrates precedence before dynamics begin:

```text
1 + 2 * 3
→ 1 + 6
→ 7
```

After block elaboration and name resolution, V-003 demonstrates lexical
shadowing with distinct binder identities:

```text
let value₁ = 1; let value₂ = value₁ + 1; value₂
→ let value₂ = 1 + 1; value₂
→ let value₂ = 2; value₂
→ 2
```

V-008 demonstrates whole-program elaboration and nested strict applications.
The trace uses short resolved binder names but makes both generated global
bindings explicit:

```text
let increment = fn(i) { i + 1 };
  let double = fn(d) { d * 2 };
    double (increment 20)
→ let double = fn(d) { d * 2 };
    double ((fn(i) { i + 1 }) 20)
→ (fn(d) { d * 2 }) ((fn(i) { i + 1 }) 20)
→ (fn(d) { d * 2 }) (20 + 1)
→ (fn(d) { d * 2 }) 21
→ 21 * 2
→ 42
```

X-003's operational form reduces through one tuple argument and the generated
product binding:

```text
(fn(arguments) {
    let (left, right) = arguments;
    left + right
}) (20, 22)
→ let (left, right) = (20, 22); left + right
→ 20 + 22
→ 42
```

The trace is cross-stratum evidence only. It demonstrates the product shape
without making tuple construction or destructuring a retained first-stratum
feature.

## Evaluator comparison

Compare a structured direct evaluator and an explicit first-order machine on:

- agreement between both V-002 definitions and every other valid result;
- agreement with the representative reduction traces;
- whether evaluation order is observable in inspectable data;
- whether the Rust call stack or panic behavior can leak into Ash behavior;
- the machinery required for lexical functions in the pure stratum;
- reuse of typed values and validation without erasing representation
  invariants.

No continuation form is required merely because later effects may need one. If
the explicit machine wins for current reasons, its frames must be typed,
inspectable data rather than Rust closures.
