# Procedural indexed derive fixture

This fixed I10/I11 source graph belongs to historical
[CP-0034](https://github.com/dikini/ash-lang/blob/79c2d0723baa218a127640903f522694580bfc1e/docs/proposals/CP-0034-top-level-declaration-macros.md).
[TASK-0068](../../../../tasks/TASK-0068-top-level-declaration-macros.md) records
the delivery evidence and remaining gates.

- `api.ash` defines the interface. `derives.ash` imports its interface and
  method and defines the proposed procedural derive.
- `one.ash`, `main.ash`, and `three.ash` invoke it on one, two, and three
  nullary constructors. Each must return `42 : Int` through the public driver.
  The expansion emits an ordinary private `Indexed<Color>` implementation
  with one `index Constructor = 1` equation per constructor, in source order.
  Inspect the emitted declaration syntax: `main.ash` must emit `Red` then `Blue`,
  and `three.ash` must emit `Red`, `Blue`, then `Green`. The equal return values
  alone cannot establish that ordering.
- `payload.ash` must reject `Red(Int)` with the author's unsupported-shape
  diagnostic at the payload's original group, and identify the deriving clause
  and macro definition as related origins. It must publish no derive output.
- `control_one.ash`, `control_two.ash`, and `control_three.ash` are handwritten
  ordinary-Ash controls for the three successful cases. Each returned `42 : Int`
  using the in-progress expression-slice compiler.
- `integrated.ash` imports `computed` from `exported.ash`, whose private type
  and implementation are produced through the procedural derive. It must
  return 42 through both the interpreter and supported build/image path after
  the compile-time host root is closed. `control_integrated.ash` is its
  handwritten ordinary-Ash counterpart and returned 42 in the interpreter.

The transformer is deliberately limited to nongeneric, private `type`
declarations with nullary constructors. Its restrictions are not language
restrictions. It inspects the protected subject via `declaration_syntax`, uses
the captured caller-context type and constructor identifiers, creates
definition-context references to the imported interface and method, and
constructs `Syntax` nodes without source-text re-lexing.

The token constructor spellings in this fixture (`Type`, `Impl`, `Less`,
`Greater`, `Equal`, `IntegerLiteral`, `LineEnd`, and `Pipe`) follow the
[current public token vocabulary](../../../../../spec/lexical-structure.md#public-token-kinds).

The ordinary Ash portions of `derives.ash` were checked with a temporary local
stand-in for the proposed `DeclarationFragment`, `DeclarationCapture`, and
`declaration_syntax` additions. This checks the function bodies against the
expression-slice compiler's Ash parser and type checker; it does not check the
new macro header, declaration fragment contents, expansion, hygiene, or output.
