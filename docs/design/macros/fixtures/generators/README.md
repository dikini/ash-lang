# Generator fixture

This is a proposed I17 source graph for
[CP-0034](../../../../proposals/CP-0034-top-level-declaration-macros.md). It
uses unimplemented macro syntax and the proposed `SyntaxFragment` interface;
it is not a passing product test.

- `main.ash` supplies an inline seed. `imported.ash` supplies the same seed
  through the checked `seeds.ash` dependency. Each must generate functions
  returning `100`, `1`, and `2`, and the weighted result must be `310 : Int`.
- `local.ash` uses the caller's own `starting_number` global in its seed. It
  must fail at that reference with the declaration-expansion staging cause and
  must publish no generated function.
- `wrong_type.ash` supplies `true` to a generator whose state is `Int`. Normal
  Ash checking must report the mismatch at the supplied expression and retain
  the macro invocation and definition as related origins.
- `bad_fragment.ash` splices a type token into an expression position and must
  fail syntax admission without publishing the function. `duplicate.ash` must
  reject the two `$number` declarations in `duplicate_forms.ash` even though
  the macro is not invoked.
- `global.ash` generates `0, 1, 2, 3` and returns `3210 : Int`;
  `reset.ash` generates `0, 1, 0, 1` and returns `1010 : Int`. These distinguish
  a template-level generator from one owned by the outer repetition.
- `mixed_depth.ash` uses one generator at outer and inner repetition depths.
  The generated values in source order are `0, 1, 2, 0, 3, 4, 5, 3`; an outer
  iteration's cached value survives its inner iterations. Its weighted result
  and `control_mixed_depth.ash` must be `546210 : Int`.
- The two generators have independent states; each advances once per name.
  Both references to `$number` in the match body use the same iteration value.

These additional negative variants each start from a fresh copy of `main.ash`
and `forms.ash`:

- Replace `next_number`'s signature with `Int -> Int` and its equation with
  `next_number state = state`. Ordinary checking must report that the step
  does not return the required state/value pair.
- Replace only the equation with `next_number state = next_number(state)`.
  Checked execution must stop at its configured bound, retain the invocation
  and step-function origins, and publish no generated declarations.
- In the existing `next_number` equation, replace
  `Syntax.IntegerLiteral, digit(state)` with `Syntax.True, "true"`. Expansion
  produces an expression fragment; ordinary checking must then reject its use
  where the generated `Int` function needs an integer.

`control_inline.ash`, `control_global.ash`, and `control_reset.ash` contain the
handwritten ordinary-Ash outputs. The in-progress expression-slice compiler
returned `310 : Int`, `3210 : Int`, and `1010 : Int`, respectively.
It also returned `546210 : Int` for `control_mixed_depth.ash`.

`digit` deliberately handles only the values `0` through `5` needed by these
fixtures; it is not a general integer-formatting library. The syntax service's
`IntegerLiteral`, `True` and `False` token mappings make `InvalidToken`
unreachable for the fixed spellings in this fixture. Its explicit fallback
constructs unit syntax to keep the ordinary Ash match exhaustive; an incorrect
service mapping would therefore make the generated Int-valued program fail
ordinary type checking. The final shared public token vocabulary must be
documented independently of this example, as required by CP-0033.

The ordinary Ash generator and interface-implementation bodies were checked
against the expression-slice compiler using a temporary local stand-in for the
proposed interface. This does not validate the macro header, generator adapter,
splice admission, staging, or runtime results.
