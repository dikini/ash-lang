# Generator fixture

This is a proposed I17 source graph for
[CP-0034](../../../../proposals/CP-0034-top-level-declaration-macros.md). It
uses unimplemented macro syntax. **Revision required:** `forms.ash` and
`duplicate_forms.ash` still use the superseded `SyntaxFragment` conversion
interface and do not satisfy the agreed `Int -> (Int, Syntax.ExpressionFragment)`
step. Revise the fixture to use ordinary Ash functions with the selected
fragment-returning type and demonstrate both construction paths. The expected outputs and failures below are preserved
for revising the source graph; they are not passing product tests or complete
acceptance inputs.

## Fixed generator behavior

The construction approaches are already selected in CP-0034. The revised I17
inputs must exercise both with the same bounded values and ordinary function
contract:

```text
next_number : Int -> (Int, Syntax.ExpressionFragment)
is_first : Int -> (Int, Syntax.ExpressionFragment)
```

For each `state` in `0` through `5`, `next_number` returns the next state
`state + 1` and a fragment representing the corresponding integer literal. The
fixed mapping is `0 -> syntax 0`, `1 -> syntax 1`, `2 -> syntax 2`,
`3 -> syntax 3`, `4 -> syntax 4`, and `5 -> syntax 5`. `is_first` returns
`(state + 1, syntax true)` for state `0` and `(state + 1, syntax false)` for
states `1` through `5`. Here `syntax 0` describes a fragment's content; it is
not an Ash source spelling or an implicit integer conversion.

Run each of the following two variants with the same callers and assertions
listed below:

- **Subtemplate:** construct the literal fragment, then insert it into a
  subtemplate through a fragment-valued hole. The resulting fragment contains
  that literal. This does not require interpolating an `Int` as syntax.
- **Procedural:** construct each literal fragment using ordinary Ash syntax
  operations. The function may use ordinary helpers of any valid type.

Both variants use the same state, cache, nesting, origin and failure assertions.
A compiler test must identify the actual syntax-definition and invocation
origins in a generated-code error; ordinary downstream checking owns that error.
The two variants are fixed behavioral inputs; their complete Ash source remains
to be transcribed using the selected construction paths. The old wrapper-based
`forms.ash` is not that source and must not be counted as a passing fixture.

## Caller cases

- `main.ash` supplies an inline seed. `imported.ash` supplies the same seed
  through the checked `seeds.ash` dependency. Each must generate functions
  returning `100`, `1`, and `2`, and the weighted result must be `310 : Int`.
- `local.ash` uses the caller's own `starting_number` global in its seed. It
  must fail at that reference with the declaration-expansion staging cause and
  must publish no generated function.
- `wrong_type.ash` supplies `true` to a generator whose state is `Int`. Normal
  Ash checking must report the mismatch at the supplied expression and retain
  the macro invocation and definition as related origins.
- `bad_fragment.ash` uses a valid expression fragment, representing `0`, in
  the type position of the generated signature (`pub $name : $wrong`). The
  ordinary declaration parser must reject that syntax without publishing the
  function. `duplicate.ash` must reject the two `$number` declarations in
  `duplicate_forms.ash` even though the macro is not invoked.
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
- Change `next_number` to return a fragment representing `true` instead of the
  integer literal, while still returning `state + 1` as the next state. Ordinary
  checking must reject its use where the generated `Int` function needs an
  integer. Apply this behavioral mutation to each construction variant.

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

The previous ordinary Ash generator and interface-implementation bodies were
checked using a temporary stand-in for the now-superseded interface. That
historical check does not validate the selected fragment-returning step, macro
header, generator adapter, splice admission, staging or runtime results.
