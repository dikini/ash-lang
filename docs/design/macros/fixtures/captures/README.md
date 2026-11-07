# Capture and repetition fixtures

These proposed I19 graphs use CP-0034 syntax, which is not implemented. They
supplement the identifier and type captures in the declaration-form fixtures.

- `main.ash` captures an expression, a pattern, and a complete braced
  signature-and-equation declaration; matches an empty `*`; and generates two
  functions through `+`. It must return `128 : Int`. `control.ash` is its
  handwritten ordinary-Ash equivalent and returned `128 : Int` with the
  in-progress expression-slice compiler.
- `counts.ash` exercises zero, one and two `*` captures and one and two `+`
  captures, in separate invocations. It must return `42 : Int` and match the
  handwritten `control_counts.ash` output.
- `empty_plus.ash` must reject the empty `+` matcher at `ones`.
- `trailing_separator.ash` must reject the comma after `first` at the `ones`
  invocation; it must not publish a partial declaration for `first`.
- `ambiguous_definition.ash` imports the unused `ambiguous` definition. Its
  matcher in `ambiguous_forms.ash` uses `,` both as a repetition separator and
  as the following literal. Definition admission rejects this ambiguous
  repetition boundary before an invocation.
- `missing_driver_definition.ash` imports the unused `missing_driver`
  definition. Its template repetition in `missing_driver_forms.ash` contains
  only literal declarations and has no repeated capture to drive it. Definition
  admission rejects the repetition without generating `fixed`.
- `mismatched.ash` matches two left names and one right name, then rejects the
  mismatched template driver lengths without publishing any output.
- `binder.ash` captures a pattern binder and an expression using that binder.
  The generated function must return 42 when called with 42. Its handwritten
  control is `control_binder.ash`. Ordinary name resolution must connect the
  caller-context pattern and body without capturing unrelated names.

For the three new failures, report the specific matcher or template cause and
its source; an invocation failure also retains the macro definition as related
context. Assert the human and JSON source roles, not fixed message wording.

The generator fixtures separately fix nested repetition, per-iteration state,
and repeated generated-value use. These macro graphs are proposed inputs, not
passing product tests.
