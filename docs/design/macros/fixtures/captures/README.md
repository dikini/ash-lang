# Capture and repetition fixtures

These proposed I19 graphs use CP-0034 syntax, which is not implemented. They
supplement the identifier and type captures in the declaration-form fixtures.

- `main.ash` captures an expression, a pattern, and a complete braced
  signature-and-equation declaration; matches an empty `*`; and generates two
  functions through `+`. It must return `128 : Int`. `control.ash` is its
  handwritten ordinary-Ash equivalent and returned `128 : Int` with the
  in-progress expression-slice compiler.
- `empty_plus.ash` must reject the empty `+` matcher at `ones`.
- `mismatched.ash` matches two left names and one right name, then rejects the
  mismatched template driver lengths without publishing any output.
- `binder.ash` captures a pattern binder and an expression using that binder.
  The generated function must return 42 when called with 42. Its handwritten
  control is `control_binder.ash`. Ordinary name resolution must connect the
  caller-context pattern and body without capturing unrelated names.

The generator fixtures separately fix nested repetition, per-iteration state,
and repeated generated-value use. These macro graphs are proposed inputs, not
passing product tests.
