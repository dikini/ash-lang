# Generator fixture

This is a fixed I17 source graph for historical
[CP-0034](https://github.com/dikini/ash-lang/blob/79c2d0723baa218a127640903f522694580bfc1e/docs/proposals/CP-0034-top-level-declaration-macros.md).
`forms.ash` defines the subtemplate variant; `procedural_forms.ash` uses
ordinary functions and the syntax service to select protected fragments. Both
use the agreed fragment-returning steps. The expected outputs and failures
below are acceptance requirements.
[TASK-0068](../../../../tasks/TASK-0068-top-level-declaration-macros.md) records
the delivery evidence and remaining gates.

## Construction details needed for transcription

The proposal selected both construction paths and required ordinary state-only
steps. CP-0034 describes a
[subtemplate and escape spelling](https://github.com/dikini/ash-lang/blob/79c2d0723baa218a127640903f522694580bfc1e/docs/proposals/CP-0034-top-level-declaration-macros.md#executable-template-escapes-and-expression-subtemplates)
and describes construction by the macro subsystem. The subtemplate source
graph and unused malformed-subtemplate cases are written below.

The procedural variant uses quotation to construct its input fragments, then
uses `Syntax.expression_syntax` and ordinary Ash traversal of `Syntax` nodes to
select one. The selected fragment keeps its original context and origin. This
exercises procedural syntax-service traversal, but does not demonstrate
constructing a fresh fragment from raw `Syntax` nodes. That distinct case has
a concrete limitation:

- The retained [syntax service](../../../../../spec/syntax-expansion.md#canonical-syntax-interface)
  and its [source declarations](../../../../../src/compiler_syntax.ash)
  expose `make_token`, which returns a token result, and `parse_expression`,
  which returns a fragment result but requires an invocation-owned `Input` and
  syntax nodes carrying an `Origin`. `Input`, `Origin`, and
  `ExpressionFragment` are opaque. An `Int` seed supplies none of them.
  `expression_syntax` can expose origins from an existing quoted fragment,
  but it does not construct a fragment or supply an `Input`. The listed
  operations do not show how this state-only step can parse arbitrary raw
  syntax into a fresh fragment.

This limitation is not an alternative design or an added API requirement.
Fallible syntax operations are handled by ordinary function code under the
existing rules; they require no generator-specific error protocol. C3
independently reviewed this coverage before the later delivery evidence.

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
- **Procedural:** build a tuple of quote-created fragments and use ordinary Ash
  functions and syntax-service operations to select a protected fragment.
  This does not establish raw-syntax construction from the service alone.

Both variants use the same state, cache, nesting, origin and failure assertions.
A compiler test must identify the actual syntax-definition and invocation
origins in a generated-code error; ordinary downstream checking owns that error.
The `forms.ash` graph provides the subtemplate source. The matching
`procedural_*.ash` callers use `procedural_forms.ash` and run the same cases.
The `zero_iterations`, `duplicate`, `invalid_step`, `diverging`, and malformed
quote cases are shared because they do not depend on the construction variant.

## Caller cases

- `main.ash` supplies an inline seed. `imported.ash` supplies the same seed
  through the checked `seeds.ash` dependency. Each must generate functions
  returning `100`, `1`, and `2`, and the weighted result must be `310 : Int`.
- `all_values.ash` exercises both generators at every state from `0` through
  `5`. It must produce `100, 1, 2, 3, 4, 5` and return `543310 : Int`, as in
  `control_all_values.ash`.
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
  `duplicate_forms.ash` even though the macro is not invoked. That file's
  step has the required return type and diverges if called; the duplicate case
  must fail at definition before it calls the step.
- `global.ash` generates `0, 1, 2, 3` and returns `3210 : Int`;
  `reset.ash` generates `0, 1, 0, 1` and returns `1010 : Int`. These distinguish
  a template-level generator from one owned by the outer repetition.
- `mixed_depth.ash` uses one generator at outer and inner repetition depths.
  The generated values in source order are `0, 1, 2, 0, 3, 4, 5, 3`; an outer
  iteration's cached value survives its inner iterations. Its weighted result
  and `control_mixed_depth.ash` must be `546210 : Int`.
- The two generators have independent states; each advances once per name.
  Both references to `$number` in the match body use the same iteration value.
- `zero_iterations.ash` invokes a `*` repetition with no groups. Its generator
  belongs to the outer repetition and has a diverging seed, so the program
  returns `42 : Int` only if zero iterations create no generator instance.

These additional negative cases use the same caller shape:

- `invalid_step.ash` and `invalid_step_forms.ash` supply a step with signature
  `Int -> Int`. Ordinary checking must report that it does not return the
  required state/value pair.
- `diverging.ash` and `diverging_forms.ash` use the correct fragment-returning
  step type but recurse indefinitely. Checked execution must stop at its
  configured bound, retain the invocation and step-function origins, and
  publish no generated declarations.
- `generated_type_error.ash` and `generated_type_error_forms.ash` return a
  fragment representing `true` while still returning `state + 1` as the next
  state. Ordinary checking must reject its use where the generated `Int`
  function needs an integer. The diagnostic identifies the actual syntax
  definition and invocation origins. Apply the same mutation to the procedural
  variant in `procedural_generated_type_error.ash` using its own `type_error`
  macro. Its diagnostic must identify the invocation in that file, the macro
  definition in `procedural_forms.ash`, and the `true` quotation in
  `boolean_bank`. `control_generated_type_error.ash` is the corresponding
  handwritten ordinary-Ash type error.
- `malformed_helper.ash` imports an unused macro whose defining module contains
  a malformed quote in an ordinary helper. `malformed_generator.ash` imports an
  unused macro whose generator contains the same malformed quote. Both must
  fail when their defining modules compile, without invoking a macro.

The inline, global, reset, and mixed-depth controls contain handwritten
ordinary-Ash outputs. The earlier expression-slice compiler returned `310 : Int`,
`3210 : Int`, `1010 : Int`, and `546210 : Int`, respectively.
`control_service.ash` runs on slice 1: its procedural expression
macro constructs a group containing two protected captures, parses it and uses
the selector to return the second fragment. It returns `42 : Int`. Its
transformer uses the `Input` supplied by slice 1; the generator steps in
`procedural_forms.ash` do not receive one. This control checks the service's
group and fragment behavior, not the proposed quotation or declaration macros.

The `digit` helper constructs fragments only for the fixed states `0` through
`5` needed here; it is not a general integer-to-syntax library. The subtemplate
variant passes each resulting fragment through `as_subtemplate` before use.

The previous ordinary Ash generator and interface-implementation bodies were
checked using a temporary stand-in for the now-superseded interface. That
historical check does not validate the selected fragment-returning step, macro
header, generator adapter, splice admission, staging or runtime results.
