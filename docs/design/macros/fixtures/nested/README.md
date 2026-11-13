# Nested declaration syntax fixture

This fixed I20 graph exercises declaration syntax.
[TASK-0068](../../../../tasks/TASK-0068-top-level-declaration-macros.md) records
the delivery evidence and remaining gates. `outer_forms.ash` imports `inner` from
`inner_forms.ash` and emits an invocation of that syntax
from its definition context. The caller imports a different `inner` from
`caller_forms.ash`. `main.ash` must return `42 : Int`, showing that the
definition-context invocation was not redirected to the caller's macro, which
would generate zero. `control.ash` is the corresponding ordinary-Ash output and
returned 42 with the in-progress expression-slice compiler.

The recursive procedural graph in the adjacent diagnostic fixtures tests
caller-context syntax and bounded recursive expansion separately.

`forward.ash` generates two mutually recursive functions. The first refers
forward to the second, and their execution returns 42. `control_forward.ash`
is the handwritten equivalent and returned 42 with the in-progress
expression-slice compiler. These names come from invocation captures and are
visible to the caller after the whole expansion is admitted.
