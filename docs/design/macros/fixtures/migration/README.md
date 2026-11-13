# Closed syntax-sum migration fixture

These proposed I18 graphs use the shared `Capture` family from CP-0033 and
the added alternatives in CP-0034.

Under the in-progress expression-slice compiler, `old.ash` must return
`42 : Int`; this graph was run and returned that value. `classify` explicitly
matches both original `Capture` cases.
Under CP-0034, the same source must fail ordinary coverage checking because
four new cases are absent. It must not silently treat them as an old case.

`new.ash` selects `new_forms.ash`, which explicitly handles all six cases and
preserves the existing expression transform. Under CP-0034 it must return
`42 : Int`, with the input origin and context preserved.
[TASK-0068](../../../../tasks/TASK-0068-top-level-declaration-macros.md) records
the delivery evidence and remaining gates.

`fallback.ash` uses `fallback_forms.ash`, which handles expression captures
and treats every other case as unsupported. It returned 42 under the
expression-slice compiler. Its ordinary function bodies also checked against
the expanded stand-in family. Under CP-0034 the complete graph must still
return 42 and its fallback must continue to classify non-expression cases as
unsupported.

With a temporary local stand-in containing the proposed expanded `Capture`
family and with the macro headers removed, the in-progress compiler rejected
the old `classify` as `coverage.non-exhaustive` and accepted the new function
bodies. This checks ordinary exhaustiveness and types only; it does not test
canonical syntax-service identity or an expanded macro invocation.
