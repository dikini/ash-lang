# Header compatibility fixture

`expressions.ash` is an expression syntax whose name is `declaration` and
whose matcher includes the literal `:` and the literal `foo`. `compat.ash`
imports and invokes it; it must return `42 : Int` under CP-0033 without a
declaration macro. This is the concrete form that makes a bare
`syntax declaration: name` prefix ambiguous.

`derive_expressions.ash` and `derive_compat.ash` similarly fix an existing
expression syntax named `derive`, whose matcher starts with the literal
`marker` and captures an expression. Its invocation must return 42 under
CP-0033 and continue to do so after CP-0034. The previously proposed derive
headers share its prefix but are distinguishable by their complete forms:
slice 1 requires an expression capture at the end of a matcher.

`forms.ash` adds the proposed parenthesized declaration-macro header, and
`both.ash` invokes both macro categories. It must also return `42 : Int` once
CP-0034 is implemented. The parenthesized header is not a valid CP-0033 matcher
group, so it does not steal the expression definition's syntax.

`renamed.ash` imports the declaration macro under another name and must return
42. `collision.ash` imports both categories under the same syntax name and must
reject the colliding import. `own_definition.ash` attempts to invoke its own
definition and must reject the unimported syntax use, preserving CP-0033's
module staging rule.

Both expression-only graphs have returned 42 with the in-progress
expression-slice compiler. The mixed graph is not implemented and has not been
run.
