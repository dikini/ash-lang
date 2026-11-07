# Declaration diagnostic fixtures

These proposed I14/I15 graphs use the unimplemented CP-0034 syntax. Each entry
file is compiled independently. None is represented as a passing product test.
Assert the structured cause and source roles in both human and JSON diagnostics,
not a fixed rendering of the message.

- `type_error.ash` expands `bad_type` successfully and then fails ordinary
  checking because `true` is not `Int`. The generated body and its definition
  are relevant origins; the invocation and selected name must also be traceable.
- `missing.ash` fails while matching `need_name` because its identifier capture
  is absent. Report the invocation and matcher definition.
- `unused_bad.ash` imports `broken` without invoking it. Its missing equation
  body is a template syntax error in `malformed_forms.ash` and must be rejected
  at definition admission.
- `forbidden_import.ash` is rejected because the template attempts to emit an
  import. Reject the literal import at template definition admission; the
  dependency graph is fixed before expansion and is not changed. Imports
  introduced by a procedural result are rejected at output admission.
- `category.ash` uses a procedural transformer to construct a protected `Int`
  type fragment and return it as the complete declaration output. The host must
  reject the fragment's category at output admission and publish nothing.
- `recursive.ash` returns an invocation with a caller-context syntax name from
  its procedural transformer. Expansion must stop at the configured depth or
  work bound, report the invocation chain and definition, and publish no partial
  result. No numerical bound is prescribed by the language.
- `unused_free.ash` imports a syntactically valid macro whose template refers
  to `unknown_helper`, which is absent from the defining module. The unused
  definition is admitted and the program returns 42. `invoked_free.ash`
  invokes it while declaring a same-spelled caller helper; ordinary resolution
  must reject the unavailable definition-context name at expansion and retain
  the invocation and definition locations. Caller shadowing cannot rescue it.
- `derive_first.ash` and `declaration_first.ash` each contain two valid
  invocations whose procedural transformers reject. The former must report
  `derive rejected`; the latter must report `declaration rejected`. Neither
  graph publishes a partial module. These are expansion failures; ordinary
  parse or type errors are not ordered by this assertion.

The TokenKind name `LineEnd` in `recursive_forms.ash` follows the in-progress
expression-slice vocabulary and is subject to the shared lexical vocabulary
contract described in CP-0033. `recursive_forms.ash` uses only the slice 1
syntax service apart from its declaration-macro header. Its transformer body
was checked against the expression-slice compiler after removing that
unimplemented header. `category_forms.ash` was similarly checked against a
stand-in for the proposed type fragment and operation. Neither declaration
expansion path has run.
