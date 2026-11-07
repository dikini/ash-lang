# Deriving-clause fixtures

These proposed I09 and R03–R05 graphs use unimplemented CP-0034 syntax. Every
entry is a separate module; none of the derive expansions has run.

- `main.ash` applies two derives to a type and a newtype. It must return
  `42 : Int`; the original subjects are each retained once and the private
  implementations are appended in listed order. `control.ash` is the ordinary
  handwritten equivalent and returned `42 : Int` with the in-progress
  expression-slice compiler.
- `renamed.ash` must return `42 : Int` using a renamed derive import and a
  trailing list comma.
- `generic.ash` applies a procedural derive to a one-parameter newtype and
  must return `42 : Int`. Its generated `impl<A> Marker<Box<A>>` uses one fresh
  introduced parameter consistently. `control_generic.ash` is the handwritten
  equivalent. This particular derive assumes one `Type` parameter; it is not
  a general algorithm for arbitrary parameter lists or constraints. The
  handwritten control returned 42, and the transformer's ordinary Ash body
  checked after removing its unimplemented derive header; the generated
  implementation and its fresh parameter have not run through slice 2.
- `opaque.ash` imports a public derived implementation for an opaque newtype
  and must return 42. `opaque_hidden.ash` must reject direct constructor use.
  Their `control_opaque...` counterparts use a handwritten public impl and the
  same ordinary visibility rules; the positive control returned 42 and the
  negative control produced `resolve.opaque-constructor` with the in-progress
  expression-slice compiler.
- `duplicate.ash` invokes `marker` twice; ordinary checking must reject the
  conflicting implementations. `unimported.ash` must reject the missing syntax
  name; `empty.ash` must reject an empty derive list; and `unsupported.ash`
  must reject a clause on an interface.
- `wrong_kind.ash` imports an expression syntax named `marker`; its use in a
  deriving clause must reject the wrong syntax category at that name.
- `ordered_first.ash` and `ordered_second.ash` list the same two procedural
  derives in opposite orders. Their respective first errors must be `first
  derive rejected` and `second derive rejected`, with the subject, listed derive
  and definition origins. Neither graph publishes a partial subject or output.
- `generated_failure.ash` derives `spawn_failure` for `Source`. Its generated
  `Generated` subject has the definition-context `first_failure` derive, which
  rejects with `first derive rejected`. The diagnostic retains the original
  invocation and generated-subject origins; the failed expansion publishes
  neither `Source` nor `Generated` as part of a successful module.
- `generated_order.ash` lists `spawn_failure` before `second_failure`. The
  first derive emits a subject whose nested `first_failure` would reject. The
  second listed derive must run before that nested output is expanded, so the
  diagnostic is `second derive rejected`, not `first derive rejected`. The
  failed expansion publishes no subject or generated output.
- `nested.ash` derives `spawn` for `Source`; `spawn` emits a private generated
  type carrying a definition-context `marker` derive and a `probe` that needs
  the derived implementation. It must type-check the probe and return 42.
  This exercises generated subjects, owner-imported syntax, introduced names,
  ordered nested expansion and the existing expansion bound.

For `main.ash`, check the expanded declaration sequence as well as execution:
`Color` appears once, followed by `Marker<Color>` then `Tagged<Color>`; `Count`
appears once, followed by `Marker<Count>` then `Tagged<Count>`. Both derives on
each subject receive that subject's original declaration, including its full
deriving clause, not an earlier derive's output. The sequence assertion is a
syntax-expansion observation; the existing checker validates the implementations.

Each failure must retain the relevant clause and derive-definition locations;
no failing derive may publish its partial output.
