# Module hygiene fixture

This proposed I12/I13/I16 graph exercises declaration and derive macros under
[CP-0034](../../../../proposals/CP-0034-top-level-declaration-macros.md). It
uses unimplemented syntax and is not a passing product test.

`main.ash` must return `252 : Int`: `first`, `second`, and `owner_result` each
return 42, and `checked` returns 126. The first two generated functions have
separate introduced `helper` bindings, isolated from each other and from the
caller module's handwritten `helper`. The macro-owner references in
`owner_result` still refer to the private `private_calculation` and to the
renamed public function through `facade`, despite same-spelled caller globals.
The declaratively derived `Marker<Color>` implementation is used in the
generated module without publishing its private type or implementation.

Required negative variants copy this directory and make one change each:

- In `generated.ash`, replace `make_value second` with `make_value first`.
  Reject the duplicate caller-visible global and publish neither conflicting
  expansion as a usable successful module result.
- In `main.ash`, replace its import with `import forms (private_calculation)`
  and replace `main`'s body with `private_calculation(())`. Reject the import of
  the macro owner's private helper; the macro's definition context does not
  make that helper visible to the caller.
- In `generated.ash`, change `helper () = 0` to `helper () = true`. The
  generated `first` and `second` must still return 42; the unrelated caller
  helper's result has no effect on them. Its signature must also be changed to
  `Unit -> Bool` so the handwritten declaration remains well typed.

The positive graph and the last variant must be exercised through the public
driver. The full I16 gate also requires the supported build/image path, host
teardown, and independent Core validation; those are not claimed here.
`control.ash` and `control_generated.ash` contain the handwritten equivalent;
the in-progress expression-slice compiler returned `252 : Int` for that graph.

`nominal_generated.ash` uses an imported macro to generate a transparent public
generic type and constructors. `nominal_main.ash` imports the generated type and
constructors and must return 42. `control_nominal_main.ash` and
`control_nominal_generated.ash` are the handwritten graph. This tests a public
caller-selected type and constructor across a module boundary.

`private_types.ash` invokes the same macro twice; each expansion introduces its
own private `Hidden` type and constructor, while the caller also has a
same-spelled type and constructor. Its two caller-selected functions must
return 42 each, giving 84. `control_private_types.ash` is the handwritten graph
with distinct private names. This checks non-term hygiene, not a special
duplicate-declaration exception.

`literal_public_forms.ash` writes a public function, type and constructor
directly in the template. `literal_public_generated.ash` uses those names in
the invoking module; `literal_public_main.ash` imports and uses them and must
return 84. The `control_literal_public_...` files give the handwritten output.
The separate `literal_public_duplicate.ash` invokes the macro twice and must
fail ordinary duplicate-name checking. In a fresh copy of the positive graph,
adding a handwritten `answer` definition in `literal_public_generated.ash`
must likewise reject its collision with the generated public function.
