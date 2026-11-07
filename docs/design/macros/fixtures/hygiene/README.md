# Module hygiene fixture

This proposed I12/I13/I16 graph exercises declaration and derive macros under
[CP-0034](../../../../proposals/CP-0034-top-level-declaration-macros.md). It
uses unimplemented syntax and is not a passing product test.

`early_terms.ash` is a supplemental focused case using the same `make_value`
definition in `early_terms_forms.ash`, isolated from the derive and
definition-private helper paths in the full graph. The two generated functions
return 42 each, giving 84, as does `control_early_terms.ash` on current Ash.
`early_terms_duplicate.ash` supplies the same helper twice;
`early_terms_handwritten_duplicate.ash` supplies the handwritten `helper` as
the second helper. Ordinary downstream resolution rejects each duplicate and
identifies the conflicting declarations and macro origins. This focused case
does not replace the full I12 graph.

`early_owner.ash` is a supplemental focused case using the same `use_private`
definition in `early_owner_forms.ash`. Its definition-private helper and
renamed facade import must resolve despite same-spelled caller functions; it
returns 42, as does `control_early_owner.ash`. `early_owner_private.ash`
rejects the caller's direct import of the private helper under ordinary access
rules. This focused case does not replace the full I13 and opacity graphs.

`main.ash` must return `252 : Int`: `first`, `second`, and `owner_result` each
return 42, and `checked` returns 126. The first two generated functions use the explicitly supplied names
`helper_first` and `helper_second`, distinct from the caller module's handwritten `helper`. The macro-owner references in
`owner_result` still refer to the private `private_calculation` and to the
renamed public function through `facade`, despite same-spelled caller globals.
The declaratively derived `Marker<Color>` implementation is used in the
generated module without publishing its private type or implementation.

Required negative variants copy this directory and make one change each:

- In `generated.ash`, replace `make_value second using helper_second` with `make_value first using helper_second`.
  Reject the duplicate caller-visible global in ordinary downstream checking;
  identify both declarations and relevant macro invocations. The module must
  not be published as a successful result.
- In `generated.ash`, replace `make_value second using helper_second` with
  `make_value second using helper_first`. Ordinary downstream checking rejects
  the duplicate private helper and identifies both invocations and declaration
  origins. In a separate copy, use `helper` as the second supplied helper and
  require a diagnostic identifying the invocation and handwritten declaration.
- In `private_types.ash`, give both invocations the type `HiddenFirst` and
  distinct constructors. Ordinary downstream checking rejects the duplicate
  private type and identifies both invocations and declaration origins. In a
  separate copy, keep types distinct but use `HiddenFirst` for both constructors;
  ordinary checking rejects the duplicate constructor with both origins.
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

`private_types.ash` invokes the same macro twice with distinct caller-selected
private type and constructor names, while the caller also has a `Hidden` type
and constructor. Its two functions must return 42 each, giving 84.
`control_private_types.ash` is the handwritten graph with distinct private
names. Repeated names are errors under ordinary module rules, as the negative
variants above check.

`literal_public_forms.ash` writes a public function, type and constructor
directly in the template. `literal_public_generated.ash` uses those names in
the invoking module; `literal_public_main.ash` imports and uses them and must
return 84. The `control_literal_public_...` files give the handwritten output.
The separate `literal_public_duplicate.ash` invokes the macro twice and must
fail ordinary duplicate-name checking. In a fresh copy of the positive graph,
adding a handwritten `answer` definition in `literal_public_generated.ash`
must likewise reject its collision with the generated public function.
