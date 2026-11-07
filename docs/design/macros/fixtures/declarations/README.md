# Declaration form fixtures

These proposed I01–I07 graphs exercise every current top-level output category
under [CP-0034](../../../../proposals/CP-0034-top-level-declaration-macros.md).
`forms.ash` defines the declaration macros. Each `case_01.ash` through
`case_07.ash` is a separate entry module in this directory and must return
`42 : Int` through the public compiler driver after slice 2 is implemented.
They are not passing product tests yet.

The cases cover, in order: a `type`; a `newtype`; an `interface`; an `impl`;
an `effect` and its handler; a `foreign library` without invoking its native
symbol; and equational plus inline globals. Each `control_NN.ash` is the
corresponding handwritten ordinary-Ash program. All seven controls returned
`42 : Int` with the in-progress expression-slice compiler.

`generic.ash` and `methods.ash` cover a generic multi-constructor type and
newtype and an interface with two methods; each must return `42 : Int`.
Their handwritten controls also returned 42. `opaque.ash` must return 42
through public functions returning an opaque newtype and an opaque type;
`opaque_hidden.ash` and `opaque_sum_hidden.ash` must reject access to their
withheld constructors. The corresponding handwritten controls returned 42 and
rejected with `resolve.opaque-constructor`.

`relation.ash`, `higher.ash` and `constrained_impl.ash` cover an interface
determination, a higher-kinded interface parameter, and a generic constrained
implementation. Each must return `42 : Int`; all three handwritten controls
returned that value.

`operations.ash` exercises a generated effect with two operations and must
return 42; `control_operations.ash` is its handwritten counterpart and returned
42 with the in-progress expression-slice compiler.

`duplicate_constructors.ash`, `duplicate_methods.ash`,
`duplicate_operations.ash`, and `mismatched_newtype.ash` must reject the
generated output for the same ordinary causes as their `control_...` files.
The controls produced `resolve.duplicate-constructor`,
`resolve.duplicate-global`, `resolve.duplicate-global`, and
`resolve.newtype-constructor-name`, respectively. Their generated diagnostics
must also retain the relevant input and macro origins.

Required basic negative variants copy the graph and change one item at a time:

- In `case_01.ash`, invoke `make_type Color constructor Red` twice. Reject the
  duplicate caller-visible type and constructor.
- In `case_04.ash`, add a handwritten `impl Marker<Color>` after the macro
  invocation. Reject the duplicate implementation using ordinary checking.
- In `forms.ash`, remove the `profile` line from `make_foreign`. Reject its
  output using ordinary foreign-library admission.
- In `forms.ash`, duplicate the existing `profile` line in `make_foreign`.
  Reject the resulting duplicate profile using ordinary foreign-library admission.
- In `case_07.ash`, replace `make_identity id for Int` with
  `make_identity id for`. Reject the incomplete type capture at the invocation.

The following additional I08 variants each start from a fresh copy of the
named graph. Apply the corresponding change to its handwritten control and
compare the ordinary checking outcome. Macro definition syntax failures are
reported at definition admission; semantic failures follow ordinary checking.

| Graph | Single change | Expected outcome |
| --- | --- | --- |
| `case_01.ash` and `forms.ash` | Change `pub type $T = $C(Int)` to `type $T = $C(Int)`. | The local match returns 42; a separate module attempting to import `Color` rejects its private visibility. |
| `generic.ash` and `extra_forms.ash` | Remove the `\|` before `$second` in `make_generic_type`. | Reject the malformed constructor separator at template admission. |
| `case_02.ash` and `forms.ash` | Change `$C(Int)` to `$C(Unknown)` in `make_newtype`. | Reject the unresolved representation type through ordinary checking. |
| `case_03.ash` and `forms.ash` | Change `$m : A -> Bool` to `$m : A ->`. | Reject the incomplete method type at template admission. |
| `case_04.ash` and `forms.ash` | Remove the `$m _ = true` equation. | Reject the incomplete `Marker<Color>` implementation through ordinary checking. |
| `case_04.ash` and `forms.ash` | Change `$m _ = true` to `other _ = true`. | Reject the unexpected method head through ordinary checking. |
| `operations.ash` and `extra_forms.ash` | Change `$second : Unit -> Int` to `$second : Unit ->`. | Reject the incomplete operation type at template admission. |
| `case_06.ash` and `forms.ash` | Add `symbol Other : Unit -> F.Address { name "fixture_other" }` after the existing symbol. | Admit both foreign symbols and return 42 without calling either. |
| `case_06.ash` and `forms.ash` | Remove the `name "fixture_make"` member from `$S`'s symbol block. | Reject the malformed symbol at template admission. |
| `case_07.ash` and `forms.ash` | Change `$name value = value` to `other value = value` in `make_identity`. | Reject the mismatch between signature and equation through ordinary declaration admission. |
| `case_07.ash` and `forms.ash` | Change `$name value = value` to `$name value = true` in `make_identity`. | Reject the generated body through ordinary type checking. |
| `case_07.ash` and `forms.ash` | Change `value: $T` to `: $T` in `make_inline`. | Reject the missing parameter pattern at template admission. |
