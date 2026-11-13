# Initial declaration and derive integration corpus

These source graphs define the fixed initial corpus for historical
[CP-0034](https://github.com/dikini/ash-lang/blob/79c2d0723baa218a127640903f522694580bfc1e/docs/proposals/CP-0034-top-level-declaration-macros.md).
[TASK-0068](../../../tasks/TASK-0068-top-level-declaration-macros.md) records
the delivery evidence and remaining gates. Handwritten controls and earlier
stand-in checks are identified by each fixture README. Each entry file is
compiled independently from its directory;
the named module files form its fixed import graph. Negative variants described
as a single edit start from a fresh copy of that graph.

| ID | Fixed input and assertions |
| --- | --- |
| I01 | [Declarations](declarations/README.md): `case_01.ash` returns 42; its duplicate invocation rejects. `control_01.ash` is the handwritten target. |
| I02 | Declarations: `case_02.ash` returns 42. `mismatched_newtype.ash` rejects the distinct constructor spelling; the control establishes the ordinary cause. |
| I03 | Declarations: `case_03.ash`, `methods.ash`, `relation.ash`, and `higher.ash` return 42. `duplicate_methods.ash` rejects; the controls exercise the ordinary targets. |
| I04 | Declarations: `case_04.ash` and `constrained_impl.ash` return 42. Adding the handwritten duplicate implementation to `case_04.ash` rejects. |
| I05 | Declarations: `case_05.ash` and `operations.ash` return 42 through the current handler syntax. `duplicate_operations.ash` rejects with the ordinary duplicate cause. |
| I06 | Declarations: `case_06.ash` returns 42 without calling native code. The README fixes missing and duplicate-profile negative variants. |
| I07 | Declarations: `case_07.ash` returns 42. The missing type-capture variant rejects at the invocation. |
| I08 | Declarations: `generic.ash` and `opaque.ash` return 42; `duplicate_constructors.ash`, `opaque_hidden.ash`, and `opaque_sum_hidden.ash` reject. The generic, opacity and duplicate controls define ordinary behavior. |
| I09 | [Derives](derives/README.md): `main.ash`, `renamed.ash`, `generic.ash`, and `opaque.ash` return 42. The duplicate, empty, unimported, unsupported, wrong-kind and opaque-constructor graphs reject. `nested.ash` returns 42 and checks generated-subject expansion; `ordered_first.ash`, `ordered_second.ash`, `generated_failure.ash` and `generated_order.ash` reject in the specified derive order with origins. |
| I10 | [Indexed](indexed/README.md): `main.ash` returns 42 after traversing two constructors; `payload.ash` returns the authored rejection with the specified origins. |
| I11 | Indexed: `one.ash` and `three.ash` return 42 with one and three generated equations, respectively; the corresponding handwritten controls also return 42. |
| I12 | [Hygiene](hygiene/README.md): `main.ash` returns 252, `nominal_main.ash` returns 42, and `private_types.ash` and `literal_public_main.ash` return 84. Distinct caller-selected private names work; duplicate generated and handwritten names reject downstream with source origins; the independently typed caller-helper variant still returns 252. |
| I13 | Hygiene: `main.ash` resolves the definition-private helper and renamed facade dependency despite caller shadowing; direct import of the private helper rejects. |
| I14 | [Diagnostics](diagnostics/README.md): `unused_bad.ash`, `unused_bad_derive.ash`, `forbidden_import.ash`, and `category.ash` reject with definition, forbidden-output and category causes, respectively, and publish no partial result. |
| I15 | Diagnostics: `type_error.ash`, `missing.ash`, `invoked_free.ash`, and `recursive.ash` reject with ordinary type, matcher, ordinary unresolved-name and expansion-bound causes. `unused_free.ash` and `unused_free_derive.ash` return 42; `invoked_free_derive.ash` rejects through ordinary resolution. Check human and JSON source roles; indexed `payload.ash` supplies an authored rejection. |
| I16 | Hygiene `main.ash` returns 252 through the public driver; indexed `integrated.ash` returns 42 after a checked procedural derive's host root closes. Exercise both interpreter and supported build/image execution, independent Core validation and the mutations specified below. A [supplemental procedural declaration graph](procedural_declaration/README.md) supplies the earlier S4 host/driver gate without replacing I16. |
| I17 | [Generators](generators/README.md): subtemplate and quote-backed procedural graphs use fragment-returning steps. Inline and imported seeds return 310; global, reset and mixed-depth cases return 3210, 1010 and 546210. Caller-global seed, wrong type, invalid fragment and duplicate binding reject. |
| I18 | [Migration](migration/README.md): the old expression macro returns 42 under CP-0033 and fails exhaustive coverage against the extended sum; the explicit migration and appropriate fallback return 42 under CP-0034. |
| I19 | [Captures](captures/README.md): `main.ash` returns 128; `counts.ash` and `binder.ash` return 42. `empty_plus.ash`, `mismatched.ash`, `trailing_separator.ash`, `ambiguous_definition.ash` and `missing_driver_definition.ash` reject for their specified syntax causes. Generator graphs exercise nested repetitions and shared iteration values. |
| I20 | [Nested declaration syntax](nested/README.md): `main.ash` returns 42 using definition-context lookup despite the caller's same-named syntax. `forward.ash` returns 42 with generated mutually recursive functions. Diagnostics `recursive.ash` exercises caller-context recursion and its bound. `derive_first.ash` and `declaration_first.ash` report their first authored expansion failure in source order. |
| I21 | [Header compatibility](header_compat/README.md): `compat.ash` and `derive_compat.ash` return 42 under CP-0033; `both.ash` and `renamed.ash` return 42 under CP-0034. `collision.ash` and `own_definition.ash` reject. |
| I22 | [Escapes](escapes/README.md): capture categories, nested subtemplates, repetition and hygiene return 246, 44, 44 and 205; a quoted-expression service round trip returns 42. Invalid escapes, fragment positions, repetition scope, unbound names, bounded failure and reserved identifiers reject as specified. |

For I16, run these additional boundary controls against the same successful
graphs in a test harness that can mutate compiler-owned intermediate data:

1. Before output transfer, substitute a syntax handle issued by a different
   compilation for the indexed transformer's captured identifier. Admission
   must reject the handle and the generated module must not be published.
2. In the independently validated Core for the indexed graph, replace the
   selected `Indexed<Color>` implementation identity with an unrelated
   implementation identity. Independent Core validation must reject the
   mutated artifact. The unmodified graph must validate and execute.

Check the source-level private-helper, opaque-constructor, caller-shadowing and
dependency-visibility cases through ordinary resolution and linking. Do not
introduce a separate per-reference grant or a grant-removal test. The slice 1
delivery found that an arbitrary same-typed unchecked Core retargeting is not by
itself evidence of an Ash source access bypass; do not require universal
source-to-Core correspondence from this corpus.

The mutation harness and build/image checks are implementation evidence to be
supplied by the owning task. These assertions do not claim a particular current
test hook or compiler representation.
