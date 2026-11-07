# Executable template escapes

These proposed I22 source graphs exercise the approved escape and subtemplate
design in [CP-0034](../../../../proposals/CP-0034-top-level-declaration-macros.md).
They are fixed acceptance inputs for unimplemented syntax, not passing product
tests. Each entry file is compiled independently in this directory.

## Successful cases

- `categories.ash` returns `246 : Int`, as does `control_categories.ash`.
  It reads `expr`, `ident`, `type`, `pattern`, and `declaration` captures as
  syntax values in escapes. `make_expr` passes its fragment explicitly to an
  ordinary helper. `local_capture` gives an Ash variable the same spelling as
  a macro capture: the escape's `$value` reads the capture, and the inner
  quote's `$value` splices the local variable. Like `nested.ash`, this graph
  imports the shared module with repetition and generator definitions.
- `early_categories.ash` is a supplemental early-driver case using the same
  six definitions and caller in `early_categories_forms.ash`, without the
  shared module's other definitions. It returns `246 : Int`, matching
  `control_categories.ash`. It does not replace the original categories gate.
- `nested.ash` invokes a template that constructs a subtemplate, whose escape
  constructs another subtemplate. It returns `44 : Int`, as does
  `control_nested.ash`; the result distinguishes `(10 + 1) * 2` from a lost
  fragment boundary. Two invocations must remain independent. Its shared
  `forms.ash` also defines repetitions and generators, which must be admitted
  even though this caller does not invoke them.
- `early_nested.ash` is a supplemental early-driver case with the same
  `nested_quote` definition and caller, isolated in `early_nested_forms.ash`
  from the shared module's other definitions. It returns `44 : Int`, matching
  `control_nested.ash`. It does not replace the original `nested.ash` gate.
- `repetition.ash` returns `44 : Int`, as does `control_repetition.ash`.
  `zip_values` reads `$value` only inside the escape, so that read must drive
  its template repetition alongside `$name`. `cached` reads `$number` twice
  in one escaped block and must reuse one generator value per iteration.
  `empty` has zero iterations and must not execute its diverging escape.
- `nested_repetition.ash` returns `46420 : Int`, as does
  `control_nested_repetition.ash`. It reads the captured expression and a
  template-level generator inside the inner escape of two nested repetitions.
  The generated functions return `10`, `21`, `32`, and `43` in source order.
- `hygiene.ash` returns `205 : Int`, as does `control_hygiene.ash`. Each
  `hygienic` invocation receives a caller-context reference to the caller's
  `helper`, despite a same-spelled local introduced by the quote. The quote in
  `definition_helper` must instead resolve the macro module's private `helper`
  despite caller shadowing. Check source origins as well as the result.
- `freshness.ash` returns `20 : Int`, as does `control_freshness.ash`. One
  invocation calls the same helper twice, constructing two quotes from the
  same source quote and literal binder. Inspect their produced syntax before
  downstream resolution: both retain the definition context and have distinct
  quotation introductions, with each reference associated with its own binder.
- `quote_roundtrip.ash` returns `42 : Int`, as does
  `control_quote_roundtrip.ash`. The retained procedural identity macro exposes
  and re-emits a quoted expression containing a nested escape and quote hole;
  `$` must survive as syntax data rather than being expanded by the identity
  macro. Compare token, group and protected-fragment structure, contexts and
  origins before and after the actual identity transformer. The `token_kinds`
  transformer checks exact construction and token-kind recognition for
  `syntax` and `$`, including invalid spellings.
- `token_exhaustive.ash` returns `42 : Int` under slice 1. Its match lists
  every original `TokenKind` constructor. Under CP-0034, ordinary coverage
  checking rejects it for the missing `SyntaxKeyword` and `Dollar` cases.
- `reserved_control.ash` returns `42 : Int`; `syntax_value`, `declaration`,
  and the compiler-owned `@builtin.compiler.syntax` path remain valid.

## Rejections

- `mismatched.ash` supplies two name captures and three value captures to
  `zip_values`. The repetition drivers have different lengths, including the
  driver used only inside an escape; reject without partial output.
- `wrong_category.ash` returns an expression fragment at a type position.
  Ordinary declaration syntax admission rejects it without publication.
- `wrong_code_type.ash` imports an unused macro whose escape assigns `true` to
  an `Int` binding. Ordinary Ash checking rejects the escaped code. The
  handwritten `control_wrong_code_type.ash` has the same ordinary cause.
- `wrong_hole.ash` imports a module whose ordinary helper binds an `Int` to a
  quote hole; ordinary Ash checking rejects it. `primitive_escape.ash` invokes
  a macro that supplies an integer as an escape result; ordinary checking or existing
  syntax admission rejects it. Neither case adds an implicit conversion or a
  macro-specific type check.
- `out_of_scope.ash` imports an unused macro whose escape reads a repeated
  capture outside its repetition scope. Definition admission rejects it.
- `unbound_outer.ash` imports an unused macro with `$missing` inside a quote
  written in the outer template. The outer template owns that splice and
  rejects its unknown name at definition.
- `illicit_helper.ash` imports a module whose ordinary helper attempts to read
  a macro capture without an escape or an explicit argument. The source is
  rejected; a helper does not acquire its caller's capture environment.
- `atomic.ash` emits an initial declaration before a later escape calls a
  diverging function. The existing execution bound stops the escape and the
  invocation publishes neither generated declaration.
- `generated_type_error.ash` emits a `Bool` expression in an `Int` function.
  Ordinary checking reports the type error, retaining the quote, definition and
  invocation origins.
- `unused_unknown.ash` imports an unused quote containing a free `missing`
  reference and returns `42 : Int`. `invoked_unknown.ash` invokes that macro
  while defining a same-spelled caller function. Ordinary resolution rejects
  the quote's unavailable definition-context reference; caller shadowing does
  not supply it.
- `reserved_term.ash`, `reserved_macro.ash`, `reserved_module.ash`, and
  `reserved_alias.ash` are
  accepted by the retained slice 1 compiler and return 42, but CP-0034 rejects
  their respective user-defined term, macro, module-path and imported-item
  alias uses of the newly reserved `syntax` word.

The [I17 generator graphs](../generators/README.md) supply unused malformed
quotes in an ordinary helper and generator. Diagnostics cases check both human
and structured output with relevant definition, invocation, input and quote
origins. A failed expansion publishes no partial declarations. The current
compiler can run only the handwritten controls, `token_exhaustive.ash` and the
four pre-reservation
compatibility cases; it cannot execute the proposed escape graphs.
