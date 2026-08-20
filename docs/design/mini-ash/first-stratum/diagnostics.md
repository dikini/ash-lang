# First-stratum diagnostics

> These diagnostic expectations are informative evidence governed by
> [DN-0016](../../DN-0016-first-mini-ash-corpus.md). They support comparison and
> do not define current Ash errors, wording, or compiler behavior.

Each rejected [program case](programs.md) supplies a user-facing failure, not
merely an expected internal error. Elm is the guide for plain explanation and a
focused correction; Rust is the guide for precise primary spans, related source
labels, and structured supporting context.

## Structured diagnostic model

A candidate should be able to produce data equivalent to:

```text
Diagnostic {
    category
    message
    primary: SourceLabel
    related: [SourceLabel]
    expected: Optional<UserForm>
    found: Optional<UserForm>
    context: [ContextItem]
    help: Optional<JustifiedCorrection>
}
```

This is a comparison shape, not an accepted Rust API. A source label contains a
source-file identity, a half-open byte span, and text that explains why the
location matters. Line and column numbers are rendered views; compiler phases
carry stable source identity and spans.

Categories below are provisional case labels. They must not be presented as a
stable public error-code scheme.

## Parser failures

| Case | Category | Primary location | Required context |
| --- | --- | --- | --- |
| `P-001` | `parse.expected-result` | End of input | The preceding global is complete; a result expression is still required. |
| `P-002` | `parse.unclosed-group` | Opening `(` | Label end of input as the point where `)` was expected. |
| `P-003` | `parse.expected-operand`, then `parse.unclosed-group` | `+`, then opening `(` | Recover at the operational body's closing brace and avoid errors derived only from the missing forms. |

Recovery should preserve the first missing-expression node only in an
error-bearing surface representation. It must not fabricate a resolved or typed
expression that can reach evaluation.

## Resolution failures

| Case | Category | Primary location | Related location |
| --- | --- | --- | --- |
| `R-001` | `resolve.unknown-name` | Use of `missing` | None unless a close in-scope spelling justifies a suggestion. |
| `R-002` | `resolve.duplicate-global` | Name in the second inline header | Name in the first interface and its equation group. |

The duplicate-global message should describe two definitions of one file-level
name. It should not call the error “shadowing,” because V-003 demonstrates that
lexical shadowing is permitted.

## Typing failures

| Case | Category | Primary location | Expected and found | Related location |
| --- | --- | --- | --- | --- |
| `T-001` | `type.definition-result` | Equation body `value` | `Bool`, `Int` | `Bool` in the global interface |
| `T-002` | `type.operator-operand` | Left operand `true` | `Int`, `Bool` | The `+` operator |
| `T-003` | `type.not-applicable` | Function position `41` | A function, `Int` | The whole application when useful |
| `T-004` | `type.argument` | Argument `true` | `Int`, `Bool` | Domain `Int` in the global interface |

T-001 must retain equation provenance even though the body elaborates through
the same typed function structure as an operational definition. T-004 must
trace the expected argument type back to the explicit interface rather than
label an internal function node.

## Cross-stratum coverage failure

Both X-002 variants produce one structured `coverage.missing-pattern` reason
whose missing set contains `false`. The equational diagnostic labels the
incomplete equation group; the inline operational diagnostic labels the
explicit match. Neither should rewrite the user's definition into the other
presentation merely to explain the omission.

An acceptable rendered T-004 diagnostic should convey this information in
plain language:

```text
This application passes a Bool where identity requires an Int.

The argument true has type Bool.
identity's declared input type is Int.
```

The example specifies information, not exact punctuation, color, gutters, or
line numbers. Renderer tests may snapshot a candidate presentation, while
structural tests assert the category, spans, expected and found types, and
relationship independently.

## Internal validation failures

Malformed typed representations are compiler failures, not user type errors.
Representation candidates must reject at least:

- `I-001`: a variable occurrence whose binder is absent from the recorded scope;
- `I-002`: an addition node annotated with a non-`Int` result;
- `I-003`: an application whose argument type differs from its function domain;
- `I-004`: a synthesized node whose source origin is absent or outside its
  source file.

An executable should report an internal failure without panicking and return a
nonzero status. It should not blame source text for an invariant broken by the
compiler.

## Provenance requirements

Candidate stages must preserve:

- the full span of every source expression and definition;
- the name and interface spans of a global definition group;
- the original clause or operational body for elaborated function nodes;
- binder-definition and occurrence relationships after resolution;
- origins for inserted functions, bindings, and checking operations;
- related origins when one error connects an argument, declaration, or
  annotation to another source form.

An origin may refer to one source span, a generated node with one causal span,
or a small relation among source locations. Copying the nearest parent span onto
every generated node is insufficient when it makes an inserted operation appear
to have been written by the user.

## Comparison and tests

For every candidate, record:

- whether diagnostic construction uses structured rule outcomes rather than
  parsing error strings;
- whether recovery limits cascades in `P-003`;
- whether both V-002 definitions preserve distinct source provenance while
  sharing semantic typing and evaluation;
- whether both X-002 definitions share one coverage reason while retaining
  presentation-specific primary spans;
- whether lowering or transformation preserves the locations needed by T-001
  and T-004;
- whether structural diagnostic tests remain stable when rendering changes;
- whether malformed source and malformed internal data return failures without
  host-language panics.

A candidate that computes correct types or values but cannot meet these
requirements fails the corpus comparison.
