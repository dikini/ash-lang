# The `ash` Executable

`ash` reads and runs one Mini-Ash source file:

```text
ash <source-file>
```

The invocation requires exactly one path. The file must contain UTF-8 text and
must be complete in itself. Mini-Ash has no modules or imports. The executable
does not read a program from standard input.

## Successful output

Success writes one line to standard output and exits with status `0`:

```text
value : Type
```

Integers, Booleans, and unit use their Ash spellings. Function values render as
`<function>` because function identity and captured bindings are not observable
Ash values. Function types use right-associated arrows and parenthesize a
function-valued domain. Tuples and nominal data render structurally. Rendering
uses `<cycle>` only when a heap location repeats on the active structural path.
Nominal result types use their source declaration spelling.

Parameterized nominal result types retain that spelling and render their
structural arguments. The executable test
`tool_rank_one_example_has_exact_cli_observation` runs:

```ash
type Option<A> =
    None
    | Some(A)

id : A -> A
id value = value

{
    let local = fn(value) {
        value
    }
    (id(Some(42)), local(false))
}
```

Its exact standard output is:

```text
(Some(42), false) : (Option<Int>, Bool)
```

The global interface quantifies `A` implicitly. Each use of `id` and `Some`
instantiates its outer scheme. The unannotated local anonymous function is the
only local initializer form that generalizes. These type operations are erased
before producing runtime values.

The executable test `tool_success_example_has_exact_cli_observation` runs this
file:

```ash
increment : Int -> Int
increment value = value + 1

fn double(value : Int) -> Int {
    value * 2
}

double (increment 20)
```

Its exact standard output is:

```text
42 : Int
```

Global functions have file-wide recursive scope. The executable test
`tool_recursive_example_has_exact_cli_observation` runs this mutually recursive
file, in which the earlier equational definition refers forward to the later
inline operational definition:

```ash
first : Unit -> Int
first ignored = second ()

fn second(ignored : Unit) -> Int {
    let retain : Unit -> Int = fn(value) {
        first value
    }
    42
}

first ()
```

Its exact standard output is also:

```text
42 : Int
```

The executable test `tool_function_result_uses_opaque_rendering` runs a file
whose result is a function:

```ash
identity : Int -> Int
identity value = value

identity
```

Its exact standard output is:

```text
<function> : Int -> Int
```

The executable test `tool_cyclic_data_uses_structural_rendering` runs:

```ash
type Stream =
    Next(Int, Stream)

{
    let rec ones : Stream = Next(1, ones)
    ones
}
```

Its exact standard output is:

```text
Next(1, <cycle>) : Stream
```

## Failures

A source rejection writes structured diagnostics to standard error, writes no
success value to standard output, and exits with status `1`. The first line of
each diagnostic is its stable reason, followed by its plain-text explanation
and source labels.

Data and pattern diagnostics include stable reasons for duplicate or unknown
types and constructors, constructor ownership and payload mismatches, duplicate
pattern binders, equation arity, refutable local bindings, non-exhaustive and
redundant cases, unsafe recursive roots, and unguarded recursive uses. A
non-exhaustive diagnostic includes one concrete uncovered pattern witness.

Rank-1 diagnostics include stable reasons for duplicate declaration type
parameters, unknown types, incorrect type-argument counts, kind errors,
infinite inferred types, ambiguous unsolved inference, and rejected
polymorphic recursion. Source diagnostics render nominal declaration spellings
and applied arguments rather than internal identities.

The executable test `tool_source_rejection_uses_status_one_and_stderr` checks
that this file reports `type.operator-operand` on standard error:

```ash
true + 1
```

Invocation, file-input, invalid UTF-8, compiler-internal, and runtime-internal
failures detected before success output exit with status `2`. They use standard
error and do not write a success value. Supplying no path or more than one path
prints `usage: ash <source-file>` to standard error and exits with status `2`.

An output write or flush failure also exits with status `2` and attempts to
report `internal.output-write` on standard error. Standard-output bytes accepted
before the failure may contain part or all of the success line; the executable
cannot withdraw them. If writing the fallback diagnostic also fails, status `2`
remains the only guaranteed observation.

Exact diagnostic colors, gutters, and prose are presentation details. The
semantic reason and causal source labels remain structured before rendering.
