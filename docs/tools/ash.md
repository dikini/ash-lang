# The `ash` Executable

`ash` loads and runs one modular Ash program:

```text
ash [--root name=path]... <entry-file>
```

The invocation requires exactly one entry path. Every `--root` option must
precede that path. The executable reads UTF-8 Ash source files and does not read
a program from standard input.

The entry file's containing directory is the implicit root for its relative
imports. A relative import maps dotted segments to child directories and adds
the `.ash` extension: `import helpers.math as Math` selects
`./helpers/math.ash` relative to the importer.

Each repeatable `--root name=path` option configures a lowercase Ash identifier
as a named root. For example, `import @std.collections.list as List` selects
`collections/list.ash` beneath the path configured as `std`. Root names must be
distinct. The executable canonicalizes configured roots and loaded sources,
rejects targets outside their owning roots, and loads each canonical source
once.

## Complete module-tree example

Given this tree:

```text
example/
|-- app/
|   `-- main.ash
`-- standard/
    `-- answer.ash
```

`app/main.ash` imports `answer.ash` through the named root:

```ash
import @std.answer as Answer

main : Unit -> Int
main () = Answer.value(())
```

`standard/answer.ash` exports the referenced function:

```ash
pub value : Unit -> Int
value () = 42
```

Run the program from `example`:

```text
ash --root std=standard app/main.ash
```

The exact standard output is:

```text
42 : Int
```

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

The executable test `tool_success_example_has_exact_cli_observation` runs this
module:

```ash
increment : Int -> Int
increment value = value + 1

fn double(value : Int) -> Int {
    value * 2
}

main : Unit -> Int
main () = double (increment 20)
```

Its exact standard output is `42 : Int` followed by a newline.

Global functions have module-wide recursive scope. The executable test
`tool_recursive_example_has_exact_cli_observation` runs this mutually recursive
module, in which the earlier equational definition refers forward to the later
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

main : Unit -> Int
main () = first ()
```

Its exact standard output is also `42 : Int` followed by a newline.

Parameterized nominal result types retain their spelling and render structural
arguments. The executable test `tool_rank_one_example_has_exact_cli_observation`
runs:

```ash
type Option<A> =
    None
    | Some(A)

id : A -> A
id value = value

main : Unit -> (Option<Int>, Bool)
main () = {
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

The executable test `tool_function_result_uses_opaque_rendering` runs a module
whose `main` result is a function:

```ash
identity : Int -> Int
identity value = value

main : Unit -> (Int -> Int)
main () = identity
```

Its exact standard output is:

```text
<function> : Int -> Int
```

The executable test `tool_cyclic_data_uses_structural_rendering` runs:

```ash
type Stream =
    Next(Int, Stream)

main : Unit -> Stream
main () = {
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
success value to standard output, and exits with status `1`. The first line is
a stable reason code followed by a plain-text explanation and causal source
labels.

Source-caused loading failures include `module.unknown-root`,
`module.not-found`, `module.path-escape`, and `module.import-cycle`. The primary
label identifies the import that caused the failure. Syntax, resolution,
access, type, coverage, and entry-contract rejections also use status `1`.
Entry failures include `entry.missing-main`, `entry.main-polymorphic`,
`entry.main-domain`, and `entry.main-open-result`.

The executable test `tool_source_rejection_uses_status_one_and_stderr` checks
that this module reports `type.operator-operand` on standard error:

```ash
main : Unit -> Int
main () = true + 1
```

Invocation, input, compiler-internal, resource, validation, and runtime-internal
failures exit with status `2`. Malformed root options and missing or extra entry
paths print this exact usage line:

```text
usage: ash [--root name=path]... <entry-file>
```

Duplicate, invalid, or unavailable named roots instead report an
`invocation.*` reason. An entry file that cannot be read, an invalid UTF-8
source, and comparable non-source input failures report an `input.*` reason.
An imported file can retain its causal import label even when the input failure
uses status `2`.

An output write or flush failure also exits with status `2` and attempts to
report `internal.output-write` on standard error. Standard-output bytes accepted
before the failure may contain part or all of the success line; the executable
cannot withdraw them. If writing the fallback diagnostic also fails, status `2`
remains the only guaranteed observation.

Exact diagnostic colors, gutters, and prose are presentation details. Stable
reason codes and causal source labels remain structured before rendering.
