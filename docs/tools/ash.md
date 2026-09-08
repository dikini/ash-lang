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

`import @builtin.cell as Cell` loads the compiler-owned cell API without a
`--root` option or filesystem lookup. `builtin` cannot be configured as a root:
`--root builtin=path` reports `invocation.reserved-root` before inspecting
configured paths. Only `@builtin.cell` exists beneath this root; another path
reports `module.unknown-builtin`. Ordinary aliases, targeted imports and
facade re-exports preserve the API's identity, but a module that acquires a
resource must directly import `@builtin.cell`.

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
function-valued domain. Tuples and ordinary nominal data render structurally.
A module `newtype` renders its representation value because its wrapper erases,
while the separately reported result type retains the nominal declaration
spelling. Rendering uses `<cycle>` only when a heap location repeats on the
active structural path.

The executable test `tool_module_newtype_observation_has_exact_cli_output`
runs this complete module:

```ash
newtype UserId = UserId(Int)

increment : UserId -> UserId
increment (UserId value) = UserId(value + 1)

main : Unit -> UserId
main () = increment(UserId(41))
```

Its exact standard output is:

```text
42 : UserId
```

The integer is the representation value; `UserId` is the statically retained
source result type. The executable performs no conversion-time registry lookup
and allocates no wrapper cell. This statement does not expose heap inspection
or promise a general ABI representation.

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

The executable test
`handled_effect_prints_the_resumed_value_and_pure_entry_type` runs one handled
request through the same command-line path:

```ash
effect Ask {
ask : Int -> Int
}

main : Unit -> Int
main () = handle (perform Ask.ask 1) with Ask {
ask value => resume (value + 41)
}
```

Its exact standard output is also `42 : Int` followed by a newline. Effect rows
are checked computation requirements, not an additional success-output field;
the executable prints the resulting value and its ordinary value type.

The executable test `resource_cell_documentation_example_has_exact_cli_output`
checks this complete resource program:

```ash
import @builtin.cell as Cell

main : Unit -> Int
main () = resource cell<R> c = 41 {
    let _ = Cell.write (c, 42)
    Cell.read c
}
```

Run it with `ash entry.ash`, without a builtin root option. It prints
`42 : Int` followed by a newline and releases the cell before observation.
Handles and captured cell access cannot escape the scope; the returned integer
is an ordinary copy.

The executable test `synchronous_hooks_documentation_example_has_exact_cli_output`
checks this complete hook program:

```ash
effect Adjust {
    publish : Int -> Int
}

increment : Int -> Int
increment value = value + 1

double : Int -> Int
double value = value * 2

main : Unit -> Int
main () = hook Adjust {
    register Adjust increment {
        register Adjust double {
            perform Adjust.publish 3
        }
    }
}
```

It prints `8 : Int` followed by a newline, with empty standard error. The outer
registration increments first; the inner registration doubles that result.
Reversing them produces `7`. Each transformer is evaluated once before its
scope begins, and normal scope return removes its registration. Subscriber
effects require handlers around the registration, not merely around the
publication site. Hooks add no automatic module registration or cleanup.

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

The global signature quantifies `A` implicitly. Each use of `id` and `Some`
instantiates its outer scheme. The unannotated local anonymous function is the
only local initializer form that generalizes. Pure execution erases these type
operations. Effect execution retains lexical instantiation so a generic
operation request matches the corresponding concrete handler; no type becomes
a source-inspectable runtime value.

Declaration parameters may state monomorphic kinds. `Type -> Type` admits a
unary type constructor such as bare `Option`; omitted kind annotations remain
fixed at `Type`, and the current language does not infer function kinds from
use. This is a phase-dependent language constraint rather than a permanent
restriction on future declaration-local inference.

The executable test `tool_higher_kinded_example_has_exact_cli_observation`
runs a higher-kinded interface, implementation, constrained global, and
operational global through the same command-line path:

```ash
type Option<A> =
    None
    | Some(A)

interface Transform<F : Type -> Type> {
    transform : (Int -> Int, F<Int>) -> F<Int>
}

impl Transform<Option> {
    transform (function, None) = None
    transform (function, Some(value)) = Some(function(value))
}

increment : Int -> Int
increment value = value + 1

apply_transform<F : Type -> Type> : (Int -> Int, F<Int>) -> F<Int> where Transform<F>
apply_transform pair = transform pair

fn relay<F : Type -> Type, A>(value : F<A>) -> F<A> {
    value
}

main : Unit -> (Option<Int>, Bool, Unit)
main () = (relay(apply_transform((increment, Some(41)))), true, ())
```

Its exact standard output is:

```text
(Some(42), true, ()) : (Option<Int>, Bool, Unit)
```

Selected interface evidence flows as ordinary function values and applications.
It adds no interface-specific runtime state. Pure execution erases scheme
instantiation; Effect execution retains ordinary lexical type/row instantiation
for exact operation matching. Neither adds a source-inspectable type value, CLI
configuration, runtime lookup, or output field.

### Method-local type parameters

An interface method may declare one complete ordered type-parameter list after
its name. The parameters scope only over that method signature. An omitted kind
is `Type`; the executable does not infer method-binder kinds or missing method
binders.

This `api.ash` module exports a higher-kinded method scheme and a constrained
global that uses it at two unrelated instantiations:

```ash
pub interface Functor<F : Type -> Type> {
map<A, B> : (A -> B, F<A>) -> F<B>
}

to_bool : Int -> Bool
to_bool value = value == 42

to_int : Bool -> Int
to_int true = 42
to_int false = 0

pub map_pair<F : Type -> Type> : (F<Int>, F<Bool>) -> (F<Bool>, F<Int>) where Functor<F>
map_pair (numbers, flags) = (map((to_bool, numbers)), map((to_int, flags)))
```

Its sibling `carrier.ash` exports a generic implementation:

```ash
pub import api (Functor, map)

pub type Box<A> = Box(A)

pub impl Functor<Box> {
map (function, Box(value)) = Box(function(value))
}
```

The `entry.ash` module imports the constrained global and explicitly selects
that implementation:

```ash
import api (map_pair)
import carrier (Box, impl Functor)

main : Unit -> (Box<Bool>, Box<Int>)
main () = map_pair((Box(42), Box(true)))
```

From the directory containing those files, run:

```text
ash entry.ash
```

The exact output is:

```text
(Box(true), Box(42)) : (Box<Bool>, Box<Int>)
```

Method parameters add no command-line option, runtime configuration, registry,
dispatch, or output field. Their schemes and authentication records are
compiler facts. Pure execution erases generated type operations; Effect
execution retains lexical instantiation without a runtime interface registry.

An absent method parameter list keeps the predecessor meaning: it binds no
method-local parameter. This complete module is rejected with
`interface.method-parameter`:

```ash
interface Project<I> {
project : (I, A) -> A
}

impl Project<Int> {
project (owner, value) = value
}

main : Unit -> Int
main () = project((0, 42))
```

Adding the complete explicit list migrates the declaration:

```ash
interface Project<I> {
project<A> : (I, A) -> A
}

impl Project<Int> {
project (owner, value) = value
}

main : Unit -> Int
main () = project((0, 42))
```

The migrated module prints `42 : Int`. The executable has no compatibility
mode and introduces no implicit method binder.

Interfaces, implementations, and global requirements do not add invocation
options or runtime configuration. The compiler selects method evidence during
checking, validates it before Core construction, and lowers it to ordinary Core
functions and applications. Successful programs therefore retain the same
output contract; the executable performs no runtime implementation
registration, lookup, or dispatch.

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
`module.not-found`, `module.path-escape`, `module.unknown-builtin`, and
`module.import-cycle`. The primary
label identifies the import that caused the failure. Syntax, resolution,
access, interface, implementation, constraint, type, pattern, coverage, and
entry-contract rejections also use status `1`. Interface-related source reasons
include `interface.*`, `impl.*`, and `constraint.*`; the stable reason
identifies the judgment that first established the rejection. Related labels
may identify the interface, implementation, method, implementation method, and
name import occurrences that caused it. When an explicitly selected
implementation crosses a facade, related labels identify each import or public
re-export hop in the authorization route. The route labels remain attached to
the same structured diagnostic at the programmatic and executable boundaries.

A targeted name import alone does not select implementation evidence, so a
method use that needs that evidence can report `constraint.unsatisfied`. A
missing or private interface named by `impl Interface` reports
`resolve.unavailable-export`; selecting a public declaration from another
namespace reports `resolve.interface-kind`. These source failures identify the
selector that established the rejection. An unavailable private or unselected
implementation is reported without exposing that declaration's metadata.

Entry failures are ordered as `entry.missing-main`, `entry.main-polymorphic`,
`entry.main-domain`, `entry.main-effects`, `entry.main-open-result`, and
`entry.main-constrained`. A nonempty effect row is a source rejection, so
execution has no source-level unhandled-operation outcome.

Effect declaration and resolution failures use `effect.operation-shape`,
`effect.unknown`, `effect.kind`, `effect.duplicate`, and
`effect.resume-outside-clause`. Effect-row and handler checking failures use
`effect.row-union-ambiguous`, `effect.handler-missing-input`,
`effect.handler-coverage`, `effect.handler-refutable-pattern`,
`effect.resume-not-consumed`, `effect.resume-already-consumed`, and
`effect.resume-capture`.

An otherwise well-formed hook target that lacks exactly one declared
`publish : P -> P` operation reports `type.hook-api`. Callback mismatches use
ordinary type errors identifying the registration's payload contract. Kind,
type/row and structural continuation failures retain precedence. An unused
registration still requires its callback's latent effects and the forwarded
hook effect to be handled.

Kind failures use `kind.not-applicable` when an applied type does not have a
function kind, `kind.argument` when a type or interface argument has the wrong
kind, and `kind.expected-type` when a value-type position receives a residual
function kind. The structured diagnostic retains expected and found kinds and
labels the causal type occurrence and the declaration that fixed its kind when
one exists.

The executable test `tool_source_rejection_uses_status_one_and_stderr` checks
that this module reports `type.operator-operand` on standard error:

```ash
main : Unit -> Int
main () = true + 1
```

The executable test
`cli_renders_the_structured_interface_diagnostic_without_reclassifying_it`
checks that an unsatisfied method occurrence exits with status `1`, begins
standard error with `constraint.unsatisfied`, and renders the same structured
diagnostic returned by the programmatic driver:

```ash
interface Render<A> {
render : A -> Int
}

main : Unit -> Int
main () = render true
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

Exhausting the graph-wide interface-and-constraint work budget reports
`internal.resource.constraint-work` with status `2`. Invalid retained evidence
reports an `evidence.validation.*` internal failure. Both are compiler
failures, not runtime selection failures.

The effect machine reports cumulative captured-control exhaustion as
`runtime.captured-control-capacity`. Reaching an impossible request or resume
state after validated Core is `runtime.invalid-control-state`. Both are
runtime-internal status-`2` failures, not source outcomes.

Resource-dependent escape reports `type.resource-escape` with status `1` and
labels the escaping expression and known acquisition/capture causes. Discard
that abandons or skips cell or registration completion reports
`effect.discard-unsafe`.
The effect machine's live-cell or live-registration capacity failure is `runtime.resource-capacity`,
an internal status-`2` failure. It publishes no partial acquisition. There is
no source-level allocation-failure branch or use-after-release outcome.

An output write or flush failure also exits with status `2` and attempts to
report `internal.output-write` on standard error. Standard-output bytes accepted
before the failure may contain part or all of the success line; the executable
cannot withdraw them. If writing the fallback diagnostic also fails, status `2`
remains the only guaranteed observation.

Exact diagnostic colors, gutters, and prose are presentation details. Stable
reason codes and causal source labels remain structured before rendering.
