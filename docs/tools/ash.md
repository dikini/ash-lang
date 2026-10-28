# The `ash` Executable

`ash` loads and runs one modular Ash program:

```text
ash [--message-format human|short|json] [--locale NAME] [--root name=path]... <entry-file>
```

The invocation requires exactly one entry path. Every `--root` option must
precede that path. The executable reads UTF-8 Ash source files and does not read
a program from standard input.

## Building an executable

The program-build path generates a Rust host containing private checked Core,
the existing evaluator and typed native bridges on Linux x86-64 GNU. Foreign
calls support Address/Bytes pointer arguments, Address results and Unit as C void:

```text
ash build --output ./program [--target TARGET] [--cargo-target-dir PATH] \
    [--native-static PATH]... [--native-shared PATH]... entry.ash
./program
```

The target is `x86_64-unknown-linux-gnu`. Repeatable `--root name=path` options
configure imports as in ordinary execution. Diagnostic options may precede
`build` or follow it, before the entry path.
Build options must precede the entry path; `--output` is required exactly once.
Success prints the executable's absolute path. The resulting program prints its
result value on one line. It can run after the original Ash source files are
removed. Startup reconstructs fresh Core identities, independently validates
the construction data, and invokes the evaluator without source compilation.

Building requires the matching Ash checkout, Rust toolchain and cached Cargo
dependencies. Native tools run offline with one build job. `--cargo-target-dir`
selects a reusable build cache; otherwise the tool uses `CARGO_TARGET_DIR` or a
cache inside the generated project. Generated Rust, its manifest and the native
tool log remain in a fresh `.ash-build` directory beside the requested output.
After copying, the build removes only its generated Cargo root package from a
shared cache, including executable aliases and leaf build metadata. Shared
dependencies and current test executables remain. A private cache inside the
generated project is removed completely. Publication follows successful cleanup.
Failed linking preserves an existing output executable and its diagnostic log,
while cleanup retires partial generated Cargo artifacts. A cleanup failure also
preserves the existing destination and records its cause in the native build log.
A compiler/runtime
configuration mismatch rejects during Rust compilation, before publication;
startup checks compatibility again.

The Rust API separates `driver::compile_path`, `build::prepare_program` and
`build::build_prepared`. The prepared phase owns generated inputs and is
consumed by linking. Reusable compiled programs retain their original source
provenance; preparation does not reopen those source paths.

`BuiltProgram::generated_source` and `BuiltProgram::build_log` still return
retained working records. Callers own their lifetime: keep useful records while
a PR or checkpoint is live, then preserve lasting conclusions and scoped results
in documentation and discard obsolete build/review history when the PR closes.
Keep records needed by another live PR or checkpoint until that need ends.
The generator does not infer PR closure or delete published executables.

### Native link inputs

Use `--native-static PATH` for a regular static archive and `--native-shared PATH`
for a shared library. Both build-only options may repeat before the entry path.
Mixed occurrence order and duplicates are preserved in the native linker inputs.
Paths retain operating-system bytes, including spaces and non-UTF-8 names.

```sh
ash build --output ./program --native-static ./libcounter.a \
    --native-shared ./libhelper.so entry.ash
LD_LIBRARY_PATH="$PWD${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" ./program
```

Rust callers configure the same ordered inputs with
`build::BuildConfiguration::native_inputs`, using
`build::NativeLinkInput::StaticArchive(PathBuf)` and
`build::NativeLinkInput::SharedLibrary(PathBuf)` before `build::prepare_program`.
Ordinary `ash entry.ash`, `driver::execute` and `driver::run_path` refuse required
source-native bindings before Ash execution; they do not compile or link a host
implicitly. The native-input options are unsupported by ordinary execution.

For an existing authored `entry.ash` and regular static archive
`libcounter.a`, a Rust caller can build the linked program with:

```rust
use ash::build::{BuildConfiguration, NativeLinkInput, build_path};
use ash::driver::RunConfiguration;
use ash::module::ModuleRoots;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut build = BuildConfiguration::new("./program".into());
    build.native_inputs.push(NativeLinkInput::StaticArchive("./libcounter.a".into()));
    let source = RunConfiguration {
        entry: "entry.ash".into(),
        roots: ModuleRoots::empty(),
    };
    let program = build_path(source, build)?;
    println!("{}", program.executable().display());
    Ok(())
}
```

This builds the executable; run `./program` separately. The C linkage integration
fixture in `tests/program_build_native.rs` constructs both supported input kinds
and uses the separate compile, prepare and build phases.

Native preparation retains the exact encoded Core and expected-contract bytes
once. The build writes them to fixed files in its generated project and embeds
them at Rust compile time. The executable reads neither these files nor the
original Ash sources at startup. Failed linking retains the generated project
and its diagnostics without replacing an existing output executable.

Each link input names an existing whole-program native file. Preparation
canonicalizes the paths and checks the supported file kind: a regular static
archive or an ELF64 little-endian x86-64 shared library. It preserves input
order, including archive dependency order. These inputs do not supply Ash
contract facts or prove that a binary follows the authored signature and foreign
assumptions. The generated host checks its supplied linked bridge registrations against
its independently validated original contracts before Ash execution.

Shared dependencies use the system loader. The build emits no automatic rpath
and provides no runtime library-name resolver. Install dependencies in the
loader's search path or set `LD_LIBRARY_PATH` explicitly for the generated
process. A missing shared dependency can prevent the host from starting.

### Supported foreign execution

A passive foreign library states the `"x86_64-unknown-linux-gnu"` profile and
symbols with source signatures and native link names. For example:

```ash
import @builtin.foreign as F

pub foreign library Fixture {
    profile "x86_64-unknown-linux-gnu"
    symbol Make : Unit -> F.Address { name "fixture_make" }
    symbol Echo : F.Address -> F.Address { name "fixture_echo" }
    symbol EchoBytes : Bytes -> F.Address { name "fixture_echo_bytes" }
    symbol Release : F.Address -> Unit { name "fixture_release" }
}
```

A client imports the module and calls `perform Fixture.Make.call ()`. Each symbol
is an ordinary effect with a `call` operation; source handlers may implement it
under the normal handler and continuation rules. The generated host interprets
remaining required symbol effects. Imports are passive and compilation alone
supplies no native binding.

`@builtin.foreign` exports opaque nominal `Address` and pure `null`, `is_null`
and `equal`. Pointer equality proves neither allocation identity nor validity.
Address has no constructor, integer conversion, arithmetic, dereference or
automatic release. It carries no ownership or resource escape authority.

Whole Unit means zero C arguments. Whole Address or Bytes means one pointer;
a flat tuple of Address/Bytes supplies pointers in source order. Address results
preserve pointers including null; Unit results use actual C void. Bytes is
argument-only. Numeric inputs/results, String inputs, Unit tuple slots, nested
tuples, out-pointers, callbacks, variadics and structs by value are unsupported.

Bytes supplies a readonly pointer whose backing is held through the synchronous
call. No length, terminator or encoding is implicit. Empty Bytes promises no
readable byte. Native code must not mutate or free managed backing. If it retains
or returns that pointer, the binding module must keep the original Bytes alive
for every subsequent use; returning Address does not infer that relation.
There is no Address-to-Bytes/String or arbitrary memory-access API.

The signature and link name assume the C ABI and behavior; the compiler does
not verify them. Binding authors express null/length checks, ordinary errors
and scoped cleanup in Ash. A returned Address alone is no allocation witness.
Internal work/storage failures remain terminal. Failure after a completed native
call neither retries it nor undoes external effects. Existing cell, handler,
cleanup, capture, image-validation and work/depth rules remain in force.

### Generated-host linkage checks

`tests/program_build_native.rs` exercises the same pointer/Bytes/void fixture
with static and shared native inputs, source-independent embedded Core startup,
repeated execution and loader/linker refusals. It observes real allocation,
null return, pointer identity, readonly Bytes and ordinary Ash cleanup, including
body error and checked discard. These checks establish observed behavior rather
than native validity or lifetime guarantees.

The required SQLite canary links the runtime library directly and calls
`sqlite3_libversion(void)` and `sqlite3_sourceid(void)` as Address-returning
functions. It checks non-null and repeated pointer equality without a C wrapper,
header dependency, numeric shim or text dereference. This is not full SQLite
coverage: interpreting the returned text needs an unsupported memory-read or
Address conversion, while `sqlite3_open` and `sqlite3_prepare_v2` require numeric
results and out-pointers; preparation also requires a numeric input. These are
explicit future gaps, not additional supported ABI forms.

Use the normal workspace verification gate for connected source, Core, images,
bridges and examples. Native-origin artifacts use the existing validation and
build machinery; no FFI receipt, protected-launch or security admission protocol
is required. Link success does not establish that the native binary obeys its
declared signature or behavior.

## Diagnostic formats and locales

Diagnostics use human-readable explanations by default. Explicit options select
the format and locale:

```text
ash --message-format human --locale bg entry.ash
ash --message-format json entry.ash
```

`human` gives localized explanations and source context; `short` gives compact
localized text. `json` writes one locale-independent JSON object per diagnostic,
with `schema_version: 1`, the original reason, responsibility, named facts and
causal labels. Runtime records retain resource details, the first teardown
failure and cleanup status. Output remains on standard error; selecting a format
does not change success output or exit status.

Diagnostic options must precede the entry path and may each occur only once.
An explicit locale overrides the first nonempty `LC_ALL`, `LC_MESSAGES` or
`LANG`. English and Bulgarian are supported. POSIX locale spelling and parent
fallback are accepted; unsupported, malformed, `C`, `POSIX` and absent locales
select English. Supplying only `--locale` selects human output.

If a failure lacks facts or source context required for presentation, an
exceptional JSON fallback retains its original reason and diagnostic details
under `developer_details`, with a marked `presentation_error`. An unavailable
catalogue also falls back to JSON, preserving available structured facts.
Neither path recursively reports a diagnostic-write failure. Automation should
select `--message-format json` and inspect reasons, facts and causal labels,
not human wording.

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
configured paths. `@builtin.cell`, `@builtin.generic_cell`, `@builtin.bytes`,
`@builtin.string` and
`@builtin.foreign` are the fixed modules beneath this root; another path
reports `module.unknown-builtin`. Ordinary aliases, targeted imports and
facade re-exports preserve the API's identity. Legacy lowercase `resource cell`
acquisition requires a direct builtin import. Named generic family acquisition
follows its defining identity through aliases and facades.

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

The separate `@builtin.generic_cell` API stores an ordinary fixed-type value.
The executable test `generic_cell_documentation_example_has_exact_cli_output`
checks this program:

```ash
import @builtin.generic_cell as Cell

main : Unit -> Bool
main () = resource Cell.Cell<R,Bool> c = false {
    let _ = Cell.write (c, true)
    Cell.read c
}
```

It prints `true : Bool` followed by a newline. Reads preserve ordinary value
sharing and earlier snapshots; replacing the slot does not change an earlier
read. Handles and values depending on the scope still cannot escape it.
Interpreted execution and generated executables require the same independent
source/Core dependency proof.

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

`cleanup action { body }` retains one `Unit -> Unit` action. Normal return
invokes it and preserves the body value. Checked `discard` invokes actions in
its owned abandoned control before continuing the clause; it does not replay
the body or remaining publication callbacks.

The following complete example uses ordinary source declarations to retain
cleanup failures separately from an application failure. Its collector resumes
each report, then prepends that error to the returned list, preserving emission
order. Save it as `cleanup.ash` and run `ash cleanup.ash`:

```ash
type Outcome<T, P> = Success(T)
| Failed(P)
type CloseResult<E> = Closed
| CloseFailed(E)
type Failures<E> = NoFailures
| FailureItem(E, Failures<E>)
type Report<A, E> = Report(A, Failures<E>)

effect CleanupFailure<E> {
    report : E -> Unit
}
effect Stop {
    stop : Int -> Unit
}

reportClose<E> : CloseResult<E> -> Unit ! {CleanupFailure<E>}
reportClose result = match result {
    Closed => ()
    CloseFailed(error) => perform CleanupFailure<E>.report error
}

outer : Unit -> Unit ! {CleanupFailure<Int>}
outer ignored = reportClose (CloseFailed 11)
inner : Unit -> Unit ! {CleanupFailure<Int>}
inner ignored = reportClose (CloseFailed 22)

main : Unit -> Int
main () = {
    let observed : Report<Outcome<Int, Int>, Int> = handle {
        let outcome : Outcome<Int, Int> = handle (cleanup outer {
            cleanup inner {
                let ignored = perform Stop.stop 7
                Success 42
            }
        }) with Stop {
            stop primary => {
                let done = discard
                Failed primary
            }
        }
        Report(outcome, NoFailures)
    } with CleanupFailure<Int> {
        report error => match (resume ()) {
            Report(outcome, errors) => Report(outcome, FailureItem(error, errors))
        }
    }
    match observed {
        Report(
            Failed(primary),
            FailureItem(first, FailureItem(second, NoFailures))
        ) => primary * 10000 + first * 100 + second
        _ => 0
    }
}
```

It prints `72211 : Int` followed by a newline, with empty standard error:
application failure `7`, inner cleanup failure `22`, then outer failure `11`.
Removing the `Stop` request and its handler leaves normal `Success 42`, with
the same ordered failures. These constructors and the reporting effect are not
builtins. Ignoring an ordinary `CloseFailed` value does not report it, and no
adapter or runtime step implicitly retries a failed release.

The collector must survive the abandonment. Cleanup cannot use a captured
source or generated hook handler that has been removed, nor silently substitute
an outer handler for a nearer matching removed handler. It can use its own
handlers, surviving outer handlers and still-live unshadowed builtin cells.
Internal exhaustion and process termination do not promise source cleanup or
successful native release.

Global functions have module-wide recursive scope. The executable test
`tool_recursive_example_has_exact_cli_observation` runs this mutually recursive
module, in which the earlier equational definition refers forward to the later
inline operational definition:

```ash
first : Unit -> Int
first ignored = second ()

fn second(ignored : Unit) -> Int {
    let saved : Unit -> Int = fn(value) {
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
<function> : Int -> Int ! {DefaultAlloc}
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

The reason codes below identify failures independently of their presentation.
All formats use the same failure classifications.

A source rejection writes structured diagnostics to standard error, writes no
success value to standard output, and exits with status `1`. Human output starts
with an explanation and includes causal source labels and the stable reason
code. JSON exposes these fields separately.

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
`entry.main-constrained`. The generated root discharges the default allocation
requirement, and exact native interpretation discharges required admitted symbols.
Any residual ordinary effect requirement or open entry row is a source rejection.
Supplied native callback entries are checked against original symbols before
Ash execution. A selected native invocation requires its exact entry; a missing
entry is a terminal runtime failure after operand evaluation and boundary
selection. Ordinary execution refuses entries requiring native interpretation
rather than building or linking implicitly. Execution has no source-level
unhandled-operation outcome.

Effect declaration and resolution failures use `effect.operation-shape`,
`effect.unknown`, `effect.kind`, `effect.duplicate`, and
`effect.resume-outside-clause`. Effect-row and handler checking failures use
`effect.row-union-ambiguous`, `effect.row-exclusion`, `effect.handler-missing-input`,
`effect.handler-coverage`, `effect.handler-refutable-pattern`,
`effect.resume-not-consumed`, `effect.resume-already-consumed`, and
`effect.resume-capture`.

`effect.row-exclusion` means that a row substitution would insert an effect
instance forbidden by the tail's existing exclusions. For example, a signature
containing `{Bonus | R}` excludes `Bonus` from every occurrence of `R`, including
a callback's row. Human output explains the exclusion; JSON identifies the
offending requirement as `excluded_effect_requirement` and, when available,
the expected type as `expected_type`. Exclusion uses exact instances, including
their type arguments.

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
that skips required outside completion or abandons a running cleanup or close
operation reports `effect.discard-unsafe`. A cleanup action requiring a removed
interpreter reports `effect.cleanup-context`, with discard, action and handler
labels. Safely owned cells, registrations and armed actions can be closed.
The effect machine's live-cell, registration or cleanup capacity failure is `runtime.resource-capacity`,
an internal status-`2` failure. It publishes no partial acquisition. Cell
acquisition has no source-level allocation-failure branch. A foreign allocation
returning null is an ordinary Address result; any error constructor or cleanup
policy belongs to the binding module. Raw Address supplies no use-after-release
check or lifetime guarantee.

Detectable runtime resource failures terminate with status `2`, without source
continuation, source cleanup, retry or rollback. Their bounded diagnostic keeps
the original reason code and identifies the resource cause, phase and resource,
with requested and available amounts when known. Causes distinguish
`runtime.capacity-exhausted`, `runtime.allocator-refused`,
`runtime.work-budget-exhausted` and `runtime.storage-reservation-failed`. The
last means the storage API did not distinguish allocator refusal from a
representation bound; it does not identify a RAM-quota violation.
If host teardown also fails, the report retains the original failure, the first
teardown failure and the observed cleanup status. Localized runtime messages are
prepared before execution; reporting does not allocate or invoke the catalogue,
and does not retry a failed write. External termination, including termination
inside an infallible host allocation API, cannot guarantee an in-process report.

An output write or flush failure also exits with status `2` and attempts to
report `internal.output-write` on standard error. Standard-output bytes accepted
before the failure may contain part or all of the success line; the executable
cannot withdraw them. If writing the fallback diagnostic also fails, status `2`
remains the only guaranteed observation.

Exact diagnostic colors, gutters, and prose are presentation details. Stable
reason codes and causal source labels remain structured before rendering.

## Maintaining diagnostic messages

Reuse the phase's reason, facts and spans. Declare a message and its typed
arguments in `src/message.rs`; for example, the existing term lookup message is:

```rust
resolve_unknown_term => "resolve-unknown-term" { name: &'a str = "missing" },
```

The example value supplies the generated catalogue test. Add the same key and
arguments to both `locales/en-US.ftl` and `locales/bg.ftl`:

```text
resolve-unknown-term = No term named `{ $name }` is in scope.
```

The phase selects `Message::resolve_unknown_term(name)` from its retained facts;
the presentation adapter supplies semantic JSON facts and label relationships.
Renderers do not need a new message-specific branch. To change wording or a
translation, edit the appropriate catalogue entry, retaining its key and named
arguments. Update exact-wording assertions where applicable; do not change JSON
reasons or facts just because the prose changed.

Run the catalogue tests and the affected phase's human/JSON tests together.
Runtime messages additionally require pre-execution preparation and tests of the
separate allocation-independent reporter; do not format them after failure.
