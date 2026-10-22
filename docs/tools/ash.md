# The `ash` Executable

`ash` loads and runs one modular Ash program:

```text
ash [--message-format human|short|json] [--locale NAME] [--root name=path]... <entry-file>
```

The invocation requires exactly one entry path. Every `--root` option must
precede that path. The executable reads UTF-8 Ash source files and does not read
a program from standard input.

## Building an executable

The program-build path supports the retained Pure subset, scalar/void foreign
calls, declared dependent opaque owners, initialized byte resource scopes and
scoped read-only copying windows on Linux x86-64 GNU. It
compiles the source graph once
and generates a Rust host containing private Core construction data, the
existing evaluator and any required typed native bridges:

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

### Optional producer receipts

Rust callers can set `BuildConfiguration::producer_receipt` to explicit
`ProducerReceiptLimits` before preparation. This opt-in records the existing
native Effect profile; it does not enable checked-owner builds or change the
ordinary build's work limits. Pure builds currently refuse this option.

The limits bound individual observed artifacts, receipt bytes, record/bridge
counts and cumulative receipt work. Preparation binds the actual emitted
program image, expected facts, generated Rust and original bridge/library/
operation mappings. The build compares the emitted files and declared native
inputs before and after linking, and retains both seed and resolved Cargo-lock
observations. After successful linking and cleanup, it observes one opened
regular staging object with a matching ELF target header before publication.
`BuiltProgram::producer_receipt()` returns the retained binary receipt path.

`ProducerReceipt::read` and `decode` enforce independent finite bounds and a
canonical versioned encoding. Unknown, duplicate, reordered, malformed or extra
records refuse. `matches_expected` compares data, not authority. The receipt
records unavailable checked-contract, complete runtime/native/header/tool,
policy, premise and context closure as missing; checked applicability refuses.
The ordinary build can still use shared libraries and inherited tool settings.
Neither observed file metadata nor matching digests prove compilation/link
correspondence, stable future pathname contents, complete native behavior or
immutable execution. No protected approval store, trusted deployment context
or executable permission is supplied by a receipt. Public checked guards remain.

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
implicitly. The native-input options are unsupported by ordinary execution and
`check-ffi`.

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
assumptions. The generated host checks its linked bridge registrations against
its independently validated original contracts before Ash execution.

Shared dependencies use the system loader. The build emits no automatic rpath
and provides no runtime library-name resolver. Install dependencies in the
loader's search path or set `LD_LIBRARY_PATH` explicitly for the generated
process. A missing shared dependency can prevent the host from starting.

### Supported foreign execution

The first source-native subset admits owner-free scalar calls and zero-operand
`void` calls. Scalar representations are signed/unsigned 8-, 32-
and 64-bit integers and the profile's 64-bit `size_t`. Ash `Int` remains
mathematical: checked narrowing refuses an out-of-range input before the native
call, reporting `Foreign.ConversionFailed`; a scalar reply widens exactly,
including unsigned 64-bit results. A successful `void` call reports
`Foreign.Returned(())` without reading a native result.

Imports and generic helpers retain complete ordered Type/EffectRow arguments.
Executable interpreter instances must be closed; unused row arguments are not
removed from their identity. The generated host supplies the mandatory native
interpretation, rather than selecting an ordinary Ash handler for a native
symbol. Work/storage admission failures terminate execution instead of becoming
conversion outcomes. A returned native call is recorded before reporting or
ordinary continuation work can refuse; subsequent failure does not retry the
call or undo its external effects.

The Pure carrier retains its restrictions on polymorphic or lexical type
operations. It admits the common side-effect-free `Foreign.checked_i64` and
`Foreign.checked_size_t` checks, both returning `Foreign.Call<Int>` with the
unchanged integer or a conversion failure. The Effect carrier also admits
generic helper abstraction/application, native requests, declared dependent
opaque or initialized byte source resource scopes, and the admitted read-only
copy-window profile. Ordinary handler precedence, local resumption, resource
capture/resume, owned discard, retained quarantine and nested reports use the
existing evaluator and authenticated original lifecycle forests. Window views
and extents retain exact live owner/family/window identities; an ordinary helper
or matching function type grants no native-call permission.

Both carriers refuse unsupported method evidence, newtype conversion, other
intrinsics and integer literal payloads outside signed 64-bit range. Evaluated
integer arithmetic and widened native results retain their mathematical
semantics. These are build-path limitations, not changes to ordinary non-foreign
execution. The source [arena library](../../libraries/README.md) provides the
minimal allocation/usage/release lifecycle. The ordinary source buffer library
supplies checked zeroed bytes and scoped access through the same generated path.
The source [copying SQLite library](../../libraries/README.md#copying-sqlite)
uses explicit native inputs, source protocol and guarded temporary copy windows.
The admitted windows run only in permitted direct provider phases, retain exact
live owner/view authority and publish independent copied bytes. They cannot
suspend, complete their owner or escape; the detailed
[source foreign rules](../../spec/static-semantics.md#source-foreign-declarations)
define these bounds.

### Generated-host linkage checks

The source Arena target runs its complete real-allocation and separately labelled
injected-refusal scenarios with both static and shared fixture libraries. Shared
execution sets its loader path only on the generated child process. The SQLite
target runs the unchanged complete copying workload with the installed shared
library and with a genuine implementation archive. The static case requires
`ASH_SQLITE_STATIC_ARCHIVE`; a missing input fails the test.

Build that archive once from the pinned official SQLite 3.46.1 amalgamation.
Run these commands from the repository root, keeping the resulting inputs while
the verification receipts depend on them:

```sh
task41_sqlite_dir=$(mktemp -d)
python3 - "$task41_sqlite_dir" <<'PY'
import hashlib, pathlib, sys, urllib.request, zipfile
directory = pathlib.Path(sys.argv[1])
archive = directory / 'sqlite-amalgamation-3460100.zip'
with urllib.request.urlopen('https://www.sqlite.org/2024/sqlite-amalgamation-3460100.zip') as response:
    contents = response.read()
assert hashlib.sha256(contents).hexdigest() == '77823cb110929c2bcb0f5d48e4833b5c59a8a6e40cdea3936b99e199dbbe5784'
archive.write_bytes(contents)
with zipfile.ZipFile(archive) as source:
    for name in ('sqlite3.c', 'sqlite3.h'):
        (directory / name).write_bytes(source.read('sqlite-amalgamation-3460100/' + name))
assert hashlib.sha256((directory / 'sqlite3.c').read_bytes()).hexdigest() == '6c35bc5f7f85eac9c49928bacbb02bb694b547aabf69197e058cca245ad80e83'
assert hashlib.sha256((directory / 'sqlite3.h').read_bytes()).hexdigest() == '89b62c671c5964e137409ce034941b7b05a3af2c9875aba41f47f9483d0c2515'
assert (directory / 'sqlite3.h').read_bytes() == pathlib.Path('foreign-adapter/vendor/sqlite3.h').read_bytes()
PY
cc -O2 -fPIC -c "$task41_sqlite_dir/sqlite3.c" -o "$task41_sqlite_dir/sqlite3.o"
ar crs "$task41_sqlite_dir/libsqlite3.a" "$task41_sqlite_dir/sqlite3.o"
export ASH_SQLITE_STATIC_ARCHIVE="$task41_sqlite_dir/libsqlite3.a"
CARGO_BUILD_JOBS=1 cargo +1.97.1 test --all-features \
  --test source_arena_execution --test sqlite_library -- --test-threads=1
```

This preserves SQLite's default compile-time options. Record the selected
compiler/archive tools, options, source/header hashes and resulting archive
hash for the actual build. The test checks defined `sqlite3_*` implementation
symbols in the archive and executable, and rejects a SQLite `DT_NEEDED`
dependency. Platform Rust/libc shared dependencies remain permitted. It removes
Ash inputs before host construction and external image/facts before execution,
then checks the complete copying result. The optional test-only
`ASH_ARENA_EVIDENCE_DIR` and `ASH_SQLITE_DIAGNOSTIC_DIR` retain generated artifacts
while the normal harness removes their execution-side source/image/facts files.

For checkpoint or explicit receipt reuse, name the archive **bytes** as an
external input; the environment variable alone pins only its path. Use the same
declared source/header/archive/tool inputs for the before/after observations:

```sh
CARGO_BUILD_JOBS=1 cargo +1.97.1 xtask verify \
  --input "$ASH_SQLITE_STATIC_ARCHIVE" \
  --input "$task41_sqlite_dir/sqlite-amalgamation-3460100.zip" \
  --input "$task41_sqlite_dir/sqlite3.c" \
  --input "$task41_sqlite_dir/sqlite3.h" \
  --input "$task41_sqlite_dir/sqlite3.o" \
  --input /usr/bin/cc --input /usr/bin/ar --input /usr/bin/nm --input /usr/bin/readelf
```

Keep the other native/header/tool inputs required by the current checkpoint in
that invocation. The [verification guide](../project/verification.md) defines
the complete input and reuse boundary. These linkage tests do not close the
milestone or authorize Main integration.

## Optional C header checking

`check-ffi` checks authored foreign declarations against explicitly supplied C
headers. Its input is a valid entry with `main` which imports the bindings to
check. It runs the complete source compiler without evaluating the entry.

```sh
ash check-ffi --header binding.h --mapping mapping.json --compiler cc \
    --output checks --root ffi=libraries entry.ash
```

The current authoring compiler is GNU C 14 or later for
`x86_64-unknown-linux-gnu`. Other target requests refuse. Headers may repeat;
other check options may appear once and must precede the entry. Existing
diagnostic format/locale and root options apply. Header/tool errors exit 2;
source rejection keeps its source diagnostic and exit status.

The mapping is JSON version 1. Each declaration selects its **defining source
path**, library, role and member, rather than an importing alias or an equal
donor. Paths in the JSON are UTF-8 and relative to the mapping file. All foreign
members in the loaded closure require exactly one mapping, including private,
unused and constant-only declarations. Profile directives need no mapping.

```json
{
  "version": 1,
  "declarations": [
    {"module":"native.ash", "library":"C", "kind":"representation",
     "member":"CInt", "c_type":"int"},
    {"module":"native.ash", "library":"C", "kind":"symbol",
     "member":"Abs", "c_name":"abs", "parameters":["int"], "result":"int"}
  ]
}
```

`representation`, `owner` and `access` take `c_type`. `constant` and `sentinel`
take a `c_name` identifier; a helper header can define a macro for a C expression.
`symbol` takes its original authored native `c_name`, ordered physical
`parameters` and `result`. Source generics and logical source arguments do not
add C parameters. Types accept C type words, qualifiers and pointer stars; use a
header typedef for complex types, including function pointers. Arbitrary C
fragments, missing/duplicate/wrong-role mappings and unsupported symbol spellings
refuse before the compiler runs.

Checks cover the admitted integer category/width/sign and `size_t`, object/byte
pointer families, owner result/output slots, offsets and view/extent roles,
fixed non-callable function-address sentinels, exact function prototypes, and
mathematical constant/sentinel values. Same-width floating types cannot stand in
for integer representations. A pointer mapping checks ABI facts and grants no
Ash owner, access, lifetime or callback permission.

The output directory contains `check-ffi.c`, `check-ffi.log` and
`check-ffi-declarations.json`. Generated `ash-ffi-declaration-N` locations map to
the original compiled source path, byte range, library, role and member in that
index. Mismatch diagnostics retain the log and, when the C compiler identifies a
generated declaration, its original source label. The tool invokes the selected
compiler with explicit arguments, including `-std=gnu11 -m64 -fsyntax-only
-Wstrict-prototypes -Werror`; it emits no object and performs no native calls.

Verification mappings cannot supply missing executable facts, change a Rust
bridge or select ownership behavior. Ordinary authored bindings build without
headers or check output. Header success does not certify a separately supplied
binary or its validity, retention and consumption assumptions.

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

The executable test `native_buffer_documentation_example_has_exact_cli_output`
checks this complete native-buffer program:

```ash
import @ffi.native_buffer as Buffer

main : Unit -> Buffer.Outcome<Buffer.Outcome<Int>>
main () = resource Buffer.Buffer<R> b = 4 {
    match Buffer.write (b, 0, 42) {
        Buffer.Success(()) => Buffer.read (b, 0)
        Buffer.Failure(error) => Buffer.Failure error
    }
}
```

From the repository root, build and run it with:

```sh
CARGO_BUILD_JOBS=1 cargo run --bin ash -- build --root ffi=libraries \
    --cargo-target-dir target/ffi-native-hosts --output ./program entry.ash
./program
```

On successful allocation, the generated program prints
`Success(Success(42))` and a newline. The outer success
records acquisition and normal body completion; the inner result is the body's
ordinary read outcome. Allocation failure skips the body. Length must be
positive and fit the bridge's addressable bound; indices and byte values are
checked before access or mutation. Release occurs before the outer success is
observed. The library owns this policy; no compiler dispatch depends on its
filename. The former `@builtin.native_buffer` import and lowercase builtin
resource form are removed. See the [migration table](../../libraries/README.md#native-buffer-migration)
for explicit source type and effect spellings. The ordinary local-newtype and
non-resource lexical-dictionary native-image limitation remains; source/Core
capture checks still apply to those programs.

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
`entry.main-constrained`. After mandatory exact owner-free native interpretation,
any residual ordinary effect requirement or open entry row is a source rejection.
Required source-native bindings are admitted separately before Ash execution;
execution has no source-level unhandled-operation outcome.

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
acquisition has no source-level allocation-failure branch. Native allocation
refusal can return `Failure(AllocationFailed)` only at the atomic attempt
boundary: preceding initializer effects remain committed, but no native body
or authority is published. Neither provider exposes source use-after-release.

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
