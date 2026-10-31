# Source bindings

`scheduling.ash` is an ordinary Ash module for the retained-control store. Use
`--root ash=libraries` and import `@ash.scheduling` to select a suspended branch
and drain it. `finish` follows returned keys until that branch finishes or the
selected key is absent. `drain` returns on a true Probe reply and follows a
newly returned key when the branch yields again. A source handler can intercept
the request; only a fresh reply from the selected Store can establish quiescence
for release. If other work remains without an available key, it need not terminate.
Neither operation adds cancellation, fairness or a termination guarantee.

`ReadyQueue`, `enqueue`, `turn` and `run_ready` provide a cooperative FIFO
policy. A turn removes the first key and appends the new key if that branch
yields again. The driver returns on a true Probe reply; an empty queue alone
does not establish that the Store is quiescent. The examples place an allocator
handler outside the Store. The current release analysis conservatively refuses
the empty-queue example when its only allocator is the host default; an
enclosing `region` and `using` supplies the supported context.

The retained-control change is integrated into Main in
[PR #167](https://github.com/dikini/ash-lang/pull/167) at
`67c79ddc32a813cc0c9ddab2962f9e2aa849b028`.

The former Arena, native-buffer and SQLite libraries depended on the retired
foreign policy API and have been removed for the implemented
[foreign-call boundary](../spec/static-semantics.md#source-foreign-declarations).

The current [native declarations](../tests/fixtures/source-native/native.ash),
[C fixture](../tests/fixtures/source-native/native_counter.c) and
[pointer client](../tests/fixtures/source-native/cases/pointers.ash) exercise the
Address/Bytes/void boundary through the existing
[program-build tests](../tests/program_build_native.rs). Static and shared native
inputs use the build machinery recorded in
[AD-0013](../docs/decisions/AD-0013-generated-native-bridges-and-program-builds.md).

The [binding module](../tests/fixtures/source-native/binding.ash) and its
[entry](../tests/fixtures/source-native/cases/binding.ash) add ordinary null and
length checks, scoped cleanup on normal completion and Stop/discard, and use of
the same Bytes before, across and after synchronous native calls. The existing
program-build harness checks both static and shared linkage and exact fixture
event order. These are fixture examples, not shipped public library modules or
certification of native validity or lifetime behavior.

Address is opaque. It carries no ownership or resource escape restriction;
pure null and pointer equality do not read memory. A Bytes argument supplies one
readonly pointer with its managed backing held during the synchronous call.
There is no hidden length, NUL terminator or encoding conversion, and empty Bytes
promises no readable byte. C must not mutate or free managed backing. If C retains or returns its pointer,
the module must keep the original Bytes alive for every later native use; the
returned Address does not extend that lifetime. The fixture releases only its own
three-byte allocation, never Bytes backing. No Address memory-read/copy API or
Address-to-String/Bytes conversion is provided.

The direct [SQLite declarations](../tests/fixtures/source-native/sqlite.ash) and
[entry](../tests/fixtures/source-native/cases/sqlite.ash) call
the [SQLite version getters](https://www.sqlite.org/c3ref/libversion.html),
`sqlite3_libversion(void)` and `sqlite3_sourceid(void)`, as Unit-to-Address symbols.
They check nonnull and repeated pointer equality; they do not dereference text.
The canary links the installed versioned `libsqlite3.so.0` runtime directly,
discovered with `cc -print-file-name=libsqlite3.so.0`. It needs no development
headers, unversioned `.so` symlink or C wrapper. The runtime must be available in
the system loader search path. The fixture additionally requires `cc`/`ar`, and
generated hosts require the matching Rust toolchain and cached dependencies.

This is not a full SQLite binding. [Open](https://www.sqlite.org/c3ref/open.html)
and [prepare](https://www.sqlite.org/c3ref/prepare.html) require unsupported C
numeric results and output-pointer slots; prepare also needs a numeric input. Numeric
representation, output storage and foreign text readback remain future gaps,
not implicit conversions or new compiler resource policy. Supported foreign
arguments are Unit, Address, Bytes and flat tuples of pointer arguments;
results are Unit (C void) or Address (C pointer).

`network_types.ash` defines the ordinary identities, parents and outgoing
messages used by the codec and intended for the network ledger.
`network_codec.ash` encodes Work and Ack frames with a tagged base-256 representation and decodes only complete canonical frames. A decoded
Work carries its child, parent and payload; the receiver is supplied separately by the authenticated delivery
context. The codec is ordinary source code. A successful parse alone does not
authenticate a peer or kind and does not establish a ledger transition,
completion or release. `network_protocol.ash` contains the ordinary two-worker Work/Ack driver and
its producing-cleanup example. The cleanup reserves a descendant before it is
sent; its acknowledgement permits parent retirement and the upstream Ack. The
driver retains a pending head on Full and services receives before retrying.
A malformed frame or failed operation takes an ordinary failure path; it is not
a completion certificate. The module does not prove honest acknowledgements,
per-message processing, liveness or native behavior. The connected execution and its evidence are recorded in the historical
[TASK-0058](https://github.com/dikini/ash-lang/blob/b5c62bf25b87bc1c2ce9f87e4efc3ca0e0107c9a/docs/tasks/TASK-0058-pinned-worker-network.md).

The source-native interpreter can execute this protocol with admitted host
callbacks. Generated native images do not currently support Network scope and
operations. The combined retained-control, Cell, byte-binding and Network test uses a
trusted Rust host callback. Separate generated-host real-C FFI and SQLite
canaries cover their respective supported bindings; they do not establish a
combined Network image. A larger unused discard-bearing native binding can
exhaust generic cleanup-inference work when composed with this protocol;
[issue #190](https://github.com/dikini/ash-lang/issues/190) tracks the compiler
cost limitation.
