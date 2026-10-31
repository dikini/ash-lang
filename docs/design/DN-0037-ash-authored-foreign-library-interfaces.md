# DN-0037: Ash-Authored Foreign-Library Interfaces

- ID: `DN-0037`
- Status: accepted
- Related: [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md), [DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md), [DN-0042](DN-0042-native-interaction-and-efficient-data.md), [DN-0054](DN-0054-base-lexical-region-memory-contracts.md), [DN-0057](DN-0057-checked-ffi-module-boundaries.md)

## Accepted and implemented

Ash-authored foreign declarations, pointer/void calls and generated evaluator
hosts are accepted and implemented on `main`. The
[specification](../../spec/static-semantics.md#source-foreign-declarations)
defines the language contract. AD-0013 defines the build architecture.

| Capability | Status |
| --- | --- |
| Passive foreign libraries with source signatures, C names and exact symbol effects | Implemented |
| Opaque Address, null tests and pointer equality | Implemented |
| Synchronous readonly Bytes arguments | Implemented |
| Whole Unit arguments, flat Address/Bytes pointer arguments, Address or C void results | Implemented |
| Ordinary Ash handlers, checks and scoped cleanup in bindings | Implemented |
| Whole-program Rust bridges, private checked Core and evaluator hosts; static/shared linkage on x86_64-unknown-linux-gnu | Implemented |
| Generic cells, lexical regions, retained control and pinned-worker composition | Implemented in ffi-ash |
| Network scopes and operations in generated executable images | Not implemented |
| Full SQLite, numeric ABI slots, out-pointers, callbacks, variadics and structs by value | Not implemented |
| Protected launch, isolated foreign execution and checked-host policy | Not implemented; earlier programme superseded |
| Compiler-managed foreign owner/provider, status, window, codec and manifest/adapter execution routes | Retired |

## Agreed ffi-ash milestone

`ffi-ash` names the current implemented dialect on `main`. It includes the
earlier module, interface, diagnostic and effect features, plus generic cells,
lexical regions, retained control, library scheduling and the fixed two-worker
network. The [feature inventory](../project/implemented-features.md) records the
complete current boundary and execution support. The name adds no compiler mode
and creates no Git tag.

The current foreign scope is the pointer/void boundary above. The earlier
copying SQLite, native-buffer and Arena libraries used the retired foreign
policy API and are absent from current Main. Their original delivery is
historical; they are not current ffi-ash library capabilities or unfinished
requirements of the accepted pointer/void design.

The [original milestone](https://github.com/dikini/ash-lang/milestone/1),
[CP-0022 transition](https://github.com/dikini/ash-lang/blob/adddeffe5d135bd03bf5fc30051965e5da70ed24/docs/proposals/CP-0022-ash-authored-foreign-interfaces.md)
and [original closure task](https://github.com/dikini/ash-lang/blob/7471200efb1bd90782fcad81be54b992fbd92982/docs/tasks/TASK-0041-ffi-ash-milestone-closure.md)
retain that earlier scope and acceptance history. This current scope supersedes
their description of the delivered language; it does not rewrite their records.

## Question

How can Ash modules declare native calls and supply binding policy without
per-library compiler dispatch?

## Objective

Authors declare the supported C signatures and link names in passive Ash
modules. Ordinary Ash functions, effects, handlers and cleanup implement null
checks, protocol and lifetime policy. Program builds generate typed Rust calls
and link explicit native inputs.

## Context

The original provider experiments supplied SQLite, scalar Arena and lifecycle
observations. Their Rust manifests and native owners were replaced by the
smaller passive foreign boundary. Lexical-region providers now use an ordinary
fixed allocate/release pair; a foreign Address alone supplies no owner or
allocation permission.

The [current binding fixtures](../../libraries/README.md) exercise pointer
arguments, Bytes backing, void results, checks and cleanup. The SQLite canary
calls version/source-id getters and compares returned pointers. It does not
read foreign text or implement database operations.

## Constraints

### ABI scope

The target is `x86_64-unknown-linux-gnu`. Whole Unit supplies no C arguments.
Whole Address or Bytes supplies one pointer; flat Address/Bytes tuples supply
pointers in source order. Address results are pointers; Unit results are actual
C void. Bytes is argument-only. Numeric slots, nested tuples, Unit tuple
components, out-pointers, callbacks, variadics and structs by value are unsupported.

### Author and compiler responsibilities

The compiler checks source signatures and exact defining identities and
independently validates Core. It generates bridges and authenticates their
association with original symbols. Native signature and behavior remain binding
assumptions. Source handlers retain nearest-handler precedence.

### Memory and execution boundary

Bytes backing remains live through its synchronous call. There is no hidden
length, terminator or encoding conversion. Native code must not mutate or free
that backing. A module that permits a native pointer to outlive the call must
retain the original Bytes for every later use. Address carries no ownership or
inferred lifetime and provides no memory read/write or freeing operation.

## Evidence and experiments

[Slim FFI tests](../../tests/ffi_slim.rs),
[source admission](../../tests/foreign_source_admission.rs),
[native program builds](../../tests/program_build_native.rs) and
[native region storage](../../tests/region_native_storage.rs) cover the
implemented boundary. The [library guide](../../libraries/README.md) identifies
the ordinary binding fixtures and direct SQLite getter canary.

Historical [provider experiments](provider-experiments/README.md) and
[checked-host studies](DN-0057-checked-ffi-module-boundaries.md) retain their
original results. Their retired APIs are not current execution paths.

## Not implemented

Full SQLite bindings, foreign text readback, richer ABI mappings, general
borrowing, protected or isolated foreign execution, a native Ash backend,
separate compiled Ash libraries and a stable Ash/Core ABI are not implemented.
