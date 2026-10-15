# Source-authored native owner fixture

`owner.ash` defines the foreign signatures, owner, acquisition policy, private
payload, handler and completion policy. `entry.ash` uses the public compiler and
build path. `native_owner.c` supplies real allocation and release; its trace
records calls rather than inferred source results.

Run the connected executable case on Linux x86-64 GNU with Rust, `cc` and `ar`:

```sh
CARGO_BUILD_JOBS=1 cargo test -p ash --all-features --test source_resource_execution -- --test-threads=1
```

The test compiles the Ash module, removes its source files, builds generated Rust
bridges and an embedded-Core executable against a static archive, then runs it.
It checks repeated and nested acquisitions, native refusal, source refusal after
native acquisition, private payload use, nearer ordinary handler precedence,
and scalar range refusal before a native call. Inner release precedes outer
release; every non-null allocation is released once.

Resource and native applications retain row/type/row arguments, with the owned
identity in the middle position. The state family itself has Type-only arguments.

`replaced_payload_owner.ash` supplies the private-data regression for PR #27.
Independent callbacks remain legal. Replacing data with a closure retaining the
current owner must reject, including when finish discards the data. A native
control distinguishes acquisition-time handler aliases from the latest payload
passed to finish by returning the old callback to the resource body and calling
the new callback from the completion report. The dependent-owner scalar query
separately checks guard-held parent lineage after acquisition, with exact native
query and cleanup traces.

`acquired_only_owner.ash` and `acquired_only_entry.ash` use the same native fixture
with a one-parameter `Outcome<T>` report. The public pipeline also checks renamed
constructor roles, a generic error parameter, malformed report fields and forged
completion claims. Run their generated-native evidence with:

```sh
CARGO_BUILD_JOBS=1 cargo test -p ash --all-features --test source_resource_acquired_only -- --test-threads=1
```

The trace establishes that refused acquisition executes no body, source refusal
destroys a provisional owner, nested success remains nested and each allocation
releases once. A source `ConsumedFailure` after the actual consuming native call
terminates without a report or second release. This is source completion-error
policy; the native fixture does not return a retained or failed destruction status.

The initialized-byte variant supplies an explicit source extent absent from the
native ABI operands. The C fixture writes one eight-byte `size_t` object on this
target; seven initialized bytes form its declared region while private data
retains the independent size value. A zero extent still owns a non-null
allocation. The same real trace checks null and source refusal, publication,
nested release order and exact destruction. Negative extent input comes from an
admitted signed native scalar reply; negative and oversized extents return
without entering allocation or executing the body.

Separate injected Rust callbacks check preflight work refusal with no acquisition
or release, and infallible extent recording before terminal post-return refusal.
They model ownership edges without allocating or reading native memory. The
declared initialization and writability remain foreign assumptions; these tests
do not establish byte read/write, copy windows or a native-buffer library port.

This fixture covers the bounded executable checkpoint under
[CP-0022](../../../docs/proposals/CP-0022-ash-authored-foreign-interfaces.md) and
[TASK-0036](../../../docs/tasks/TASK-0036-source-contracts-core-and-generic-execution.md).
It does not establish byte access, dependent owners, outward capture/discard,
retained-owner quarantine, library ports or the complete milestone outcome.
