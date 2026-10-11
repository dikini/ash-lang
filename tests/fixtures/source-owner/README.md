# Source-authored opaque owner fixture

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

This fixture covers the bounded executable checkpoint under
[CP-0022](../../../docs/proposals/CP-0022-ash-authored-foreign-interfaces.md) and
[TASK-0036](../../../docs/tasks/TASK-0036-source-contracts-core-and-generic-execution.md).
It does not establish byte access, dependent owners, outward capture/discard,
retained-owner quarantine, library ports or the complete milestone outcome.
