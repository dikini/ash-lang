# DN-0039: Files and Filesystem Resources

- ID: `DN-0039`
- Status: exploring
- Related: [DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md),
  [DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0035](DN-0035-region-memory-management-and-verified-providers.md),
  [DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md),
  [DN-0041](DN-0041-typed-serialization-and-data-pipelines.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This note explores a file and filesystem library as a separate resource
> workstream. It defines no current Ash semantics, selects no implementation
> architecture, and authorizes no implementation. It adds no completion
> requirements to the ongoing SQLite, arena or common-resource experiments.

## Question

Can an Ash library expose ordinary file and filesystem operations through
checked resources, effects and handlers, while keeping host ABI and memory
support generic? What contracts let copying APIs work first and later support
arena-backed buffers without weakening lifetime or completion guarantees?

The intended outcome is a reusable standard-library candidate, an additional
foreign-library authoring example, and executable input/output for the typed
data pipelines in [DN-0041](DN-0041-typed-serialization-and-data-pipelines.md).
An unsuccessful experiment need not merge; a successful bounded experiment
should preserve a path into Ash rather than require a replacement implementation.

## Context

The [current specification](../../spec/README.md) defines passive modules,
constrained interfaces, exact effects, lexical handlers, and the closed cell
and native-buffer resources. Handles provide reusable access; the scope owns
completion. Dependency checking prevents access escaping through values,
closures and requests. Capture/resume moves owned control, and checked discard
closes abandoned obligations in structural order.

The [native-buffer contract](https://github.com/dikini/ash-lang/blob/2766e8260e2590d9ebdca7abd699115b3cd02a8a/spec/dynamic-semantics.md#scoped-native-buffer-execution)
does not define filesystem policy or fallible file close. Current lexical
lifetime checking does not establish foreign layout, pointer stability,
exclusive mutation, or the validity of a view after its backing storage changes.

[DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md) supplies
experimental resource-definition, acquisition, interpretation and completion
contracts. Its [execution record](provider-experiments/execution.md) records
branch evidence, including packed `Bytes` and UTF-8 `String`; those deliveries
are not normative main semantics. Its Rust-authored manifests and adapters are
an experimental bridge, not the intended long-term library-authoring requirement.

[DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md) asks how authors
can describe a foreign interface in Ash from the host headers and binary.
Files exercise that direction with lengths, native errors, acquisition,
irreversible writes and fallible completion. They do not require an Ash ABI.

## Constraints

- Always follow the types. A resource type definition must relate provider
  state, owner identity, access, effect operations, initialization and
  completion before an instance spelling is proposed.
- Extend the existing Ash pipeline and root workspace. Use project-local
  worktrees under `.worktree/`; do not introduce another Ash implementation.
- Keep library-specific symbols, flags, errors and policy in the binding.
  Generic compiler support must also serve SQLite and other providers.
- Start with synchronous copying operations on regular files and a declared
  host profile. Native addresses remain private to the foreign boundary.
- Keep unrestricted handle use distinct from uniqueness, exclusive access,
  payload copying and the scope's single completion obligation.
- Keep arena owners lexical and nontransportable. Data must not escape by
  carrying its arena owner, extending ownership through reference counting, or
  hiding a dependent value in an otherwise independent result.
- Exclude concurrency, asynchronous I/O, process transfer, callbacks, memory
  mapping and a new collector from the first experiment.

## Candidate directions

### Distinguish file access from filesystem authority

An open file needs an owner and completion. Metadata lookup, removal and rename
do not necessarily create an open file. They still require an explicit
filesystem effect and its interpreter. A directory traversal may eventually
introduce a separate scoped resource.

Compare two filesystem interfaces: an explicitly interpreted filesystem
service, and an identity-indexed directory/root resource that supplies relative
path operations. The second can express a parent dependency, but lexical
identity alone does not prove OS-level path confinement, symlink behavior or
race freedom. State any such foreign assumptions separately.

The first delivery should select one authority model and one supported host
profile. Do not introduce implicit program-global providers or silently use
process current-directory state. Program-lifetime standard streams and global
resources need a separate contract.

### Typed roles before syntax

The following names are schematic roles, not declarations or new Ash syntax.
`R` names a fresh file-owner identity; `D`, when used, names an existing
filesystem/directory owner. A host profile determines native representation.

| Role | Relationship to establish |
| --- | --- |
| Path | An ordinary host-profile-specific value; conversion from `String` is explicit and fallible where necessary. |
| Open configuration | Path, permissions and creation/truncation policy, with a declared filesystem effect and any parent dependency. |
| Provider state | Private ownership of the native handle; clients cannot manufacture it from an integer or pointer. |
| File access | A non-owning value indexed by `R`, with operation permissions and any dependency on `D`. |
| Effect interface | Exact operations for that access; state-changing cursor operations remain effects even when the returned data is copied. |
| Initialization | Existing configuration enters acquisition; failure creates no file owner or body execution. |
| Completion | One owner obligation, a close outcome and an explicit consumed/retained disposition. |
| Public module contract | Types, effects, permission relationships and completion facts sufficient for independent client checking. |

Investigate distinct readable and writable access types, or checked mode
parameters on one family. Do not assume the experimental owner-parameter
mechanism already admits arbitrary mode indices. Acquiring read-only access
must not produce write authority, and access permissions must not imply
exclusive aliases. Repeated reads through aliases share the file position
unless the interface explicitly provides positioned reads.

There are two surface roles: defining a resource family and acquiring an
instance within a lexical body. Reuse the existing effect, handler and resource
conventions where their actual types suffice. The initializer is an ordinary
expression checked in the preceding environment. It is not an unexplained
configuration name introduced by the resource syntax.

Host paths need their own encoding contract. A UTF-8 convenience constructor
may be useful, but a host-native path must not silently lose non-UTF-8 data.
Paths are ordinary data; they are not proof that access will succeed.

Authors must specify the foreign signatures/representations, path policy,
operation permissions, native error/progress interpretation and completion
disposition. Checking can infer ordinary expression types, selected interface
evidence, effect rows and owner dependencies from those contracts. It cannot
infer the truth of a foreign ABI or OS guarantee from an Ash function body.
Bounds known only at runtime require checked conversion before the host call.

### First copying operations

Define operation contracts using ordinary result types, not exceptions or
automatic retry hidden in the evaluator. The initial interface should express:

- Open for reading and open/create for writing, with explicit destructive flags.
- Read at most a positive bound, returning copied `Bytes` or a distinct EOF.
- Write some copied input, returning committed progress or an error.
- Compose `read_all` and `write_all` as library operations with explicit limits
  and a no-progress rule.
- Close through scoped completion. Add positioning and metadata as subsequent
  executable deliveries when their types and target ranges are specified.

A read result needs a distinction between EOF and bytes produced. Invalid or
zero request bounds have an explicit policy; an empty buffer must not become
an ambiguous EOF signal. A write result accounts for committed bytes. A helper
that performs several calls must preserve accumulated progress if a later call
fails. Previously written bytes are not rolled back by a failed Ash result.

Short reads and partial writes are ordinary host behavior. A copying buffer
does not remove that protocol. [Linux read](https://man7.org/linux/man-pages/man2/read.2.html)
and [Linux write](https://man7.org/linux/man-pages/man2/write.2.html) document
these observations for the proposed first host profile.

Text decoding is a separate operation on copied `Bytes`, with an explicit
encoding/error policy. File I/O must not replace invalid input or assume every
file is text. Copied bytes and successfully decoded owned strings may outlive
the file owner.

### Completion and host profiles

Close status and ownership disposition are separate facts. On Linux a failing
close can still release the descriptor; retrying can affect a reused descriptor.
A successful close also does not establish durable storage.
[Linux close](https://man7.org/linux/man-pages/man2/close.2.html)

Record the exact supported ABI and close behavior, including interruption.
Do not transfer a Linux assumption to FreeBSD or another profile without
evidence. Where completion reports a retained owner, specify who contains that
obligation after the source scope ends and what further action is permitted.
A report must not disguise a retained native owner as successfully released.

Distinguish successful body return, a body returning an error value, abandoned
control, and internal runtime failure. Preserve body and close outcomes when
both exist; do not flatten them into an unexplained single failure. Native
host teardown is separate from source completion and cannot claim that a
source close operation ran successfully.

Flush, storage synchronization and close need separate meanings. If the first
adapter uses unbuffered descriptor I/O, say so. A buffered stream adapter would
need an additional buffer ownership and flush contract.

### Arena integration

Copying I/O can ship without typed arena allocation or borrowing. Later compare
reading into private scratch storage and copying out, initializing a fresh
arena allocation before publication, and a separately checked mutable buffer
borrow. The last two are new contracts, not permissions supplied by an immutable
arena reference.

For a destination arena, the result depends on the destination storage lifetime,
not automatically on the file lifetime. Reading into an allocation must account
for capacity, alignment where relevant, initialized length and partial failure.
Publish no readable reference to uninitialized bytes. Either preserve initialized
progress or roll back an unpublished allocation under a stated contract.

Borrowed views additionally need an access interval that excludes refill,
mutation or reclamation. A live file and a live arena do not establish that
interval. Memory mapping remains a later distinct resource study.

## Semantics, Core and verification obligations

| Boundary | Required design account |
| --- | --- |
| Resolution and typing | Authenticate resource, provider, operation and host-contract identities; check initializer effects before admitting the fresh owner. |
| Dependencies | Propagate file, parent and later buffer/view dependencies through aggregates, generic calls, methods, closures and requests. |
| Elaboration | Lower library policy through the generic resource mechanism; retain exact effect identity, permissions and completion relationships. |
| Core validation | Independently reject manufactured access, wrong operation signatures, foreign binding mismatches, copied owner authority and invalid close contracts. |
| Execution | Admit bounds and result storage before relevant publication; interpret the exact activation; preserve host progress and cleanup order. |
| Captured control | Resume preserves the same owner; discard completes owned inner resources without skipping outside or running obligations. |
| Host failure | Report native error, progress and disposition without converting an internal adapter mismatch into an ordinary I/O error. |

Any new operational rules must describe open success/failure, copied read/write,
normal close, abandonment and teardown. Reuse existing transitions where they
already express the behavior. A filesystem library alone does not justify a
new format-specific or file-specific recursive Core form.

Proof obligations include dependency preservation, activation freshness,
no duplicated completion, no post-completion access, and initialized storage
before exposure. Foreign ABI, OS behavior and adapter correctness remain
explicit assumptions unless separately verified. Existing continuation proofs
cover only their stated fragment; successful file programs do not extend them.

## Evidence and experiments

Develop connected batches with public e2e and integration cases. Use focused
native tests or regressions when a contract or demonstrated failure needs them;
do not require a unit test or full workspace build after every helper change.

| Delivery | Executable evidence |
| --- | --- |
| F-0: contract and shared baseline | A typed operation/lifecycle contract, declared host profile, agreed common interfaces and ownership of shared compiler files. |
| F-1: copying read | An imported Ash module opens a real fixture, reads binary and UTF-8 data, observes EOF, closes and returns independent copied data. |
| F-2: copying write | Ash writes, closes, reopens and checks exact bytes; bounded helpers report progress and no-progress failures. |
| F-3: composition | Imported helpers, nested files, acquisition refusal, close failure, capture/resume and owned discard preserve outcomes and cleanup order. |
| F-4: filesystem operations | Defined path and authority contracts support metadata/positioning and selected rename/remove operations on isolated fixtures. |
| F-5: data pipelines | Real configuration and row-processing programs compose with DN-0041 without a file-dependent decoded result. |
| F-6: arena access | A separately specified initialization or borrowing regime produces safe scoped buffers and rejects refill/use-after-scope cases. |

Negative evidence includes write through read-only access, handle escape through
a closure, stale activation reuse, invalid native length conversion, unexpected
host disposition and attempted publication of uninitialized storage. Exercise
partial I/O and close errors through controlled adapter fault injection as well
as actual host calls. Injection establishes wrapper behavior, not OS conformance.

Record copied bytes, native calls, allocations, peak buffers and metadata,
including completion and captured-control state. A `read_all` program may use
document-sized storage; a bounded streaming program should report its actual
buffer and processing-state bounds. External file contents are not included as
live Ash memory, but all adapter-owned buffers are.

## Dependencies and authoring tools

F-1 needs the copying byte representation and verified common resource seam,
not arena borrowing or the whole SQLite library. F-3 needs the common control
and completion contract. F-6 needs an agreed arena/buffer access extension.
File and serialization module work can progress independently of unrelated
shared compiler repairs; shared files have one agreed writer at a time.

A bounded first bridge may use the existing experimental manifest and native
adapter. Document that dependency. The eventual Ash-authored binding follows
DN-0037: headers and a host binary, Ash declarations and policy, declarative
link inputs, and generic compiler/runtime infrastructure.

Useful tooling includes signature and target diagnostics, native link errors
at the originating declaration, checked public summaries, operation/lifecycle
traces, an isolated temporary-filesystem fixture runner, fault injection and
allocation/copy counters. These should expose contracts and observations
without requiring users to inspect compiler internals or native addresses.

## Retention and adoption

A later bounded prototype should test whether a library-defined file provider
can preserve scoped authority and honest progress/completion reports through
real Ash programs. Compare direct library operations with compositions through
generic helpers and data pipelines. Retain successful source modules and
evidence; revise a contract exposed as insufficient before extending execution.
Do not merge an unsuccessful implementation merely because it is bounded.

Language deltas require a change proposal, implementation task, specification
updates, validation, relevant proof work and integration evidence. Accepted
non-language choices follow the architectural-decision workflow. Library
adoption additionally requires a supported target contract, authoring blueprint,
examples and tooling. This note changes no current specification or active task.

## Open questions

- Which filesystem authority model and host profile should the first delivery use?
- Which operation permissions should be separate access types, and which need
  mode parameters or runtime checks?
- What close dispositions and report structure fit each admitted target?
- How should relative paths, directory lifetime and symlink policy interact?
- Which initialization/buffer contract enables arena I/O with the least copying?
- Which measured costs belong to library policy, generic runtime support or
  foreign ABI conversion?
