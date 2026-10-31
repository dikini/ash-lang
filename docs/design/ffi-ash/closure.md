# ffi-ash dialect closure

`ffi-ash` is the official checkpoint of the implemented language on `main`.
The signed annotated `ffi-ash` tag identifies its exact commit. The
[specification](../../../spec/README.md) at that commit defines the dialect;
the [feature inventory](../../project/implemented-features.md) lists its
implemented features and execution support.

## Retained dialect

The checkpoint contains:

- Rank-1 functions, explicit recursion, mathematical integers, tuples, nominal
  data, patterns, exhaustive matching and module/local newtypes.
- Passive modules, visibility and facades, fixed higher kinds, method-only
  interfaces, explicit implementation selection, method-local parameters,
  relational determination and scoped exact evidence.
- Exact effects and rows, lexical handlers, one-shot resume and checked discard,
  legacy integer cells, generic cells, synchronous hooks and scoped cleanup.
- Managed immutable Bytes and UTF-8 String, byte access/conversion and unbounded
  base-256 integer splitting.
- Passive pointer/void foreign declarations, opaque Address, synchronous readonly
  Bytes arguments and ordinary Ash binding policy.
- Lexical regions with default and explicit allocation selection, fixed
  allocate/release pairs, actual supplied storage, closures, recursive immutable
  graphs and bulk release after required completion.
- Scoped continuation Stores, non-owning keys, one-shot restoration, exact
  support/interpreter admission and checked quiescent release.
- Ordinary coroutine selection, recursive drain, cooperative FIFO scheduling
  and explicit gas safe-point examples.
- Two pinned workers with independent roots, copied FIFO byte channels,
  readiness watches, endpoint settlement and carrier-local failure retention.
- The ordinary Work/Ack protocol and codec, including producing cleanup and
  ordinary error handling.
- Human/localized and JSON diagnostics, generated Rust native-call bridges,
  evaluator hosts and cumulative compiler/runtime resource checks.

The accepted design records are [DN-0037](../DN-0037-ash-authored-foreign-library-interfaces.md),
[DN-0053](../DN-0053-scoped-generic-cells-without-native-owners.md),
[DN-0054](../DN-0054-base-lexical-region-memory-contracts.md),
[DN-0056](../DN-0056-scoped-continuation-retention-and-library-scheduling.md)
and [DN-0058](../DN-0058-pinned-worker-host-and-channel.md).
[AD-0013](../../decisions/AD-0013-generated-native-bridges-and-program-builds.md)
and [AD-0017](../../decisions/AD-0017-pinned-worker-host-and-transport.md)
record build and worker architecture.

## Execution support

| Path | Included | Unsupported |
| --- | --- | --- |
| Source-native interpreter | The complete dialect, including pinned workers and admitted native callbacks | The ordinary CLI does not compile native bindings implicitly. |
| Generated executable host | Ordinary language, cells, regions, retained control, scheduling and pointer/void native bridges on x86_64-unknown-linux-gnu | Network scopes and operations are not encoded in private images. |

Generated hosts contain checked compiler-private Core and the evaluator. There
is no native Ash backend or stable Ash/Core ABI. Work/Ack bookkeeping is ordinary
library code; the compiler does not certify acknowledgements or per-message
processing completion.

## Design-branch reconciliation

The reconciliation compares these exact inputs:

| Input | Commit |
| --- | --- |
| Main before documentation alignment | `99095827fce67bf10b2960be5ede0e16a1a22c5d` |
| Accepted documentation alignment | `d8f52a08ce0051f621b6d944edd7b4dd83122fa5` |
| docs/region-ownership-algebra | `9b756f8eaa12b355e27df7dc9dcbba64a0ac8a2f` |
| Shared ancestor | `bade38c635755a608695dd58c8cbef1254aace4c` |

Four notes retain useful additional design material:

- [DN-0032](../DN-0032-algebra-of-scoped-resource-composition.md): resource
  context composition does not merge regions or transfer ownership.
- [DN-0035](../DN-0035-region-memory-management-and-verified-providers.md):
  placement/allocation, ownership, lifetime, reclamation and access are distinct;
  the reference corpus includes the strengthened and additional MM-19–22 cases.
- [DN-0042](../DN-0042-native-interaction-and-efficient-data.md): native-backed
  storage and packed shapes connect to those contracts.
- [DN-0044](../DN-0044-no-default-runtime.md): storage policies are compositions
  with explicit lifetime and completion obligations.

Those additions are informative design for unimplemented extensions. Their
descriptions of the current lexical base now agree with the specification.
They do not turn borrowing, collection or alternative ownership schemes into
implemented features.

Main retains its newer DN-0049 and DN-0053–57 implementation, status and evidence
text. DN-0051, DN-0052, the license and dependency policy were already retained.
The earlier generic-cell proposal and tasks remain retired. The minimal-FFI
checked-host documents retain their historical contracts and are explicitly
superseded. Earlier foreign manifests and libraries are not restored.

The design branch is reconciled by content, without merging its old source tree
or changing its original ref. The checkpoint changes documentation only;
implementation, tests, source libraries, Cargo configuration and lockfile are
unchanged from the Main input above.

## Boundaries and simplification

Imports and interface selection remain static; their evidence lowers to checked
ordinary functions. Newtypes erase after validation. Scheduling policy and the
Work/Ack protocol remain ordinary Ash. The runtime retains only the owning Store,
region, resource and transport mechanisms required by those programs.

The old foreign provider/owner, status, window, codec and manifest/adapter
execution routes are retired. The protocol-specific network checker and one-way
completion checker are retired. The checked-host F1-F8 programme and whole-image
AD-0015/AD-0016 choices are superseded.

General borrowing, usage/lifetime-based placement inference, region ownership
transfer, alternative object reclamation, moving collection, worker migration,
shared Stores, general cancellation and automatic checkpoint insertion are not
implemented. Neither are full SQLite, richer ABI mappings, protected/isolated
foreign execution, Float, filesystem/serialization APIs, source proof terms,
existential packaging or first-class polymorphic source values.

Earlier milestone tags retain their original contents. The dialect name and tag
do not add a compiler selector or compatibility grammar.

## Verification record

The official tag is applied to the frozen closure commit after:

1. A fresh complete `cargo xtask verify`: format, metadata, check, build,
   denied-warning Clippy, all-target/all-feature tests and denied-warning rustdoc.
2. Full-tree Markdown lint with the line-length rule disabled, changed-document
   relative-link and anchor checks, and whitespace checks.
3. Independent review of the dialect boundary, reconciliation and actual gate
   receipts, with all findings resolved.
4. Confirmation that the reviewed and verified commit is unchanged and that
   implementation and build inputs retain their original contents.

The signed tag annotation records the verified commit, exact gate command,
input fingerprint, seven-stage results, receipt hash and independent review
result. Local receipts and logs remain in the retained verification cache under
the [verification policy](../../project/verification.md). The annotation supplies
the published checkpoint record without changing verified source files.

The existing region, retained-control and one-shot proof models keep their
recorded theorem scopes. This documentation-only closure changes no Lean source
and adds no new compiler-correctness or native-memory-safety theorem.
