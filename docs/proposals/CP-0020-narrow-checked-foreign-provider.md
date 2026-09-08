# CP-0020: Narrow Checked Foreign Provider

- ID: `CP-0020`
- Status: accepted
- Related: [DN-0026](../design/DN-0026-effect-ash-resource-first-milestones.md),
  [DN-0027](../design/DN-0027-effect-ash-program-design.md),
  [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [DN-0018](../design/DN-0018-runtime-established-static-evidence.md),
  [cleanup evidence](../design/effect-ash/reliable-cleanup-evidence.md),
  [AD-0001](../decisions/AD-0001-implementation-environment.md)

> Accepted by the user on 2026-09-08. This proposal is not current Ash.
> The selected provider is a bounded native byte buffer. Implementation requires
> a task and execution plan under this contract.

## Current behavior

The integration branch through `2cae3be` implements scoped cells, exact sealed
provider evidence, non-owning activation handles, synchronous hooks and reliable
cleanup. These branch results are not yet integrated into `main`.

[Scoped cells](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
introduce fresh lexical identity and evidence, reject escaping stored dependencies,
and retain owners through capture. [Runtime resource scopes](../../spec/dynamic-semantics.md#scoped-cell-execution)
separate activation identity from the owned payload. Their acquisition failures
are internal failures, not typed source results. No foreign allocation or native
pointer is exposed.

[Cleanup](../../spec/dynamic-semantics.md#scoped-cleanup-actions) defines structural
normal and owned-abandonment closing. Source actions may report ordinary typed
failures, but internal failure does not run source cleanup or promise successful
native release. This proposal must supply the selected provider's own native
ownership rules rather than infer them from a fresh type or cleanup syntax.

## Proposed behavior

### Choice and alternatives

Select one compiler-owned native byte-buffer provider, backed by one fixed
C allocation/deallocation pair. It introduces a real native allocation boundary,
ordinary allocation failure, checked access and release without paths, strings,
filesystem permissions or I/O policy.

Two alternatives were considered:

- A private scratch file exercises fallible reads, writes and close, but requires
  platform-specific close/rollback rules and additional I/O semantics. It is not
  selected for this mechanism-focused slice.
- A Rust-owned byte vector is simpler but is not evidence of a checked foreign
  boundary. It may be a test double, not the product implementation.

The native buffer deliberately does not demonstrate fallible native close.
It satisfies the narrow provider milestone through real allocation failure and
ownership-safe release; it does not claim the same failure model fits files.

This slice exercises the mechanics: checked foreign acquisition, typed failure,
authority introduction, static erasure with retained runtime identity, captured
ownership and structural release. It does not establish the general FFI design
or the API through which libraries will define acquisition.

### Fixed API and acquisition

Add compiler-owned `@builtin.native_buffer`. Imports, aliases and facade
re-exports preserve its defining identities. An acquiring module must directly
import this module, using the same rule as cell acquisition. Source files,
copied signatures, `impl` and `with` cannot introduce its sealed authority.

The module exports these exact families and their ordinary data constructors:

| Name | Proposed contract |
| --- | --- |
| `Handle<R>` | Opaque non-owning handle; no source constructor or pointer conversion. |
| `Provider<R>` | Sealed exact relation introduced for the successful acquired body. |
| `Outcome<T>` | Ordinary data: `Success(T)` or `Failure(Error)`. |
| `Error` | Ordinary data: `InvalidLength`, `AllocationFailed`, `InvalidIndex`, `InvalidByte`. |
| `Ops<R>` | `length : Handle<R> -> Int`, `read : (Handle<R>, Int) -> Outcome<Int>`, `write : (Handle<R>, Int, Int) -> Outcome<Unit>`. |
| `length`, `read`, `write` | Methods requiring exact `Provider<R>` and requesting corresponding `Ops<R>` operations. |

The proposed acquisition form is `resource native_buffer<R> b = length { body }`.
`native_buffer` is a fixed resource designator, not a new general declaration
form or an identifier reserved outside that position. Existing `resource cell`
syntax and behavior do not change.

The length expression evaluates once as `Int` in the preceding scope. The body
checks under fresh rigid `R`, `b : Handle<R>`, exact `Provider<R>` evidence and
its local builtin interpreter. If the body has type `T`, the acquisition has
type `Outcome<T>`. Successful normal completion releases the allocation and
returns `Success(body_value)`; allocation failure returns `Failure(error)`
without entering the body. A body that itself returns an `Outcome` remains
nested; there is no automatic flattening, propagation or error classification.

The outward row is the initializer row union the body row with exactly
`Ops<R>` removed. Neither result type, outward row nor stored result dependency
may export `R` or its acquisition. A failed allocation introduces no runtime
handle, activation, provider capability or body execution. Checking the body
does not claim that allocation always succeeds.

This is illustrative proposed source, not an executable current-Ash example:

```ash
import @builtin.native_buffer as Buffer

main : Unit -> Buffer.Outcome<Buffer.Outcome<Int>>
main () = resource native_buffer<R> b = 4 {
match Buffer.write (b, 0, 42) {
Buffer.Success(()) => Buffer.read (b, 0)
Buffer.Failure(error) => Buffer.Failure error
}
}
```

On successful allocation the expected observation is `Success(Success(42))`.
The implementation must retain and check the exact source, constructor identity
and actual CLI rendering rather than treating this illustrative spelling as a
new display-format requirement.

### Access and failure rules

Length must be positive and representable within the bridge's checked addressable
allocation bound. Other lengths return `Failure(InvalidLength)` without a native
call. The bound is no greater than either the native size type or the host's
valid pointer-offset range; conversion and arithmetic may not wrap.

Successful allocation contains exactly that many zero-valued bytes. `length`
returns the original length. Reads and writes use zero-based indices; an index
outside `[0, length)` returns `Failure(InvalidIndex)` without memory access.
A write then checks its value is in `[0, 255]`, otherwise returning
`Failure(InvalidByte)` without mutation. Invalid index takes precedence over
invalid byte. Success reads a copied `Int` or writes one byte and returns
`Success(())`; no resizing, bulk views or ownership transfer is admitted.

Native allocation returning no block produces `Failure(AllocationFailed)`.
Compiler/evaluator exhaustion, malformed Core, activation mismatch and host
contract violations remain internal failures, never one of these constructors.
The `Error` family belongs only to this provider, not a universal error domain.

### Trusted native boundary and partial acquisition

Use one statically linked, private bridge to the host C `calloc`/`free` pair.
No source symbol names, external declarations, ABI descriptions or loader are
introduced. Initial product evidence targets the existing Linux development
host with eight-bit bytes. Other targets require an explicit bridge support
declaration and the same conformance evidence; unsupported builds must not
silently substitute a simulated provider or typed allocation failure.

This evidence staging does not narrow AD-0001's x86-64 and ARM64 requirements.
The task must state the target matrix, native execution coverage and any
unavailable cross-target check before approval. Keep the compiler crate's
`unsafe_code = "forbid"`: isolate the bridge in a small runtime adapter with
a safe owning API, documented unsafe invariants and audited linking/dependencies.
Native pointers stay inside that adapter, not in semantic types or transformations.

The bridge's native contract follows C's allocation/deallocation requirements:
`calloc` supplies zero-initialized storage or a null result, while `free` has
no recoverable result and requires valid allocation ownership. See
[WG14 N1570, sections 7.22.3.2–3](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).
The native specification informs the bridge obligation; it does not define Ash
source semantics. No assumption about `errno`, zero-sized allocations or a
recoverable failure from `free` is required.

Acquisition proceeds in this order:

1. Evaluate and validate the length; charge work and reserve all fallible Ash
   publication, outcome, owner and activation storage before a native call.
2. Attempt native allocation once. A null result takes the typed failure path.
3. Hold a successful pointer in an unpublished owning guard until the prepared
   scope, handle and lexical activation are installed together.
4. Transfer that single owner to the resource frame and enter the body.

There must be no unguarded interval after native success. A preparation or
publication failure after native success releases the unpublished allocation
once, publishes no body authority and retains the internal failure. Tests must
inject such a failure even if normal publication is made infallible. No implicit
native allocation retry is performed.

### Identity, ownership and erasure

Reuse the existing resource distinctions; introduce no additional certificate,
allocation identity class or runtime provider registry:

| Carrier | Authority and lifetime |
| --- | --- |
| Lexical brand `R` and sealed provider facts | Authenticate scope, exact API relation, generated methods and dependencies through linked and Core validation; erase static evidence after its last checked use. |
| Existing acquisition activation key | Distinguishes executions, including repeated/reentrant acquisition at one source site; remains in lexical instantiation and non-owning handles through their checked uses. It is not a native address. |
| Non-owning `Handle<R>` | May be copied and transported while its owner is live; native access still requires the exact selected activation. |
| Owned native block and length | One unpublished guard or one resource frame owns them, never both; ownership moves with capture and ends at structural release or internal host teardown. |

The exact builtin operation identity and activation information needed for
dispatch remain at runtime. Erasing static evidence does not erase executable
method functions, dispatch metadata, the activation or native owner prematurely.
A native address may be reused after release; it cannot resurrect an old key.

Handle, closure, selected-evidence and operation-payload dependencies follow the
existing cell rules, including imported and generic helpers. Copied integers
and provider error constructors contain no buffer dependency and may escape.
An outside handler cannot receive a buffer-dependent value. An inner scope may
return an outer handle to a point still inside the outer owner's lifetime.

Ordinary exact source handlers retain precedence. Interception neither creates
native authority nor extends lifetime. The builtin bridge runs only when the
authenticated builtin interpreter is selected and its handle matches that
activation. A mismatched or retired handle must fail before pointer access.

### Exit and release contract

| Exit or state | Required behavior |
| --- | --- |
| Initializer fails or is abandoned | No allocation by this scope and no owner; preceding owners follow existing rules. |
| Invalid length or native allocation failure | Return the typed failure; do not enter the body. |
| Native success followed by failed publication | Guard releases once; internal failure, no partial scope or evidence. |
| Body returns normally | Complete structurally inner cleanup, release the native block once, then return `Success(body_value)`. |
| Body returns an error constructor | Same normal release; preserve that value inside `Success`, without reclassifying it. |
| Outward request captures and resumes | Move the same native owner with the capture; do not release or duplicate it. |
| Owned discard | Close contained owners at their structural positions, release this block once, skip abandoned body/suffix/result wrapping and continue the discarding clause. |
| Outside owner or running source cleanup would be skipped | Retain existing rejection; native storage grants no extra abandonment permission. |
| Internal evaluator failure after acquisition | Iterative host teardown releases native owners once, without running source actions or rolling back earlier writes. |
| Divergence or external process termination | No source promise of eventual release, cleanup execution or recoverable outcome. |

An inner cleanup action may use a still-enclosing buffer through its retained
builtin interpreter. A captured source override cannot silently fall back to
that interpreter: preserve the existing per-action closing-context check.
Cells, registrations, source cleanup and native buffers close by control nesting,
not allocation timestamps. There is no separate native cleanup schedule.

Native release here is a fixed host deallocation, not an ordinary source action
or a recoverably fallible close operation. It never raises `CleanupFailure` or
retries. Source cleanup can still report its own typed errors through ordinary
collectors. A later file provider must separately define close-failure ownership;
this choice does not add an always-successful close assumption to all resources.

### Work, publication and implementation boundaries

Extend the closed set of resource kinds and existing evaluator/resource carriers
only as required for this second builtin. Do not add a provider trait registry,
parallel interpreter, generic destructor protocol or duplicated capture analysis.

Native owners count toward existing live resource-owner capacity, including
captured owners. Charge proportional initialization work before allocation and
one access's validation, conversion and result preparation before any write.
Charge all added compiler scans, row/dependency facts and retained collections
through their current owning ledgers. Native length cannot bypass a work limit
or overflow a charge. Source `AllocationFailed` cannot stand in for exhaustion.

Reserve fixed release/disposal work with ownership acquisition so internal
teardown does not need fresh fallible allocation or a new budget grant to free
an already-owned block. A failed write check or preparation leaves storage
unchanged; failure after earlier completed writes preserves those writes until
release. No general execution rollback or external allocator-time guarantee is
introduced. Pure and provider-free programs allocate no native-owner state.

## Semantic delta

Add one compiler-owned API and one fixed acquisition designator, a typed
allocation-result wrapper, native-byte access under existing resource authority,
and fixed native release on admitted exits and internal host teardown. Extend
closing-context proof to this retained builtin resource interpreter. Existing
cell result types, source cleanup, evidence selection and handler rules remain
unchanged. There is no source FFI, existential result or manual release.

## Affected specification areas

- [Syntax](../../spec/syntax.md): fixed resource designator and acquisition form.
- [Name resolution](../../spec/name-resolution.md#compiler-owned-cell-module):
  second compiler-owned module, exact imports and sealed API provenance.
- [Static semantics](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies):
  provider result/row rules, dependencies and retained-interpreter compatibility.
- [Elaboration](../../spec/elaboration.md#surface-erasure): closed resource-kind
  admission, exact result wrapping, independent authority and erasure boundaries.
- [Dynamic semantics](../../spec/dynamic-semantics.md#scoped-cell-execution):
  guarded native acquisition, operations, typed failures and structural release.
- [Specification overview](../../spec/README.md) and [tools](../tools/ash.md):
  admitted provider, support boundary, examples and failure classification.

## Resulting specification truth

After complete implementation and integration into `main`, Ash admits this one
checked foreign allocation boundary. Successfully entered bodies have a fresh
activation and sealed authority for one owned native block. Ordinary source
cannot fabricate a pointer or export its lifetime. Native allocation failure is
typed; evaluator failure is not. Normal and owned-abandoned exits release through
the existing structural resource mechanism, and host teardown owns native
deallocation independently of source cleanup. No statement generalizes these
rules to arbitrary foreign resources.

## Interactions

Library-defined acquisition is a required later capability, deferred until a
suitable FFI design establishes its trusted boundary. The fixed builtin in this
slice is a concrete witness, not a decision that every future provider must
require compiler changes. That later design must explain how library acquisition
introduces fresh scoped authority, transfers ownership safely and supplies
provider-specific failure and release rules.

Keep those boundary contracts explicit without adding a provider registry or
general acquisition protocol now. The buffer's `Outcome` wrapper and infallible
native release are provider-specific choices, not universal requirements for
future acquisition. Evidence from this slice transfers only within its tested
scope; it does not promise that future FFI work needs no representation changes.

Proof work can rely on checked provenance, not treat `Provider<R>` as a proof of
allocation success on every execution, numeric bounds, alignment beyond bytes,
disjointness or eventual release. Bounds are checked per access; no refinement
or certificate calculus is added.

Existential packaging remains excluded by current escape rules, but the native
owner is not identified with a source path or address. Future packaging must
explicitly transfer owner and authority together rather than redesign their
separation. Suspension, concurrency and dynamic loading must separately justify
their lifetimes and identity rules; no scheduler or plugin mechanism enters now.

The native buffer cannot stand in for evidence about fallible file close,
filesystem access policy or partial I/O. Those are later file-provider work,
not requirements of this mechanism-focused slice.

## Non-goals

Library-defined acquisition; general ABI or `extern` syntax; source pointers,
casts or address arithmetic;
dynamic libraries and provider registries; files, sockets, strings and paths;
resize, slices, borrowed views or zero-copy export; manual free and ownership
transfer; proofs, refinement arithmetic or existential packages; asynchronous
completion, cancellation, multi-shot control or concurrency; new source cleanup
failure semantics; a general native-support portability layer.

## Required evidence

The task may refine implementation steps and measurements, not these semantics.
The existing ten-unit forecast is a scope weight, not a measured execution
budget. Any need for a general ownership system, second row
solver, new runtime identity class or broad resource-limit increase returns to
proposal review.

| ID | Required proof |
| --- | --- |
| FOREIGN-01 | Syntax, imports/facades, direct acquisition import, sealed evidence, copied-API rejection, exact types/rows, nested `Outcome` behavior and unchanged cell syntax/result types. |
| FOREIGN-02 | Real bridge allocation and zeroed bytes; length/read/write exact results; invalid length/index/byte precedence; unchanged storage on rejected writes; checked host conversions. |
| FOREIGN-03 | Deterministic native allocation-failure injection yields only the typed failure and no body/authority; pre-call exhaustion makes no native call; injected post-success publication failure frees once with no published owner. Real native success tests are mandatory, not mock-only evidence. |
| FOREIGN-04 | Duplicable aliases while live; independent acquisitions and repeated/reentrant same-site executions; native-address reuse cannot revive a stale activation; no handle/closure/evidence/payload escape, including imports and generic instantiation. |
| FOREIGN-05 | Mixed cell/registration/cleanup/native-buffer order; inner action access; capture/resume; recursive owned discard; skipped suffixes and result wrapping; outside-owner and running-action negatives. |
| FOREIGN-06 | Captured source override rejection versus surviving builtin/action-local interpretation; exact generic coincidence; open rows/lacks and imported callback authority; no universal closed-row restriction. |
| FOREIGN-07 | Independent linked/Core forgery of builtin kind, provider, method, operation, handle, owner, brand, result wrapper, effect row and origin; positives and negatives after both Core transforms; native call counters stay zero for rejected Core. |
| FOREIGN-08 | Exactly-once native deallocation across normal return, typed body failure, discard, partial publication and internal teardown; no source action on internal failure and no fake recoverable `free` failure. |
| FOREIGN-09 | Exact/one-short/fresh compiler and runtime boundaries; active plus captured owner capacity and reuse; proportional native length charges; deep success and failure disposal at retained stack bounds; no state or allocation for Pure/provider-free execution. |
| FOREIGN-10 | Audited isolated bridge, safe API, unsafe invariants, dependency/linking review and AD-0001 target evidence; real backend plus fault-injection separation; source/CLI examples and all predecessor migrations; independent effects, provenance/proof, existential-pressure and Rust/resource reviews; full `cargo xtask verify`, strict lint, documentation/notation/link checks and clean local integration. |

No evidence row is closed by acceptance. The accepted scope selects the native
buffer and explicitly excludes fallible native close. An implementation task
must retain all evidence obligations above.

## Review status

Bounded independent semantic review found no actionable gap in the proposed
acquisition, ownership, failure, erasure and closing-context rules. Markdown,
local-link and authority checks passed. The source example remains prospective.
User acceptance on 2026-09-08 covers the contract and the deferred requirement
for library-defined acquisition with a suitable FFI design. No implementation
or executable conformance evidence is claimed.
