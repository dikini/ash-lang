# CP-0023: Scoped Generic Cells

- ID: `CP-0023`
- Status: proposed
- Related: [DN-0053](../design/DN-0053-scoped-generic-cells-without-native-owners.md),
  [DN-0038](../design/DN-0038-resource-properties-and-mutable-variable-usage.md),
  [DN-0054](../design/DN-0054-base-lexical-region-memory-contracts.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This proposal is not current Ash. It specifies a transition from the ash-ffi
> checkpoint and does not authorize implementation while its status is proposed.

## Current behavior

The target baseline is `ffi-base`, commit
`354c76b391fe4af665cf6a03479a9874a57cb3e3`. References to baseline behavior below
mean that checkpoint, rather than the older checkout containing this proposal.

The baseline's
[scoped cells](https://github.com/dikini/ash-lang/blob/354c76b391fe4af665cf6a03479a9874a57cb3e3/spec/static-semantics.md#scoped-cells-and-resource-dependencies)
store `Int`. Acquisition introduces a fresh resource identity, reusable access,
sealed provider evidence and an exact local effect interpreter. The resource
scope owns release. Handles, hidden closure captures, evidence and indexed
operation metadata retain their resource dependencies. An outside handler cannot
receive a payload that depends on an owner it lies outside.

The baseline's
[source resource declarations](https://github.com/dikini/ash-lang/blob/354c76b391fe4af665cf6a03479a9874a57cb3e3/spec/static-semantics.md#source-resource-declarations)
can carry private Ash data but require an authenticated foreign owner. Their
State/data operations do not provide a general mutable slot. Native retention
also distinguishes source completion from actual owner consumption; retained
dependencies remain protected after ordinary access is revoked.

The missing behavior is a scoped, typed slot for an ordinary Ash value without
native acquisition. It requires contents dependency tracking through replacement
and later reads, in addition to the baseline's tracking of handle dependencies.

## Proposed behavior

### Public family and compatibility

Add compiler-owned module `@builtin.generic_cell`, exporting exactly the
following defining identities. The import alias is ordinary source syntax.

| Export | Contract |
| --- | --- |
| `Cell<R,T>` | Opaque reusable access; kind `Type -> Type -> Type`; no source constructor. Also the authenticated resource family, with owned argument at position zero. |
| `Provider<R,T>` | Sealed interface evidence introduced only by acquisition of that exact cell instance. |
| `Ops<R,T>` | Exact effect instance with `read : Cell<R,T> -> T` and `write : (Cell<R,T>, T) -> Unit`. |
| `read` | `Cell<R,T> -> T ! {Ops<R,T>}` with requirement `Provider<R,T>`. |
| `write` | `(Cell<R,T>, T) -> Unit ! {Ops<R,T>}` with requirement `Provider<R,T>`. |

Both parameters have kind `Type`. The method schemes quantify `R` and `T` at
rank 1. A generic helper may require and forward `Provider<R,T>` with the
existing `where` syntax. An ordinary `impl`, `with`, matching name or compatible
representation cannot manufacture this evidence or access.

The legacy `@builtin.cell` exports, `Handle<R>`, `Provider<R>`, `Ops<R>`, and
lowercase `resource cell<R>` retain their complete behavior, including that
form's direct-import requirement. No constructor changes arity and no facade
is claimed to make the two APIs aliases. Sharing a runtime kernel is optional.

Qualified imports, selective imports, renaming and facade reexports of the new
family preserve its defining identity and complete arguments. A facade may
expose acquisition through that authenticated family; it does not need an
additional direct import of `@builtin.generic_cell`. This follows the named
resource form, rather than adding a second lowercase acquisition form.

### Acquisition, typing and scope

Use the existing named-resource grammar with the full two-argument application:

```ash
import @builtin.generic_cell as Cell

main : Unit -> Int
main () = resource Cell.Cell<R, Int> c = 41 {
    let _ = Cell.write (c, 42)
    Cell.read c
}
```

This proposed program returns `42`; it is not executable on the baseline.
All Ash examples below likewise specify proposed acceptance programs.

1. Resolve the canonical family and its two kind-`Type` arguments. The owned
   position is a fresh binder `R`; check `T` in the preceding scope. `T` must
   not mention the new `R`. Other arities or argument kinds reject.
2. Check the initializer as monomorphic `T` in the preceding scope and evaluate
   it exactly once. Neither the fresh `R` nor the new value binder `c` is in
   scope there. Existing preceding bindings with the same spelling still
   resolve normally. The existing primary-expression initializer grammar
   requires parentheses around a compound initializer such as a call.
3. After successful preparation, introduce a fresh rigid lexical identity,
   `c : Cell<R,T>`, exact `Provider<R,T>` evidence and the local interpreter for
   `Ops<R,T>`. Every execution creates a fresh runtime activation, including
   recursive or repeated execution of one lexical acquisition site.
4. If the body checks as `A` with row `E`, the expression has type `A` and the
   union of the initializer row with `E` minus exactly `Ops<R,T>`. Other effect
   instances remain outward. Nested source handlers already account for their
   direct outward requests under ordinary row rules.
5. Check the result type, outward row, escaping schemes, selected evidence and
   retained value dependencies for escape of the closing owner. A value may
   leave an inner lexical block while remaining inside its cell's resource
   scope. It cannot retain that cell beyond the resource scope.

`T` is fixed for an activation and admits ordinary reusable, discardable values:
scalars, products, nominal data, non-owning access and functions subject to the
dependency rules below. It is not a polymorphic scheme. Reads are applications,
so an unannotated read binding does not acquire the syntactic-function
generalization available to some local anonymous functions. Native State,
views, continuation capabilities and other restricted values retain their
existing transport and storage prohibitions, including through wrappers.
There is no new `Copy` or `Drop` constraint and no implicit source destructor.

`R` identifies this cell's logical owner, not an allocation region. Its lifetime
is exactly its resource scope. Choosing longer-lived backing storage cannot
extend access, return a live-reader closure beyond that scope or defer the
scope's required completion.

### Retained payloads and resource cycles

For each initializer and each write that reaches a cell slot, every resource
owner required by the payload must be proved to strictly outlive that slot's
owner. Here “outlive” means a distinct enclosing resource activation whose
logical scope encloses the cell scope and whose ownership/completion obligation
cannot be discharged before the cell completes. It does not mean that memory
happens to remain allocated or guarantee that access cannot be revoked.

Native quarantine can revoke ordinary access while an enclosing owner remains
protected. Storing its handle preserves the existing exact liveness and
revocation checks; the outlives relation neither prevents quarantine nor
restores access. Closing the cell cannot discharge that native owner's retained
dependencies.

The required owners include actual retained access, selected aggregate fields,
closure captures, selected evidence methods, resource-indexed operation
metadata, and dependencies reached through another cell. An unused environment
entry alone does not create a dependency. Exposing an identity-free arrow or
placing access in an ordinary wrapper does not remove a dependency.

This invariant has the following consequences:

- An inner cell may retain access or a closure dependent on an enclosing owner.
- A cell cannot retain access to itself or a closure capturing its own access.
- An older cell cannot retain a younger or incomparable owner, even if a later
  write would clear the payload before that owner closes.
- Direct and indirect cycles of resource dependencies reject. The checker
  must follow hidden captures and transitive cell dependencies, not just type
  arguments or the immediately stored handle.
- Ordinary immutable sharing and cyclic graphs with no prohibited resource
  dependency remain permitted under the existing data rules.

The relation is about activations, not equality of source binder spellings.
An enclosing invocation's cell and a recursive invocation's cell at the same
source site are distinct. A payload from the enclosing invocation may satisfy
the strict relation for the inner invocation. The recursive positive case below
is required; treating every repeated site as self-dependency is insufficient.

Admission proves the relation for every possible target slot and payload at a
write. Aliases, branch-selected handles and helpers cannot select a less
restricted target after checking. Relevant unknown behavior may reject when
the relation cannot be proved; runtime testing of a key is not a substitute
for source and Core dependency checking.

An intercepted write that never reaches a slot creates no retained slot edge.
It still obeys ordinary request-payload and handler-result dependency checks.
Forwarding to a cell interpreter applies the same retained-payload invariant
as a direct write.

### Reads, snapshots and closures

A builtin read returns the current ordinary value without consuming access.
Where ordinary Ash shares a represented value, the read shares that value; it
does not deep-copy data, erase dependencies or freeze transitively reachable
cells. A write replaces the slot's one payload root and returns `Unit`. Dropping
the old root does not complete resources referenced by non-owning handles.

The read result has the dependencies of the value returned at that point. A
live-reader closure retains the cell and cannot escape its owner. A closure
retaining only an independent copied snapshot can escape. If the snapshot
contains access or a closure dependent on an outer owner, that dependency
survives the read and any later capture.

Later replacement does not change earlier snapshots or retroactively add
dependencies to them. Analysis must retain this distinction through known
aliases, imported helpers, branch joins and recursive calls. Joins include all
possible returned or stored dependencies; they cannot choose a safe branch and
discard an unsafe alternative. The required cases below set minimum precision.
They do not require an exact analysis of arbitrary higher-order programs.

Ordinary source handlers keep lexical precedence over the builtin interpreter.
An intercepted read returns the handler's actual reply and its dependencies,
which may differ from the stored value. Checking must not infer independence
solely from the builtin operation's name. A locally intercepted write that is
not forwarded leaves the slot unchanged. Interception grants no handle,
provider or completion authority.

### Execution and completion

Conceptually an acquired cell owns an activation key, its checked payload type
and one ordinary payload root. Access values are non-owning keys, not additional
owners. This description does not select a heap representation.

| Transition | Required behavior |
| --- | --- |
| Acquire | Evaluate and validate the initializer once; admit storage, work and live-resource capacity before publishing a fresh owner, handle, evidence or body entry. |
| Read at builtin interpreter | Authenticate the operation, complete instantiated arguments and handle against the exact live activation, then return its current value. |
| Write at builtin interpreter | Evaluate the handle and replacement in ordinary strict left-to-right order; authenticate the exact operation, types and live activation; finish all fallible preparation before replacing the root once; return `Unit`. |
| Capture and resume | Move and restore the same owner and payload with the continuation. Do not reacquire, copy ownership or restore an earlier payload. |
| Normal completion | After required inner completion, revoke access and remove the payload root once; return the checked body answer directly. |
| Checked discard | Complete owned abandoned scopes in structural order, retaining required enclosing interpreters; release this cell once after its dependent cleanup. |

Primitive read and write invoke no user callback. A helper that reads, invokes
an effectful callback and writes has no extra atomicity guarantee. Repeated
calls and aliases observe the same slot while its owner remains live.

Cells have no foreign finalizer, retained native disposition, manual close or
outcome wrapper. Values shared elsewhere remain subject to their own storage
and dependencies; closing a cell does not promise immediate reclamation of all
reachable represented data. It also does not consume any referenced foreign
owner.

Live-resource capacity includes captured cell scopes. Ownership transfer,
payload retention and teardown must remain bounded and iteratively disposed
under the existing ledgers. Capacity or work exhaustion is an internal failure,
not a recoverable source allocation result. Refusal cannot publish a partial
cell or partially perform a builtin write. Internal termination promises no
source cleanup; divergence promises no eventual release.

### Dependency admission, Core and diagnostics

Contents-flow facts relate each read result and replacement to the possible
target activations and retained dependencies. They must survive module imports,
public helper summaries, type/effect instantiation and Core copying. A helper's
plain result type is not a sufficient summary when hidden captures matter.
Known abstractions retain their inferred relationships; crossing a module or
ordinary helper boundary alone is not grounds to reject a required positive.

Use an authenticated typed effect/resource carrier within the existing Core
dialects. It must retain the defining family, owned position, complete `R,T`
application, initializer, value binder, body and exact rows. Independent linked
Core validation must reconstruct acquisition, contents-flow, owner relations,
handler replies and escape checks from admitted Core and defining metadata.
A source-only side table or copied assertion cannot supply authority. No new
pure Core effect form is introduced. The concrete carrier encoding and shared
implementation with legacy integer cells remain implementation choices.

Transformed and restored Core must pass those same checks. Dynamic keys
distinguish activations of a lexical identity; they cannot replace the static
relation. Malformed Core with altered owner, provider, operation or payload
facts fails independent validation. A stale or mismatched runtime key fails
internally before access or mutation and cannot become recoverable source
behavior.

An escaping or unproved retained resource dependency reports
`type.resource-escape` at the initializer, replacement or escaping expression,
with acquisition and causal capture/call labels where known. Unsafe discard
keeps `effect.discard-unsafe`. Ordinary syntax, resolution, kind, type, row and
structural continuation failures retain their existing precedence. Changing
an `Int` slot to `Bool` is a type error, not a dependency diagnostic.

Inference, dependency summaries, joins, recursive analysis, retained collections
and independent Core checking charge their owning ledgers before proportional
work or retention. The analysis must terminate within finite budgets. Failure
publishes no partial checked module or permission; a fresh sufficient budget
permits retry. Implementation may choose the analysis, but cannot drop required
positive cases to obtain termination.

## Semantic delta

| Baseline | Proposed transition |
| --- | --- |
| Builtin mutation stores only `Int`. | Add a separate sealed family storing one ordinary monomorphic `T`; preserve the legacy API. |
| Named resource acquisition executes authenticated native lifecycle declarations. | Also recognize this compiler-owned family in the existing grammar, with no native owner or source lifecycle declaration. |
| Dependencies track handles and ordinary value/call flow; builtin reads copy independent integers. | Track mutable contents and the actual dependencies of read results, including handler replies and earlier snapshots. |
| Native private data belongs to the bounded State/data contract. | Generic payload roots have their own scoped builtin semantics; native State/data admission does not broaden. |
| Scoped ownership already controls release and continuation capture. | Extend the same structural obligations to generic payload roots, with strict stored-payload outlives checks and explicit rejection of resource cycles. |

## Affected specification areas

The implementation checkpoint must update these baseline specification areas
together. Pinned links identify the review target even in an older checkout.

- [Syntax](https://github.com/dikini/ash-lang/blob/354c76b391fe4af665cf6a03479a9874a57cb3e3/spec/syntax.md):
  document the compiler-owned named-family acquisition and its complete
  arguments; retain the grammar and legacy form.
- [Name resolution](https://github.com/dikini/ash-lang/blob/354c76b391fe4af665cf6a03479a9874a57cb3e3/spec/name-resolution.md):
  builtin exports, family provenance, imports/reexports, sealed evidence and
  the owned argument's scope.
- [Static semantics](https://github.com/dikini/ash-lang/blob/354c76b391fe4af665cf6a03479a9874a57cb3e3/spec/static-semantics.md#scoped-cells-and-resource-dependencies):
  fixed payload typing, effect rows, contents flow, strict owner relation,
  hidden capture, handlers, escape, diagnostic labels and precedence, and
  charged analysis.
- [Elaboration](https://github.com/dikini/ash-lang/blob/354c76b391fe4af665cf6a03479a9874a57cb3e3/spec/elaboration.md):
  typed resource carriers, module summaries, independent validation and
  transformation obligations.
- [Dynamic semantics](https://github.com/dikini/ash-lang/blob/354c76b391fe4af665cf6a03479a9874a57cb3e3/spec/dynamic-semantics.md#scoped-cell-execution):
  generic roots, authentication, replacement, activations, structural completion
  and failure boundaries.

## Resulting specification truth

After the complete product checkpoint is integrated, Ash has a sealed generic
cell family whose reusable access supports reads and writes of one monotype
without acquiring a native owner. Each cell lives exactly within its resource
scope. Every retained payload dependency strictly outlives that cell; direct
and indirect resource dependency cycles reject. Read results preserve actual
value dependencies and snapshots, while exact source handlers retain precedence.

Surface typing, linked Core validation and execution agree on family identity,
payload type, activation, contents dependencies and structural completion.
Existing integer cells, rank-1 typing, request-payload boundaries, native
retained-owner protections and failure behavior remain current alongside the
new family. These statements remain proposed until that integration.

## Interactions

[DN-0053](../design/DN-0053-scoped-generic-cells-without-native-owners.md) retains
the design rationale and alternatives. This proposal selects the concrete API
and minimum contents-flow behavior for that candidate.

[DN-0054](../design/DN-0054-base-lexical-region-memory-contracts.md) remains a
separate exploration. Generic cells need neither region-backed ordinary
construction nor a new allocation context. Future region-backed values must
retain their region dependencies when placed in cells; assignment cannot
relocate them or extend their validity. Future backing storage must outlive the
slot without extending the cell's resource-scope authority.

The existing request-payload rule still applies at every owner boundary,
including hidden captures, evidence and indexed operation metadata. A younger
dependency cannot be sent to an outer interpreter merely because storage exists
there or because the request's final answer is independent. Interception inside
that dependency's owner does not authorize later forwarding across it.

Native retention keeps its current distinction between source completion and
actual consumption. Retained owners keep their declared dependency edges and
transitive protection, quarantine revokes ordinary access, Current teardown is
blocked before native entry while a retained dependent remains, and host
destruction attempts dependents before enclosing owners once. Generic cell
release neither consumes those owners nor drops those native edges. This
proposal adds no native dependency kind, State transport, retaining owner or
permission to release backing storage after source completion alone.

Mutable-variable syntax may later elaborate to this resource scope, but it must
separately specify bare reads, access sharing, assignment order and local
generalization. The present API requires explicit read and write calls.

## Non-goals

- Region creation, arenas, region object layout, reservation/initialization,
  explicit or implicit allocation contexts, region promotion or general graph
  reclamation from DN-0054.
- Arbitrary Ash-state resource declarations or changes to source-authored
  foreign resource lifecycles, State/data rules, ABI or retained-owner handling.
- Cells that outlive their resource scope, transported owners, temporary
  younger dependencies, resource dependency cycles or cycle collection.
- Linear payloads, empty cells, take, swap, exclusive borrows, user disposal,
  manual close, concurrency, atomic updates or transactions.
- Mutable-variable grammar, new lifetime/capture annotations, polymorphic cells,
  higher-rank typing or changes to legacy integer-cell APIs.

## Required evidence

Acceptance of this proposal settles the semantics; it is not implementation
acceptance. A later authorized product task must deliver the API, source
checking, elaboration, module summaries, independent Core checking, execution
and specification updates together. Each case below is a required observation
at that checkpoint, not evidence already obtained. Cases must run through the
public source path and affected Core validation paths, with assertions for the
stated value, diagnostic or failure boundary.

### Positive source cases

| ID | Program or setup | Required observation |
| --- | --- | --- |
| CELL-P01 | Acquire `Cell.Cell<R,Int>` at `41`, alias the access, write `42` through the alias and read through the original. Repeat for `Bool`, a tuple and nominal data. | Returns the replacement with one shared slot; acquisition evaluates its initializer once. |
| CELL-P02 | Read `41` into `old`, write `42`, return `(old, Cell.read c)`. Separately return a closure capturing only `old` and call it after the scope. | Pair is `(41,42)`; escaped snapshot closure returns `41`. |
| CELL-P03 | Inside outer `Cell.Cell<A,Int> a = 7`, acquire inner `Cell.Cell<B,Cell.Cell<A,Int>> b = a`; return `Cell.read b` to code still inside A, then read it. | Returns `7`; B's completion does not revoke A. |
| CELL-P04 | The snapshot program below stores an outer-dependent closure after reading an independent closure. | Earlier snapshot escapes both scopes and returns `7`. |
| CELL-P05 | The recursive program below acquires the same lexical family site twice and stores an outer activation's capture in the inner cell. | Returns `9`; distinct live activations and exactly one release per acquisition. |
| CELL-P06 | Pass aliases through a constrained local helper, an imported helper and a facade; include a well-typed branch choosing between two aliases of the same cell. | Same slot observations and dependency relationships as direct calls; facade acquisition needs no direct builtin import. Distinct rigid owner types do not become interchangeable. |
| CELL-P07 | A source handler for exact `Ops<R,Int>` replies `99` to a read of a slot holding `41`; intercept a write without forwarding, then read outside that handler. Separately forward a write once. In a function-cell variant, a handler inside R discards a replacement capturing R without forwarding it. | Overridden read returns `99`; intercepted write leaves `41`; forwarded write changes the slot once. The discarded function replacement creates no slot dependency or resource cycle. |
| CELL-P08 | A local read handler replies with an identity-free closure capturing another owner; consume it while all dependencies remain live. An independent handler reply may escape. | Actual reply dependencies govern admission and behavior. |
| CELL-P09 | Send an independent snapshot to a handler outside the cell scope; send an outer-dependent value across an unrelated inner scope to a handler still inside its owner. | Both admit and preserve values under the existing per-owner crossing rule. |
| CELL-P10 | Store an already admitted cyclic immutable value with no resource dependency, then read and project a finite prefix. | Preserves the ordinary value's observable sharing/cycle behavior; no resource-cycle diagnostic. |
| CELL-P11 | Store a fixed monomorphic function and call repeated reads at that type; nest legacy and generic cells and use their respective providers. | Repeated results agree; only each acquired exact effect instance is discharged. |

CELL-P04 fixes the required distinction between a snapshot and current contents:

```ash
import @builtin.generic_cell as Cell

independent : Unit -> Int
independent () = 7

main : Unit -> Int
main () = {
    let saved = resource Cell.Cell<A, Int> a = 1 {
        resource Cell.Cell<B, (Unit -> Int)> b = independent {
            let old = Cell.read b
            let replacement : Unit -> Int = fn(ignored) {
                let held = a
                42
            }
            let _ = Cell.write (b, replacement)
            old
        }
    }
    saved ()
}
```

Replacing the final `old` in B's body with `Cell.read b` must reject when A
closes: that returned closure retains A even though its arrow contains no A.
The harmless read of `a` into the closure-local `held` is a retained capture;
it invokes no cell operation and therefore adds no effect to the arrow.

CELL-P05 fixes activation-sensitive checking without polymorphic recursion:

```ash
import @builtin.generic_cell as Cell

visit : (Bool, Unit -> Int) -> Int
visit (again, initial) = resource Cell.Cell<R, (Unit -> Int)> c = initial {
    match again {
        true => {
            let next : Unit -> Int = fn(ignored) {
                let held = c
                9
            }
            visit (false, next)
        }
        false => {
            let saved = Cell.read c
            saved ()
        }
    }
}

initial : Unit -> Int
initial () = 7

main : Unit -> Int
main () = visit (true, initial)
```

Both invocations use the same monomorphic payload type. The inner initializer
depends on the enclosing invocation's live cell, rather than its own new cell.

### Negative source cases

| ID | Program or setup | Required rejection |
| --- | --- | --- |
| CELL-N01 | Write `Bool` to `Cell<R,Int>`; acquire with an initializer of the wrong type or wrong argument kind/arity. | Ordinary resolution, kind or type failure before dependency checking. |
| CELL-N02 | Return a handle, a wrapper containing it, or a closure that reads it beyond its own scope; repeat through imports and selected evidence. | `type.resource-escape`, even with an identity-free exposed result type. |
| CELL-N03 | Initialize a function cell with an independent function; replace it with a function whose body binds `let held = c` then returns `42`, capturing that same cell. | `type.resource-escape` at retention; fixed payload type and still-live scope do not admit self-dependency. |
| CELL-N04 | Inner function cell B stores a closure capturing outer A; write a closure capturing B into A. Repeat with ordinary wrappers and helper-hidden captures. | Reject the younger dependency and indirect cycle; clearing A later does not repair it. |
| CELL-N05 | Store a younger-dependent value in an older cell without a cycle; include a branch where only one possible payload or target is unsafe. | `type.resource-escape`; absence of a cycle alone is insufficient. |
| CELL-N06 | Return the later read in CELL-P04 beyond A, or let a handler-provided dependent read result escape its owner. | `type.resource-escape`; neither snapshot inference nor the builtin operation name erases actual dependencies. |
| CELL-N07 | Send a closure capturing R to an ordinary handler outside R, including via a write aimed at an outer cell; the final body answer is independent. | `type.resource-escape` at the crossing payload. Include selected evidence and indexed metadata variants. |
| CELL-N08 | Use a fresh R or c in its own initializer without a preceding same-spelled binding; put fresh R in T. | Resolution/scope rejection. A companion with valid preceding shadowed bindings must resolve to those bindings. |
| CELL-N09 | Manufacture the sealed provider using `impl` or `with`, use a same-spelled counterfeit family, or call a method without its exact provider. | Existing sealed-provider, family-resolution or unsatisfied-requirement failure; no acquisition authority. |
| CELL-N10 | Read one stored identity function and use that same monomorphic value at incompatible argument types; attempt a scheme-valued or higher-rank T. | Existing rank-1/type restrictions; reading does not generalize a stored value. |
| CELL-N11 | Store native State, a prohibited view or a continuation capability, directly or inside ordinary wrappers. | Existing storage/transport restriction, not an invented generic-cell exemption. |

### Control, validation and failure cases

| ID | Required paired evidence |
| --- | --- |
| CELL-C01 | Capture after a write, resume and observe the latest payload with no reacquisition; nested acquisitions and same-site recursion keep distinct keys. Malformed donor or stale access must not reach another activation. |
| CELL-C02 | Checked discard releases an owned cell once after dependent cleanup; an inner cleanup can still use the enclosing cell. Reject attempts to skip required outside completion or abandon a running cleanup. Include capture while evaluating the initializer, before the new cell exists. |
| CELL-C03 | Validate direct, imported, copied, identity-transformed and ordinarily optimized Core with the same observable results and dependencies. Independently reject changed T, owned position, provider, operation, row, target owner, hidden capture or contents-flow claims. A body-free helper summary must not authorize erased dependencies. |
| CELL-C04 | Exercise exact sufficient, one-short and fresh retry budgets for source inference, recursive summaries, Core construction/validation, acquisition and write preparation. Refusals publish no partial permission or cell and mutate no slot; already performed operand effects are not rolled back. |
| CELL-C05 | Measure live-resource capacity with active and captured cells, large shared payloads, and deep owned discard. Accounting precedes proportional work/retention; teardown is iterative; no silent relaxation of stack, work or capacity limits. |
| CELL-C06 | Retain the complete legacy integer-cell regressions and ash-ffi payload-crossing, State/data, native retention, blocked teardown and host-destruction evidence. In a mixed case, cell C stores enclosing native A's access; inside C, dependent native B completes with retention and quarantines A. Reading the handle from live C remains permitted; a later native operation through it is denied by baseline liveness/quarantine checks before native entry. Closing C neither consumes A nor removes native dependency protection. |

Required assertions distinguish source rejection, independent Core rejection,
runtime internal failure and successful execution. Failure injection cannot
stand in for native observations in the retained-owner regressions. The product
checkpoint must retain focused results, independent review, the prescribed full
verification gate and matching normative specification before this proposal is
removed under the artifact lifecycle.
