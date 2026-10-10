# DN-0036 readiness for Ash-authored foreign interfaces

This review starts design work under
[DN-0037](../DN-0037-ash-authored-foreign-library-interfaces.md), using Main
`5c5fb914ff3ee729305a2d8a2df86ff348725e84` and inspected worktree evidence on
2026-10-09. It is informative evidence and a proposal brief. It selects no new
syntax, accepts no compiler architecture and authorizes no implementation.

The user selected a first target: an end-to-end Ash-authored **copying SQLite
binding on one host ABI**, with general borrowing and wider Arena graphs left
for later proposals. The user also selected generated native bridges as the first
execution/linking direction. This scope is a first DN-0037 checkpoint, not completion of
the whole foreign-authoring program.

The later [ffi-ash milestone scope](../DN-0037-ash-authored-foreign-library-interfaces.md#agreed-ffi-ash-milestone)
selects `x86_64-unknown-linux-gnu`, generated Rust runtime bridges, optional
separate C/header checks, whole-program checked-Core embedding, and native-buffer
and minimal-arena source libraries alongside SQLite. [AD-0013](../../decisions/AD-0013-generated-native-bridges-and-program-builds.md)
records the converged build boundary. [CP-0022](../../proposals/CP-0022-ash-authored-foreign-interfaces.md)
proposes the semantic transition; it remains unaccepted. The historical evidence
below keeps its original pins and limitations.

## Two library cases, one common boundary

The user agreed that unfinished Arena work is not a prerequisite for continuing
DN-0037. SQLite remains the first complete authoring delivery. A minimal native
arena lifecycle is the second worked design case from the outset: declare
configuration, opaque state, acquisition, usage and release in Ash and execute
them through the same generated bridges. This case must observe native calls
and ownership transitions, rather than fabricate a source result.

The common declaration and bridge model must express both libraries without
SQLite-specific or arena-specific compiler dispatch. The arena case tests that
configuration, access, refusal and release contracts transfer beyond SQLite.
It does not require broader graph storage or completion of the unverified
Arena recovery branch.

A native arena supplies storage; a region describes the scope and dependencies
under which access is valid. Declaring an allocator's ABI alone does not supply
region safety. The design must keep native ownership, scoped identity and access
discipline distinct, so that later borrowing and containment rules can state
which owner and validity interval justify an access.

General borrowing, typed arena allocation, containment and wider graphs remain
follow-on semantic work. They are not first-delivery capabilities or hidden
prerequisites. The proposal must document these exclusions and identify where
their future contracts meet the initial scoped-access model.

## Assessment

There is enough DN-0036 evidence to start a bounded proposal. There is not yet
evidence for the central DN-0037 authoring claim: an author can bind a supported
native library using Ash declarations and native build inputs without writing
a library-specific Rust adapter, Rust manifest or C shim.

DN-0036 established the resource and evaluator side of that boundary. SQLite
provides a realistic reference binding and comparison corpus. The main missing
mechanisms are source-authored foreign contracts, generated ABI bridges, temporary
native storage and validity rules, and native build/link integration.

Finishing all wider Arena experiments is not a prerequisite for this copying
checkpoint. Their failures and missing borrowing contracts limit broader
claims, and supply negative cases for the design. They should not silently
expand the first proposal.

## What transfers from DN-0036

| Area | Established evidence | Transfer limit |
| --- | --- | --- |
| Resource definitions versus instances | Checked library resource families; one initializer evaluation in the preceding scope; fresh instance identity and runtime activation; dependent-escape rejection. [Source tests](../../../tests/provider_sqlite_source.rs), [P-1](../provider-experiments/semantics.md#selected-first-execution-contract). | Experimental rules are not yet normative general resource semantics. Reusing them in a product proposal requires an explicit semantic delta. |
| Complete owner arguments | Ordered Type/row arguments, inherited roles, kinds, saturation, substitution and import preservation. [Owner tests](../../../tests/provider_owner_rows.rs). | These facts authenticate Ash applications, not a C calling convention or native representation. |
| Provider preparation and final authority | Immutable checked templates, occurrence-preserving specialization and freshening, independently authenticated final Core and transform rejection. [Correspondence](../provider-experiments/semantics.md#implementation-correspondence-at-the-common-checkpoint), [Core provider implementation](../../../src/core/provider.rs). | Prepared source metadata grants no executable permission. A new source declaration and native binding path must preserve the same authority distinctions. |
| Native ownership | Guarded acquisition before publication, non-owning access, exact finish dispositions, retained-owner quarantine and dependency-ordered host teardown. [Runtime contracts](../../../src/foreign/runtime.rs), [retention tests](../../../tests/provider_retention_source.rs). | Runtime contracts currently delegate native behavior to trusted Rust implementations. Ash-authored policy needs a generic ownership bridge; ordinary report constructors cannot create consumption authority. |
| Control and completion | Resume without reacquisition, structural discard, cleanup through live outer resources, handler precedence, formal open-row callback and distinct captured-control demands for equal substitutions/body rows. [Control tests](../../../tests/provider_control_source.rs), [SQLite control](../../../tests/provider_sqlite_control.rs). | These are executed finite cases, not a general simulation theorem. The callback is Ash code, not a foreign callback ABI. |
| Copied values | Immutable Bytes/String, checked integer widths, UTF-8 and explicit-length copies, distinct NULL/empty values and conversion failures. [Copying tests](../../../tests/provider_sqlite_copying.rs), [contract](../provider-experiments/contracts.md#sqlite-copying-workstream-obligations). | Copying does not eliminate temporary native addresses, initialization obligations or API-specific invalidation. |
| Real SQLite sessions | Acquisition, preparation, binding, stepping, copying, reset/clear, transactions, imported row helpers, persistence/reopen and separate body/completion errors. [Session tests](../../../tests/provider_sqlite_sessions.rs), [packaged hosts](../provider-experiments/examples/sqlite-copying/README.md). | The native calls and part of the protocol/conversion policy are still hand-written Rust. No Ash-only authoring claim follows. |
| Arena storage | Actual scoped backing, usage/release and sealed scalar Layout/storage for Unit, Bool and checked signed-64 Int. [Scalar results](../provider-experiments/arena-results.md), [tests](../../../tests/provider_arena_allocation.rs). | It establishes a finite native publication protocol, not arbitrary C layout, initialized output slots, general pointers, borrowing or graph storage. |
| Publication and terminal failure | Separate preparation, result admission and commit where native publication can be deferred; consumption survives report conversion failure. [Runtime interfaces](../../../src/foreign/runtime.rs), [codec failures](../../../tests/foreign_codec_failures.rs). | External side effects such as a database update are not generally rollbackable. The new design must specify failure after each irreversible call. |
| Compiler costs | Measured source/final/Core work, exact budgets, phase reports and calibrated admission. [Admission account](../provider-experiments/calibrated-admission-2026-10-08/README.md). | Calibration admitted realistic programs; it did not prove low complexity or remove their measured work. CPU/RSS and authoring effort need separate assessment. |

The [regression evidence](../provider-experiments/arena-regression-2026-10-09/README.md)
records 39 public cases, five stack/dictionary regressions, 49 adapter unit
cases, ten backing cases, five real SQLite hosts and scalar Arena. The full
integration gate records 3,475 passes, zero failures and one existing ignored
generated-calibration case. That total covers the workspace; it is not a count
of foreign-authoring tests.

All six packaged hosts fit their nominal calibrated phase budgets. The copying
program still charges 1,213,287 source units, and the file session charges
1,609,027 independent-Core units. No deficit is used in those receipts, but
there is little headroom in the largest phases. A native-authoring design must
measure added declaration, conversion and validation work, rather than assume
these programs have become cheap.

## What still lives in hand-written native code

The [native adapter](../../../foreign-adapter/README.md),
[Rust implementation](../../../foreign-adapter/src/lib.rs),
[build script](../../../foreign-adapter/build.rs) and
[C shim](../../../foreign-adapter/sqlite_bridge.c) identify the work that an
Ash-only binding must replace or express through common primitives:

- Raw foreign signatures and ABI representation checks, symbol requirements
  and linkage. The current audited target is `x86_64-unknown-linux-gnu`.
- Stable NUL-terminated input buffers and explicit-length byte buffers,
  checked narrowing, nullable handles, output slots and partial acquisition.
- SQLite-specific sequencing, including checking a suspect column result
  before another API call changes the relevant diagnostic.
- Input copying with `SQLITE_TRANSIENT`. The existing shim supplies a special
  destructor-function-pointer sentinel; a plain scalar/opaque-pointer profile
  must explicitly account for it. This does not require calling back into Ash.
- Returned column pointer/length validity, immediate independent copying,
  UTF-8 checks and bounded diagnostic copying.
- Statement protocol and owner dependencies. Finalization consumes a
  statement even on its reported error; refused connection close retains it.
- Native guard destruction for unpublished or quarantined state. That is
  separate from running source completion or inventing a successful result.

The proposed allocation of responsibilities is: author-declared ABI facts and
foreign assumptions; ordinary Ash protocol, conversion and reporting policy;
common checked primitives for memory/calls/ownership; and common toolchain
support for building and linking. Generated glue may implement the primitives,
but cannot acquire extra authority from being generated.

## Outstanding work and dependency on the first proposal

| Outstanding work | Relation to the selected SQLite checkpoint |
| --- | --- |
| Ash-authored symbol/signature/representation declarations and their body-free public contracts | Required. Moving Rust manifest data into Ash is one checkpoint, but not the end-to-end authoring result. |
| Generic native call lowering, independent Core checking and execution | Required. Retaining library-specific `ExecutableForeignModule` implementations behind source declarations would leave the main objective unfinished. |
| Temporary native buffers, initialized output slots, nullable/partial handles and copied output access | Required. The design can bound them to the selected synchronous profile without offering general borrowing. |
| Precise copy-window and invalidation rules | Required. A live connection/statement does not imply every returned pointer is still valid. The design must permit the selected pointer/length query sequence and reject invalidating calls before copying. |
| Build inputs, symbol/target/configuration diagnostics and compilation/linking | Required. The current Cargo script is a tested baseline, not an Ash native-linking interface. |
| Generic close/refusal/quarantine/destruction policy expressible without Rust per-library code | Required. Normal completion and safe host teardown must both have concrete contracts. |
| Product adoption of reused resource/packed-value semantics | Required as an explicit proposal dependency or included semantic delta. Presence on Main does not make the experiment normative. |
| General borrowing, retained SQLite inputs/views and broader containment | Deferred. A copying API needs limited temporary validity, but not the general retained-view program. |
| Wider Arena payloads, stored Ref/Link, shared graphs, nested loading, graph copying, scratch arenas and cycles | Deferred. Partial results do not establish these capabilities. They are not prerequisites for the selected SQLite binding. |
| Formal proof development | Separate workstream, excluded from this proposal. Independent compiler/Core validation remains required. |

## Relevant worktree and recovery evidence

The remaining directories were inspected read-only. No paused task was resumed
and no historical compiler, native test or proof build was rerun.

| Location and source pin | Relevant information | Status |
| --- | --- | --- |
| `.worktree/recovery/arena-completion-20261009` | Raw successful baseline/integration logs and native host outputs; historical rounds 20–24 and the static failure audit are now in `historical-investigation-20261009.tar.gz`. Portable receipts are under [Arena regression evidence](../provider-experiments/arena-regression-2026-10-09/README.md). | Successful baseline evidence is distinct from failed wider rounds. Archive members preserve the original capture names; old absolute paths are historical provenance. |
| `codex/arena-provider-recovery-20261009`, `1aef8c1` | 92-file checkpoint preserving unfinished wider Arena, generic layout/family, capture and cleanup work. [Recovery manifest](../provider-experiments/arena-regression-2026-10-09/recovery-files.json). | Unverified and not a Main ancestor. It includes later edits and is not the exact source of each historical test round. |
| Historical `ash-doc-lib-pin` and `ash-doc-modular-pin` worktrees | Earlier passive-module/interface/kind checkpoints. | Ancestors of Main; useful provenance, not additional DN-0037 implementation. Their generated Cargo caches were removed during cleanup. |

The paused Core alignment, proof coverage, proof tooling and proof-navigation
assets are a separate workstream. Their worktrees remain untouched and are not
dependencies or deliverables of this proposal brief. No formal proof work is
included here.

The failed wider Arena evidence contains three transferable lessons:

1. Cleanup inference can change stored rows after a prepared capture projection
   was authenticated. The round-24 audit identifies stale projection as a
   candidate cause, not an observed exact failed node. Trusted row changes need
   an explicit transform/reauthentication account; replacing a receipt with
   today's metadata would hide the authority obligation.
2. A same-typed dictionary is not interchangeable with the original selected
   binder. One round-24 negative test failed because its donor selector searched
   ordinary Bind nodes while the real dictionary lived in a scope table. That
   is a demonstrated test-selection defect, not evidence for relaxing checking.
3. Generic composite substitution, outgoing terminal payloads and repeated
   type-universe comparison remained unresolved in wider connected cases.
   Those limitations must be measured again if the proposal reaches them.

## Starting proposal brief

The first proposal should state the user-visible result before choosing syntax:

> Given supported C headers and a library binary, an author writes the selected
> SQLite binding and lifecycle policy in Ash, declares native requirements,
> and builds/runs an Ash client through common tools. No hand-written
> library-specific Rust manifest, Rust adapter or C shim is required.

Headers are author input. The compiler checks Ash declarations; a C parser is
not a prerequisite. Header/binary matching and successful symbol resolution do
not prove that native code obeys its declared memory or consumption assumptions.

Candidate initial ABI shapes are fixed-width scalar arguments/results, opaque
handles, nullability, byte/string buffers, output parameters, and the required
SQLite sentinel. The tested Linux x86-64 GNU profile is a sensible first
candidate. General aggregate-by-value ABI, variadics, native callbacks,
asynchrony, dynamic loading, owner transport and a stable Ash ABI remain outside
that candidate. Static archives and ordinary link-time shared-library
dependencies are native inputs; they need not imply a runtime `dlopen` feature.

The source design must identify separately:

- Native dependency and symbol identity, target ABI and configuration.
- Foreign representation, including addresses that carry bounded access rather
  than becoming ordinary integers or transferable ownership.
- Call effects and explicit foreign assumptions: initialization, retention,
  invalidation, consumption/refusal and failure.
- Ash-facing conversions, protocol and result types, reusing ordinary
  functions, effects, handlers and resource definitions where possible.
- Checked module-summary and Core facts, including original authority and
  independent validation after transformations.
- Runtime guard and temporary-storage transitions, plus observable failure
  behavior after a native effect has already occurred.

### Data-access disciplines must be language contracts

The user requires the language to distinguish borrowing, copying and other
access disciplines. The first implementation may support a small subset, but
it must not erase that distinction behind a native pointer type or Rust-only
adapter convention. This requirement remains when general borrowing is added
later.

Treat representation, access discipline and ownership transition as separate
typed facts. Two calls can have the same C signature while one copies an input
and the other retains its address. Conversely, a call may borrow its input and
return an independent copied result. A single per-operation "copying" flag is
therefore insufficient; the contract belongs to each affected input/result and
its owner or validity window.

| Discipline | Meaning the language must distinguish | First checkpoint |
| --- | --- | --- |
| Independent copy | The result owns its Ash-managed contents and has no dependency on the source native storage. Copying an address, handle or embedded reference is not an independent copy. | Required for admitted scalar, Bytes and String results. No promise of arbitrary graph copying. |
| Borrow for a synchronous call | Temporary input storage stays valid during the call; the foreign callee is declared not to retain that access. Access permission and length/encoding remain explicit. | Required for SQL, paths and transient input buffers. |
| Temporary returned access for copying | Native-owned memory is read only within an admitted copy window, under the exact owner and API validity rules, then converted into independent data before the window closes. | Required for selected column/diagnostic copies. This does not expose a general escaping native view. |
| Retained borrowed input or reusable borrowed view | Access depends on a live owner and additional invalidation/mutation restrictions after the initial call. | Explicitly unsupported in the first checkpoint; general borrowing needs a later contract. |
| Ownership consumption or transfer | A native ownership transition occurs; it cannot be reproduced by copying an access value or constructing a report. | Only the required guarded acquisition and finish dispositions. General source owner transport remains excluded. |

The initial raw SQLite declarations must distinguish native input copying
through `SQLITE_TRANSIENT` from retained input through `SQLITE_STATIC`.
The former lets the temporary input buffer close after the call under the
declared foreign contract; the latter must reject in this first binding rather
than accidentally receive the same contract. Neither the function signature
nor pointer constness establishes retention or validity.

Returned column data requires more than "borrow for one call": obtaining its
pointer and querying its matching length are separate selected calls. The
design must describe that finite copy window, permitted queries and invalidating
operations. It must reject stepping, resetting, finalizing or other declared
invalidation before copying completes. It must also prevent a window from
escaping through a result, closure, evidence or captured control. A native
diagnostic has its own validity and query-order contract; do not reuse the
column rule merely because both contain bytes.

Public checked contracts must preserve these roles across imports and generic
helpers. Core must retain enough facts to validate them independently. Runtime
guards must enforce the admitted ownership/validity transitions. User-facing
inspection and diagnostics should distinguish a copied value, a live temporary
borrow and an unsupported retained borrow, rather than expose compiler phases.

The exact source forms and whether disciplines are expressed by constructors,
declaration associations, effects or a combination remain design questions.
The acceptance condition is behavioral: unsupported or invalid borrowing cannot
be silently admitted as copying, and valid copying does not retain an unnecessary
native dependency. Foreign adherence to the declared contract remains an
explicit assumption.

### Selected execution direction and alternatives

| Approach | Benefit | Cost or limitation |
| --- | --- | --- |
| Generate typed ABI bridges and link an execution host that uses the existing Ash evaluator | Fits the tested native build route; fixed signatures are available to a native compiler; avoids per-library hand-written glue and does not require a native Ash backend. Selected first direction. | Requires a generic bridge generator, a generated-host build/link path and authenticated mapping from checked declarations to emitted bridges. The interpreter cannot use the new library until that host is built. |
| Generic descriptor-driven ABI call engine | One generic execution engine can consume supported signatures without compiling a bridge per signature. | Adds an ABI engine and representation/dependency surface to audit. Symbol provision, output memory, sentinel values and ownership contracts still need design; runtime dynamic loading is not automatically admitted. |
| Move manifests into Ash while retaining the existing Rust adapters | Separates source contract admission from ABI execution and can provide an intermediate comparison. | Insufficient as the selected delivery: the author still needs library-specific host code. It must be labeled preparation, not Ash-only binding support. |

Generated Rust bridges are now an accepted build direction in AD-0013, not an
implemented capability. The source semantic proposal still needs acceptance
under the [artifact guide](../../project/artifacts.md).

### Generated bridge boundary

The proposed path is checked Ash foreign declarations → target-resolved bridge
plan → generated native wrappers → compiled and linked execution host → existing
Ash evaluator. This does not require compiling ordinary Ash functions to native
code. The host supplies the generated bindings to the generic runtime.

Each wrapper must correspond to an exact original foreign operation and its
complete checked ABI signature. Generation must preserve that association
through compilation, linkage and runtime registration. Symbol names alone do
not authenticate bindings. Preflight checks must finish before associated
resource acquisition; imports remain passive.

The native compiler checks emitted call sites against the declarations and
selected target representation. This catches incompatible generated types and
unsupported target shapes earlier than a descriptor-driven runtime call. It
does not establish that an incorrectly declared external binary obeys the ABI,
or that native code obeys retention, invalidation and consumption assumptions.
A header parser is not required. AD-0013 places optional generated C/header
verification in a separate authoring command, rather than the runtime call path.

The generated wrapper handles the admitted ABI boundary: scalar conversion,
opaque handle representation, temporary buffers, output storage and return
conversion. Ordinary Ash definitions express SQLite protocol, error mapping
and lifecycle policy using checked primitives. The generator must contain no
SQLite symbol dispatch or special ownership policy. Source-declared sentinel
representation, including `SQLITE_TRANSIENT`, remains an obligation of the
bounded profile rather than a reason to retain a handwritten SQLite shim.

The first semantic draft must specify four connected transitions:

1. A foreign declaration establishes representation facts and explicit access,
   initialization and ownership assumptions; checking produces an immutable
   contract with its defining origin.
2. Target resolution produces a bridge plan only for supported representations
   and native inputs. Compilation and linking produce an executable binding
   authenticated against that plan.
3. A call receives admitted access and initialized storage, executes once, and
   records native ownership disposition even if result conversion fails.
4. Copying closes temporary access after independent data has been admitted;
   acquisition publishes a guarded owner; completion consumes it or quarantines
   the same retained owner with its dependencies.

These are design obligations, not selected source syntax. Outstanding choices
include output initialization on each outcome, partial acquisition destruction,
finite pointer/length copy windows, sentinel declarations, and how build inputs
and target facts are exposed through the public tools. Formal proofs remain a
separate workstream.

## Simplification and phase discipline

Use one canonical checked foreign contract to feed module summaries, Core
operands and target binding, rather than retaining separate source, manifest,
runtime and generated-glue descriptions that must be reconciled repeatedly.
Which views can be shared follows their actual authority and lifetime.

The preparation-cost investigation supports encoding distinct processing states
and immutable inputs in types. A candidate implementation discipline separates
unchecked declarations, checked contracts, target-resolved plans and executable
bindings. Transitions should consume or borrow the appropriate prior phase,
making duplicate preparation and use of unfinished data difficult to express.
This is a candidate architecture, not new Ash syntax or accepted implementation.

Branding data does not validate it. Reuse must be tied to exact input identity,
target/configuration and dependency versions. Scope owners remain per activation.
Independent Core checking must still reconstruct its obligations; transformed
inputs cannot reuse authority for a different projection. Host teardown and
foreign-call side effects are not cached preparation.

Prefer ordinary Ash wrappers for SQLite protocol and error mapping. Keep common
memory/call primitives small and typed. Do not duplicate the compiler, create a
closed-only binding engine, or require arbitrary graph Layout support to admit
the copying profile.

## Evidence required before acceptance and delivery

1. Define the exact semantic delta from current `spec/`, including adoption or
   bounded replacement of experimental resource/Bytes/String behavior.
2. Work one complete binding from declarations through resolution, typing,
   public summaries, Core, native binding, initialization, calls and completion.
   Explain every remaining trusted primitive and foreign assumption.
3. Preserve the five complete SQLite programs, native values/copy counts,
   completion order, failure classifications and retained-owner observations.
   Pair the new path with the Rust reference path; do not weaken useful cases.
4. Demonstrate missing/wrong symbols, unsupported target/configuration, wrong
   representations, invalid lengths/UTF-8, uninitialized outputs, partial
   acquisition, stale access and forged authority with causal diagnostics.
   Binary symbol presence alone cannot diagnose every falsely declared ABI.
   Pair copy versus retained-input declarations with the same raw signature;
   distinguish independent contents from copied handles and reject a native
   view used after its declared invalidation or escaping its copy window.
5. Recheck independent Core and transforms, resume/discard/cleanup, finish
   conversion failures and dependency-ordered quarantine/destruction.
6. Use a contrasting small native API within the same declared profile to test
   that generation/dispatch contains no SQLite-specific policy. It need not be
   another complete library implementation or broaden the ABI.
7. Conduct the headers-plus-binary walkthrough using documented Ash tools,
   without compiler source knowledge or per-library hand-written host glue.
   Record declaration burden, generated code, copies, build/link time and
   compiler costs separately from native behavior and formal claims.

The next design step is to turn these roles into precise typed contracts for
the selected generated-bridge route. Surface syntax should follow those choices.
Only then can a complete proposed semantic transition state the resulting
specification truth and required product checkpoint.
