# TASK-0037: Program build and interface verification

- ID: `TASK-0037`
- Status: active
- Related: [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [GitHub issue #3](https://github.com/dikini/ash-lang/issues/3)

> This task organizes authorized work. It does not define Ash semantics.

## Dependencies

Accepted CP-0022/AD-0013 and TASK-0036 checked contracts/Core. Build phases may
be developed against authenticated generic contracts; executable admission must
use the completed source/Core path.

## Work

1. Add additive compile/build/execute APIs and explicit `ash build` configuration,
   preserving existing non-foreign run_path/RunConfiguration callers.
2. Resolve the bounded target and explicit native link inputs; generate typed Rust
   call bridges and a host containing private checked Core and the existing evaluator.
3. Authenticate linked bindings against original library/operation contracts before
   acquisition. Revalidate reconstructed Core; no runtime compiler or name-only dispatch.
4. Support static archives and ordinary shared linkage, including the non-callable
   sentinel representation, without a library-specific runtime C shim.
5. Provide separate optional `ash check-ffi` C/header checks and mismatch diagnostics.
   Verification mappings supply no executable values or ownership authority.
6. Document reproducible source-only library authoring and native build/run inputs.

## Progress

Assignment, blockers, live progress and PR status belong to the linked GitHub
issue. This task retains scope, ordered work and durable implementation findings.

## Verification

Build and execute a checked Ash program with real scalar/native ownership calls,
then each library port. Verify static/shared linkage, unsupported targets/shapes,
missing symbols, stale or mismatched bridge registrations and Core. Run separate
header checks with a deliberate type/value mismatch. Inspect generated Rust for
exact origin/signature mapping and absence of library policy. Record source/config
pins, commands and native observations; one Cargo job and final integrated gate.

## Discoveries

The optional header checker retains original prepared library allocations from
the canonical compiler pass, including unused and constant-only libraries. It
returns this authoring catalogue only after complete source, linking and Core
checking. Ordinary run/build paths do not collect it. Versioned mappings name
defining source paths and exact library/member roles; imported aliases and equal
donors cannot replace them. A separate finite authoring ledger pays mapping,
index and C emission work using the existing structural work guard.

C checks independently assert the authored integer category/width/sign, address
families, exact native prototypes and mathematical constant/non-callable sentinel
values. GNU C syntax-only compilation produces no object and never evaluates
Ash. Mappings and output are absent from runtime facts, images and Rust bridge
preparation. The [tool guide](../tools/ash.md#optional-c-header-checking) describes
the explicit entry, mapping/header/compiler inputs, retained diagnostics and
target limitations. These implementation findings do not certify a binary or
change the source contract's validity, retention or consumption assumptions.

The private image carries associated method spellings, lexical forwarding,
complete applications, helper occurrence selections and original evidence
anchors. Executable forwarding records are reconstructed and independently
checked before provider binding; passive native facts are compared separately
with the generated host's original EXPECTED_FACTS. A forwarding-only corruption
can preserve that comparison and still fail independent Core admission. A
changed original method name fails the fact comparison first. Neither boundary
runs Ash semantic checking or selects an implementation at startup. Registry
provenance admission can reconstruct original declaration coordinates through a
paid, bounded syntax-only walk of resident embedded defining text; it never
reopens source paths, resolves names or infers source types.

Selective imports and facades retain provenance-bound source headers and a
passive implemented-interface census even when the resource name or prior
implementation is not exported. The census only rejects forbidden association;
it carries no method body, implementation selection or executable permission.
Explicit source import routes still govern available names.

The evaluator and private Core stay the execution engine. Bridge generation
replaces the experiment's handwritten executable adapters; header verification
is optional and cannot repair missing source contracts.

Standalone Core reconstruction needs original source provenance, registry and
method catalogs in addition to nodes. Capture those inputs while the canonical
compiler owns the admitted graph; reopening source paths after compilation can
read changed files. Reconstruction must preserve shared original contract
allocations and then invoke the existing independent modular validator. Recursive
serialization of Core alone would lose authority and safe traversal properties.

The initial private construction carrier explicitly refuses unsupported registry
and method facts instead of dropping them. Flat records reconstruct unchecked
Core with fresh identities, then invoke the existing modular validator. Decode,
reconstruction and independent validation share one cumulative bounded meter;
generated startup performs no source semantic checking. Its independent registry
proof may inspect embedded defining syntax for exact declaration coordinates,
within the same cumulative meter. The matching-runtime identity
includes compiler/runtime sources, package dependencies, target, enabled features
and Rust toolchain inputs. Generated hosts must preserve dependency versions and
features as well as the admitted program data.

Program preparation owns its generated host inputs and native configuration.
Linking consumes that completed phase, rather than encoding or checking the
source graph again. Generated source and tool logs remain reviewable; executable
publication follows successful linking. The private construction carrier has
bounded Pure, scalar/void Effect and dependency-free opaque or initialized-byte
source-resource profiles. The latter retains original defining forests once and
exact per-scope copying claims. Restore first admits the original templates, then independently
validates each specialized scope before binding. These profiles do not complete
foreign access, retained owners or the library deliveries.

Core builder payload admission is part of reconstruction work. Lending the
same cumulative meter to builder operations preserves both prior charges and
failed-operation charges; a fresh builder allowance would hide that work.
The image path also reserves its exact node and materialized-binder storage
fallibly before construction, rather than relying on vector/set growth.

Generated Cargo profiles must preserve compiler feature, optimization, panic and
assertion settings. The emitted host checks its baked runtime identity in a Rust
constant assertion as well as at startup. This prevents successful linking from
publishing a host whose dependency configuration rejects the admitted image.

Generated typed wrappers retain their own emitter-selected coordinates and
expected source facts behind an opaque provider. Startup independently checks
the full normalized library/source correspondence once, then consumes sealed
exact members into a binding table. Per-member registration uses original
operation/library/index and allocation identity; a native spelling or arbitrary
callback cannot replace that authority. Validation of final reconstructed Core
precedes registration, without replaying ABI preparation at each request.

Explicit native inputs are whole-program linker files in caller-supplied order,
including static archive dependency order. The bounded file-kind check admits
regular archives and ELF64 little-endian x86-64 shared libraries; it supplies no
contract facts or evidence that a binary obeys declared assumptions. Shared
linkage uses ordinary loader search without an automatic rpath. Loader paths
for executable evidence belong to the child process, not the compiler's global
environment. Configuring these inputs currently uses the Rust build API.

Rust-callback Core/image/phase witnesses do not establish real C linkage or
native observations. The public scalar case must retain exact I8 range refusal
with zero calls, unsigned 64-bit widening, void Unit, imported mixed Row/Type/Row
instances and repeated calls for both static and shared inputs. A combined entry
requires tuple `(127, 900, 18446744073709551615, (), 83)` and trace `iuvii`;
two fresh runs follow source removal before preparation/linkage. Shared-loader
refusal must precede every native call without the explicitly supplied child
loader path. This remains a bounded scalar profile, not ownership/access or
library-port completion.

Imported generic helpers contribute defining global parameter rows in addition
to nominal and effect parameters. The private image must retain those original
owner identities, ordered parameter IDs, complete kinds and origins; accepting
only nominal/effect variables loses a valid helper's scheme metadata. One flat
row carrier restores the canonical facts by consuming guarded records. Exact
table coverage and the independent Core checks still authenticate each row
against its actual lexical type abstraction. The private matching-runtime
format changes with this carrier; it promises no cross-version compatibility.

Provider interface parameters also belong to the canonical type-variable table.
Reconstruction installs their original parameter records before attaching the
interface owner definitions; exclusive wire coverage and independent owner-row
authentication remain separate checks. Omitting that installation refused a
valid source-resource image before any native call.

Generated binder IDs are local to each original lifecycle forest. Image encoding
must keep a separate binder cache for each forest and the executable program.
Sharing that cache reused an acquisition parameter's `Int` metadata for a finish
parameter with the same local ID and type `(State, D)`; independent restored Core
correctly rejected it. Wire records retain each forest's typed binders, and
restoration checks them in their original lexical scope.

Writing binary image/fact payloads as hexadecimal Rust arrays inflated each
encoded byte into five text bytes plus indentation, then charged reserve and
write for that expanded text. The imported-helper C program exhausted the
unchanged preparation allowance at emission. Native preparation now owns the
two exact encoded byte vectors; the consuming tool stage writes fixed payload
roles for compile-time inclusion. Counting and copying charge actual generated
Rust text. Independent expected-fact authentication remains mandatory, and the
executable must run after the generated source and payload files are removed.
Pure emission retains its existing path.

Private wire records must preserve Core's structural Type depth rather than
counting serialization wrappers. Row, instance and argument records retain
the surrounding depth; unary application function spines represent width.
Function, tuple, quantifier body and application argument edges add depth, as
does entry into an effectful function's children. One shared rule now governs
encoding and reconstruction. The public 42/43 nested-row regression exposed
the old artificial cutoff; the existing linked hosts also exercise 43 nested
phantom rows. Work charges, backward-reference checks and the original depth
allowance remain unchanged.

The complete source-owner witness exposed executable structural tables in the
independently emitted declaration expectations. Seal shared-table prefix lengths
after original registry and method-catalog encoding, before executable graph
encoding. Expectations retain every original native, owner, resource, interface
and global declaration fact while omitting subsequently appended Core records.
The private wire carries checked prefix lengths; independent byte correspondence
authenticates them. The construction image and final Core validation remain
complete, and work limits remain unchanged. The measured expectation payload
fell from 90,992 to 12,748 bytes. Cumulative decoding, correspondence,
reconstruction and library admission fell from 439,090 to 273,893 work units,
before member bindings and runtime program admission. These measurements precede
the added fixed decode-bound checks; the existing full image witness now uses one
default startup allowance across those phases.

The deeper row witness also exposed a separate startup cost: correspondence
serialized the construction image's facts into an owned buffer solely to
compare and discard it. A diagnostic measurement reached 384,923 units through
Core reconstruction, exceeding the unchanged 327,680 startup allowance. The
68,722-byte expected payload accounts for one avoidable copy and allocation.
Owned emission and streaming comparison now share the same canonical wire
traversal. Comparison pays each byte once and checks exact length; startup
still decodes the original independent expectations and completes all Core,
library, symbol, provider and required-binding checks. The diagnostic allowance
does not change delivery acceptance or production limits.

Scalar private images retain each original source member coordinate alongside
its packed role-table coordinate. This preserves defining order when a library
gains owner declarations; the wire format remains private to its matching
compiler. The scalar encoder and reconstructed native boundary refuse owner,
address and current-state facts rather than dropping them. Broader passive ABI
preparation therefore supplies no new executable ownership authority.

Pure scalar preflight images share the existing flat records and registry
reconstruction path with native images, followed by the independent Pure subset
check. The Pure boundary still rejects native symbols, effects, providers,
resource scopes and generic user functions. Only the exact common codec's
formal metadata and original scalar-check facts enter this profile; no Pure
program is promoted to Effect Core. Image tests retain one original codec
allocation for both checks and reject forged roles, binders, provenance,
coverage and mixed dialect claims.

The complete arena program exposed repeated structural type records in its
private construction image. Exact flat tags and ordered canonical child slots
now share records during encoding. Declaration identities, row tails, argument
tags and occurrence-owned quantifier records remain distinct; original origins,
certificates and evidence are not interned. Source traversal, depth checks,
fallible storage and work charges still apply before reuse. Reconstruction
expands each required owned type and independently checks final Core.

The diagnostic arena image fell from 146,384 to 67,267 bytes. Its cumulative
decode, expectation correspondence, reconstruction and final Core validation
fell from 375,187 to 285,700 units, within the unchanged 327,680 startup allowance.
The budget regression uses the complete public arena fixture and source removal,
then checks default, exact, one-short, prefixed and fresh-retry allowances. These
measurements describe reconstruction; actual library admission and native
execution require the separate generated-host evidence.

## Deviations

None authorized. Return concrete semantic gaps to CP-0022 instead of resolving
them locally. Keep excluded features outside this task.
