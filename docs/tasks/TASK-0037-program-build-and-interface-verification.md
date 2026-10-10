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
generated startup performs no source checking. The matching-runtime identity
includes compiler/runtime sources, package dependencies, target, enabled features
and Rust toolchain inputs. Generated hosts must preserve dependency versions and
features as well as the admitted program data.

Program preparation owns its generated host inputs and native configuration.
Linking consumes that completed phase, rather than encoding or checking the
source graph again. Generated source and tool logs remain reviewable; executable
publication follows successful linking. The private construction carrier has
bounded Pure and owner-free scalar/void Effect profiles. These profiles do not
complete foreign ownership/access execution or the library deliveries.

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

## Deviations

None authorized. Return concrete semantic gaps to CP-0022 instead of resolving
them locally. Keep excluded features outside this task.
