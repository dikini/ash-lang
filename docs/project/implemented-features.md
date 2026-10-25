# Implemented features

This inventory describes the product boundaries in the connected smaller-FFI
checkpoint. The [specification](../../spec/README.md) governs language semantics;
accepted [decisions](../decisions/README.md) govern non-language architecture.
Test links identify regression obligations, not a new execution receipt.

The [active transition](../tasks/TASK-0050-checked-ffi-regions-control-program.md)
still owns implementation, final review, normal verification and Main integration.
This inventory does not mark those gates complete. Historical experiments and
receipts retain only their original input, scope and checkpoint claims.

## Specified language features

Each row describes a capability present in the implementation and specified in
`spec/`. Design references explain its development; they do not replace the
specification. The evidence column identifies executable regression suites or
retained evidence, rather than reporting a new test run.

| Feature and implemented boundary | Specification and design references | Implementation evidence |
| --- | --- | --- |
| Primitive values: mathematical `Int`, `Bool` and `Unit`; integer addition, multiplication and equality, with strict operand order. Ash integer arithmetic does not overflow. | [Primitive typing](../../spec/static-semantics.md#primitive-operations), [execution](../../spec/dynamic-semantics.md#primitive-operations); [DN-0006](../design/DN-0006-initial-type-system.md). | [Integer tests](../../tests/integer.rs), [primitive pipeline](../../tests/primitive_vertical.rs). |
| Functions: equational and operational definitions, anonymous functions, curried application and lexical closures. | [Function presentations](../../spec/syntax.md#global-function-presentations), [application](../../spec/dynamic-semantics.md#application); [DN-0005](../design/DN-0005-surface-function-definitions.md). | [Functions](../../tests/functions.rs), [semantic cases](../../tests/semantics.rs). |
| Sequential bindings and lexical shadowing, including typed local bindings and blocks. | [Blocks](../../spec/static-semantics.md#blocks), [local scope](../../spec/name-resolution.md#local-scope); [DN-0006](../design/DN-0006-initial-type-system.md). | [Bindings](../../tests/bindings.rs), [resolution](../../tests/resolution.rs). |
| Global and explicit local recursion, including checked recursive groups. Guarded cyclic data has finite observation. | [Recursive groups](../../spec/static-semantics.md#recursive-block-groups), [execution](../../spec/dynamic-semantics.md#recursive-bindings), [observation](../../spec/dynamic-semantics.md#observation); [DN-0008](../design/DN-0008-typed-core-and-elaboration.md). | [Recursion](../../tests/recursion.rs), [specification examples](../../tests/spec_examples.rs). |
| Rank-1 polymorphism, inference, explicit declaration parameters and ordinary monomorphic value positions. No first-class source schemes or polymorphic recursion. | [Inference and restrictions](../../spec/static-semantics.md#inference-and-rank-1-restrictions), [explicit Core operations](../../spec/elaboration.md#explicit-rank-1-operations); [rank-1 evidence](../design/mini-ash/rank-1-polymorphism/evidence.md). | [Polymorphism](../../tests/polymorphism.rs). |
| Structural tuples, nominal algebraic data, constructor values, typed patterns and exhaustive matches/equations. | [Data typing](../../spec/static-semantics.md#tuples-and-constructors), [coverage](../../spec/static-semantics.md#patterns-matches-and-coverage); [DN-0007](../design/DN-0007-data-and-pattern-typing.md). | [Data and ADTs](../../tests/data_and_adts.rs), [corpus](../../tests/corpus.rs). |
| Module `newtype`: distinct nominal identity over one representation, explicit construction/matching, and allocation-free erasure after validation. | [Type/constructor scope](../../spec/name-resolution.md#type-and-constructor-scope), [type erasure](../../spec/dynamic-semantics.md#type-instantiation-and-erasure); [module newtype evidence](../design/effect-ash/module-newtype-evidence.md). | [Module newtypes](../../tests/module_newtypes.rs), [resource interactions](../../tests/newtype_resources.rs). |
| Local `newtype`: lexical compile-time identity, escape rejection, and closures that retain values without exposing the local identity. No runtime-fresh nominal identity. | [Local nominal scope](../../spec/static-semantics.md#local-nominal-scope); [local newtype evidence](../design/effect-ash/local-newtype-evidence.md). | [Local newtypes](../../tests/local_newtypes.rs). |
| Passive modules: acyclic dependencies, rooted and relative imports, one canonical load per source, dependency-ordered checking and a closed entry `main`. No module initialization or runtime module objects. | [Module identity](../../spec/name-resolution.md#module-paths-and-identity), [globals/modules](../../spec/static-semantics.md#globals-and-modules); [DN-0022](../design/DN-0022-passive-static-modules.md). | [Loading](../../tests/module_loading.rs), [entry checking](../../tests/module_entry.rs), [module linking](../../tests/module_elaboration.rs). |
| Visibility and facades: public/private declarations, qualified and targeted imports, renaming, targeted re-exports, opaque types and hidden carriers. Defining identities survive import routes. | [Imports](../../spec/name-resolution.md#imports-and-namespaces), [visibility](../../spec/name-resolution.md#public-private-and-opaque-declarations); [DN-0022](../design/DN-0022-passive-static-modules.md). | [Module visibility](../../tests/module_visibility.rs), [library imports](../../tests/library_imports.rs). |
| Fixed kinds, including higher-kinded parameters and kind-correct bare or partial type applications. Ash does not infer function kinds from use. | [Kinds](../../spec/static-semantics.md#kinds-monotypes-and-schemes); [kind evidence](../design/lib-ash/kinds-evidence.md). | [Kinds](../../tests/kinds.rs), [kinded modules](../../tests/kind_modules.rs), [resource bounds](../../tests/kind_resources.rs). |
| Method-only interfaces, constrained rank-1 globals, anonymous implementations, prerequisites and explicit implementation import/re-export. Selected evidence lowers to ordinary functions. | [Interfaces](../../spec/static-semantics.md#interfaces-and-constrained-schemes), [implementations](../../spec/static-semantics.md#implementations), [evidence](../../spec/elaboration.md#interface-evidence-lowering); [DN-0023](../design/DN-0023-interfaces-and-implementations.md). | [Interfaces](../../tests/interfaces.rs), [selection](../../tests/interface_selection.rs), [interface modules](../../tests/interface_modules.rs). |
| Explicit method-local type parameters: one authenticated method scheme can be instantiated at different types. | [Interfaces and constrained schemes](../../spec/static-semantics.md#interfaces-and-constrained-schemes); [method-parameter evidence](../design/lib-ash/method-parameters-evidence.md). | [Interface corpus](../../tests/interface_corpus.rs), [method resource bounds](../../tests/method_parameter_resources.rs). |
| Multi-parameter relational interfaces with one total forward determination edge, coherence checks and dependent-argument improvement. No associated-type projections or arbitrary dependency graphs. | [Constraint satisfaction](../../spec/static-semantics.md#constraint-satisfaction-and-checked-evidence); [relational-interface evidence](../design/lib-ash/relational-interfaces-evidence.md). | [Implementations](../../tests/implementations.rs), [selection](../../tests/interface_selection.rs), [summary authentication](../../tests/interface_generic_summary.rs). |
| Scoped exact interface evidence through lexical `with`, tied to an active local nominal. Supplied methods may capture earlier values; this is not local implementation search or proof evidence. | [Scoped exact evidence](../../spec/static-semantics.md#scoped-exact-evidence); [scoped evidence report](../design/effect-ash/scoped-evidence-evidence.md). | [Scoped evidence](../../tests/scoped_evidence.rs), [interactions](../../tests/scoped_evidence_interactions.rs). |
| Declared effects and computation rows, generic row tails, exact effect identities and checked row exclusions. A linked entry must have an empty effect row. | [Computation rows](../../spec/static-semantics.md#computation-types-and-effect-rows), [effects](../../spec/static-semantics.md#effects); [DN-0009](../design/DN-0009-effects-handlers-and-continuations.md). | [Effect rows](../../tests/effect_rows.rs), [typing](../../tests/effect_typing.rs), [modules](../../tests/effect_modules.rs). |
| Exhaustive lexical handlers, `perform`, single-use non-escaping `resume`, and checked owned `discard`. Discard closes recursively owned captures in structural order and skips abandoned results. | [Effects](../../spec/static-semantics.md#effects), [handler execution](../../spec/dynamic-semantics.md#effect-handlers-and-completion); [capture/discard evidence](../design/effect-ash/capture-discard-evidence.md), [DN-0033](../design/DN-0033-direct-effects-and-continuation-capabilities.md). | [Effect execution](../../tests/effect_runtime.rs), [independent Core](../../tests/effect_core.rs). |
| Scoped mutable integer cells through sealed `@builtin.cell`: fresh runtime activations, reusable non-owning handles, dependency escape checks and one release on completion or owned abandonment. | [Cell typing](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies), [execution](../../spec/dynamic-semantics.md#scoped-cell-execution); [resource evidence](../design/effect-ash/resource-scope-evidence.md). | [Resource typing](../../tests/resource_scope_typing.rs), [runtime](../../tests/resource_scope_runtime.rs), [Core](../../tests/resource_scope_core.rs). |
| Synchronous typed hooks: lexical roots and registrations, outer-before-inner transformers, checked callback effects/dependencies and owner preservation across resume/discard. | [Hook typing](../../spec/static-semantics.md#synchronous-typed-hooks), [execution](../../spec/dynamic-semantics.md#synchronous-hook-execution); [hook evidence](../design/effect-ash/synchronous-hooks-evidence.md), [DN-0012](../design/DN-0012-coeffects-and-hooks.md). | [Hook runtime](../../tests/hooks_runtime.rs), [typing](../../tests/hooks_typing.rs), [Core](../../tests/hooks_core.rs). |
| Scoped cleanup actions: retain one `Unit -> Unit` action, invoke it on normal completion or admitted abandonment, preserve the body result, and reject skipped outside/running completion. Typed reporting can keep ordered cleanup failures separate from body outcomes. | [Cleanup typing](../../spec/static-semantics.md#scoped-cleanup-actions), [execution/reporting](../../spec/dynamic-semantics.md#scoped-cleanup-actions); [cleanup evidence](../design/effect-ash/reliable-cleanup-evidence.md). | [Abandonment](../../tests/cleanup_abandonment.rs), [reporting](../../tests/cleanup_reporting.rs), [partial acquisition](../../tests/cleanup_partial_acquisition.rs). |
| Managed immutable `Bytes`, UTF-8 `String`, string literals and ordinary construction, access, equality and UTF-8 conversion functions. No native binding is needed for these operations. | [Primitive expressions](../../spec/static-semantics.md#primitive-expressions), [byte/string modules](../../spec/name-resolution.md#independent-byte-and-string-modules). | [Byte/string tests](../../tests/bytes_strings.rs), [string literals](../../tests/string_literals.rs), [packed Core](../../tests/packed_core.rs). |
| Generic cells through `@builtin.generic_cell`: fixed ordinary payload type, current contents and read snapshots, complete operation identity, dependency admission and scoped completion. | [Generic-cell foundation](../../spec/static-semantics.md#generic-cell-foundation), [cell execution](../../spec/dynamic-semantics.md#scoped-cell-execution). | [Resource typing](../../tests/resource_scope_typing.rs), [runtime](../../tests/resource_scope_runtime.rs), [Core](../../tests/resource_scope_core.rs). |
| Passive foreign symbols and canonical opaque Address with pure null/equality, readonly synchronous Bytes pointers and actual C void. Each symbol is an ordinary effect and may be handled by ordinary source handlers. Module-authored checks and cleanup supply policy. Raw Address adds no ownership, memory-access or resource escape authority. | [Foreign declarations](../../spec/static-semantics.md#source-foreign-declarations), [execution](../../spec/dynamic-semantics.md#native-symbol-execution). | [Slim FFI](../../tests/ffi_slim.rs), [source admission](../../tests/foreign_source_admission.rs), [native host cases](../../tests/program_build_native.rs). |

## Compiler and execution tools

These are implemented engineering capabilities. Their references are accepted
decisions, tool documentation and source, rather than additional source-language
semantics.

| Feature and implemented boundary | Governing reference | Implementation evidence |
| --- | --- | --- |
| One modular pipeline, with separate parsing, resolution, checking, linking, Core validation and evaluation boundaries. Failures retain their owning stage. | [AD-0005](../decisions/AD-0005-parser-architecture.md), [AD-0006](../decisions/AD-0006-front-end-semantic-boundaries.md), [validation boundary](../../spec/elaboration.md#validation-boundary). | [Driver](../../src/driver.rs), [architecture checks](../../tests/architecture.rs). |
| Typed Pure and Effect Core dialects, explicit evidence/type operations, independently checked transformed Core and ordered resolved-global binder authority. | [AD-0007](../decisions/AD-0007-typed-core-dialects.md), [AD-0009](../decisions/AD-0009-ordered-resolved-global-binder-authority.md); [DN-0008](../design/DN-0008-typed-core-and-elaboration.md). | [Core validation](../../tests/core_validation.rs), [interface validation](../../tests/interface_validation.rs), [validator](../../src/core/validate.rs), [transforms](../../src/core/transform.rs). |
| Explicit evaluator machine with ordered frames and owned completion state, bounded work, fallible allocation and iterative disposal. | [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md), [dynamic semantics](../../spec/dynamic-semantics.md). | [Machine](../../src/eval/machine.rs), [runtime diagnostics](../../tests/runtime_diagnostics.rs), [effect milestone review](../design/effect-ash/milestone-closure-evidence.md). |
| CLI execution of one entry module with named roots and value/type output. No stdin program or implicit native host build. | [`ash` tool guide](../tools/ash.md). | [CLI](../../tests/cli.rs), [module CLI](../../tests/module_cli.rs), [public driver](../../src/driver.rs). |
| Structured diagnostics, causal source labels, human/short/JSON presentation and English/Bulgarian localization. | [AD-0010](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md), [diagnostic options](../tools/ash.md#diagnostic-formats-and-locales). | [Presentation](../../tests/diagnostic_presentation.rs), [JSON](../../tests/diagnostic_json.rs), [catalogues](../../tests/diagnostic_catalogues.rs). |
| Generated whole-program Rust hosts with typed pointer/void bridges, explicit static/shared inputs and independently reconstructed private Core. No stable Core wire format or implicit native compilation during ordinary run. | [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md), [build guide](../tools/ash.md#building-an-executable). | [Native hosts](../../tests/program_build_native.rs), [program builds](../../tests/program_build.rs), [normal preparation](../../tests/foreign_native_program_preparation.rs). |
| Cumulative input-derived compiler, rewrite, preparation and startup work allowances, paid sizing, overflow/exhaustion checks and separate depth limits. An allowance is no universal complexity or native correctness guarantee. | [AD-0013 gas policy](../decisions/AD-0013-generated-native-bridges-and-program-builds.md#native-preparation-and-startup-gas), [failure/work rules](../../spec/static-semantics.md#failure-ownership-and-constraint-resources). | [Work reporting](../../tests/compiler_work_reporting.rs), [preparation regressions](../../tests/foreign_native_program_preparation.rs). |
| Root Cargo workspace containing the compiler and verification tooling. Native calls reside in explicitly generated linked hosts. | [Dependency policy](dependencies.md), [generated builds](../decisions/AD-0013-generated-native-bridges-and-program-builds.md). | [Workspace](../../Cargo.toml), [bridge generation](../../src/build/bridge.rs), [verification tool](../../xtask/src/main.rs). |

## Foreign boundary and historical evidence

The supported mapping is whole Unit to no C arguments; whole Address or Bytes
to one pointer; flat Address/Bytes tuples to pointers in order; Address results
to pointers; Unit results to actual C void. Bytes is argument-only. Its backing
is held through the synchronous call, without hidden length, NUL or encoding.
Native code must not mutate or free managed backing. A retained or returned
pointer requires the module to keep the original Bytes alive for later use;
Address does not infer that relation.

The direct SQLite version/source-id getter canary checks non-null and repeat
pointer equality. It does not read text or establish full SQLite coverage.
Numeric slots, out-pointers, callbacks, variadics, structs by value, nested tuples
and Address-to-Bytes/String or arbitrary memory-read/write operations remain
unsupported. Existing scoped cleanup and handlers express binding policy;
foreign behavior remains assumed rather than ensured.

[DN-0036](../design/DN-0036-foreign-library-and-memory-provider-experiments.md)
and its pinned evidence preserve earlier provider, SQLite and Arena experiments.
Those experiments do not establish current product APIs. Their native owner,
status, window, host, quarantine, codec and manifest/adapter execution routes are
retired. Ordinary cells, resource-family kind/import metadata, cleanup, capture,
rows and generic compiler validation remain separate product mechanisms.
Nonbuiltin provider execution is unsupported. No current full SQLite, arena
storage or compiler-managed foreign resource lifecycle is claimed.

## Boundaries and verification

The source language remains rank-1. Proposition/proof terms, general associated
projections, existential packaging, first-class polymorphic values and escaping
or multi-shot resumptions have no delivered source support. General borrowing,
regions, retained control, workers and concurrency remain separately scoped
future work. The retained Float experiment does not introduce Float semantics.

Examples and regression references must match the connected implementation.
The [normal verification guide](verification.md), final-head independent review
and transition acceptance remain separate requirements. Neither this inventory,
a larger work allowance nor historical native receipts completes them. Finite
native observations establish only the exercised calls and ordinary invariants;
they do not certify a native binary, foreign lifetimes or complete compiler
correctness.
