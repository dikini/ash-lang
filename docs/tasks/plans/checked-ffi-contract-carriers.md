# Checked FFI Contract Carriers Implementation Plan

Owned by [TASK-0051](../TASK-0051-checked-ffi-contract-carriers.md).
Authority is accepted [CP-0024](../../proposals/CP-0024-checked-foreign-host-profile.md).
This plan implements its obligations; it cannot invent source or Core authority.

Goal: preserve checked foreign contracts through source, summaries, linking,
Core and image reconstruction without a legacy execution bypass.

Architecture: extend the existing original foreign contracts and their checked
phase projections. Explicit H selects one original Type formal; assumption and
owner facts retain their original module route and complete Type/Row context.
The runtime and Linux executor remain separate delivery boundaries.

Tech stack: Rust compiler/evaluator, existing contextual parser, canonical typed
Core, Cargo integration tests and existing private-image validation.

## Slice 1: Retain checked declaration intent and refuse incomplete admission

Files: `src/parser/foreign_grammar.rs`, `src/parser/foreign_project.rs`,
`src/surface/foreign.rs`, `src/foreign/source_contract.rs`,
`tests/foreign_source_syntax.rs`, `tests/foreign_source_contracts.rs`,
`spec/syntax.md` and `spec/static-semantics.md`.

1. Add a syntax test for public/private `foreign checked library` alongside legacy
   declarations. Run the new test and observe the missing syntax failure.
2. Add a preparation rejection test showing the checked marker cannot enter the
   legacy ABI route, even for otherwise valid scalar declarations. Observe its
   failure before the implementation permits parsing.
3. Add the explicit marker to the surface library, contextual recognition,
   concrete-shape validation and projection. Preserve exact source spans and
   reject malformed contextual prefixes.
4. Refuse the unsupported checked route at source-contract preparation with an
   existing appropriate contract error and original declaration span. No native
   startup, bridge or independent-result permission can arise.
5. Run the new tests, all three affected suites, formatting and targeted lint/doc
   checks. Document only this implemented subset and explicit refusal.
6. Obtain exact-head independent review, repair findings, retain with an unsigned
   commit, and update TASK-0051 acceptance only for this subset.

## Slice 2: Carry checked declarations and original assumptions

Extend `src/surface/foreign.rs`, foreign grammar/projection, resolution and
`src/foreign/source_contract.rs` / `checked_source.rs` together. Tests cover
original assumption names, duplicates, unknown references, exact selected H,
non-Type or missing H, and same-kind donor substitution. Use existing original
module/ordinal identities rather than matching names. Keep automatic inherent
assumption floors and authored references distinct. Preserve complete ordered
Type/Row arguments and charge construction/checking. Unsupported paths refuse.

## Slice 3: Introduce host scopes and checked effects

Add the accepted host expression through surface, resolved, elaborated and
Effect Core forms using existing scope/identity infrastructure. Test a closed
checked scalar call, residual legacy/ordinary rows, nested distinct H, host escape,
ordinary-handler attempts to eliminate H and wrong-host owner use. Interpret only
admitted exact owner-free native instances at the host boundary; owner operations
remain under the actual resource lifecycle. Core reconstructs these rules.

## Slice 4: Preserve body-free contracts and checked primitives

Extend module summaries, wrapper/capture facts, copy/specialization and linked
validation. Add the distinct checked builtin identities/codecs from CP-0024;
legacy byte/copy functions cannot authorize checked access. Test imported wrappers
without source-body inference, opaque/re-exported origins, complete Type/Row
instantiation, hidden captured S/C/H, branch/recursive joins and forged assumption
or dependency removal. Nearest ordinary-handler precedence remains unchanged.

## Slice 5: Independently validate retained Core and private images

Extend existing Core and private-image reconstruction with canonical checked
contracts, exact host/owner/window lineage and complete projection comparison.
Mutate origins, host effects, assumptions, independence, full argument vectors
and native-window order after construction. Each mutation must reject separately;
constructor APIs and serialized checked flags grant no permission. Run exact,
one-short and fresh sufficient work/capacity cases without effect replay.

## Handoff and final checks

Every slice reports Delivered, Remaining, Awaiting and Owner against TASK-0051.
No partial slice closes F3 or removes CP-0024. Full F3 acceptance requires the
complete source/summary/Core/image behavior and independent review. F-core waits
for connected F4/F6 and accepted F2 prerequisites; one build operator owns that
frozen full gate. Current Main remains the original specification until separate
verified integration.
