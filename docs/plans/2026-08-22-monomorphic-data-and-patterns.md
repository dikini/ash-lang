# Monomorphic Data and Patterns Implementation Plan

> Use the executing-plans, test-driven-development, Rust, context
> reconstruction, and verification workflows while carrying out this plan.

## Goal

Implement CP-0003 as one retained Mini-Ash increment and prepare the isolated
branch for review without integrating it.

## Architecture

Resolution performs two-pass allocation of file-wide nominal and constructor
identities and converts every source type occurrence to a resolved type. Typed
elaboration uses immutable registries, one semantic equality rule, one expected-
type pattern checker, and one memoized usefulness analysis. Tuples,
constructors, and structured matches remain explicit in validated Core. The
explicit evaluator uses a per-evaluation heap for constructor cells and guarded
recursive slots, with iterative matching and rendering.

## Execution

1. Add the positive, rejection, diagnostic, trace, provenance, malformed-Core,
   transform, and deep corpus. Witness failures before production changes.
2. Add surface declarations and types; allocate nominal and constructor
   identities in two passes; resolve all type and constructor occurrences; add
   immutable resolved and Core registries; centralize type equality and validate
   registry closure.
3. Add tuple and constructor tokens, grammar, recovery, projection, typing,
   Core nodes, validation, left-to-right evaluation, heap cells, observations,
   and finite structural rendering.
4. Add patterns and match syntax; resolve pattern binders; check patterns from
   expected types; implement recursive usefulness; retain structured match Core;
   evaluate with an explicit matching stack; lower equations, local patterns,
   tuple-domain headers, and anonymous tuple parameters through the same forms.
5. Extend recursive groups to functions and guarded data. Preallocate slots,
   install templates and locations simultaneously, initialize data in order,
   follow aliases for matching and rendering, and reject unguarded recursive
   uses statically.
6. Extend identity traversal and literal folding, independently validate and
   evaluate results, update all normative and tool documentation, retain
   integration evidence, link transferable findings, and complete the full
   requirement audit.
7. Stop for review. After explicit integration confirmation, remove CP-0003,
   TASK-0009, and this plan; rerun verification; create the required signed
   merge commit.

Each behavioral substep uses one minimal failing test, confirms the expected
failure, implements the smallest passing behavior, reruns the focused suite,
and refactors only while green. Representation-only migrations use the existing
suite as characterization evidence.

## Verification checkpoints

- Lexer/parser/projector: `cargo test --locked --test lexer --test parser`
- Resolution: `cargo test --locked --test resolution`
- Typing/runtime feature corpus: `cargo test --locked --test data_and_adts`
- Core and transforms: `cargo test --locked --test core_validation --test semantics`
- Diagnostics and provenance: `cargo test --locked --test diagnostics --test provenance --test cli`
- Documentation: `cargo test --locked --test spec_examples`
- Complete: `cargo xtask verify`

Manual checks cover Markdown style, relative links and anchors, artifact
authority, `ebnf`/`sequent` syntax and matching prose, exact changed-site
searches, reverted API-mutation probes, and every CP-0003 evidence requirement.
