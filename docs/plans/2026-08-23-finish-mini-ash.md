# Finish Mini-Ash Implementation Plan

> Use the executing-plans, test-driven-development, Rust, context
> reconstruction, and verification workflows while carrying out this plan.

## Goal

Implement CP-0004, close the Mini-Ash milestone, and prepare the isolated branch
for review without integrating it.

## Architecture

Resolution allocates declaration-scoped type parameters and retains kinded type
application with provenance. Elaboration uses private inference variables,
separate kinding, equality, instantiation, generalization, and unification
rules, then emits zonked Core with explicit type abstractions and applications.
Core independently validates those facts. The evaluator erases type operations;
the existing value and heap model remains unchanged.

## Execution

1. Add transition artifacts and the positive, rejection, diagnostic,
   malformed-Core, transform, resource, and executable corpus. Witness failures
   before their production slices.
2. Add parameterized declaration and type-application syntax, projection,
   type-parameter identities, scopes, kinds, resolved types, constructor
   schemes, and source diagnostics.
3. Add inference, rigid checking, implicit global quantification,
   constructor/global instantiation, function-only local generalization,
   occurs checks, ambiguity handling, and monomorphic recursive checking.
4. Add explicit Core type operations, independent validation, transform
   preservation, and evaluator erasure.
5. Add cumulative type-work accounting and deep, wide, malformed, and
   small-stack evidence. Retain the rank-1 integration report.
6. Update the complete normative specification and executable `ash`
   documentation.
7. Run the Mini-Ash inventory and simplification audit. Apply only private,
   behavior-preserving cleanup justified by full verification; retain the
   closure report and update the trajectory.
8. Stop for review. After explicit integration confirmation, retire CP-0004,
   TASK-0010, and this plan, rerun verification, and integrate as directed.

Each behavioral substep uses one minimal failing test, confirms the expected
failure, implements the smallest passing behavior, and refactors only while
green. Representation migrations use the existing suite as characterization
evidence and add malformed-boundary tests before new public builders.

## Verification checkpoints

- Syntax: `cargo test --locked --test lexer --test parser --test polymorphism`
- Resolution and typing: `cargo test --locked --test resolution --test polymorphism --test diagnostics`
- Core and transforms: `cargo test --locked --test core_validation --test semantics --test polymorphism`
- Runtime and compatibility: `cargo test --locked --test data_and_adts --test recursion --test polymorphism`
- Documentation: `cargo test --locked --test spec_examples`
- Complete: `cargo xtask verify`

Manual checks cover Markdown style, relative links and anchors, artifact
authority, formal notation and matching prose, exact changed-site searches,
reverted API-mutation probes, and every CP-0004 evidence requirement.
