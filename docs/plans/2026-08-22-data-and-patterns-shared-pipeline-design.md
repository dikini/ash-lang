# Data and Patterns Shared-Pipeline Remediation Design

## Status and authority

This document records the implementation design for remediating the TASK-0009
review findings. It does not define Ash semantics or architecture. CP-0003
defines the authorized semantic transition, and AD-0005 through AD-0008 define
the affected compiler boundaries.

## Goal

Move the implemented monomorphic data, tuple, pattern, match, and guarded-cycle
behavior into the retained Mini-Ash pipeline. Remove source-text routing and the
parallel `extended` pipeline after equivalent shared-stage behavior has direct
evidence.

## Current cause

The candidate implementation selects a private parser, checker, Core wrapper,
and evaluator by inspecting source text. That path reproduces semantic stages
but does not use the retained token-complete CST, stable resolved binder model,
typed Core arena, independent validator, or explicit evaluator machine. The
review failures therefore share one cause: the candidate owns a second pipeline
instead of contributing feature families to the existing closed assemblies.

## Retained evidence

The existing source corpus remains the behavioral oracle for nominal identity,
tuples, constructor values, typed patterns, coverage, guarded cycles, and
rendering. The registry model, type-equality rule, guardedness judgment, heap
alias model, iterative matching, and iterative rendering may transfer after
their inputs and outputs use retained stage representations. The private parser,
spelling-based environments, `ExtendedCoreProgram`, recursive evaluator, and
fixed-fuel usefulness control do not transfer as product boundaries.

## Architecture

All files follow one pipeline:

```text
source -> lexer -> concrete tree -> surface projection -> resolution
       -> typed elaboration -> independent Core validation
       -> explicit evaluator machine -> observation
```

Feature-owned parser functions add declarations, patterns, tuples, and matches
through the existing closed grammar tables. Projection produces ordinary
surface nodes only after verifying complete token coverage and absence of
recovery nodes.

Resolution allocates file-wide nominal and constructor identities before
resolving payload types. It allocates stable identities for every pattern
binder and emits resolved type occurrences. Resolved and Core programs carry
immutable type and constructor registries.

Typed elaboration checks patterns from expected types and constructs typed
structured Core. One memoized usefulness rule serves matches, equations, and
irrefutable bindings. Complexity or resource exhaustion is distinct from an
unusable pattern result.

The selected Core dialect gains feature-local tuple, constructor, pattern,
match, and recursive-data families. Core validation consumes only Core and its
registries. It independently checks identities, types, binder scope, coverage,
guarded roots, provenance, handles, and reachability.

The retained evaluator machine gains explicit tuple, constructor, match,
pattern, allocation, and recursive-initialization work. A per-evaluation heap
stores locations, constructor cells, tuples, closures, uninitialized slots, and
aliases. Matching and rendering use explicit work stacks.

## Migration sequence

The migration keeps the branch executable after each vertical slice:

1. Add shared-stage corpus cases that currently pass only through the private
   path, and prove that bypassing the retained parser is observable.
2. Add CST, projection, Surface, and resolved representations for declarations,
   tuples, constructors, and resolved types.
3. Add registry-bearing Core and finite tuple and constructor execution through
   the retained machine.
4. Add stable resolved patterns, structured match Core, memoized usefulness,
   equation lowering, and local pattern bindings.
5. Add heap-backed guarded recursive data initialization to the retained
   recursive-group machine path.
6. Complete independent validation, transforms, provenance, traces, deep-stack
   tests, diagnostics, and retained evidence.
7. Remove source-text routing and the private pipeline, run complete
   verification, and request another review.

## Failure handling

Source failures remain structured outcomes owned by syntax, resolution, or
typing. Each carries stable reasons and causal spans. Projection never passes
recovery nodes forward. Malformed Core and impossible runtime states remain
structured internal failures. Resource limits never masquerade as coverage or
matching results.

## Verification

Each slice begins with a focused failing test and ends with its stage suite.
The completion gate includes parser recovery and token completeness, resolved
identity and scope evidence, malformed-Core rejection, transform preservation,
small-step traces, deep explicit-stack cases, executable specification examples,
Markdown and link checks, and `cargo xtask verify`.

## Exclusions

The remediation does not change CP-0003 semantics and does not add
polymorphism, records, aliases, modules, pattern compilation, effects, general
laziness, garbage collection, or source-visible identity or mutation.
