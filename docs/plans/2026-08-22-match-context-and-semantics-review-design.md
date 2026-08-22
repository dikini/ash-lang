# Match Context and Semantics Review Design

## Status and authority

This temporary design belongs to active TASK-0009. It records how to correct
review findings and does not define Ash semantics. The current specification,
accepted AD-0004, accepted CP-0003, and AD-0006 govern the correction.

## Problem

Checked matches currently re-enter elaboration through synthesis. Their first
arm therefore loses an available result type, so an anonymous function in that
arm is rejected even when the surrounding function interface supplies its
type. The normative static rules also describe binders where the implemented
language accepts typed irrefutable patterns.

The evaluator enters each guarded recursive data initializer, suspends a frame,
and stores the returned constructor location as an alias before continuing to
the next initializer. The dynamic specification compresses those transitions
into a big-step premise. Its representative scalar-binding derivations also
describe heap locations where the environment actually stores values.

## Design

The elaborator keeps its existing synthesizing match path. A checked match
passes the expected result type and provenance into match elaboration, which
checks every arm body against that type. The match still synthesizes its
scrutinee, checks coverage once, and emits the same structured Core form.

The static specification separates match synthesis from match checking. The
synthesis rule lets the first arm determine the result type and checks later
arms against it. The checking rule gives the surrounding expected type to every
arm. Function and local-binding rules check a pattern against its domain or
initializer type, extend the environment with all returned bindings, and
require singleton exhaustiveness.

The dynamic specification replaces the recursive initializer's big-step
premise with two one-step rules. One rule enters the next source-ordered
initializer and saves its slot, remaining members, body, and recursive
environment in a continuation frame. The second consumes the returned location,
stores the alias, and resumes initialization. Function-only groups proceed
directly to the body after allocation because their templates already inhabit
the recursive environment.

Representative derivations bind integer and closure values directly. Heap
locations remain limited to tuples, constructors, recursive data slots, and
aliases.

## Evidence

A new executable regression places anonymous functions in both arms of a match
whose surrounding operational function declares an `Int -> Int` result. It
must execute through the retained parse, resolve, elaborate, validate, and
evaluate pipeline. Existing synthesizing matches, mismatch diagnostics,
coverage checks, recursive cycles, formal-notation review, and executable
specification tests remain green.

## Exclusions

This correction adds no function inference, polymorphism, pattern compilation,
new Core form, evaluator transition, or allocation behavior. It does not change
match coverage, evaluation order, or nominal identity.
