# Syntax Resource Memory Remediation Design

## Status and authority

This temporary design belongs to active TASK-0009. It records a compiler
resource correction and does not define Ash semantics. The current
specification, accepted CP-0003, and accepted AD-0005 through AD-0008 govern
the correction.

## Problem

The retained 100,000-field tuple coverage case completes with a structured
resource failure but peaks at 213,736 KiB RSS. A 1,000,001-field probe peaks at
1,945,036 KiB before usefulness rejects it. The structured coverage budget
therefore starts too late to bound the complete source pipeline.

A counting-allocation probe over 25,000, 50,000, and 100,000 fields found
linear allocation at every front-end stage. At 100,000 fields, the parser owns
about 989 requested bytes per field, the surface tree adds 208, the resolved
tree adds 323, partial elaboration adds 231, and elaboration transient work
adds 432 at the peak. Each field produces about four tokens, ten retained
events, three concrete nodes, and seven concrete elements. Retaining obsolete
front-end stages raises the measured peak, but releasing them alone leaves a
1,000,001-field peak of 1,367,760 KiB.

## Considered approaches

Explicitly releasing the concrete and surface trees reduces peak RSS by about
30 percent without changing any stage result. It does not bound lexing or
parsing and is insufficient alone.

Compacting tokens, events, concrete nodes, or integer payloads could reduce the
per-field slope. That work changes the accepted parser representation and
requires separate comparison evidence. It is not necessary to establish a
finite resource boundary for this increment.

The selected approach combines stage release with one cumulative syntax-work
budget shared by lexing and parser-event construction. It addresses both
identified causes while retaining the parser architecture and every accepted
language form.

## Design

One internal syntax budget starts with 1,500,000 work units. Retaining a token,
retaining a lexical diagnostic, or retaining a parser event consumes one unit
before allocation. The limit is an implementation resource boundary, not a
source tuple-width or language restriction.

The lexer carries the remaining budget and any exhaustion fact into parsing.
Once exhausted, it stops scanning and returns the bounded prefix with a
structured syntax-work resource failure. The parser does not attempt grammar
construction for a lexer-exhausted input.

Parser event insertion uses the same budget. If it exhausts, parsing continues
only far enough to leave its control flow and owned values safe; it does not
retain more events or construct a partial concrete tree. The returned
resource-bearing concrete result retains the already bounded token prefix and
diagnostics, has no projected root, and cannot cross projection. A resource
failure remains an internal compiler outcome even when the bounded prefix also
contains a source diagnostic.

The existing 100,000-field source uses about 1,400,040 token and event units,
so it continues to reach usefulness and prove tuple materialization charging.
A wider source crosses the syntax budget first. Direct unchecked-Core tests
continue to exercise coverage resource mapping independently of source syntax.

After successful projection, the driver releases the concrete tree before
resolution. After successful resolution, it releases the surface tree before
elaboration. This changes ownership lifetime only; the resolved and Core forms
already own their required types, identities, spellings, and provenance.

## Error behavior

Syntax work exhaustion uses a stable `ResourceFailure::SyntaxWork` value and
renders as `internal.resource.syntax-work` with the active limit. It is not a
source rejection. Resource status takes precedence in the stage reason code
because scanning or parsing did not complete, while retained prefix
diagnostics remain available as subordinate evidence.

## Evidence

Tests must prove the budget accepts its exact boundary and rejects the next
charge transactionally; lexing and parser events share one cumulative count;
resource trees do not project; the public pipeline reports the structured
internal reason; the 100,000-field usefulness case still reaches its existing
typing failure; and direct malformed-Core coverage exhaustion still maps to
Core validation resource failure.

Measurement repeats the 100,000-field and 1,000,001-field probes. The larger
probe must stop during syntax construction with bounded peak RSS. Full project
verification, Markdown checks, relative-link checks, and authority review
remain required.

## Exclusions

This correction adds no source-level width limit, new syntax, semantic
diagnostic, compact CST, token interning, arena, allocator dependency, integer
representation change, pattern compilation, or general memory quota. It does
not change token, event, surface, resolved, or Core representation.
