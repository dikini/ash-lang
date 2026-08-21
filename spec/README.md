# Ash Specification

This directory is the canonical Ash specification. It is normative and
describes exactly the implemented language and runtime behavior.

## Current Ash

Ash currently has one retained language increment: Mini-Ash, a single-file,
monomorphic, pure-functional language. Every accepted file contains zero or
more sequential function definitions followed by one result expression.

The specification is split by concern:

- [Lexical structure](lexical-structure.md) defines admitted source text,
  tokens, whitespace, and logical line boundaries.
- [Syntax](syntax.md) defines the surface grammar, precedence, and
  associativity.
- [Name resolution](name-resolution.md) defines lexical scope and binder
  identity.
- [Static semantics](static-semantics.md) defines types and bidirectional
  typing.
- [Elaboration](elaboration.md) defines how surface presentations converge on
  typed semantic terms.
- [Dynamic semantics](dynamic-semantics.md) defines values and deterministic
  small-step evaluation.

The [`ash` tool documentation](../docs/tools/ash.md) describes invocation,
output, diagnostics, and exit status. Those are tool behaviors, not additional
language semantics.

## Change discipline

Future behavior belongs in [design notes](../docs/design/README.md) and
[change proposals](../docs/proposals/README.md), not here. A language change
updates this specification in the same merge as the implementation and tests
that make the new statements true. Partially implemented or intended behavior
must not appear here.
