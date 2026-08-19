# Ash Specification

This directory is the canonical Ash specification. It is normative and describes exactly the language and runtime behavior implemented on `main`.

## Current Ash

No executable Ash language, compiler, or runtime exists on `main`. Consequently, Ash currently has no implemented syntax, grammar, static semantics, dynamic semantics, or runtime behavior to specify.

Repository and artifact conventions are project rules, not language semantics.

## Change discipline

Future behavior belongs in [design notes](../docs/design/README.md) and [change proposals](../docs/proposals/README.md), not here. A language change updates this specification in the same merge as the implementation and tests that make the new statements true. Partially implemented or intended behavior must not appear here.

The primary notation for formal semantics remains an open methodological question. [DN-0001](../docs/design/DN-0001-reboot-foundations.md) records small-step operational semantics as a candidate suited to the expected future language, but no approach has been accepted.
