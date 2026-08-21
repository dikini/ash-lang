# Specification discipline

> The canonical specification describes exactly the Ash implemented on `main`.

The specification is normative. It contains only behavior that an Ash program can exercise through the implementation on `main`. It excludes intended features, partially implemented semantics, design options, and historical behavior.

A language change begins outside the specification. Exploration belongs in a design note. A concrete semantic transition belongs in a change proposal. The implementation, positive and negative tests, and specification update merge together only when the complete accepted behavior works through its current semantic and execution route.

Infrastructure may merge before surface syntax can reach it. Such infrastructure does not create specification truth. If implementation reveals that proposed semantics are incomplete or wrong, revise the proposal and its required evidence rather than encoding a local choice in code or tests.

[AD-0004](../decisions/AD-0004-small-step-semantic-method.md) establishes one
small-step operational account as the primary normative method for dynamic
semantics. Big-step explanations, representative traces, executable evaluators,
and mechanized models remain derived or non-normative views checked against
that account. The decision selects a documentation and semantic-accounting
method; it does not add Ash behavior to the specification.
