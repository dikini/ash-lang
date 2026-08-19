# Specification discipline

> The canonical specification describes exactly the Ash implemented on `main`.

The specification is normative. It contains only behavior that an Ash program can exercise through the implementation on `main`. It excludes intended features, partially implemented semantics, design options, and historical behavior.

A language change begins outside the specification. Exploration belongs in a design note. A concrete semantic transition belongs in a change proposal. The implementation, positive and negative tests, and specification update merge together only when the complete accepted behavior works through its current semantic and execution route.

Infrastructure may merge before surface syntax can reach it. Such infrastructure does not create specification truth. If implementation reveals that proposed semantics are incomplete or wrong, revise the proposal and its required evidence rather than encoding a local choice in code or tests.

The formal-semantic method is unresolved. The foundation note identifies small-step operational semantics as a strong candidate because expected future work includes effects, explicit continuations, concurrency, cancellation, and runtime state. This is design evidence, not an accepted method. Settle the method explicitly before substantial semantic specification work and avoid two competing normative semantic systems.
