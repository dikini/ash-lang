# TASK-0046 execution plan

Owned by [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md).
Accepted CP-0023 governs semantics; this plan adds no source rules.

1. Extend the existing finite capture/value/control graphs with ordered generic
   slot roots. Preserve read snapshots, exact target aliases and activation
   contexts independently of native retained-data unions. Start with paired
   P04/P13/N12 and same-site P05 source and analysis probes.
2. At actual builtin initialization/replacement, prove every retained owner is
   strictly enclosing. Follow selected handlers and resumed mutations; preserve
   outward crossing, native revocation and structural completion checks.
3. Carry the graph through public/imported summaries and instantiation. Rebuild
   the proof independently from linked Core after copies, transforms and images.
   Replace pending dependency denial only where proof succeeds; retain a
   separate execution gate until TASK-0047 supplies its runtime.
4. Cover all fifteen assigned case families and variants, finite joins and
   recursive analysis, exact/one-short/retry budgets and iterative refusal.
   Update matching static semantics/elaboration and durable task findings.
5. Freeze unsigned code inputs, run focused resource suites, analysis/summary/
   Core/transform/image/budget probes and proportionate affected callers. Obtain
   independent review and repair before recording dependency readiness.

Use Rust 1.97.1, `CARGO_BUILD_JOBS=1 RUSTC_WRAPPER=`, and the product checkout's
existing `target` cache. Preserve finite limits and stack sizes. Exact model
runtime is unavailable. Runtime case observations remain with TASK-0047,
integrated native/budget evidence with TASK-0048, and the full gate with TASK-0049.
