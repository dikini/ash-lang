# Local retained control execution plan

This plan belongs to [TASK-0057](../TASK-0057-local-retained-control.md). It
organizes work and has no independent semantic or architectural authority.
Remove it when the task closes.

1. **C1 contract and model.** Review [CP-0026](../../proposals/CP-0026-scoped-owned-continuation-storage.md)
   against the current specification and the [bounded proof assignment](../../design/DN-0056-scoped-continuation-retention-and-library-scheduling.md#c1-bounded-ownership-and-completion-proof-assignment).
   Model finite owner locations, structural completions and explicit transitions;
   check refusal and negative examples as well as successful traces. Record the
   correspondence and limits. Run the frozen AD-0012 integration gate and obtain
   independent review before accepting the proposal or starting C2.
2. **C2 store.** After authorization, reuse the existing captured-continuation,
   frame, cleanup and iterative-disposal machinery. Add only the authenticated
   fixed-port store operations and their checked ownership moves. Exercise
   preparation failure, generation reuse, current-consumer returns, nested
   clause state, shared outer-cell access and cleanup with focused
   source/Core/runtime tests. Keep public release admission closed until C3
   establishes its conditions.
3. **C3 release analysis.** Mechanize the selected finite relation and
   fixed-point rules with explicit correspondence and a frozen proof gate.
   Extend existing actual-control and callable analysis with authenticated
   result/state correlation, freshness and conservative unknown behavior.
   Independently reconstruct it on linked Core, including transformed control,
   imports, handlers and cleanup. Verify bounded exhaustion grants no release.
   Run the full Cargo checkpoint once C2/C3 are connected and ready for C4.
4. **C4 libraries.** Use the same store for coroutine selection, cooperative
   scheduling and explicit gas-guarded checkpoints. Test R waiting for P while
   Q stays retained, final drain, repeated yielding, cleanup, nested resumes,
   both guard outcomes and loss of a ready-queue entry. Keep policy in library
   control; do not infer fairness or termination.
5. **C5 retention.** Map all original C1–C5 criteria to implementation,
   specification, proof, review and runtime receipts. Complete the final pinned
   workspace gate, independent review and retained-result verification. Apply and
   read back acceptance updates after retention; preserve unfinished criteria.
   Retire transition artifacts only at their authorized checkpoint. Main
   integration remains separate.

For C3, first compare the concrete alias, import and mutual-recursion examples
against a store-focused projection of the existing capture graph and its actual
handler, resume and cleanup walk. The current unlabeled match choices lose the
case/state correlation, so retain only the relevant scrutinee, pattern and value
flow. A three-case result domain with two work states has at most 12
input/case/output triples per summary; that count alone does not bound the full
analysis. A candidate tracks a relevant port's origin and validity, and forgets
correlation conservatively at ambiguous joins, instead of retaining a powerset
of every port origin. Check whether argument forwarding and all required cases
remain expressible before selecting it. Record measured state and work growth,
charge retained facts and scans, and reject on exhaustion. Likely changes span
`src/core/capture.rs`, `src/core/capture/control.rs`, imported summary transport,
and linked validation; confirm the actual carriers before editing. Reusing the
existing walk avoids duplicating handler selection and completion semantics in
a second interpreter. These counts are planning estimates, not a proved bound
or an acceptance substitute.

For each delivery record exact source and target refs, baseline and retained
commits, focused checks, last full-gate receipt, intervening changes, next gate
and owner. Use the assigned product checkout and shared Cargo target with one
build job. Reviewers inspect frozen inputs and request reruns from the product
developer. Do not infer a full workspace pass from focused checks.
