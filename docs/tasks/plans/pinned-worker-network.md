# Pinned worker network execution plan

Owned by [TASK-0058](../TASK-0058-pinned-worker-network.md). This plan orders
work and does not define semantics or authorize implementation. Original issue
acceptance remains authoritative for scope; no criterion is complete here.

## Deliveries and acceptance

1. **N1 — [#76](https://github.com/dikini/ash-lang/issues/76).** Reviewed at
   `b296e17ce9e4f1760ce73df4f4716ef0c0fb2093`: CP-0027 and DN-0058 cover entry and capture admission, endpoint authority,
   resource-free copies, FIFO, commit/failure ownership, visibility, wait races,
   stale notifications, genuine End and backing settlement. Specify actual
   source/Core admission and control-envelope provenance. CP-0027 and AD-0017
   record the accepted transition and host/channel decision. Review and verify
   this adoption on its retaining branch before N2 implementation.
   Preserve assumptions and terminal failure limits. No worker recovery,
   silent transfer or native-stack suspension. Record retained verification and
   acceptance readback before closing N1.
2. **N2 — [#77](https://github.com/dikini/ash-lang/issues/77).** With accepted
   N1, build admitted pinned workers, copied channels, notifications and
   one-way completion. Construct local resources on their owner; only it drives
   its Store. Preserve accepted unpublished, queued and receiver-held work;
   keep receiving while bounded sends finish; release only after endpoints,
   cleanup, registrations and backing users settle. Discharge the bounded
   worker/channel preservation assignment before using it for release.
3. **N3 — [#78](https://github.com/dikini/ash-lang/issues/78).** In parallel
   with N2 only when assigned, freeze the finite-list model and prove
   registration, retirement, acknowledgement, whole-entry and order-preserving
   RemoveById, freshness and successor state, and restricted checking-rule
   soundness. Adopt checker semantics and any verifier decision before product
   work. Bind untrusted plans to actual linked definitions; check induction,
   dependencies and all reachable branches. Unsupported transforms preserve a
   checkable form or reject; exhaustion grants no permission. Test mutations,
   imports and transformed Core. No general source proof language.
4. **N4 — [#79](https://github.com/dikini/ash-lang/issues/79).** After reviewed
   N2 and the N3 proof/checker gate, compose verified ledger transitions,
   actual local completion and transport premises into recursive drain
   summaries. Register children before publication; cover parents until
   authentic acknowledgement. Reject stale emptiness, forged completion,
   obsolete state, raw publication and envelope confusion; revalidate after
   transformations and through imports. Exercise adversarial and budget cases.
5. **N5 — [#80](https://github.com/dikini/ash-lang/issues/80).** With connected
   N2–N4 and adopted normal/abandonment obligations, seal new roots but allow
   covered descendants; keep both workers and notifications serviceable for
   feedback. After stable application quiescence, close application sends,
   observe genuine End, finish service and cleanup, and settle endpoints,
   workers and backing. AppQuiet alone does not release support. Test bounded
   feedback and producing cleanup.
6. **N6 — [#81](https://github.com/dikini/ash-lang/issues/81).** Demonstrate
   request/reply using local regions/cells, retained computations, copied
   messages and an ordinary Ash binding over supported bytes/pointers. Exercise
   SQLite to the extent supported and report remaining gaps; a small fixture
   complements but does not replace that canary. Do not require obsolete
   checked/isolated FFI or process containment. Verify shutdown and failure
   limits without claims of deadlock freedom, termination or native correctness.
   Complete specification, proof/full gates, independent review, retained
   verification, acceptance updates and separately authorized Main delivery.

## Checkpoints and ownership

The orchestrator schedules gates; the assigned developer is the sole product
writer and heavy-build operator. Reviewers inspect immutable pins and receipts.

- **N-core:** connected worker/channel and bounded preservation ready for
  dependents. Fresh full workspace gate on the pinned integrated candidate;
  owner: assigned developer. Independent review and actual retained verification
  remain required for every slice.
- **N-proof:** frozen ledger, checked soundness and actual linked Core
  reconstruction ready for N4/N5 release reasoning. Fresh proof and full
  workspace gate on pinned integrated inputs; owner: assigned developer.
- **N-final:** integrated bidirectional shutdown, examples and specification.
  Fresh proof, native and full workspace gate; independent final review,
  retained verification and acceptance readback. Owner: assigned developer.
  This gate may serve as pre-Main only when inputs remain equal. Main is a
  separate human gate and remains outside milestone-branch integration.

Each delivery records exact source and configuration pins, focused commands and
results, review, retained ref and commit, original acceptance subset, remaining
scope and next owner. Do not mark a criterion complete while any original
obligation or required checkpoint remains. Preserve M1–M3 evidence and the
compatible shared cache; no fresh cold build is implied.
