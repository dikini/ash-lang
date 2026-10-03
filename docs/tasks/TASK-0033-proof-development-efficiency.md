# TASK-0033: Proof development efficiency

- ID: `TASK-0033`
- Status: active
- Related: [AD-0012](../decisions/AD-0012-proof-development-feedback-and-build-reuse.md),
  [TASK-0032](TASK-0032-core-one-shot-alignment.md)

This task organizes tooling work and does not define Ash semantics.

## Work

Follow the [execution plan](proof-development-efficiency-plan.md). Implement
module receipts, resource-bounded scheduling and timings. Enable one Lean and
one Rust LSP workspace. Benchmark frozen proof sources without editing the
active alignment checkout or weakening its verification gate.

## Verification

Run the new runner tests, exercise an existing reviewed integration input, and
compare serial and two-job frozen builds. Record actual LSP requests and limits
of the resulting tooling. Preserve unsigned commits.
