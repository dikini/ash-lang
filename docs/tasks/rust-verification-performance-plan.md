# Rust verification performance implementation plan

Owned by [TASK-0042](TASK-0042-rust-verification-performance.md).

## Goal and boundary

Deliver AD-0014 and temporary generated-host artifact cleanup through the
existing PR #18 branch and shared product checkout/cache. Preserve the retained
ffi-ash checkpoint and its semantic/work/depth/stack invariants. The developer
owns writes and Cargo; the PM assigns the heavy-build window.

## Steps

1. Preserve the reviewed receipt regressions, exact-input refusal rules and
   default-feature checking/product linkage. These are implemented.
2. Carry the authorized host-cleanup patch and its ten focused checks into the
   same candidate. Preserve copied programs, shared dependencies, current test
   binaries and diagnostics; retire only temporary generated root artifacts.
3. Consolidate durable tool, task and workflow findings. Keep the whole-task
   timing comparison incomplete and record operating/timing/cleanup ownership.
4. Publish the immutable candidate on the existing PR branch. Obtain independent
   review of its entire delta and the exact gate recipe before the PM assigns
   one fresh seven-stage gate on the compatible cache.
5. Authenticate all stage pins, target counts and matching native/image evidence.
   If assigned, immediately test exact reuse without duplicate stage execution.
   Review and retain that evidence separately from the fresh gate.
6. After explicit PM integration assignment, preserve both histories with an
   unsigned merge. Apply/read back the bounded acceptance record after
   independent retained verification. Return cleanup Result and Next owner.
7. Complete the controlled old/revised comparison only under a later explicit
   assignment with comparable inputs/cache states. Do not restart obsolete
   archives/operators or infer causal savings from historical gate timings.

## Completion evidence

This partial delivery requires receipt/cleanup regressions, a fresh candidate
seven-stage gate, matching native/image proof, manual documentation checks,
independent verdict, verified retention and scoped cleanup handoff. Exact reuse
is a distinct witness. The full task additionally requires a controlled
old/revised comparison; it remains active until that evidence exists.
