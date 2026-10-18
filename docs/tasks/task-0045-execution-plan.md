# TASK-0045 execution plan

Owned by [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md).
This plan implements accepted CP-0023 within the foundation publication boundary;
it defines no language rules.

1. Extend canonical builtin loading and authenticated metadata to the separate
   two-argument family. Test kinds, exports, sealing and facade identity.
2. Resolve named acquisition in the preceding scope and reuse generated exact
   forwarding evidence and the Effect Resource carrier. Retain complete types,
   validate ordinary facts independently, and preserve image roles and copying.
3. Reject generic-sensitive module summaries and linked Core admission after
   ordinary checking until TASK-0046 supplies dependency proof. Test diagnostics,
   restricted payloads and the publication boundary without claiming execution.
4. Update matching specification passages and task evidence, run the four focused
   resource suites, relevant unit tests, formatting and lint. Freeze a local
   commit for independent review before any downstream work.

Verification uses toolchain 1.97.1, one Cargo job and the product checkout's
`target` directory. `RUSTC_WRAPPER=` bypasses the configured sccache wrapper,
which cannot start in the sandbox. Runtime acceptance and integrated checkpoint
verification remain pending.
