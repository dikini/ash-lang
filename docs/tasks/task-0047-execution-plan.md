# TASK-0047 execution plan

Owned by [TASK-0047](TASK-0047-generic-cell-execution-and-completion.md).
Accepted [CP-0023](../proposals/CP-0023-scoped-generic-cells.md) governs the
runtime transition. This plan defines neither source semantics nor new storage
regions. Execute sequentially in the existing product checkout; the developer
owns source and Cargo, and the reviewer reads frozen inputs.

1. Add a public source runtime test in `tests/resource_scope_runtime.rs` for
   generic Bool, tuple, nominal and function payloads, snapshots and aliasing.
   Run the selected target/case with one job and observe the existing execution
   gate refuse before changing runtime code. Keep the legacy integer cases.
2. Extend `src/eval/machine.rs` resource payload ownership with a generic
   ordinary `Value` root and its full instantiated effect authority. Reconstruct
   the instance from authenticated typed Core and lexical instantiation before
   publication. Preserve the existing legacy branch and fresh activation keys.
   Prepare storage, work and trace before publishing or replacing a root. Add
   owning unit tests for exact R/T, wrong family, donor/stale keys and unchanged
   state on refusal. Charge proportional copy, alias and type work first.
3. Connect generic read/write selection through the existing handler search.
   Add actual P07 read99/intercept41/forward/self-capture-discard and P12 Tick99
   cases, then P13 escaped7 with the N12 typing negative preserved. Replace the
   pending evaluator gate only with this connected kernel; connect generated
   execution/build preparation separately and update its gate regression.
4. Extend the public runtime corpus for all P01–P13 variants, using existing
   helper/facade fixtures where applicable. Assert P02 pair(41,42)/escaped41,
   P03 outer7, P04 escaped7 and P05 same-site9 with distinct activation keys and
   exactly one release each. Preserve source/Core dependency-negative pairs.
   Observe actual sharing/cyclic prefixes and monomorphic/mixed API behavior.
5. Extend `tests/resource_scope_runtime.rs` and cleanup suites for C01 latest
   root across capture/resume, C02 initializer capture before ownership, owned
   discard after inner cleanup and still-live enclosing access. Add owning
   machine tests for captured capacity, fresh reuse and exact/one-short/fresh
   retry acquisition/write preflight with prior operand effects retained.
   Exercise deep normal/discard/failure disposal on unchanged stack limits.
6. Update `spec/dynamic-semantics.md` and affected evaluator/tool documentation
   from verified behavior. Preserve static proof, exact handler semantics,
   native liveness/quarantine and the restricted private lifecycle profile.
   TASK-0048 owns the complete connected tamper/budget/native matrix; this task
   supplies owning evidence rather than deferring its charging implementation.
7. Freeze an unsigned candidate and record source/test/config/tool inputs.
   Run the prescribed resource_scope_runtime/resource_scope_core and cleanup
   targets, whole library and affected source/native callers, strict affected
   Clippy/fmt/rustdoc, all sequentially with `CARGO_BUILD_JOBS=1 RUSTC_WRAPPER=`.
   Obtain independent code and technical-evidence review, repair/reverify and
   read back the retained commit. Record actual values/counts in TASK-0047 and
   hand them to TASK-0045/0046 owners. TASK-0048 integrated evidence and TASK-0049
   fresh `cargo xtask verify` remain required before original case acceptance.

Use Rust 1.97.1 and the stable existing target cache. Preserve work, capacity,
depth and stack limits. All local commits are unsigned. No push, PR, Main
integration, cleanup or DN-0054 mechanism is included. Exact model runtime is
unavailable; the developer dispatch uses `gpt-6.1-sol`, `medium`.
