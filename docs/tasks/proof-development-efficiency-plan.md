# Proof development efficiency implementation plan

**Goal:** Reduce repeated Lean compilation and provide local Lean/Rust feedback.

**Architecture:** Retain the existing reviewed integration interface and final
coherence gate. Replace only its serial compilation stage with independently
validated module receipts and a resource-bounded dependency scheduler.

**Tools:** Python standard library, pinned Lean 4.33.1, Rust 1.97.1 language
server, and a pinned Lean LSP MCP installation.

1. Add `tools/lean/test_module_build.py` using actual tiny Lean modules. Cover
   retry after failure, source/import/options invalidation, corrupted receipts,
   warnings and unapproved axioms, and dependency ordering. Run it before
   implementing `tools/lean/module_build.py` and confirm missing functionality.
2. Implement receipts and scheduling. Default to one job, one compiler thread
   and a 4 GiB Lean memory limit. Require 4 GiB host headroom plus a reservation
   per running job before starting another. Cap explicit concurrency at two.
   Use a host lock to prevent overlapping integration runners.
3. Track the current v5 integration logic as `tools/lean/integrate.py`, replacing
   its replay with the tested scheduler. Preserve review, source, report, axiom
   and final coherence checks. Record failed progress without complete evidence.
4. Enable Rust analyzer and a Lean LSP MCP workspace with imported artifacts
   from verified frozen evidence. Check diagnostics, hover and proof state.
   Avoid automatic whole-project builds and broad plugin hooks.
5. Benchmark the existing frozen 29-module completion closure with one and two
   jobs. Do not overlap language-server builds or the active goal's compilers.
   Record wall time, per-module peak RSS, cache hits and provenance.
6. Document commands and cache-aware batching in `docs/project/proof-tooling.md`.
   Run grouped verification and independent review. Commit unsigned. Remove
   this task and plan when finished, retaining the decision and reusable guide.
