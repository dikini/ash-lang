# AD-0012: Proof development feedback and build reuse

- ID: `AD-0012`
- Status: accepted
- Related: [AD-0001](AD-0001-implementation-environment.md),
  [TASK-0032](../tasks/TASK-0032-core-one-shot-alignment.md)

## Decision

Use Lean and Rust language servers for navigation and local diagnostics. Keep
the reviewed, frozen Lean integration build as the proof acceptance gate.
Language-server feedback does not establish proof coverage or integration.

Track the existing integration runner in the repository and retain its source,
compiler, review, dependency, report and axiom checks. Save each validated
successful module independently so a failed batch can reuse completed work.
Key reuse by source, compiler and library pins, options, expected reports and
selected import hashes. Recheck stored artifact and log hashes before reuse.

Build serially by default. An explicit two-job setting may compile independent
ready modules when CPU and memory headroom permit. Bound compiler threads and
memory, serialize integration runners on the host, and record per-module wall
time and peak resident memory. A failed module blocks its consumers; independent
successes remain reusable. Publish complete integration evidence only after all
existing coherence checks pass.

## Context

The current runner reuses unaffected parent artifacts, but its serial replay
publishes fresh module records only after the entire replay succeeds. Retrying
a failed batch therefore repeats successful work. Large modules and shared
imports also make blind parallelism expensive on the development host.

Related changes can share a compile of their reverse consumers. Uncertain
changes to widely imported modules need an early focused check. Independent
changes need not wait for a larger batch. Timings and retry reuse provide
evidence for choosing future batch sizes.

## Consequences

This increment adds development tooling without changing Ash semantics or Lean
proofs. Compiler upgrades, broad proof-module splits, experimental incremental
snapshots and mandatory full builds on every edit are outside this decision.

## Verification

Exercise dependency ordering, concurrency bounds, failure recovery and cache
invalidation with actual small Lean modules. Benchmark a frozen existing
integration closure with one and two jobs, checking resource headroom first.
Verify language-server navigation and diagnostics with the pinned toolchains.
