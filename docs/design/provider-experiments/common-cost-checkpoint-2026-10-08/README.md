# Common resource cost checkpoint, 2026-10-08

Status: paused at the user's request. This is diagnostic evidence for
[DN-0036](../../DN-0036-foreign-library-and-memory-provider-experiments.md),
not an accepted optimisation, language semantics or a completed delivery.
The candidate remains outside the integration branch.

The connected candidate passes all 63 Value capture tests under normal limits.
Its native forwarding case fails with `TypeResourceExhausted` under those
limits. The completed diagnostic comparison shows a cost regression:

| Program | Baseline Source work | Candidate Source work | Baseline independent Core work | Candidate independent Core work |
| --- | ---: | ---: | ---: | ---: |
| Copying | 1,212,707 | 33,595,389 | 903,995 | 1,034,670 |
| Bound NUL | 1,212,707 | 33,595,389 | 903,990 | 1,034,665 |
| Persistence | 597,882 | 757,922 | 1,609,101 | 1,733,738 |
| Resume | 203,215 | 253,310 | 289,063 | 310,657 |
| Forwarding | 216,584 | 401,561 | 315,193 | 338,902 |

Source work is cumulative source-checking work, not source size, elapsed time
or total work across all phases. Normal Source capacity is 327,680; independent
Core capacity is 983,040. [The complete comparison](comparison.json) records
all six owners, exact deltas and raw-log hashes. Resolution, module linking
and linked-interface costs are unchanged. Final elaboration is unchanged
except persistence, which increases by 36 units.

This compares the entire compound candidate against Common commit
`5a1da1ce97808ba68ad961a5cc6d80dadb6d09de`, using the same 29 experimental SQLite
input files already preserved at recovery commit
`11de19c8e627d74d5e0e3c25dc4a8cfb4f5e0ce6` and the same forwarding overlay.
It does not isolate the marginal cost of the newest producer change against
Fusion's earlier constructor candidate. The unrelated working semantics draft
was preserved without staging it; it is not an executable input.

All five baseline programs completed their original native assertions. Three
candidate programs completed with the temporary 20,971,520-unit diagnostic
ceiling. Copying and bound NUL exhausted that ceiling; both failed attempts are
retained. A bounded continuation changed only the diagnostic ceiling to
268,435,456 and added refusal-counter observation. Both programs then completed
the original native assertions. All five candidate results therefore have
completed measurements; these diagnostic passes do not establish admission
under normal limits.

The first comparison returned after 156.955 seconds, the continuation after
60.661 seconds. Each used one Cargo job and reused compiled artifacts between
programs. Exact Common, SQLite and Original source/index/HEAD guards were
restored after each round. Normal policies are restored and no Cargo, Rust,
LSP or Lean engines remain. No candidate source or diagnostic ceiling is
selected for integration. Full architecture and workspace verification were
not repeated for this unsuccessful candidate.

The real copying program published 127 Raw and 120 Evidence preparations and
reused the root at six further occurrences. Forwarding published seven Raw and
four Evidence preparations and reused the root twice. These counts establish
that the connected path executed; they do not explain the work amplification
or prove which sharing would be valid. Broad merging of environments by equal
types would discard live route, readiness, capture and creation distinctions.

On resume, first attribute the additional work before another implementation
round. A read-only review found an unread `local_memo` and duplicate journal in
the candidate's `producer.rs`; consuming local values into the sole completed
memo may avoid actual cloning. Preserve ordered alternatives, saved routes,
authority and duplicate-publication checks. This is an investigation candidate,
not an implemented fix or an explanation of the 27.7-fold copying regression.
Core alignment remains paused.

Fusion preserves the exact candidate in unsigned recovery commit
`7af4f896cdadc9636c0b7ff2a275069928506eb8` on
`codex/algebraic-definition-checkpoint`. Arena preserves its separate unfinished
scalar work at unsigned recovery commit
`1f3f26180686469d3361d865bb9191df913402aa`; that source remains uncompiled and
incomplete. SQLite is clean at `b0fa2a5ff46a7342ca2bba7bf1f513fcd1c32ca3`.
Core alignment stays at preservation commit
`657f6c0c3d674cd09802bb555f25364f1acfac68`. These workstreams and their child
agents have stopped; recovery commits do not constitute verified deliveries.

## Retained evidence and reproduction

[The manifest](manifest.json) authenticates the capsule's raw receipts, original
runner sources and patches. Large full-worktree snapshots are losslessly
compressed; [the archive index](archived-snapshots.json) records their decoded
names and SHA-256 hashes. Logs use `.txt` here and retain their original bytes.
Failed normal and 20,971,520-unit attempts remain separate from completed runs.

The recorded runners include local evidence paths and are historical launch
records. To reproduce the programs from Git in an isolated worktree:

1. Start at Common commit `5a1da1ce97808ba68ad961a5cc6d80dadb6d09de`.
2. Apply `measurement-inputs.patch`, then `native-forwarding-overlay.patch`.
3. For the baseline, apply `diagnostic-forward.patch`.
4. For the candidate, apply `candidate-forward.patch` and
   `candidate-connected-coverage.patch` before `diagnostic-forward.patch`.
   For completed copying/NUL costs, replace the temporary `20_971_520` ceiling
   in `src/types.rs` with `268_435_456`.
5. Run the exact commands in
   [the comparison results](source-producer-cost-v3-20261008/results.json) and
   [the copying/NUL continuation](source-producer-cost-v3-completion-20261008/results.json)
   with `CARGO_BUILD_JOBS=1`, no `ASH_*` overrides and one test thread.

Use independent baseline and candidate worktrees, or reverse only these exact
patches between lanes. These are disposable diagnostic source changes. Keep
them out of source delivery commits and restore normal ceilings afterward.
The public native assertions are unchanged by the diagnostic patches.
