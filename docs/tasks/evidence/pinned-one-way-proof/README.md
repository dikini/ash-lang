# Pinned one-way completion source proof gate

The bounded source gate passed for `OneWayCompletion.lean` at SHA-256
`870b4f0f4b134e49a2d97a1039d8f362700cb2ff1f7d667877d6cb9816e1573c`.
The adopted `check.sh` registers the full five-module closure. The generated
fixed-path productive replay script is not adopted.

The [source review](review.json) and [independent gate audit](independent-gate-audit.json)
record actual Sol 6.1 high verdicts. The [operator verification](operator-verification.json)
is a separate receipt. [Reviewed configuration](batch-reviewed.json),
[executed configuration](batch-reviewed-escalated.json),
[checkpoint](checkpoint-reviewed.json), [manifest](manifest.json),
[progress](module-progress.json), [raw evidence](evidence.json),
[proof log](proof.log) and [module logs](logs/) retain the run inputs and outputs.
Raw paths identify the actual local run; they are not portable replay paths.
Binaries and caches remain ignored in the local evidence bundle.

Lean 4.33.1 ran with one job, 4096 MiB compiler memory and 4096 MiB headroom.
OneWayCompletion compiled freshly in 229.771 seconds with peak RSS
1,708,856 KiB. Four parent modules reused validated evidence from the
[worker/channel gate](../pinned-worker-channel-proof/README.md).
This was not an all-modules-fresh run. All five modules exited successfully.
The 283 ordered axiom reports comprise 18, 31, 33, 71 and 130 reports.
`Processing.normalized_frame_sites_sound` appears twice in the last module;
the count does not imply 130 distinct theorems. Only `propext`, `Quot.sound`
and `Classical.choice` occur. The two failed setup attempts stopped before
compilation and grant no proof evidence; their logs are retained separately.

This establishes the bounded modeled source gate. Rust-to-model correspondence,
actual Core and native behavior, runtime preservation, refinement, N-core and
full N2 acceptance remain separate obligations. This receipt grants no runtime
release authority and does not close N2.
