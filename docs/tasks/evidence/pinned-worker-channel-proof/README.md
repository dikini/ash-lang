# Pinned worker/channel bounded source proof gate

The frozen source gate passed for reviewed commit
`eecc85178641f4eaf41cae696653e80003c24432`. Its closure, in registration
order, is `Ownership`, `OwnershipExamples`, `DrainSafety` and `WorkerChannel`.
The first three sources match the retained C3 sources; `WorkerChannel` is the
new N2 model. The generated `check.sh` is the reviewed baseline plus the
`WorkerChannel` registration. Its adoption does not imply that the productive
script was rerun after adoption.

The independent [source review](source-review.json) cleared the candidate for
this gate. After the run, a separate [independent gate audit](independent-gate-audit.json)
passed and found registration adoption ready. Both files are root-recorded
receipts of the actual Sol 6.1 high collaboration verdicts. The [operator
audit](operator-audit.json) records separate post-run checks and copied artifact
hashes; it is not the independent verdict.

The gate used `Lean 4.33.1` (compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and one job, with 4096 MiB
compiler memory and 4096 MiB headroom. Its command was:

```text
python3 -u /tmp/ash-m4-n2-gate-eecc/tools/lean/integrate.py /tmp/ash-m4-n2-inputs-eecc/config-run2.json
```

This was a disposable detached source-gate checkout, using a truthful empty
registration seed and all four reviewed source patches. The paths in the raw
records identify that run, not portable replay paths. The [configuration](config-run2.json),
[seed](empty-seed.json), [checkpoint](checkpoint.json), [manifest](manifest.json),
[progress](module-progress.json), [stdout](gate-run2.stdout), [proof log](proof.log)
and [raw evidence](evidence.json) are retained here. The complete independently
copied source snapshots, module artifacts, logs and audit script also remain in
the local ignored `target/ash-m4-evidence/n2-frozen-eecc-run2/` directory;
their paths and hashes are in the operator audit. Binaries and caches are not
committed. The first attempt was resource-blocked before compilation; run 2
changed only the output prefix.

The runner reported 153 ordered axiom reports: 18, 31, 33 and 71 respectively.
The first three modules used validated cache receipts; `WorkerChannel` compiled
in this run. All four exited successfully. The [individual module logs](logs/)
contain the reports; the only observed axioms were `propext`, `Quot.sound`
and `Classical.choice`. Compiler and library pins, direct imports, expected
report names, cache fingerprints, source hashes and artifact hashes are in the
raw records.

| Reviewed input | SHA-256 |
| --- | --- |
| `Ownership.lean` | `5103f2a5b155da16d98b75d8d65a8cb0edd9bf9056c2de033f35efe3e81b71ee` |
| `OwnershipExamples.lean` | `0ca6f7915479fca02a8abc8099e845b27a6706e2030ea51a8350d44f7b194c99` |
| `DrainSafety.lean` | `c676f253d761fe44dbf9d1d9240a6a6451affbfc410f60bbaaf6986d1fba6677` |
| `WorkerChannel.lean` | `d31d533006014f51865324b00799e5731ac909024a5b51e55e5071f4a9fac29b` |
| `worker-channel-correspondence.md` | `751a1b77f3217fa1fa43f17a3085abe76ad34292f65666ac5be949a67c32ab29` |
| Run configuration | `455ccd91888c3696dace5a1e76fcf003527399cc06dd590e6e9de5a47de0659e` |
| Raw evidence | `7912a3af94493e8e9d91f22e39e88f9e9f2011421067e2f52b917a770e0fa3c7` |
| Independent gate audit | `918077c6c0d6e5dfece470e87a1237c28fce44be3747fa4d37a98a3aca37e915` |

This evidence establishes the bounded source proof gate only. Actual C3
completion correspondence, Rust and native behavior, refinement, N-core and
full N2 acceptance remain pending. The model's premises and implementation
obligations are recorded in [worker/channel correspondence](../../../design/retained-control/worker-channel-correspondence.md).
It grants no release authority.
