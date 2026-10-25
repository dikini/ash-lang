# Lexical region R1 candidate evidence

The [model and module guide](README.md) and [single correspondence report](correspondence.md)
define this evidence's scope. CP-0025 is accepted for transition after independent
source/map review and actual frozen-gate audit. Frozen integration and exact
transfer have passed; current-head review, milestone retention, retained
verification and R1/R2 issue acceptance remain pending. This record closes no
product criterion or issue checkbox.

## Frozen integration and transfer

The candidate starts at `a21d0001c34a4ac5a0557e34cfcfb4ea2b1e44a0`, targeting
milestone baseline `31fcfa5674f7cbd46ee583507f47a5c0cf21170e` through
[PR #146](https://github.com/dikini/ash-lang/pull/146).
The frozen Lean 4.33.1 gate completed with eight modules and 195 expected axiom
reports. The module scheduler independently validated eight cached artifacts,
logs, compiler/library/options/report pins and selected direct-import hashes;
it made zero fresh compiler invocations. Final source, tool, configuration,
review and import-coherence audits passed. Reported axioms contain only
`propext` and `Quot.sound`. This is bounded model evidence, not a native allocator
or compiler-correctness theorem, and not a workspace product gate.

The eight reviewed `.lean` files and generated `check.sh` were copied byte for
byte from the gate snapshot. `lean-toolchain` was preserved. No artifacts, caches,
logs, draft scripts or backups were copied into this proof directory.
The transfer audit matches every transferred byte to the gate manifest and each
Lean source to the reviewed final package.

The empty seed claims zero earlier region registrations or proofs. Its eight
existing compiler/library pins were revalidated. Before the gate, the sole
controlled baseline delta replaced an obsolete empty-registration comment in
`check.sh`; its new hash was pinned in a new seed. The old seed remains intact.
The gate did not claim that this edited script matched the unchanged Git tree.

## Exact working records

These records remain available while the delivery and acceptance are live under
the [documentation policy](../../project/documentation.md#working-records-and-build-history).
They identify evidence, not additional report copies or semantic authority.

| Record | Path | SHA-256 |
| --- | --- | --- |
| Reviewed candidate manifest | `/tmp/ash-m2-model-review-final1/MANIFEST.json` | `092bbf0348fff787c9f4619bc8ef96413395b2d6ad7e7721bf6b1fe1f52825c4` |
| Independent final source/map verdict | `/tmp/ash-m2-core-review/final1-review.json` | `da7fc23c7b302333c75c284b7b7eff20c2a397b4a94c32790c9f0976cb6c2e8e` |
| Approved runner configuration | `/tmp/ash-m2-r1-integration-approved1.json` | `60be43605a986ce86e96fefffadfc90b9b4c47d8797ed476829ffdcb6bbbec1d` |
| Empty seed | `/tmp/ash-m2-model-review-final1/empty-seed.json` | `693dce7eb8e859b99a3467406cbb4391d7d2d11ce76d17b0dbbe0926d0e7bdde` |
| Controlled baseline delta | `/tmp/ash-m2-model-review-final1/BASELINE-DELTA.json` | `d8062da5db428e5825410381e1403348568ec6b434d816e40457f357de5e1cdf` |
| Frozen gate receipt | `/home/dikini/Projects/ash-lang/.worktree/generic-cells/target/lexical-regions-r1-integration1-evidence.json` | `6e380777bc48ff455a1457d9d6d665c70cde1e2a9a8c65351bcabb7623334b62` |
| Independent actual-gate audit | `/tmp/ash-m2-core-review/integration1-gate-review.txt` | `0f800241a98d9d9b96e2f35c6bb275f78dbb5d400d4e490fcc4aef3f2802f950` |
| Exact source/registration transfer | `/tmp/ash-m2-source-transfer1.json` | `0725859cdda5ca90f74f3dab5b2bf788cf0507bfbce7a5dfe79dac88131bdb5e` |

The gate receipt carries all source/registration/toolchain hashes, selected
artifact/log/import pins, expected report names, component-review pins and
scheduler scope/timing. The transfer audit references that receipt and records
the source/registration hashes and preserved toolchain. Local development runs
are superseded for integration evidence; they do not become extra acceptance
gates.

## Remaining ownership

Root has cleared the independent gate audit and semantic adoption. Root owns
publication and milestone integration. The author supplies the retained verification and
acceptance readback after integration; the reviewer checks that record.
Until those steps complete, R1/R2 remain candidate deliveries and product R3
remains held. Main integration retains its separate gate.
