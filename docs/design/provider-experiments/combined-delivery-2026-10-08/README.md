# Combined Original delivery evidence

Informative DN-0036 evidence, without current language authority, product adoption or a formal proof.

The complete Original gate passes at `7a518e83230fec568978b269b1d69776ab6051c5` and tree `8af28e134fbe17e19034d77bf56335a9a6bc6421`. All six ordered stages complete: format, metadata, build, strict lint, workspace/all-target/all-feature tests and warning-denied documentation. Outer Cargo target summaries record 3,475 passes, 0 failures and 1 ignored case (the generated calibration fixture) across 119 targets; 4 targets contain no executed cases. Nine nested child summaries are excluded from these totals. The [combined-delivery-2026-10-08 receipt](README.md) retains raw output, exact commands, the corrected outer-target summary and unchanged source/eight-draft evidence. Main delivery, focused Main checks, fresh combined native phase measurements and related cleanup remain pending. This is bounded DN-0036 experimental retention, without semantic adoption or a formal proof.

## Reproduce

Run serially from a checkout containing the checked source and the recorded Rust toolchain. A command list is not a fresh pass receipt.

```sh
CARGO_BUILD_JOBS=1 RUST_TEST_THREADS=1 RUSTC_WRAPPER= cargo xtask verify
CARGO_BUILD_JOBS=1 RUST_TEST_THREADS=1 RUSTC_WRAPPER= cargo test --locked -p ash --lib elaborate::provider::tests::resource_fact_late_actual_failure_drains_retained_canonical_actual_on_small_stack -- --exact --test-threads=1
CARGO_BUILD_JOBS=1 RUST_TEST_THREADS=1 RUSTC_WRAPPER= cargo test --no-fail-fast --locked -p ash --test architecture --test provider_arena_allocation --test provider_sqlite_copying --test provider_sqlite_sessions --test provider_sqlite_control -- --test-threads=1
CARGO_BUILD_JOBS=1 RUST_TEST_THREADS=1 RUSTC_WRAPPER= cargo fmt --all -- --check
CARGO_BUILD_JOBS=1 RUST_TEST_THREADS=1 RUSTC_WRAPPER= cargo test --locked -p ash --lib evidence_validation::tests::concrete_adapter_source_catalog_has_an_exact_retry_boundary -- --exact --test-threads=1
CARGO_BUILD_JOBS=1 RUST_TEST_THREADS=1 RUSTC_WRAPPER= cargo test --locked -p ash --test method_parameter_resources -- --test-threads=1
CARGO_BUILD_JOBS=1 RUST_TEST_THREADS=1 RUSTC_WRAPPER= cargo fmt --all -- --check
CARGO_BUILD_JOBS=1 RUST_TEST_THREADS=1 RUSTC_WRAPPER= cargo test --locked -p ash --no-fail-fast --test method_parameter_resources --test resource_provider_resolution -- --test-threads=1
```

## Receipt boundaries

The full-gate files record the successful V4 checked Original commit. The V5 repair receipt predates its integration and runs against its independently pinned source; the nine-file source review connects that source to the checked integration. The review JSON's historical pending full-gate field is superseded by this receipt, not rewritten.

The initial failed gate belongs to c18ed9f3a07294ad1db06d3499cd00017c213cf0: 1,733 passes and three architecture failures across three outer Cargo targets; six nested child summaries do not contribute to totals. It is counterevidence, never a successful full gate. Its later stages were not completed.

Historical Arena manifests 833b and 3d351316 retain their selected receipt identities. Historical SQLite pending paragraphs retain their checkpoint scope. Paused Lean/Core/proof work, unrelated drafts, failed optimization machinery and all shared stashes remain excluded. Native combined/Main host measurements and cleanup require separate observed receipts.

V2 at `dadac04356c69bc3491ebd83c62ca9b2d1b81e70` failed only the stale source-formula test: 2,657 passes and one failure across 60 outer Cargo targets. Its library (1,675), architecture (45) and executable deep-method cases passed; later gate stages were not completed. V2 is not a full pass. The focused formula repair retains SHA-256 `4bc1405e4220634da719aface787b046b4fca377aae0dbb4819eeb43e9cd7896` for `tests/method_parameter_resources.rs`; V4 descends the reviewed dadac basis with only the two exactly reviewed test files and documentation changes. All nine V5 production/inventory basis files are unchanged. Toolchain evidence was recaptured for the V4 checked source.

V3 at `0bc24185fdfbb3be803d1031a6c5980c85e9d661` failed with 3,115 passes, one stale checkpoint failure and one ignored case across 97 outer Cargo targets. It is not a full gate pass. The remaining-suite audit preserves command exits [101, 0, 0]: only the known root integration expectation failed; the other workspace package command and warning-denied rustdoc succeeded. This audit is not an all-green gate. The connected test-only checkpoint repair at `80c9fc29b91c5dc8d79584a11ecf723537f2b51d` retains SHA-256 `70b6484bfd7d88dea69b4e520305715dd9bd49175ecc5b1b0d95893b89745830`; its focused formatting plus 17 integration cases pass. No production semantics or limits changed.

## Retained file hashes

- [v3-failed-gate-receipt.json](v3-failed-gate-receipt.json): SHA-256 `ea4ff7b719efd4a6dc67e85bc25f90aaecc5111cdc47534a81fcbaf4b621f00e`.
- [v3-failed-gate-summary.json](v3-failed-gate-summary.json): SHA-256 `00bfbfb941d2a17222ad82e09d0f8cad62ba1edbf7e570a65ef387b88678576f`.
- [v3-failed-gate-output.log](v3-failed-gate-output.log): SHA-256 `54bf5ae324443d31209183a84e5b56e82acb1776d90e14a42987bd9c7f01cef3`.
- [remaining-suite-audit-receipt.json](remaining-suite-audit-receipt.json): SHA-256 `1e5c855bafb40b40450986de64104dcdfa6f09a2a5db3fead4ea8e71251bedec`.
- [remaining-suite-audit-output.log](remaining-suite-audit-output.log): SHA-256 `5fa31f06c0df5146d80cabe432fa1b9bc23a7034a422835e5be2af01d26f2ab0`.
- [checkpoint-fix-receipt.json](checkpoint-fix-receipt.json): SHA-256 `8365bf13fc9909dfc4db9fd8e330747b679e77ffd4a9e4f492548a3f410292a9`.
- [checkpoint-fix-output.log](checkpoint-fix-output.log): SHA-256 `cc56bb8a7f4b23c8a1b82a3a30b7f6c3ac804fd4853da092a8efcec231e29838`.
- [checkpoint-fix-source-review.json](checkpoint-fix-source-review.json): SHA-256 `661a2334193eeb6476b2f7a24663c2c4d44db7e0ea3cb8748d4605fe999503d5`.
- [full-gate-receipt.json](full-gate-receipt.json): SHA-256 `4ac92b014f137bea143946b5e07afcaf6a4570fb1d67a156285d5c1e52e5f5ad`.
- [full-gate-output.log](full-gate-output.log): SHA-256 `2628df65f92f1dfd19af19008cf59c779d40026f7cd5276dbd0d3753452edb1a`.
- [full-gate-summary.json](full-gate-summary.json): SHA-256 `6ed575b2126f6e68915a330883c5a6cba3f5340a39232204920406e2f9dc1e04`.
- [full-gate-summary.txt](full-gate-summary.txt): SHA-256 `921047a368e3039a5919f1ac3e7976e57df787a6461286c64de731b7676a11a0`.
- [v2-failed-gate-output.log](v2-failed-gate-output.log): SHA-256 `2afc0f531d5b06e5b240e3dd238b448664cab1886dbfbd423f5902fec18c2b06`.
- [v2-failed-gate-receipt.json](v2-failed-gate-receipt.json): SHA-256 `817686c9062c4c317b4635e4d05516158f83a7c58c1a9e45ff74dbe7b02fd971`.
- [v2-failed-gate-summary.json](v2-failed-gate-summary.json): SHA-256 `f577c77539f37ae0c962b458b0e5a4d5dee9fab160048d297a58792cab356ca9`.
- [formula-fix-source-review.json](formula-fix-source-review.json): SHA-256 `f0bbea4665e90832f421b6e7711c5657ce6fea04cc2d1bf47578a3a5d75b2ce7`.
- [formula-fix-receipt.json](formula-fix-receipt.json): SHA-256 `275030099bae93ac0351eeb4c7591856980d342778d806b1a1ae2db5f93e343b`.
- [formula-fix-output.log](formula-fix-output.log): SHA-256 `4cdc960f58e680a405bacd0870068e04979412d9100736b6287437316523bcac`.
- [v5-repair-receipt.json](v5-repair-receipt.json): SHA-256 `18c7b5c553f9d64e17320aacac7e25668143d162e5e60399ce96e6266728f6f3`.
- [v5-repair-output.log](v5-repair-output.log): SHA-256 `7ca413624a11a49a4ae43920f603846b7eae3561761823d71c8b73e50d5b8f4a`.
- [shared-repair-source-review.json](shared-repair-source-review.json): SHA-256 `d3b7effdf90cf05324b6eb95d1705e22b306029ce341bafe3fd9e22e3c446412`.
- [initial-failed-gate-output.log](initial-failed-gate-output.log): SHA-256 `be46824629983c87aded795fd1c7647ee5f8ffb10b7fb38d0903658ce1f8de45`.
- [initial-failed-gate-summary.json](initial-failed-gate-summary.json): SHA-256 `9e6df3aea6850ed8c48db1a21aee2e3647e86a3414a61c10b7ebfc4cc3d6bc59`.
- [initial-failed-gate-receipt.json](initial-failed-gate-receipt.json): SHA-256 `7ae369ea3b8e2a1cd96ac7f74f7224b8a76cbb61575972f9d3e11bc1e87753ae`.
- [toolchain.json](toolchain.json): SHA-256 `d664c96f99e5b075ea0392253a6a2ab342c99a3bea62a9b55ad7e0f4b3c67912`.
