# Main delivery evidence and disposition

Main merge `f51f538455cb997e5e1f5db6eec8cf36d616c7d1` retains Common `f56070ccb88d21ba833c5ca70106070318b9145a`. Focused verification at this Main source passes 39 cases across six Cargo targets, with 0 failures and 0 ignored cases. All five packaged SQLite hosts and the selected scalar Arena host pass their recorded source/native assertions. The [main-delivery-2026-10-08 receipt](README.md) retains exact commands, raw logs, source pins, phase measurements and cleanup disposition. The full workspace gate belongs to Original `7a518e83230fec568978b269b1d69776ab6051c5`; its documentation descendant `f56070ccb88d21ba833c5ca70106070318b9145a` and this Main merge retain the executable source. Later result prose does not constitute another full gate. Broader TASK-0034 payload/graph-sharing/copying work and paused Lean/Core/proof work remain unfinished and excluded. This retains informative DN-0036 evidence without semantic or production adoption or a formal proof.

## Actual phase measurements

| Program | Phase | Used | Nominal | Deficit | Allowance | Assessment | Future optimization target |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- |
| scalar Arena | SourceChecking | 88793 | 1245184 | 0 | 124518 | WithinBudget | no |
| scalar Arena | FinalElaboration | 27096 | 393216 | 0 | 39321 | WithinBudget | no |
| scalar Arena | IndependentCore | 82277 | 1638400 | 0 | 163840 | WithinBudget | no |
| text-entry.ash | SourceChecking | 164084 | 1245184 | 0 | 124518 | WithinBudget | no |
| text-entry.ash | FinalElaboration | 60696 | 393216 | 0 | 39321 | WithinBudget | no |
| text-entry.ash | IndependentCore | 91011 | 1638400 | 0 | 163840 | WithinBudget | no |
| copying-entry.ash | SourceChecking | 1213287 | 1245184 | 0 | 124518 | WithinBudget | no |
| copying-entry.ash | FinalElaboration | 166073 | 393216 | 0 | 39321 | WithinBudget | no |
| copying-entry.ash | IndependentCore | 903995 | 1638400 | 0 | 163840 | WithinBudget | no |
| session-entry.ash | SourceChecking | 598589 | 1245184 | 0 | 124518 | WithinBudget | no |
| session-entry.ash | FinalElaboration | 377132 | 393216 | 0 | 39321 | WithinBudget | no |
| session-entry.ash | IndependentCore | 1609027 | 1638400 | 0 | 163840 | WithinBudget | no |
| control-resume.ash | SourceChecking | 203627 | 1245184 | 0 | 124518 | WithinBudget | no |
| control-resume.ash | FinalElaboration | 103926 | 393216 | 0 | 39321 | WithinBudget | no |
| control-resume.ash | IndependentCore | 289063 | 1638400 | 0 | 163840 | WithinBudget | no |
| control-discard.ash | SourceChecking | 263417 | 1245184 | 0 | 124518 | WithinBudget | no |
| control-discard.ash | FinalElaboration | 147288 | 393216 | 0 | 39321 | WithinBudget | no |
| control-discard.ash | IndependentCore | 109243 | 1638400 | 0 | 163840 | WithinBudget | no |

All eighteen completed phase measurements are WithinBudget with zero deficits; this receipt introduces no accepted deficit target. Charged work is not CPU or memory. WithinBudget is ideal; exact AcceptedDeficit <=floor(nominal/10) is permitted only with a named phase optimization target. OutsideAllowance or incomplete evidence fails.

## Reproduce

Use any checkout containing this delivery and its pinned Rust toolchain. The optional retained cache directory may be selected through CARGO_TARGET_DIR per command; default reproduction uses the normal workspace target.

```sh
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo test --locked -p ash --test provider_sqlite_source --test provider_sqlite_copying --test provider_sqlite_sessions --test provider_sqlite_control --test provider_arena_source --test provider_arena_allocation -- --test-threads=1
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo run --locked -p ash-foreign-adapter --example arena_typed -- tests/fixtures/provider-experiments/arena-typed/allocation-entry.ash
```

The [package reproduction recipe](../README.md#reproducing-common-source-cases) builds sqlite_session and runs text-entry.ash, copying-entry.ash, session-entry.ash, control-resume.ash and control-discard.ash against a fresh private copy/database. Full results and native assertions, rather than exit status alone, define the retained host evidence.

### Five packaged SQLite programs

```sh
(
    ash_repo=$(pwd -P)
    CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo build --locked -p ash-foreign-adapter --example sqlite_session || exit
    sqlite_example_dir=$(mktemp -d) || exit
    cp "$ash_repo"/docs/design/provider-experiments/examples/sqlite-copying/*.ash "$sqlite_example_dir"/ || exit
    printf 'Example directory: %s\n' "$sqlite_example_dir"
    cd "$sqlite_example_dir" || exit
    sqlite_example_status=0
    for sqlite_entry in text-entry.ash copying-entry.ash session-entry.ash control-resume.ash control-discard.ash
    do
        "$ash_repo/target/debug/examples/sqlite_session" "$sqlite_example_dir/$sqlite_entry" || sqlite_example_status=1
    done
    exit "$sqlite_example_status"
)
```

## Aborted preparation boundary

The first Main focused invocation was interrupted with exit -2 while preparing the path-reused cache. It supplies no successful test claim; its raw receipt/output are retained separately. Only the completed v2 invocation establishes the 39-case result. Its aborted build cache is separately retained at `.worktree/cache/aborted-main-build-before-cache-transfer-20261008`, inode 50213201; it is additional to the six planned original caches and supplies no passing evidence.

## Actual cleanup disposition

Normal removal completed for the Original, Common, SQLite, calibration, Arena and Fusion checkouts after exact-tip Main ancestry, draft/archive/backup and cache identity checks. All branch and archive refs and 33 shared stashes are unchanged. Selected drafts now remain uncommitted in Main; conflicting originals and archived Fusion trials are retained under ignored .worktrees/consolidation-draft-retention-2026-10-08. All six non-Main caches were retained by same-device rename. Main target and all five protected paused Core/Lean/proof/external documentation-pin worktrees and caches are unchanged. The failed Fusion candidate remains archived and unmerged.

Eight exact reviewed inaccessible OS service identities were exempted from fd inspection. Relevant build processes, children and all other accessible processes remained checked; Root and coordinated source writers held an exclusive stopped-engine lease. No OS services were stopped.

The independent [exclusions and cache audit](final-exclusions-and-cache-audit.json) confirms the rejected Fusion and paused Core tips are not Main ancestors and preserves the Main target and aborted-cache identities.

The independent [admission audit](final-admission-evidence-audit.md) and [machine-readable review](final-admission-evidence-audit.json) corroborate the recorded evidence without rerunning a compiler or host. Original private source locations within these raw review artifacts are historical provenance. The [aggregate portable map](aggregate-portable-map.json) resolves every aggregate source path to its single retained raw copy. The [candidate revision record](private-candidate-revision.json) records these private preparation edits.

## Retained evidence hashes

- [aborted-main-cache-preservation.json](aborted-main-cache-preservation.json): SHA-256 `99d2b4d3db9449ae14a0c7be6ea5f1e36113a5b437a2545c2aae328e4d1e6d01`.
- [aggregate-portable-map.json](aggregate-portable-map.json): SHA-256 `bbc9570a0e16d621468c2744be416c70b02009e5c78a32484404f6233ca4ceb3`.
- [aggregate.json](aggregate.json): SHA-256 `806e6ad659a67acff44db17c0de8ea74defe85e1f938308255f0d714e475bfdb`.
- [arena/output.log](arena/output.log): SHA-256 `bf4aa8d54e14ecd7c3c7371fc7dcc6183b98a77837990cd6fcfda0f6d4f65e83`.
- [arena/receipt.json](arena/receipt.json): SHA-256 `7e7744e9547a66f4d8281139f4c2abd58602688035d9ad2721aa08a84ffd44ac`.
- [arena/validated-native-and-costs.json](arena/validated-native-and-costs.json): SHA-256 `a03a396f434ee82a66d124b137ab58b0cedd11b3a159cc02e08f258bc28d8d03`.
- [cleanup-helper-receipt.json](cleanup-helper-receipt.json): SHA-256 `0aa9557732c302d8519ef726f0d9e00be0b5be7f48c51598c792e9344666d32f`.
- [cleanup.json](cleanup.json): SHA-256 `6e9cdf1e2cdf11a8b0e1f739ae8f3fb74fce59acdf6df89225124e1ca0712f33`.
- [evidence/check-main-arena-evidence.py](evidence/check-main-arena-evidence.py): SHA-256 `338dcb1957c76c5cfbcb7b08f5c25681b5355d18170abcc722ef274d44f1ff46`.
- [evidence/check-main-sqlite-host.py](evidence/check-main-sqlite-host.py): SHA-256 `abdffbc81030ff768dc013e02b740cd90e80c6384dbd3861c45f770d91c053bc`.
- [evidence/main-focused-check-aborted/output.log](evidence/main-focused-check-aborted/output.log): SHA-256 `77e52e2e13baccf7a3117cca27dd899cfbc75397715dcaab55f55bec87719246`.
- [evidence/main-focused-check-aborted/receipt.json](evidence/main-focused-check-aborted/receipt.json): SHA-256 `3640bf0cbd64e7391921206fa7a7e7d92c7bc932921403c3e7bb3c0e99250bec`.
- [evidence/main-merge-source-transfer.json](evidence/main-merge-source-transfer.json): SHA-256 `56b1a059e00fb44fd015a1d824b0649eabb7b379653c4f635d6135f82ce637d5`.
- [evidence/main-sqlite-host-build/output.log](evidence/main-sqlite-host-build/output.log): SHA-256 `86bbf50995d11a423c00af5fe1986046ee1404afb52e1c0092c977b397235f7d`.
- [evidence/main-sqlite-host-build/receipt.json](evidence/main-sqlite-host-build/receipt.json): SHA-256 `e29715e2aa171844519d5e9ebdd0714b07580ebb0171aeb9683440031aac7f72`.
- [evidence/main-toolchain.json](evidence/main-toolchain.json): SHA-256 `df677ff8d8257313f3fe2b9bb3b053261b0507ff66566bc0257e1eb958bef7b7`.
- [evidence/original-final-gate-v4/output.log](evidence/original-final-gate-v4/output.log): SHA-256 `2628df65f92f1dfd19af19008cf59c779d40026f7cd5276dbd0d3753452edb1a`.
- [evidence/original-final-gate-v4/receipt.json](evidence/original-final-gate-v4/receipt.json): SHA-256 `4ac92b014f137bea143946b5e07afcaf6a4570fb1d67a156285d5c1e52e5f5ad`.
- [evidence/original-final-gate-v4/summary.json](evidence/original-final-gate-v4/summary.json): SHA-256 `6ed575b2126f6e68915a330883c5a6cba3f5340a39232204920406e2f9dc1e04`.
- [evidence/phase_report.py](evidence/phase_report.py): SHA-256 `2d5e0e50072f2f72f370314f270d7470e070c3cacf6e058f3a417ad79d72f851`.
- [final-admission-evidence-audit.json](final-admission-evidence-audit.json): SHA-256 `9751b0b522d4e4c6406188bccaa7e36ade8150f5a4071c7ac6cc100224abca77`.
- [final-admission-evidence-audit.md](final-admission-evidence-audit.md): SHA-256 `c01ad4b0fa6aafe7cf3da6cf335121f4e394710eda3bc4caa9ed1ff0512f59e8`.
- [final-exclusions-and-cache-audit.json](final-exclusions-and-cache-audit.json): SHA-256 `169e47ff85ccd61597ac87577933166df301f822b7d0d9ed86b3ae610075dc93`.
- [focused/output.log](focused/output.log): SHA-256 `0ea70cb1eb54ffc634b024f6c07ad873ddeaf533383ee70172b3f34ecc832e21`.
- [focused/receipt.json](focused/receipt.json): SHA-256 `95bcd9a4571e1da396e799cafc914bed0d11aeaf7a9d30e74fafd245773dc220`.
- [private-candidate-revision.json](private-candidate-revision.json): SHA-256 `b10f8ff3e7cc5859b6bd3de4eca416372d5da3fcdcf4fde0add5385ffbddbb54`.
- [sqlite/control-discard.ash.stderr](sqlite/control-discard.ash.stderr): SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- [sqlite/control-discard.ash.stdout](sqlite/control-discard.ash.stdout): SHA-256 `15ab6332b7cdae5f9b827777c3015e92abbc582eba4d5229299174fc015982b1`.
- [sqlite/control-resume.ash.stderr](sqlite/control-resume.ash.stderr): SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- [sqlite/control-resume.ash.stdout](sqlite/control-resume.ash.stdout): SHA-256 `0decbe46b07127f4ee196a3f90503017b936ef04351e820c68ca6ac88847865d`.
- [sqlite/copying-entry.ash.stderr](sqlite/copying-entry.ash.stderr): SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- [sqlite/copying-entry.ash.stdout](sqlite/copying-entry.ash.stdout): SHA-256 `d398cc600b4b1eb6ab06f5d46112ec902dfb2139f07411564da1643b63513232`.
- [sqlite/pins.json](sqlite/pins.json): SHA-256 `8299ef438eb38fa1b2438c8e319265e1f57a75bf72fcbc9d2482668228f92814`.
- [sqlite/results.json](sqlite/results.json): SHA-256 `cb2050c104912c9d4c44b188722e7ca6f525d595cc276e57a53896528bddd56f`.
- [sqlite/session-entry.ash.stderr](sqlite/session-entry.ash.stderr): SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- [sqlite/session-entry.ash.stdout](sqlite/session-entry.ash.stdout): SHA-256 `74ad6961d0a446c4c13677cfb3724e41e81b300e6a76f3c5a8377541f0ae05be`.
- [sqlite/text-entry.ash.stderr](sqlite/text-entry.ash.stderr): SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- [sqlite/text-entry.ash.stdout](sqlite/text-entry.ash.stdout): SHA-256 `0191907d715aec25edca943617865f207fb54e98ea36d47e94f19fe9c255455b`.
