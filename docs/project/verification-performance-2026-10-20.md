# Rust verification performance record — 2026-10-20

This record closes TASK-0042's controlled comparison under
[AD-0014](../decisions/AD-0014-rust-verification-stage-reuse.md).
It records tooling evidence, not Ash language semantics. The implementation
was already integrated through PR #18 (`4716b960`) and Main delivery
`354c76b3`; the comparison was the remaining task obligation.

## Retained behavior and findings

The runner checks every default-feature target, links default-feature product
libraries, binaries and examples, and builds/runs all-feature tests once.
All-feature tests cannot replace default-feature checking. Plain verification
is fresh; explicit stage selection is partial. Explicit reuse requires exact
successful local receipt, log, source, configuration, environment, tool and
external-input equality. Failed or moved-input commands cannot publish reusable
success. These boundaries and operating commands are documented in the
[verification guide](verification.md).

Generated native Cargo roots retire after staging the copied executable and
before publication. Package-scoped cleanup preserves shared dependencies and
current tests; private generated caches retire completely. Link, copy and
cleanup failures preserve the existing destination and diagnostic log.
Caller-owned source, manifests, payload and logs retain their own lifetime.
The [build tool guide](../tools/ash.md) documents that behavior.

The full current suite exercises all 17 xtask regression cases and five
artifact-cleanup unit cases. Coverage includes explicit partial/fresh/reused
runs, changed or missing logs, failures, source/configuration/environment and
external-input movement, permissions, PATH/compiler/wrapper delegation and
cleanup failure paths. Historical focused cleanup checks and the immediate
seven-stage reuse witness at `1325097` remain dated evidence in that task's
Git history; no new reuse witness was measured for this closure.

## Controlled comparison

Both command plans ran serially on frozen current commit
`56ad7d66a854addedd19d3824e2ab65410e5d6eb`, tree
`32d9804bcbb1c5876a80ffdd6b78e448319ca80d`.
Main remained `3bde9db1c0be9b8cf8a5fadf1ea7a154933ae032`.
Historical `847b78f` supplied only the old command array, not product sources.
The existing physical `.worktree/generic-cells` checkout and its `target` and
`target/ffi-native-hosts` caches stayed at the same paths. Compatible caches
were neither copied nor
cleared wholesale or made cold.
Package-scoped generated-root cleanup continued normally.
One Cargo job was enforced.

Both plans ran formatting, locked no-dependency metadata, strict all-target
all-feature Clippy, all-target all-feature tests and warnings-denied workspace
rustdoc without dependencies. Old six additionally used
`cargo build --workspace --all-targets --locked`. Revised seven replaced that
with `cargo check --workspace --all-targets --locked` and
`cargo build --workspace --lib --bins --examples --locked`.
The frozen recipe retains every argument.

Three untimed preparation commands warmed the union of required artifacts:
default all-target build, default all-target check and the identical
`RUSTDOCFLAGS="-D warnings"` documentation command. They took 0.656, 0.450
and 0.212 seconds respectively in the accepted attempt. The measured commands
reported no relevant outer compilation, checking or documentation generation.
Both leg starts had identical default-feature and all-feature outer test
fingerprint sets (549 records), and all 182 shared native artifact/fingerprint
records, including compiled-library
path, mode, size and modification time. Retained native build logs showed only
new generated host roots, with no shared Ash/dependency recompilation.

The direct pinned optimized current xtask executable ran the revised gate;
old commands ran under the same explicit base environment, avoiding Cargo
alias environment injection. The same `ASH_OWNER_EVIDENCE_DIR` value covered
both legs. All 30 named external full records, actual tools, Cargo configuration
and canonical environment pins matched before/after. Documentation children
alone added the same `RUSTDOCFLAGS` override. Environment values are hashed in
input records; the recipe records explicit overrides, not their complete
plaintext environment.

| Cargo subprocess | Old six seconds | Revised seven seconds |
| --- | ---: | ---: |
| format | 6.744 | 7.142 |
| metadata | 0.016 | 0.015 |
| check | — | 0.385 |
| build | 0.332 | 0.224 |
| clippy | 0.315 | 0.365 |
| test | 1135.075 | 1244.570 |
| documentation | 0.318 | 0.359 |
| Total | 1,142.801 | 1,253.060 |

The revised command total was 110.259 seconds (9.65%) slower in this one
ordered warm old-then-revised sample. Most of the difference was in test time;
the observation does not attribute it to the runner, algorithm or concurrency.
It establishes neither a general speedup nor a general regression, and says
nothing about cold-build duplicate-link savings. No valid pair was repeated
to seek a favorable result.

The actual current runner took 1,274.316 seconds; its 21.256-second remainder
above child time includes input/tool snapshots, hashing, receipt/log handling
and dispatch. It is not a measurement of hashing alone. The old Python
observer/controller took 1,163.094 seconds, including a 20.293-second remainder;
that is not historical old Rust-runner wall time. Common observer operations,
preparation, storage observation and post-run authentication remain separately
recorded. Exact model runtime is unavailable; requested developer settings were
`gpt-6.1-sol` / `medium`, without an independent effective-settings API.

## Fresh checkpoint and native proof

The revised leg passed all seven stages freshly, with zero reuse. Both legs'
140 outer harness identities exactly matched metadata: 133 integration targets,
two libraries, two binaries and three examples. Two custom-build targets were
excluded from the metadata count of 142. Each leg passed 4,112 tests, failed
none, ignored one optional calibration test and filtered none. Nine nested
summaries were retained separately and excluded from those totals.

Each leg retained 63 actual owner-host observations outside the build cache.
C06's permitted and denied programs retained all 19 files per host. Their case
preimage hashes and entry/owner/native/static-link tuple matched the case keys.
The generated host constants and compiled ELF contain runtime fingerprint
`1726d5f5b691a5d5ec0dc8a2e435e907fa43412284ebae7ff4e7a035cdc704e2`.
This is the all-feature/resource-calibration-matched configuration, not a claim
that the historical default-feature identity changed. Each ELF embeds the
exact retained serialized program image; fingerprint matching is a separate
generated-host compile-time check.

The permitted execution returned `Completed(42, RetainedError(()))`, exit zero
and native parent byte 99. Denied post-quarantine ordinary access exited one
with the control-state diagnostic, empty stdout and parent byte zero. Both
traces showed parent acquire at 64 bytes, child acquire at four bytes, child
retention and exactly one child release followed by exactly one parent release.
Readback retains actual native symbols, ELF header, compiler
comment, interpreter, dynamic dependencies and resolved-library byte pins.
The genuine static SQLite archive used SHA-256
`7c2b4dc4aa149543e60252b5fffcb62088398470a09885cebb5e3120459c0617`;
its actual pinned source/header/object/archive and native tools were checked.

## Refused attempt and storage

The first closure attempt is retained as an invalid comparison. Its six
commands exited zero, but rustdoc regenerated Ash documentation, violating the
reviewed warm condition; the revised leg never launched. Cargo's documentation
fingerprint included the task Markdown modification time. Build/check warmup
had not warmed that dependency. The separately reviewed repair added the exact
untimed warnings-denied doc command and preserved the strict measured refusal.
No product source or measured guard changed to accept the first attempt.

All 1,263 first-attempt records and the original generic-cell gate/native
evidence remain preserved. The accepted attempt added 59,764,244,480 allocated
record bytes, with zero cache growth from its 177,803,362,304-byte baseline.
Terminal free space was 98,370,674,688 bytes, above the reviewed 60-GiB floor.
The active compatible cache and all other worktrees remain owned by their
existing users; this closure authorizes no further cache retirement.

## Durable receipts

Raw local records are outside build output at
`.worktrees/task0042-closure-20261020/attempt-2/` in the repository's primary
checkout. They include the recipe/operator, command logs, actual current stage
receipts, input snapshots, native hosts, native readback and disk observations.
The refused first attempt remains in the parent evidence directory.

Recipe SHA-256:
`33c820540f6dda848a2d121aa69d0ccffee19a2fc6c2f424776b8b93c90756bd`.

Operator SHA-256:
`e6f344b80ff20944f5161cf8331f407ccea90dc2790411309dc4f2f4d82381e9`.

Frozen/final input JSON SHA-256:
`e9dd52c219b7b1b4f27bae40ce34b06cc91842b095dbbc614e4697d1c03bf534`.

Terminal success SHA-256:
`0480f615cbf597440e6825611fbbb92054b50a3afcdd9eda995787af95cba787`.

Native readback SHA-256:
`8386ff76db312d8feb38207349b687ee4094e13a96a0825f9d610757865f74ce`.

Old-leg record SHA-256:
`9f42f779253d95af6d833e39cb7fdd1f15cc66e2d9099594aee157645c3ffffe`.

Revised-leg record SHA-256:
`cafbc1d90976394525f48bfad3e72fdc1ceadac9abae25832c5b9d003acc60fa`.

### Fresh format receipt

Receipt SHA-256:
`330ba4ae719c4f4076d4d0a1c3d7b77326bb3a4b1eeb9d746af7bcc8552a0c75`.

Log SHA-256:
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

### Fresh metadata receipt

Receipt SHA-256:
`e0bd7f65951f11fab22b9b6f65be75f2b3538d3541ca8a10bbba18078d7fa3b0`.

Log SHA-256:
`6b5d88f0feb5de4b5f95039b3ffcf291c493b3d92b663658264b8cb2ac8c37a7`.

### Fresh check receipt

Receipt SHA-256:
`55c0afdde2e7643379c8eb7c0c16f55511766d6314157078362f44ba81518a3a`.

Log SHA-256:
`2461b00c8697c4189b2de92ca6fb05b5d72273c78a0a47b1ce4e83ccca077b70`.

### Fresh build receipt

Receipt SHA-256:
`eff0a945e0b656eaa677b06e691a99e2d16a1eef85e34a5f2370f2ca756c1944`.

Log SHA-256:
`732186322402325172940531d8d6d7cfac85dc902585b2bef6715ad6839dacfd`.

### Fresh clippy receipt

Receipt SHA-256:
`4aeb8d9a7ed6e1251d3a2bf85294ae298251d7f3a752dc80f3be950189958d3f`.

Log SHA-256:
`4f27ac380b22e1d975eee20ce727fa8cbc09061177f6253af0777fd4de7b7506`.

### Fresh test receipt

Receipt SHA-256:
`d30360b191da513127705dee9b38a1a5ddb57b37e8f33fc624bcd34ef2e90095`.

Log SHA-256:
`e2a4705569454b61bf3ff61cda7115b3eb909ecdbe76c1bbe6f1238603039ce2`.

### Fresh documentation receipt

Receipt SHA-256:
`360feb1afa1d8256911842a76498d77008b835ad926429952659378363cbc4fe`.

Log SHA-256:
`5cef694037da908680415c93dba95293cebd0547f3394ec7ad06a50d5b013670`.

## Dependency and retention boundaries

The implementation added xtask dependency edges for existing resolved serde
`1.0.229` (derive), serde_json `1.0.151` and sha2 `0.10.9`, rather than new
runtime/foreign ABI dependencies or custom cryptography. The original review
recorded MIT-or-Apache-2.0 licensing, with transitive MIT, Unlicense-or-MIT and
Unicode-3.0 notice obligations; Ash's unspecified license prevented a final
compatibility claim. First-party xtask forbids unsafe code. Dependency source
inspection was a role/safety review, not an independent audit. The historical
2026-08-21 advisory-database observation is not a current security claim.
The complete dependency/license review remains in TASK-0042's Git history.

This measured configuration is Linux x86-64 with pinned Rust 1.97.1. The runner
requires Git and UTF-8 names; shell fixtures are Unix-specific. Other target
performance is unmeasured. Product profiles, tests, compiler/runtime identity
algorithm and work/depth/stack limits were unchanged.

The full fresh gate binds to `56ad7d66` and its all-file input pin. Later
completion and retirement Markdown changes do not inherit that exact receipt
identity. Their acceptance requires manual Markdown, link and authority review
plus demonstrated equality of executed source, configuration, tools and native
inputs. Any later executable/configuration change requires affected fresh
checks before integration. Main integration and origin synchronization are
separate retained-ref checks assigned by the PM after closure review.
