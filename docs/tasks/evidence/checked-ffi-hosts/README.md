# Static checked foreign-host evidence

This checkpoint implements scalar host checking and independent Core
correspondence. It supplies no checked native execution, owner lifecycle,
Linux containment, complete F3 acceptance or full workspace gate.

[Verification](verification.json) records commands, exits, source/configuration
pins and exact raw output. The common [manifest](source-configuration.json)
includes every regular file under `src/` and `tests/`, plus `Cargo.toml`,
`Cargo.lock`, `rust-toolchain.toml`, `.cargo/config.toml` and `build.rs`.
Its aggregate is SHA-256 of UTF-8 JSON with sorted keys and separators `(',', ':')`,
without a trailing newline. Each value is SHA-256 of the file's exact bytes;
keys are repository-relative POSIX paths. Every final command independently
compared its before/after manifest with this common manifest.

The final tests include static source/Core positives, lexical and forged-mode
negatives, exact/one-short/fresh work boundaries, sealed builtin reconstruction,
legacy image/owner regressions and an actual generated legacy build/run. Owner
callback cases are injected legacy tests. The generated regression uses compiler
scalar checks without native links. Neither establishes checked native execution.

The two retained red logs precede the final repair and have their own manifests.
The first exposed synthetic Host metadata missing parsed effect coordinates in
original-source admission. The diagnostic second run, with temporary test-only
tracing, isolated projected builtin local14 encountering expected local4. Exact
resident-source/role reconstruction and an original-slot proof now account only
for absent legacy builtin locals4..13. Generic contiguity, kinds and scope checks
remain in force. The temporary traces are absent from the final source.

Raw Cargo output is preserved byte for byte, including blank lines at EOF.
Whitespace checks exclude captured `.log` files; they cover source, specification,
task, plan and JSON evidence. The test runner is an operator capture mechanism,
not an additional product validation path.
