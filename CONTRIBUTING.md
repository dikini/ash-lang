# Contributing to Ash

Ash is still establishing its language and implementation architecture. Before starting, read the [README](README.md), the [artifact guide](docs/project/artifacts.md), and the artifact that authorizes your work.

Use the artifact that matches the change:

- explore an uncertain question in a design note;
- record a converged non-language choice in an architectural decision;
- propose a language-semantic change in a change proposal;
- organize authorized implementation in a task.

A design note may authorize a bounded prototype or experiment needed to compare candidates. Label it as experimental, state the question and evidence it serves, and do not expose it as Ash behavior or treat it as production architecture. Product implementation still requires an accepted proposal or decision and an active task.

Language changes move from exploration to a proposal, then to implementation, tests, and the specification update that makes the new statements true. Merge those last three together. Architectural changes move from exploration to a decision, then to implementation tasks.

Keep changes narrow. State uncertainty rather than hiding it. Do not use historical Ash, speculative design, tasks, or implementation behavior as a substitute for the canonical specification. If implementation exposes a semantic gap, update the proposal before proceeding.

Follow the [documentation policy](docs/project/documentation.md) and
[writing guide](docs/project/writing.md). Before submitting a change, review
every changed file, verify its required evidence, check relative links, and
confirm that normative and informative statements remain distinct.

## Implementation environment

Ash uses Rust and Cargo as accepted by
[AD-0001](docs/decisions/AD-0001-implementation-environment.md). Rustup reads
`rust-toolchain.toml` automatically and selects the pinned toolchain. Run
`cargo xtask verify` before submitting a change.

Whenever `Cargo.toml` or `Cargo.lock` changes, record the evidence required by
the [dependency policy](docs/project/dependencies.md). Package trouble does not
authorize an automatic toolchain change; review the package, its configuration,
available replacements, or a local patch first.
