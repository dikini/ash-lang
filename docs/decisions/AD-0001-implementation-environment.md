# AD-0001: Implementation Environment

- ID: `AD-0001`
- Status: accepted

## Decision

Ash uses stable Rust and Cargo for its compiler, interpreter, and runtime implementation.

The repository pins a specific stable Rust release so local development, automated checks, and release builds use the same compiler and Cargo version. The project reviews each new stable release promptly and updates the pin unless a documented incompatibility prevents it. A package incompatibility prompts review of the package, its configuration, available replacements, or a local patch before the project considers changing the Rust version. A toolchain downgrade requires explicit review.

The first execution path is an interpreter for the functional Core language. It is the start of an evolving implementation, not disposable bootstrap code or a permanently privileged semantic oracle. Later REPL, AOT, and JIT paths should reuse representations, validation, transformations, diagnostics, and runtime services when that reuse does not reduce their quality.

Shared compiler components remain independent of execution backends. LLVM, MLIR, Cranelift, and other backend types must not appear in Core or its transformations. MLIR is a possible future lowering target, not an implementation-environment dependency.

Safe Rust is required for semantic representations and compiler transformations. Unsafe Rust is permitted only in isolated runtime, FFI, or backend adapters whose invariants and verification are stated. Compiler phases use explicit types and validate their IR after construction, parsing, and transformation. A linked compiler-generated executable reconstructs the compiler-verified representation without repeating its semantic validation, as specified by [AD-0013](AD-0013-generated-native-bridges-and-program-builds.md).

Ordinary x86-64 and ARM64 desktop and server systems are development hosts. The interpreter and runtime must remain suitable for application-class x86-64 and ARM64 hardware, including Raspberry Pi-class systems. Mobile hardware is a deployment consideration even when an operating-system policy or distribution agreement prevents a particular execution model. Microcontrollers are not an initial requirement.

The repository commits `Cargo.lock`. Each direct package dependency requires a stated purpose and a classification as compiler, runtime, build, development, or test support. Dependency review records its source, license expression, supported targets, maintenance state, use of unsafe code, and presence in distributed artifacts.

License compatibility is evaluated as a relation among the future Ash license, the dependency license, and the dependency's distribution role. This decision does not select the Ash license or define a license allowlist. Until the project selects a license, dependency checks collect and validate the information needed for that later evaluation. Missing, ambiguous, or unverified license information prevents dependency approval.

## Context

The first Ash implementation must support typed, inspectable compiler representations, explicit continuation data, reliable traversal and rewriting, parser diagnostics and recovery, IR validation, and a reproducible contributor setup.

Deployment reach constrains the environment more than compiler-host reach. Compiler development will usually occur on desktop or server systems. Ash programs should eventually run wherever application-class processor and memory resources are sufficient, including ARM64 single-board computers and mobile-class hardware. The first interpreter therefore matters both as compiler code and as deployed runtime code.

Memory safety and a sound, expressive static type system are minimum requirements. Ash may adopt stronger verification methods over time, but the host language need not provide refinement or dependent types.

Three implementation shapes were considered:

- Rust for the compiler, interpreter, and runtime gives the broadest direct deployment support and keeps the shared implementation in one language. Rust ownership makes some graph representations and transformations more deliberate.
- An OCaml compiler with a Rust runtime gives concise functional representations but creates a permanent language boundary. The initial interpreter would either inherit the host runtime's deployment limits or duplicate execution work in Rust.
- A Haskell implementation gives stronger host type-system expression for some compiler invariants but places more deployment weight on the GHC runtime and cross-compilation support. Separating the runtime would again create a second implementation language.

The platform, safety, typing, reuse, and runtime requirements distinguish these choices without implementing the same Core and parser prototype in every host language. The first typed-Core work will still test the main Rust-specific risk: whether the selected representation expresses typed transformations and validation without distorting the compiler architecture. A serious mismatch is evidence to revisit this decision.

## Consequences

- Rust and Cargo become required contributor tools.
- The project tracks current stable Rust while retaining reproducible builds through an explicit toolchain pin and lockfile.
- Dependency selection includes platform, safety, maintenance, and license evidence rather than package functionality alone.
- Compiler and runtime packages may share one workspace without sharing every execution-engine component.
- Backend adapters consume Ash-owned lower representations and do not determine Core architecture.
- The initial workspace and checks can be established before parser or Core representation work converges, removing a circular dependency among those decisions.
- Rust ownership and external native-library interfaces remain implementation risks. Core representation work and future backend tasks must test them where they arise.
- This decision does not define Ash syntax, semantics, Core representation, parser architecture, project license, or a future code-generation backend.

## Verification

Automated checks must provide the following evidence as the corresponding components enter the repository:

- the workspace builds with the pinned toolchain and committed lockfile;
- formatting, linting, tests, and documentation checks pass across the workspace;
- required development hosts run the workspace tests;
- required deployment targets compile, and platform claims receive native execution tests before release;
- dependency source, advisory, license, target, and unsafe-code information is checked whenever `Cargo.lock` changes;
- semantic and transformation components forbid unsafe code;
- first-party unsafe code is isolated and documents the invariant that makes each use sound;
- malformed Ash input produces structured diagnostics rather than panics;
- IR construction and transformations include positive tests, rejected invalid cases, and invariant-preservation checks;
- independently implemented execution paths receive differential tests when they are expected to agree;
- specification-conformance tests accompany normative functional-Core behavior when that behavior is implemented.

If a required check cannot run on every change, the governing task must state when and where it runs and what evidence substitutes for it in routine development.
