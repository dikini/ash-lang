# Dependency policy

This policy applies to Rust packages used for compilation, runtime behavior,
builds, development, and tests.

## Required evidence

Every direct package requires a recorded purpose, dependency role, source,
version requirement, target support, maintenance state, advisory review,
unsafe-code review, license expression, and effect on distributed artifacts.
Review the resolved transitive graph as well as the direct package.

## License compatibility

Evaluate license compatibility as
`compatible(Ash license, dependency license, distribution role)`. The Ash
license is currently an unspecified parameter. Do not replace it with a
provisional allowlist or claim compatibility before the project selects it.

Before that selection, require a machine-readable SPDX expression or a reviewed
license file and record all obligations needed for the later evaluation.
Missing, ambiguous, or unverified license information prevents approval.

## Review procedure

1. State why the standard library or an existing package is insufficient.
2. Classify the package as compiler, runtime, build, development, or test use.
3. Inspect direct and transitive sources, versions, features, targets, advisories,
   license data, unsafe code, and distribution effects.
4. Record the evidence in the task or change that introduces the package.
5. Run the workspace verification command with the updated lockfile.
6. Review this evidence again whenever `Cargo.lock` changes.

Package incompatibility with the pinned stable toolchain prompts review of an
upgrade, feature configuration, replacement, patch, or removal before any
toolchain change. A toolchain downgrade requires explicit review.
