# AD-0014: Rust verification stage reuse

- ID: `AD-0014`
- Status: accepted
- Related: [AD-0001](AD-0001-implementation-environment.md),
  [AD-0011](AD-0011-milestone-worktree-lifecycle.md),
  [TASK-0042](../tasks/TASK-0042-rust-verification-performance.md)

## Decision

Keep default-feature all-target type checking and default-feature library,
binary and example linkage. The all-feature test stage builds and runs test
executables once; the default-feature build no longer links a second set of
test harnesses. Formatting, locked metadata, strict workspace Clippy, workspace
tests and rustdoc with warnings denied remain required.

`cargo xtask verify` runs fresh verification by default. Explicit stage
selection produces partial evidence. Explicit reuse can complete a gate from
successful local stage receipts whose exact commands, working-tree inputs,
configuration and saved logs still match. Reports distinguish executed stages
from reused stages. A partial run never establishes a complete gate.

The first implementation uses a conservative whole-repository input pin rather
than guessing which tests read which files. Source and configuration must match
before and after each executed stage. Failed or moved-input runs cannot create
reusable success. A missing, malformed, incompatible or changed receipt/log
causes fresh execution. Receipts are trusted local execution records, not
signed attestations or replacements for independent review.

Reuse binds to the checkout path, tool versions, effective environment and
Cargo configuration. Git-visible inputs include untracked, non-ignored files.
Additional external inputs must be named explicitly. Changes to ignored
fixtures, unrecorded host dependencies or an uncertain environment require a
fresh run. Required final integrated gates remain fresh unless their governing
artifact explicitly accepts transferred evidence.

## Context

The user authorized duplicate-compilation removal and verification reuse after
the ffi-ash gate audit, with coordination and before/after measurements. PR #16
took 1,623.23 seconds: default-feature build 659 seconds, Clippy 97 seconds,
all-feature test compilation 391 seconds, test execution 427.28 seconds and
rustdoc 34.34 seconds. The candidate had 125 Ash integration-test targets.

Keeping the existing command matrix preserves repeated test-harness linkage.
Making every build all-feature would lose explicit default-feature coverage.
Default-feature checking plus product linkage and one all-feature test stage
preserve those distinct obligations with less duplicate code generation.

Conservative exact-input reuse initially addresses repeated pre-publication
checks, unchanged retries and retaining-tree equality. Dependency-specific
reuse after Markdown or test changes needs a demonstrated input model and is
outside this delivery. Test removal, test concurrency, production compiler
profiles, runtime fingerprint algorithm changes and production budget changes
are also excluded.

The xtask alias uses an optimized verification-only profile so hashing the
whole checkout does not become another gate delay. The product commands keep
their default profiles. Repeated references to one executable are hashed once
per snapshot; snapshots still re-read their inputs across stage boundaries.

Measured milestone candidate `dd3239e` includes the root manifest and lockfile
in its matching-compiler fingerprint. The tooling overlay therefore changes
that candidate's identity even though its fingerprint algorithm and product
sources are unchanged. Measurements must record the overlaid
source/configuration identity and retain required native and embedded-image
proof under the original product configuration separately.

## Consequences

The workflow can share verification evidence across its developer, reviewer
and integrator without silently skipping required checks. Local receipts retain
commands, logs, pins and timings. Deleting them affects performance, not truth.
Changes to any repository input invalidate all stage receipts conservatively.
Milestone workers continue to serialize heavy builds and freeze inputs.

## Verification

Test command coverage, explicit partial selection, successful reuse, source,
configuration and external-input invalidation, changed/missing logs, failed
commands and moved inputs. Measure old and revised command plans serially on
the same frozen milestone sources and configuration, with comparable cache
states. Record reused time separately from fresh-gate time and retain logs.
