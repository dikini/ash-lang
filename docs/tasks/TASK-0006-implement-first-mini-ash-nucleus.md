# TASK-0006: Implement the First Mini-Ash Nucleus

- ID: `TASK-0006`
- Status: active
- Related: [CP-0001: First Mini-Ash Nucleus](../proposals/CP-0001-first-mini-ash-nucleus.md), [AD-0004: Small-Step Semantic Method](../decisions/AD-0004-small-step-semantic-method.md), [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0007: Typed Core Dialects](../decisions/AD-0007-typed-core-dialects.md), [AD-0008: Explicit Evaluator Machine](../decisions/AD-0008-explicit-evaluator-machine.md), [DN-0016: First Mini-Ash Corpus Stratum](../design/DN-0016-first-mini-ash-corpus.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

- CP-0001 is accepted and exclusively owns the language behavior implemented by
  this task.
- AD-0004 through AD-0008 govern the specification method, parser, front-end,
  Core, and evaluator boundaries.
- The [execution plan](../plans/2026-08-21-first-mini-ash-nucleus.md) sequences
  implementation and verification. It is temporary and leaves the tree when
  this task completes.
- The pinned stable Rust toolchain and
  [dependency policy](../project/dependencies.md) govern implementation.
- Implementation runs in an isolated worktree. Integration into `main`
  requires independent review, fresh verification, user confirmation, and the
  required signed merge.

The accepted arbitrary-precision `Int` requires a numeric representation.
Rust's standard library provides only fixed-width integer types. Implementing
and maintaining Ash-owned arbitrary-precision arithmetic would add substantial
correctness, performance, unsafe-code, and review cost without advancing the
language experiment, so a focused existing package is preferable.
The preliminary dependency choice is exactly `num-bigint` 0.5.1 with default
features disabled and only its `std` feature enabled:

- purpose: represent and calculate arbitrary-precision Ash integers;
- role: runtime dependency included in the distributed interpreter;
- source: [crates.io](https://crates.io/crates/num-bigint/0.5.1) and the
  [rust-num repository](https://github.com/rust-num/num-bigint);
- license expression: `MIT OR Apache-2.0`; this supplies clear license
  metadata but does not claim compatibility with Ash's still-unselected license;
- toolchain and targets: upstream declares Rust 1.60 and a pure-Rust
  implementation, below Ash's Rust 1.97.1 pin and without a native-library
  dependency;
- maintenance: version 0.5.1 was current during task planning, and the upstream
  repository showed recent 2026 activity;
- unsafe-code review: upstream uses contained unsafe operations for validated
  UTF-8 conversion, arithmetic CPU intrinsics, and division; optional random
  support also contains unsafe code but is not enabled.

The first implementation step must resolve the transitive graph, rerun advisory
and source checks, inspect every resolved package's machine-readable license
expression or license files, inspect enabled features and target support,
record the exact distributed dependency set, and stop if that evidence
contradicts this preflight. Because Ash has no selected license, this review
collects exact license evidence rather than inventing a `cargo-deny` allowlist.
It must also record `cargo audit`'s expected `RUSTSEC-2021-0090` name-collision
warning for this private workspace package named `ash`; the advisory concerns
an unrelated crates.io package and must not conceal any dependency advisory.

## Work

Implement CP-0001 as one retained Rust pipeline:

```text
UTF-8 source
  -> spanned tokens and logical line boundaries
  -> token-complete error-bearing concrete syntax
  -> recovery-free spanned surface syntax
  -> resolved binders
  -> bidirectional typed elaboration
  -> independently validated pure Core
  -> explicit first-order evaluator machine
  -> rendered value and type
```

The implementation includes:

- the `ash <source-file>` executable;
- the complete CP-0001 positive, negative, diagnostic, invariant, provenance,
  architectural-locality, and deep-machine evidence;
- separate normative specification documents for lexical structure, syntax,
  resolution, static semantics, elaboration, and dynamics;
- user-facing executable documentation;
- dependency evidence required by policy.

No implementation step may add behavior excluded by CP-0001. A semantic gap
returns to the proposal before work continues.

## Progress

- CP-0001 received explicit semantic acceptance.
- The task and execution plan are active.
- Dependency preflight selected `num-bigint` 0.5.1. The resolved-graph review
  below approved that selection for the first implementation increment.
- Product implementation has started with the arbitrary-precision integer
  boundary.
- The typed pure Core families and their consuming independent validator are
  implemented in the task worktree. The composition evidence below retains
  handwritten closed dialect wrappers.

### Dependency review: 2026-08-21

The Rust standard library has no arbitrary-precision integer type. The direct
dependency is therefore exactly `num-bigint = { version = "=0.5.1",
default-features = false, features = ["std"] }`. It is a runtime dependency:
the distributed interpreter will contain its compiled code behind an Ash-owned
`Integer` type. Ash APIs do not expose package-owned types.

`Cargo.lock` resolves this graph from the crates.io registry:

- `num-bigint` 0.5.1 depends normally on `num-integer` 0.1.47 and
  `num-traits` 0.2.19;
- `num-integer` 0.1.47 depends normally on `num-traits` 0.2.19;
- `num-traits` 0.2.19 uses `autocfg` 1.5.1 only while building.

The enabled features are `std` on all three runtime packages and `i128` on
`num-integer` and `num-traits`. `autocfg` has no features. Random-number,
serialization, arbitrary-data, quickcheck, and `libm` support are disabled.
The runtime dependency metadata has no target-specific dependency edges or
native-library targets. Locked checks succeeded on
`x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu`. The packages declare
minimum Rust versions 1.60, 1.31, 1.60, and 1.0 respectively, all below Ash's
Rust 1.97.1 pin.

`cargo search` reported every resolved version as current on 2026-08-21. The
unarchived upstream repositories reported activity in May through August 2026:
`rust-num/num-bigint` last pushed on August 12,
`rust-num/num-integer` on August 12, `rust-num/num-traits` on July 7, and
`cuviper/autocfg` on May 22.

The registry metadata and packaged license files agree:

- `num-bigint`, `num-integer`, and `num-traits` declare
  `MIT OR Apache-2.0` and contain both license texts;
- `autocfg` declares `Apache-2.0 OR MIT` and contains both license texts.

The three rust-num packages have identical packaged license-file hashes:
Apache-2.0 `a60eea817514531668d7e00765731449fe14d059d3249e0bc93b36de45f759f2`
and MIT `6485b8ed310d3f0340bf1ad1f47645069ce4069dcc6bb46c7d5c6faf41de1fdb`.
`autocfg` has the same Apache-2.0 hash and MIT
`27995d58ad5c1145c1a8cd86244ce844886958a35eb2b78c6b772748669999ac`.
None of the four packaged crates contains a `NOTICE`, `COPYING`, or separate
copyright file. Their only packaged licensing files are `LICENSE-MIT` and
`LICENSE-APACHE`. The rust-num MIT text identifies “The Rust Project
Developers” as the 2014 copyright holder. The `autocfg` MIT text identifies
Josh Stone as the 2018 copyright holder.

A later distribution review must evaluate both alternatives for the embedded
runtime packages `num-bigint`, `num-integer`, and `num-traits`:

- under the MIT alternative, copies or substantial portions must include the
  applicable copyright notice and the MIT permission notice;
- under the Apache-2.0 alternative, recipients must receive a copy of the
  Apache-2.0 license, modified files must carry prominent change notices, and
  a distributed source form must retain applicable copyright, patent,
  trademark, and attribution notices. Apache-2.0's additional NOTICE
  redistribution condition is not triggered by these locked packages because
  none includes a NOTICE file.

`autocfg` is a build dependency and is not embedded in the distributed
interpreter. If Ash later redistributes that package itself, the corresponding
MIT or Apache-2.0 obligations above must be evaluated using its Josh Stone
copyright notice. This record supplies the obligations for later compatibility
and packaging review; it neither selects a license alternative nor claims
compatibility while Ash's license remains unselected.

`cargo audit` succeeded with no dependency advisory. It emitted the expected
allowed `RUSTSEC-2021-0090` warning because the private workspace package is
named `ash`; the advisory applies to an unrelated crates.io package.
`cargo deny check advisories sources bans` also succeeded with its default
configuration. A license allowlist was intentionally not created.

Source inspection found no unsafe blocks in `num-integer` or `autocfg`.
`num-bigint` uses validated unchecked UTF-8 construction when rendering,
x86/x86-64 add-carry and subtract-borrow intrinsics, and x86/x86-64 division
assembly with a checked operand invariant. Its random-generation module also
contains an unsafe slice construction, but that code is excluded because no
random feature is enabled. `num-traits` uses an unchecked float-to-integer
intrinsic only after bounds and finiteness checks. Mini-Ash uses no random,
division, subtraction, or float-conversion API in this increment, and its own
integer wrapper remains safe Rust.

## Verification

Completion requires every item in CP-0001's Required evidence section and the
execution plan's final evidence matrix. At minimum:

- `cargo xtask verify`;
- direct unit and integration tests for every accepted semantic stage;
- end-to-end corpus, diagnostic, CLI, large-integer, provenance, validator,
  transformation, locality, and deep-frame tests;
- independent review of implementation, tests, normative specification, tool
  documentation, dependency evidence, and authority boundaries;
- Markdown lint plus relative-link, anchor, formal-notation, and verbal-
  explanation review;
- a clean worktree and confirmation that no disposable probe or temporary
  execution plan remains in the completed merge.

## Discoveries

The accepted semantics require arbitrary precision. The resolved dependency
review supports retaining `num-bigint` 0.5.1 behind an Ash-owned integer type.
It also found reviewed unsafe float conversion in the transitive `num-traits`
package in addition to the `num-bigint` sites noted during preflight.

The Core composition gate compared the current handwritten assembly with
generic injection helpers. Eight small `CoreBuilder` methods in
`core::dialect` are the only construction sites that wrap feature-owned
payloads. Generic injection would add traits and type parameters without
removing the dialect's required closed dispatch, so the implementation retains
the handwritten assembly.

The pure-feature probe adds a test-only `mock_feature` module to a shadow
dialect that explicitly mirrors the value, variable, and computation layers.
With transformation included, the addition changes exactly seven sites: the
feature module, the `ShadowExprKind` closed assembly, the `mock_shadow`
construction site, and the top-level validation, child-traversal,
transformation, and consumer dispatches. Existing feature payload modules and
their helpers do not change. The probe checks feature-owned structural types
and exact child handles: functions expose one child; bindings, applications,
and primitives expose two; literals, variables, and the mock expose none.
Temporarily omitting the mock arm from `consume_shadow` produced Rust error
`E0004` for the uncovered `ShadowExprKind::Mock` case; restoring the arm made
the architecture test pass. The contrary evidence is explicit: a feature
addition remains local, but every closed consumer still needs one exhaustive
dispatch arm.

The separate operation-family probe defines an uninhabited test-only pure
operation type and a mock future operation family. A test-only typed
`Computation<F>` boundary contains either a production `PureComputation` or an
operation from `F`, with a structural result type on both arms. Its pure
instantiation contains a validated primitive computation, and the compiler
treats the pure pattern as irrefutable because the pure operation type has no
inhabitants. The mock request crosses the operation arm of the same boundary
without changing a pure feature payload or adding an operation variant to
`PureExprKind`. This is compile-time evidence for the future seam only;
Mini-Ash Core contains no effect operation, continuation, handler, CPS region,
or placeholder `Impure` node.

An arena-local numeric index alone allowed a handle from one `CoreBuilder` to
alias the same index in another builder. `NodeId` now pairs that index with a
lazily allocated process-local arena identity. The allocator reserves its
maximum value as an exhaustion sentinel. Construction rejects a foreign root,
independent validation rejects a foreign child, and validated lookup rejects a
foreign handle even when its numeric index exists locally. The identity remains
an implementation handle, not a stable language identity.

The first scope pass revisited a shared child once per incoming path. A chain in
which each primitive used its predecessor twice therefore expanded
exponentially. The validator now computes free-binder requirements once per
arena node in iterative DAG postorder and retains one occurrence handle for
each required binder. A 65-node doubled-edge chain records exactly 65 analyzed
nodes. Requirement-map copying costs the sum of copied map sizes and can remain
quadratic for an adversarial DAG with many distinct free binders; it no longer
expands shared paths exponentially.

Public `Type` and `Origin` values use recursive ownership outside Core. Core
admission now consumes and rebuilds both payloads iteratively before allocating
an arena, constructing a binder, or storing a node. The current replaceable
resource budget admits 128 recursive wrappers, aligned with the parser's
structural budget; this is compiler resource behavior rather than Ash
semantics. Exact-limit Type, Generated Origin, and Related Origin payloads
validate and drop on a 256 KiB stack. Payloads at 129 and 50,000 wrappers return
distinct typed construction failures, and the rejection path dismantles both
inputs iteratively.

The complete resolver-assigned binder namespace is reserved transactionally in
`CoreBuilder` before binder construction starts. Generated binders skip the
whole reserved set, including sparse high identities. Resolved materialization
requires a reservation and succeeds once per identity; later reservation is a
typed phase failure. Failed payload admission leaves the reserved namespace
intact but does not materialize the binder, so a corrected payload can be
retried. Independent validation still rejects a cloned binder used at two
definition sites.

Numeric binder identity alone allowed a `TypedBinder` from one `CoreBuilder` to
be inserted into another builder whose next generated binder had the same
number. `TypedBinder` now carries a private arena capability established by
successful binder construction after payload admission. Function and binding
construction reject a capability from another arena without adding a node or
consuming a binder identity. A 50,000-wrapper payload probe on a 256 KiB stack
confirms that payload resource failures take precedence and dismantle their
inputs before the foreign-capability error. Independent validation also rejects
a privately corrupted binder capability under its existing scope-invariant
reason, while same-arena cloned definition reuse remains independently rejected.

The retained Core transform uses explicit postorder work data. Feature payload
modules own their child lists, while `PureExprKind` is the one closed child
dispatch. Identity traversal preserves every type, binder identity, and origin
in V-008, and a separate shared-DAG case preserves graph sharing. Literal `Add`
and `Multiply` nodes fold only when both immediate operands are literal nodes.
A fold produces an `Int` literal with `ConstantFolding` provenance caused by
the replaced operation, then returns to unchecked Core and independent
validation. It does not fold integer equality or add a general optimizer
framework. Pre- and post-transform values agree; identity traces agree through
the old-to-new node mapping, while folding traces omit the replaced operation
and operands.

Successful checking now records a `TypeChecking` origin on the checked Core
root. The original expression remains the primary cause and an explicit
annotation supplies the related expected-type span. Function provenance also
retains the equation body or operational body as an explicit relation in
addition to the equation, interface, definition, and operational header. The
T-001 and T-004 tests confirm that their diagnostic causes still point to the
equation body and declared result or argument type after both presentations
converge to shared Core.

The parser-locality probes measured four changed test sites for a mock
operator: its feature descriptor, test-only operator token, token matcher, and
closed operator table. The isolated descriptor parses an actual semicolon-token
expression through the production precedence engine without adding it to the
selected Mini-Ash dialect. This is contrary evidence against treating the
current token enum and matcher as one physical feature site. The mock nested
form also measured four changed sites: its feature parser,
closed prefix variant, closed prefix assembly entry, and closed prefix dispatch.
The production infix table remained unchanged. These are parser-layer
measurements. A real new spelling or concrete node would also require its owning
lexer, concrete syntax, and projection changes; the probes do not claim
otherwise. A changed Boolean type-equality outcome affected exactly one test-
only rule helper and left the caller and unrelated `Int` outcome unchanged. The
foreign-dialect probe remains an unchecked storage-envelope mutation rejected
by independent dialect validation, not a new `PureExprKind` variant.

The evaluator now separates its closed entry and return dispatches from
feature-owned transition helpers. Its transition-ownership matrix is:

| Core feature | Entry helper | Explicit frames | Return helpers |
| --- | --- | --- | --- |
| Integer | `enter_integer` | None | None |
| Boolean | `enter_boolean` | None | None |
| Unit | `enter_unit` | None | None |
| Function | `enter_function` | None | None |
| Variable | `enter_variable` | None | None |
| Binding | `enter_binding` | `Bind` | `return_binding` |
| Application | `enter_application` | `ApplyFunction`, `ApplyArgument` | `return_application_function`, `return_application_argument` |
| Primitive | `enter_primitive` | `PrimitiveLeft`, `PrimitiveRight` | `return_primitive_left`, `return_primitive_right` |

A test-only mock pure evaluator feature changes exactly two evaluator sites:
its entry helper and the mock arm in the closed entry dispatch. Existing entry
and return helpers do not change. A suspending future feature could still need
a new frame variant and return-dispatch arm; the probe demonstrates transition
ownership, not open evaluator dispatch.

A validated Core chain of 10,000 left-nested additions evaluates and drops on a
256 KiB host thread stack. Identity traversal and revalidation complete on the
same thread. Evaluation records exactly 10,000 simultaneously retained
explicit frames and 20,001 entry events, so source depth grows machine storage
without proportional Rust call depth. Separate end-to-end and machine tests
cover literal, sum, product, equality, rendered output, and traced integer
nodes beyond both signed and unsigned 64-bit ranges.

## Deviations

None.
