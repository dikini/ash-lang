# Design notes

Design notes record exploration, research, alternatives, experiments, tradeoffs, uncertainty, and future architectural pressure. They are informative and do not define Ash semantics or accept architecture. A note may govern a disposable prototype limited to its stated question, comparison cases, and retention conditions when code is necessary to compare candidates; the prototype remains evidence rather than product implementation.

Use [the template](template.md), allocate the next `DN-NNNN` ID, and link related artifacts. When a non-language choice converges, record it in an architectural decision. When a language-semantic change becomes concrete, write a change proposal.

## Current notes

### Foundations

- [DN-0001: Ash Reboot Foundations](DN-0001-reboot-foundations.md)

### Immediate architecture

- [DN-0002: Core Representation](DN-0002-core-representation.md)
- [DN-0003: Parser Architecture](DN-0003-parser-architecture.md)
- [DN-0004: Implementation Environment](DN-0004-implementation-environment.md)

### Surface language, typing, and elaboration

- [DN-0005: Surface Function Definitions](DN-0005-surface-function-definitions.md) — equational and operational function presentations and their elaboration.
- [DN-0006: Initial Type System](DN-0006-initial-type-system.md) — candidate first-nucleus kinds, types, polymorphism, inference, and unification.
- [DN-0007: Data and Pattern Typing](DN-0007-data-and-pattern-typing.md) — products, ADTs, visibility, patterns, irrefutability, and coverage.
- [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md) — explicit typed Core, representation contracts, execution, and semantic policy seams.

### Effects and dynamic composition

- [DN-0009: Effects, Handlers, and Continuations](DN-0009-effects-handlers-and-continuations.md) — effect APIs and rows, handler composition, and continuation contracts.
- [DN-0010: Identities and Resource Lifetimes](DN-0010-identities-and-resource-lifetimes.md) — static/runtime identity, ownership, withdrawal, and captured resources.
- [DN-0011: Modules, Providers, and Resolution](DN-0011-modules-providers-and-resolution.md) — passive modules and typed composition at static-link and runtime-load stages.
- [DN-0012: Coeffects and Hooks](DN-0012-coeffects-and-hooks.md) — typed handler hook points, subscription, composition, effects, and lifetime.

### Downstream type-system stress and exploration

- [DN-0013: Session and Resource Protocol Stress Tests](DN-0013-session-and-resource-protocol-stress-tests.md) — tests for protocol, multiplicity, continuation, and handler composition machinery.
- [DN-0014: Finite Kinds and Promotion](DN-0014-finite-kinds-and-promotion.md) — finite nominal static domains and restricted datatype promotion.

`DN-0005` through `DN-0014` adapt user-supplied explorations preserved in Git history at commit `abd793c`. Their placement here records useful design context; it does not add them to the development trajectory.
