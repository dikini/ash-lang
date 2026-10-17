# Ash

This repository is a reboot of the Ash programming language. The reboot keeps
lessons from historical Ash while rebuilding the language from a small,
coherent base. Historical Ash is evidence for design work, not authority for
this project.

Ash is a rank-1 language with nominal data, interfaces, effects, lexical
handlers and scoped resources. Programs are acyclic graphs of passive source
modules. Each `.ash` file contains imports and declarations. Function signatures
may state interface constraints and effect rows. The entry module supplies a
local `main` function with an empty outward effect row:

```ash
main : Unit -> Int
main () = 42
```

The [canonical specification](spec/README.md) defines the implemented language
and runtime behavior.
The [`ash` tool guide](docs/tools/ash.md) explains module roots, invocation,
output and failures, including [explicit native link inputs](docs/tools/ash.md#native-link-inputs)
and [generated-host linkage checks](docs/tools/ash.md#generated-host-linkage-checks).

The annotated `mini-ash` and `modular-ash` Git tags retain the earlier single-file
and passive-module/interface milestones. The completed library and effect
increments add explicit implementation selection, higher-kinded parameters,
relational interfaces, module and local `newtype`, scoped evidence, checked
one-shot resume/discard, cells, native buffers, synchronous hooks and cleanup.
Current source contains no dialect selector; the tags retain historical
milestone states rather than selectable compiler modes.

The [earlier Main feature inventory](docs/project/implemented-features.md)
records the specified capabilities and bounded Rust-authored provider experiments
of its named historical snapshot. Those experiments remain separate evidence
from the bounded Ash-authored foreign-interface profile in the specification. The
[design-note scope summary](docs/design/README.md#implementation-and-evidence-boundaries)
identifies implemented slices, experimental evidence, and open directions.

Project artifacts answer different questions:

- [design notes](docs/design/README.md) explore options and uncertainty;
- [architectural decisions](docs/decisions/README.md) record accepted non-language decisions;
- [change proposals](docs/proposals/README.md) propose language-semantic changes;
- [tasks](docs/tasks/README.md) organize active implementation work;
- the [development trajectory](docs/trajectory.md) records dependencies and maturity;
- [project documentation](docs/project/README.md) defines documentation,
  dependencies, and the development discipline;
- [tool documentation](docs/tools/README.md) describes the retained Ash
  executables.

## What makes Ash different

Ash is not only a language for expressing programs. It aims to be a language for
expressing truth about programs: values, behavior, invariants, and the laws that
must hold. In the long-term direction, Ash wants programs to state not only
what a computation does, but also what properties are required, which facts are
assumed, which obligations are proven, and which remain subjects for testing.
The language is designed to combine executable code with sound reasoning so that
real systems can be built with principled guarantees rather than only informal
confidence.

In other words, Ash aims to support the full arc from implementation to
specification to evidence: ordinary computation, static guarantees, property
checks, and proof-backed facts in one consistent language story.

Human contributors should start with [CONTRIBUTING.md](CONTRIBUTING.md). Agents
should start with [AGENTS.md](AGENTS.md) and reconstruct only the context needed
for their task.
