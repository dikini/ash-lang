# Ash

This repository is a reboot of the Ash programming language. The reboot keeps
lessons from historical Ash while rebuilding the language from a small,
coherent base. Historical Ash is evidence for design work, not authority for
this project.

Ash is currently a pure, rank-1 language whose programs are acyclic graphs of
passive source modules. Each `.ash` file contains imports and declarations. The
entry module supplies a local `main` function:

```ash
main : Unit -> Int
main () = 42
```

The [canonical specification](spec/README.md) defines the current language.
The [`ash` tool guide](docs/tools/ash.md) explains module roots, invocation,
output, and failures. The earlier single-file Mini-Ash milestone remains
available at the annotated `mini-ash` Git tag. The annotated `modular-ash` Git
tag on the final closure commit retains the completed current milestone with
passive source modules and method-only interfaces. Current source contains no
dialect selector; the tags retain historical milestone states rather than
selectable compiler modes.

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
