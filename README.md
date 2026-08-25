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
available at the `mini-ash` Git tag; it is not a selectable dialect in the
current source tree.

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

Human contributors should start with [CONTRIBUTING.md](CONTRIBUTING.md). Agents
should start with [AGENTS.md](AGENTS.md) and reconstruct only the context needed
for their task.
