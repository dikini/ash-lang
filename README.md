# Ash

This repository is a reboot of the Ash programming language. The reboot keeps
lessons from historical Ash while rebuilding the language from a small,
coherent base. Historical Ash is evidence for design work, not authority for
this project.

The first retained milestone, Mini-Ash, is an executable single-file, rank-1,
pure-functional language. The
[canonical specification](spec/README.md) defines its current syntax and
semantics. The [`ash` tool guide](docs/tools/ash.md) explains how to run a
source file.

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

Human contributors should start with [CONTRIBUTING.md](CONTRIBUTING.md). Agents should start with [AGENTS.md](AGENTS.md) and reconstruct only the context needed for their task.
