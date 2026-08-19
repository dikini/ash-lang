# Ash Reboot Foundation Design

## Goal

Create the smallest repository foundation that lets contributors reconstruct current Ash project context and begin design or implementation work without inventing process or semantics.

## Structure

The root remains navigational. `README.md` introduces the project, `AGENTS.md` gives agents a context-reconstruction entry point, and `CONTRIBUTING.md` gives humans the contribution flow.

Current language truth lives under `spec/`. Informative project guidance lives under `docs/project/`. Artifact classes use separate directories under `docs/`: design notes, architectural decisions, change proposals, and tasks. `docs/trajectory.md` records maturity and dependencies without becoming a sequential roadmap.

The existing foundation note becomes `DN-0001`. It remains informative and retains its role as the source of reboot principles and open design directions. Separate Core and parser design notes extract only their supported intent, constraints, questions, candidate directions, and experiments. Neither note accepts an architecture.

The completed bootstrap brief and these implementation plans are preserved in Git history, then removed from the final working tree because they do not describe continuing project state.

## Authority and flow

The canonical specification is the only source of current language and runtime semantics. Accepted architectural decisions describe non-language choices. Change proposals describe possible semantic transitions, but do not change current Ash. Tasks organize work and cannot define semantics. Design notes remain exploratory.

Language work flows from design to a change proposal, then to tasks, implementation, tests, and a specification update in one merge. Architectural work flows from design to an architectural decision, then to tasks. If implementation exposes a semantic gap, work returns to the proposal instead of settling the gap locally.

## Local agent guidance

`AGENTS.md` describes minimum context for design, implementation, QA, specification, and planning. Three local skills provide focused reusable guidance:

- reconstructing Ash context for any role;
- doing Ash design work;
- implementing and verifying Ash changes.

The skills link to canonical repository documents rather than repeating them. Their behavior is checked with role-specific scenarios before they are added.

## Deliberately unresolved decisions

This bootstrap does not choose an implementation language, build system, package manager, CI system, formatter, parser framework, formal-semantics method, parser architecture, or concrete Core encoding. The trajectory makes the implementation environment and the two immediate architecture investigations visible as early work.

## Validation

Validation is an audit, not new project tooling. It checks the final tree, local Markdown links, stable artifact identities, terminology, authority boundaries, and every requirement in the bootstrap brief. The canonical specification must remain tiny and must state plainly that no executable Ash exists.
