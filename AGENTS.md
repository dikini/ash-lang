# Working on Ash

> Reconstruct the minimum sufficient context for the task from the repository rather than relying on remembered knowledge of Ash.

Start with the [artifact guide](docs/project/artifacts.md). Treat sources according to their authority:

1. `spec/` is current, normative language truth.
2. Accepted architectural decisions are current non-language decisions.
3. Change proposals describe possible semantic changes, not current Ash.
4. Tasks describe active work and never define semantics.
5. Design notes explore ideas and uncertainty; they are informative.

Read only the relevant slice:

- Design: current specification, related design notes and decisions, alternatives, evidence, and future pressure.
- Product implementation: current specification, the accepted proposal or decision, active task, relevant tests, and invariants.
- Design experiment: the governing design note, the question being tested, comparison criteria, and disposal or retention conditions. Experimental code is evidence, not product implementation or language truth.
- QA/testing: specification obligations, proposal evidence requirements, positive and negative cases, and invariants.
- Specification/documentation: current specification, an implemented proposal's semantic delta, tests, and decisions that affect wording or structure.
- Planning: trajectory, dependencies, active proposals, tasks, and their maturity.

Do not import historical Ash as current authority. Do not infer semantics from a task, implementation detail, test accident, design note, or proposal. If product implementation reveals missing or incorrect proposed semantics, return to the proposal or design work instead of making a local semantic decision.

The project-local skill under `.agents/skills/` provides a focused context-reconstruction workflow. Verify changes using the evidence required by the governing artifact, then check links and authority boundaries in any documentation you change.

Before creating or editing project prose, follow the [writing guide](docs/project/writing.md).
