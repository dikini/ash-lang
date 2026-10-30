# Working on Ash

> Reconstruct the minimum sufficient context for the task from the repository
> rather than relying on remembered knowledge of Ash.

Context is sufficient when it forms a causal semantic model: explain affected
current behavior, crossed boundaries, transferable evidence, downstream
pressure, simplification opportunities, and intentional exclusions. A list of
documents read is not a substitute.

Start with the [artifact guide](docs/project/artifacts.md). Treat sources
according to their authority:

1. `spec/` is current, normative language truth.
2. Accepted architectural decisions are current non-language decisions.
3. Change proposals describe possible semantic changes, not current Ash.
4. Tasks describe active work and never define semantics.
5. Design notes explore ideas and uncertainty; they are informative.

Read only the relevant slice:

- Design: current specification, related design notes and decisions,
  alternatives, evidence, and future pressure.
- Product implementation: current specification, the accepted proposal or
  decision, active task, relevant tests, and invariants.
- Design experiment: the governing design note, the question being tested,
  comparison criteria, and disposal or retention conditions. Experimental code
  is evidence, not product implementation or language truth.
- QA/testing: specification obligations, proposal evidence requirements,
  positive and negative cases, and invariants.
- Specification/documentation: [documentation policy](docs/project/documentation.md),
  current specification, an implemented proposal's semantic delta, tests, and
  decisions that affect wording or structure.
- Planning: trajectory, dependencies, active proposals, tasks, and their
  maturity.

Do not import historical Ash as current authority. Do not infer semantics from a
task, implementation detail, test accident, design note, or proposal. If product
implementation reveals missing or incorrect proposed semantics, return to the
proposal or design work instead of making a local semantic decision.

The project-local skill under `.agents/skills/` provides a focused
context-reconstruction workflow. Verify changes using the evidence required by
the governing artifact and documentation policy, then check links and authority
boundaries in any documentation you change.

Use `ash-orchestrator` to initiate and coordinate authorized agent work,
`ash-developer` for delivery and `ash-reviewer` for independent review. The
short
[agent workflow](docs/project/agent-workflow.md) defines shared handoffs and
acceptance ownership. Read only the applicable role and current assignment;
load dispatch details only when dispatching. Model/effort preferences are in
`.agents/ash-workflow.yaml` and apply at dispatch, without new action
permissions.

Follow [connected delivery planning](docs/project/agent-workflow.md#connected-delivery-planning)
when work crosses implementation boundaries: agree on producer/consumer
interfaces before parallel implementation, keep one production integration
acceptance path, and estimate the entire remaining delivery chain. When stuck,
use the same independent reviewer to challenge the plan and preserve confirmed
findings in the existing task or delivery ledger.

Apply the [writing guide](docs/project/writing.md) to all Ash communication,
including chat, reviews, plans, commit and PR messages, and repository prose.
