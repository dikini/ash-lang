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

# Common sense rules

1. Think Before Coding
  Don't assume. Don't hide confusion. Surface tradeoffs.
  Before implementing:
      State your assumptions explicitly. If uncertain, ask.
      If multiple interpretations exist, present them - don't pick silently.
      If a simpler approach exists, say so. Push back when warranted.
      If something is unclear, stop. Name what's confusing. Ask.

2. Simplicity First
  Minimum code that solves the problem. Nothing speculative.
      No features beyond what was asked.
      No abstractions for single-use code.
      No "flexibility" or "configurability" that wasn't requested.
      No error handling for impossible scenarios.
      If you write 200 lines and it could be 50, rewrite it.
  Ask yourself: "Would a senior engineer say this is overcomplicated?" If yes, simplify.

3. Surgical Changes
  Touch only what you must. Clean up only your own mess.
  When editing existing code:
      Don't "improve" adjacent code, comments, or formatting.
      Don't refactor things that aren't broken.
      Match existing style, even if you'd do it differently.
      If you notice unrelated dead code, mention it - don't delete it.
  When your changes create orphans:
      Remove imports/variables/functions that YOUR changes made unused.
      Don't remove pre-existing dead code unless asked.
  The test: Every changed line should trace directly to the user's request.

4. Goal-Driven Execution
  Define success criteria. Loop until verified.
  Transform tasks into verifiable goals:
      "Add validation" → "Write tests for invalid inputs, then make them pass"
      "Fix the bug" → "Write a test that reproduces it, then make it pass"
      "Refactor X" → "Ensure tests pass before and after"
  For multi-step tasks, state a brief plan:
    1. [Step] → verify: [check]
    2. [Step] → verify: [check]
    3. [Step] → verify: [check]
  Strong success criteria let you loop independently. Weak criteria ("make it work") require constant clarification.
