# Milestone team launch template

After the current development round finishes, fill the bracketed fields and
copy the launch prompt into a new Ash chat. Use a checkout containing the
[agent workflow](agent-workflow.md) and its role skills. Supply role overrides
or use the [repository preferences](../../.agents/ash-workflow.yaml).

## Launch prompt

Launch an Ash delivery team to achieve this milestone.

- Milestone and outcome: [name/link and intended outcome]
- Issues: [issue links or numbers]
- Governing artifacts and tasks: [links]
- Retaining branch: [milestone integration branch]
- Merge/signing policy: [method and requirements]
- Full-gate checkpoints: [shared-runtime and dependent-library completion
  boundaries, conditions and owners; final integrated candidate before Main]
- Role overrides: [model and reasoning effort for orchestrator, developer and
  reviewer; otherwise use `.agents/ash-workflow.yaml`]

Start a fresh orchestrator using `ash-orchestrator`, with a compact handoff
containing this scope, permissions and the complete role settings. The
orchestrator starts developer and independent reviewer agents as work becomes
eligible. Preserve the chosen settings through later assignments and replacement
workers.

The expected starting state is that the previous development round has finished
and no delivery PRs are open. Verify that state, current refs, dependencies and
accepted authority before assigning work.

Authorize implementation, required tests and documentation, task updates,
delivery branches, pushes, PR creation, independent reviews, integration into
the retaining branch, and acceptance updates. Close issues only when their whole
scope is satisfied. Main integration requires a separate instruction.

Make acceptance tracking observable during normal delivery:

1. Capture the initial checkbox states and available evidence for the selected
   issues. Reconcile stale status while preserving criterion wording and
   concurrent edits.
2. Each PR identifies the exact issue criteria it addresses and whether its
   contribution covers the whole criterion or a subset.
3. After reviewed, verified retention, the developer applies the acceptance
   update and reads it back. The reviewer checks the evidence; PM confirms the
   update before advancing.
4. Keep partial criteria unchecked, recording Delivered, Remaining, Awaiting
   and Owner, with PR, retained commit and evidence links.

Use existing issues, PRs and tasks for records. Keep handoffs compact. Continue
through the agreed milestone outcome and required gates. Return concrete
semantic decisions to this chat; incorporate accepted refinements through updated
artifacts and a short delta.

Use [checkpoint gating](agent-workflow.md#verification-cadence): focused
verification and independent review for each delivery, full workspace gates at
the named boundaries and on the final integration candidate before Main. Carry
the last full-gate receipt, intervening deliveries and next checkpoint through
handoffs. Keep milestone-wide regression verification pending between gates;
criterion-specific evidence and Main's separate human merge gate still apply.

Finish with a compact table: issue/criterion, initial and final status,
contributing PRs, retained commit/evidence, confirmed acceptance update, and any
remaining obligation/owner.
