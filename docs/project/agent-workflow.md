# Agent workflow

Apply [AGENTS.md](../../AGENTS.md), the [artifact guide](artifacts.md),
[documentation policy](documentation.md) and
[AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md). This guide adds
coordination and acceptance responsibilities, without new semantic authority
or action permissions.

| Role | Owns |
| --- | --- |
| [Orchestrator / PM](../../.agents/skills/ash-orchestrator/SKILL.md) | Eligible work, dependencies, assignments, initiating the next action and closure. |
| [Developer](../../.agents/skills/ash-developer/SKILL.md) | Implementation, evidence, repairs and acceptance updates after retention. |
| [Reviewer](../../.agents/skills/ash-reviewer/SKILL.md) | Independent review, PR verdict, authorized developer notification and acceptance checks. |

The orchestrator assigns integration explicitly. Developer/reviewer exchanges
can proceed directly within authorization; the orchestrator ensures the next
action has an owner and is initiated. It acts when invoked and while active;
later wakeups require an explicitly requested automation.

## Shared contract

- Use governing artifacts and authorized scope. Reconstruct context at a new
  assignment; revisit changed boundaries on repair/re-review. Return semantic
  gaps to proposal/design work. Tasks hold durable findings; issues/PRs hold live
  progress. Use existing task acceptance when no issue exists; add no tracker.
- Handoffs carry artifact/issue/PR links, exact head and target refs/commits,
  scope, receipts, requested action and next owner. Distinguish local and remote
  refs. Preserve unrelated work and explicit wait instructions.
- Freeze verification inputs and compare source/configuration pins before/after.
  Use one Cargo job, compatible caches and checks required by the task. Separate
  real native observations from injected failures and foreign assumptions.
  Preserve work/depth/stack limits.
- Old full gates, fresh connected checks, no review findings, verified retention
  and complete acceptance are separate claims. Evidence transfers only within
  demonstrated input/configuration equality; required integration gates remain.
- Recheck live refs before current verdicts or integration. Refresh affected
  evidence after movement. Apply the authorized merge/signing method; a specific
  override affects that delivery only. Main and checkpoint cleanup retain their
  separate gates under AD-0011.

## Acceptance

Check a criterion only when its entire original scope has required evidence on
its intended retaining branch. Contract-only criteria use recorded acceptance.
Partial delivery stays unchecked with:

```text
Delivered: subset; PR; retaining ref/commit; evidence link.
Remaining: missing obligations. Awaiting: review/integration/verification.
Owner: next responsible agent/person.
```

Until retained verification passes, say candidate/merged scope. The author prepares this record,
the reviewer checks it, and the author applies and reads it back after verification,
preserving concurrent edits. If another agent integrates, it supplies the
retained commit/receipt. PM confirms the update before advancing or closing.
Uncheck disproven criteria and record the cause; partial PRs do not auto-close issues.

Role model/effort preferences are in
[ash-workflow.yaml](../../.agents/ash-workflow.yaml). Read
[dispatch rules](../../.agents/skills/ash-orchestrator/references/dispatch.md)
only when launching work or sending an authorized follow-up.

For a new milestone team, fill the
[launch template](milestone-launch-template.md).
