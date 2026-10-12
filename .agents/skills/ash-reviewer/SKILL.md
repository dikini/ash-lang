---
name: ash-reviewer
description: Use when independently reviewing or re-reviewing an Ash PR, checking acceptance evidence, or verifying an authorized integration.
---

# Ash reviewer

Use the short [shared contract](../../../docs/project/agent-workflow.md) and
[context reconstruction](../reconstructing-ash-context/SKILL.md). Be distinct
from the author; a frozen snapshot protects inputs but does not make self-review
independent. Read changed boundaries on re-review rather than repeating intake.

1. Pin live PR head/target, governing artifacts, task/criteria and prior findings.
   Attach a user-requested PR. Confirm publication, notification and any separate
   integration authorization.
2. Inspect affected behavior, positive/negative evidence, independent validation,
   ownership/control, budgets and documentation. Reproduce important checks and
   inspect receipts; avoid double-counting nested test summaries. Check criterion
   coverage and proposed delivered/remainder notes against actual evidence.
3. Recheck live pins. If moved, review the delta/refresh checks or scope the verdict
   to the old snapshot. Publish actionable findings or a bounded verdict on the
   PR before authorized notification; honor local-only requests. State tested
   inputs, results and missing gates. No findings does not imply merge readiness.
4. Notify the developer directly when authorized, with review URL, tested head,
   finding/gate status and next action; otherwise return that handoff to PM.
   Resolve findings only after the repair and original failure are verified.
5. If assigned authorized integration, verify the actual retained result and give
   the author its commit/receipt. Check its acceptance update, or apply/read back
   the authorized update yourself with explicit ownership. Partial delivery does
   not close a criterion, checkpoint or milestone.

Return completed outcomes and next owner. Read the shared contract's dispatch
reference only if launching an agent or sending a chat follow-up.
