---
name: ash-orchestrator
description: Use when coordinating Ash development across agents, assigning authorized work, initiating reviews, or advancing delivery through integration and acceptance.
---

# Ash orchestrator / PM

Use the short [shared contract](../../../docs/project/agent-workflow.md).
Own initiation and dependency/closure checks; keep implementation and independent
review with their roles. Read [dispatch rules](references/dispatch.md) when
launching work or sending authorized follow-ups.
Accept milestone launch handoffs from the planning chat and carry its role
settings through the run. Continue through the agreed milestone outcome and
evidence; report any final gate outside the authorized scope as outstanding.

1. Reconstruct the relevant trajectory, governing artifacts, active tasks and
   live issue/PR state. Check dependencies, existing workers and human permissions.
   Product implementation requires accepted authority and an active task;
   experiments require their named question and retention conditions. Assign
   developer, independent reviewer, integrator and acceptance owner. Do not
   duplicate active work or turn a proposed contract into implementation authority.
2. Initiate the next eligible action with a compact assignment: role/action,
   scope and governing links, criterion subset, exact refs/commits, required
   evidence, completion condition and permissions. Apply role preferences.
   Parallelize independent work; serialize shared writers and heavy builds.
3. On a reviewable delivery, initiate independent review at its current head.
   Developer and reviewer may handle repairs/re-review directly when authorized.
   Track the actual next actor; if a handoff only promises action or leaves both
   waiting, dispatch that action. Wait for results with compact status rather than
   repeatedly reading full chats or evidence. Retrieve details only for changes,
   blockers or disputed claims.
4. When current review and required gates are satisfied, initiate the authorized
   integration. Otherwise assign the missing check/repair; do not treat a clear
   review as a full gate or merge permission. Require the retained commit and
   verification receipt, then initiate the author's acceptance update and confirm
   it was applied/read back. Review the whole issue/dependencies before closure.
5. Start the next authorized slice from the verified retaining tip after the
   previous record closes. Keep remaining obligations visible even if a bounded
   PR passed. Escalate concrete semantic gaps or missing authorization with a
   prepared handoff; preserve progress on independent authorized work. Honor
   explicit waits, Main's separate gate and checkpoint cleanup policy.

Keep live assignments/blockers in existing issues/PRs and durable scope/findings
in tasks. Return completed deliveries, active next owner/action and any decision
needed. This skill starts work when invoked; it does not schedule its own wakeup.
