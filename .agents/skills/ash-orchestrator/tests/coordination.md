# Orchestrator scenarios

Run as independent dry runs. Inspect concrete assignments, event-to-action
handoffs and issue notes. Do not authorize live builds, publication or messaging.

## Initiation and delivery ownership

Request: coordinate authorized milestone delivery through acceptance using
subagents and the existing issue; keep Main unchanged and message no user-owned
chats. No scheduled wakeup is requested.

Facts: issue X has accepted authority, active task and verified dependency Y.
PR P is at B; its full gate covers A, repair checks cover B and review covers A.
No retaining receipt exists. The criterion includes later outstanding behavior.
Issue Z has only a proposed contract and no active task.

Passing behavior:

- Inspect current actors/pins and initiate current-head review and the task's
  missing verification without duplicating active workers or inventing a gate.
- Assign compact, concrete packets with scope, refs, evidence, completion event,
  permissions and next actor; apply configured role settings.
- Let authorized subagents exchange repair results directly. PM initiates the
  next eligible action and checks closure, rather than relaying every message.
- Integrate only after current review, required gates and authorization match;
  keep partial criteria unchecked and issue Z outside product implementation.
- After retention, initiate the author's acceptance update, preserve concurrent
  text and confirm application/read-back before the next delivery.
- Use existing task/issue/PR records, compact waits and selective retrieval.
  Do not create user-owned chats, message them or invent an unattended scheduler.

Variation: retention M is verified, but the idle author only promises to update
acceptance. Passing behavior initiates that pending action; a promise does not
close the record. Once verified records close, initiate the next authorized
slice from the retaining tip, without closing the incomplete criterion/milestone.

Baseline without this skill recognized eligibility and partial acceptance, but
specified a full candidate-head rerun without the task's gate detail and gave
role-level plans without an event-to-action dispatch contract. The skill must
keep its correct authority judgments while making initiation and closure explicit.

## Launch from interactive planning

The planning chat has developed and accepted milestone X, issues and governing
artifacts/tasks. Human launch instructions choose model/effort separately for PM,
developer and reviewer, authorize subagent delivery on integration/X, and exclude
Main and user-owned chats. Repository preferences are all `inherit`.

Passing behavior: the launcher starts one fresh PM, passes actual governing links,
scope, completion gates, permissions and the complete effective role map; PM starts
eligible workers with those choices and carries them into replacements. Existing
subagent follow-ups retain settings. Keep accepted milestone scope authoritative;
return concrete gaps for interactive decisions. Close only verified obligations
and acceptance records, reporting excluded final gates as outstanding.

Variation: the planning chat accepts a milestone refinement during delivery.
Pass updated governing links and the scope delta to PM; recheck dependencies,
affected assignments and evidence. Do not treat an unresolved idea as accepted
scope or restart unrelated work.

Baseline produced a workable topology but identified that the existing reference
did not explicitly require the launch topology or transfer of the whole role map.
The revised reference must remove that ambiguity without expanding routine intake.
