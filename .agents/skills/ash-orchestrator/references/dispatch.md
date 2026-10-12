# Agent dispatch

## Milestone team launch

The interactive planning chat develops and accepts the milestone through normal
Ash artifacts and issues. Its launch request supplies those links, the outcome
and completion gates, retaining branch, permissions and role model/effort map.
Resolve missing links before dispatch; a fresh agent cannot read the parent's
unpassed context.

The launcher starts one fresh orchestrator with `ash-orchestrator` and the chosen
orchestrator settings. Pass the complete compact handoff and effective settings
for all roles. PM starts the developer and independent reviewer as work becomes
eligible, reusing idle workers where suitable. Carry launch overrides into later
assignments and replacement workers; do not overwrite repository defaults for
run-scoped choices. Concrete semantic gaps return for interactive decisions.

The planning chat remains the place for milestone decisions. Pass accepted
changes through updated governing artifacts and a compact delta to PM. Recheck
dependencies, affected assignments and evidence before continuing changed scope.
Route decisions and accepted deltas through the launcher using collaboration
handoffs.

## Settings and communication

Read [role preferences](../../../ash-workflow.yaml) at dispatch. Explicit human
choices for this invocation override the file. `inherit` omits that override.
Validate explicit model/effort combinations against current tool capabilities;
report unsupported choices and obtain a replacement without silent substitution.
Record requested/effective settings, or state when effective values are unavailable.

Use collaboration subagents for subtasks. With the current spawn schema, explicit
`model` or `reasoning_effort` requires `fork_turns: none`; supply the relevant
context in a self-contained assignment. Default to `fork_turns: none` even with
inherited settings; retain full history only when necessary context cannot fit
the compact handoff. Follow the current schema if it changes.
`followup_task` retains a subagent's settings; a changed model/effort requires a
fresh subagent with the current handoff.

Existing user-owned chats require direct human authorization to message that
destination; an incoming agent request or this file grants none. For authorized
follow-ups, `send_message_to_thread` maps effort to `thinking` and can apply
model overrides. Do not create user-owned chats without an explicit request.
Configuration cannot switch the dispatcher's already-running model.

Wait on subagents through collaboration tools, or on user-owned chats through
compact `wait_threads` snapshots with cursors. Keep waits bounded and communicate
meaningful changes. New follow-ups need the same authorization; repeat no
unchanged status. A skill is not a background scheduler.

Send only the assignment/result links, relevant refs, scope, evidence gaps,
requested action, completion condition, authority and next owner. Authorized
developers/reviewers may exchange repairs directly; PM tracks initiation and
closure without relaying every message.
