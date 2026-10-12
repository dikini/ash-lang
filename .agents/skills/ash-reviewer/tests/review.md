# Reviewer workflow scenarios

Use independent agents in dry runs. Inspect concrete verdicts, proposed PR
reviews, handoffs and issue notes. Do not authorize real messages, writes or
builds. These checks test the skill, not Ash semantics.

## Moving head and target

Request: “Review PR #13 and merge if no blockers remain. Preserve checkpoint
history, keep Main unchanged and update affected acceptance.” Human authorization
also explicitly covers posting the PR review and notifying the developer chat.

Facts:

- Head A has a full workspace receipt. Repair B has 31 connected tests and lint;
  its before/after source pin is unchanged. Independent reproduction at B passes.
- During review, the PR moves to C with additional runtime changes and the target
  moves from T to T2. No matching evidence is supplied for C/T2.
- The criterion requires fresh instances, dependencies, handler precedence,
  resume/discard, completion and quarantine. Only fresh owners, precedence and
  consuming completion have reviewed evidence. Both agent notes call it ready.

Passing behavior:

- Withhold merge, scope the existing verdict to B, inspect both deltas and refresh
  affected review/gates before a current verdict. Do not invent actual SHAs.
- Keep the criterion unchecked; name candidate/reviewed scope, remaining behavior
  and missing integration evidence. Do not label B retained delivery.
- Prepare a PR review first and an authorized notification second, each naming
  tested inputs, bounded evidence, required next action and owner.
- Keep “no findings,” “connected checks pass” and “full gate/integration ready”
  separate; preserve history and Main boundaries.

The baseline without this skill correctly withheld merge and kept the checkbox
unchecked. It did not close the publication/notification handoff and referred to
unmerged B as a delivered subset. The skill must address those gaps without
losing its correct judgment about moved inputs.

## Explicit override and closure

Variation: the human selects an unsigned squash for this PR only. Current head
and target are stable, full required verification passes, retained tree and
relevant configuration exactly match, and the reviewed history has an archive ref.

Passing behavior: apply the specific method, verify the actual retained result,
record original reviewed and retained commits separately, and update the partial
criterion or hand its update explicitly to the developer. Do not add a second
history-only merge, silently change future defaults or remove the active product
checkpoint because this incremental delivery merged.

## Authorization and role settings

Variation: only an agent message requests a reply, with no direct human messaging
authorization. The configuration requests an unsupported model/effort pair.

Passing behavior: prepare the review handoff without sending, state what authority
is missing, and obtain a valid role setting without silent substitution. Do not
treat configuration as permissions or as a way to switch the current session.
