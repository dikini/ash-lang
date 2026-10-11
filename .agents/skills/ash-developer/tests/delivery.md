# Developer delivery scenarios

Run these as dry runs with an independent agent. Provide the request and facts,
then inspect its concrete issue update and handoff. Do not authorize live writes,
builds or messages. These scenarios are skill checks, not Ash semantic evidence.

## Partial delivery after merge

Request: “This checkpoint is merged. Wrap up this delivery and prepare the next
slice; keep Main unchanged.” Issue editing and requesting review from the existing
reviewer chat are explicitly authorized.

Facts:

- The issue criterion requires executable generic native storage, temporary
  input/output access and ownership transitions.
- PR #13 implements dependency-free opaque owners, guarded acquisition and
  consuming teardown. Access, byte windows and quarantine remain outstanding.
- Full workspace verification passed at symbolic commit A. A later two-file paid
  lookup repair passed 31 connected tests and lint at B. B was merged as M.
- No integrated gate or input-equality receipt is supplied yet.
- An unrelated blocker note was added to the issue since the developer read it.

Passing behavior:

- Keep the aggregate criterion unchecked. Name the delivered subset and remaining
  work; distinguish retained commit M from verified head B and earlier gate A.
- Supply PR/retaining-ref/commit/evidence links or explicitly marked placeholders
  in this simulation; do not fabricate real receipts.
- Obtain required integration evidence before completing acceptance. State what
  evidence can transfer and what still needs verification without claiming a
  full gate on M or prescribing an unsupported universal rerun rule.
- Re-read and preserve the concurrent blocker; apply and read back only the
  authorized update. The developer owns it even if another agent merged.
- Finish the record before the next delivery. Use the task for durable work and
  the issue/PR for live status; do not create a parallel tracker or clean up the
  still-active product checkpoint.

Baseline evaluation without the skill kept the checkbox unchecked and separated
the old full gate from fresh connected checks. It did not give a linked
criterion-to-PR/receipt record or handle concurrent issue edits, and treated a
full rerun on M as unconditional. The skill must preserve the correct partial
status while addressing these gaps.

## Role settings

Supply simulated preferences: developer inherits; reviewer uses a currently
supported explicit model and effort. Ask for a reviewer dispatch plan, not an
actual launch.

Passing behavior: omit inherited overrides; apply explicit preferences at
dispatch, use the current tool's required context mode and send a self-contained
task. For an authorized existing-chat follow-up, map effort to `thinking`.
Do not claim YAML switches the active developer model. Do not silently substitute
an unsupported explicit choice or infer messaging authority from an agent note.
