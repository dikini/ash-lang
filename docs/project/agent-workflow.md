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
- Use one branch per PR. For sequential PR development, keep one physical
  product checkout and its shared target cache.
  Switch branches only after the current frozen gate and handoff release the
  checkout and the working tree is clean. The developer is the sole product
  writer and heavy-build operator. Reviewers inspect immutable pins, artifacts
  and receipts and request necessary reruns from that operator. A fresh gate
  does not imply a cold build; separate caches require an
  assigned comparison or isolation need under AD-0011.
- Use the [Rust verification guide](verification.md) for selected checks and
  explicit local receipt reuse. Partial evidence does not establish a full gate;
  required integrated gates remain fresh unless their governing artifact permits
  transfer.
- Old full gates, fresh connected checks, no review findings, verified retention
  and complete acceptance are separate claims. Evidence transfers only within
  demonstrated input/configuration equality; required integration gates remain.
- Recheck live refs before current verdicts or integration. Refresh affected
  evidence after movement. Apply the authorized merge/signing method; a specific
  override affects that delivery only. Main and checkpoint cleanup retain their
  separate gates under AD-0011.

## Working records and timing

Generated hosts retire their unique Cargo root artifacts after copying and
before publication; shared dependencies, current tests and published outputs
remain. See the [build tool contract](../tools/ash.md). Callers retain useful
source/log records while a PR or checkpoint needs them.

At PR closure, consolidate lasting findings in existing task/tool documentation
and retire obsolete working history and superseded output under the
[documentation policy](documentation.md). Preserve live checkpoint dependencies
and compatible caches. Require a cleanup Result and Next owner before starting
the next PR; do not sweep unrelated artifacts or unretained source/commits.

Collect available timing by operation: inspection/dispatch, compile/link,
tests/native hosts, documentation, review, integration/acceptance, cleanup and
waiting. Keep tool-call durations and batch/turn wall time separate. Record model
and effort; label exact model runtime unavailable when it is not exposed.
Elapsed-minus-tools is only a proxy. Use existing receipts and task/handoff
records; timing collection does not authorize extra verification or benchmarks.

## Connected delivery planning

For work crossing implementation boundaries, plan one production vertical slice
before dividing it among agents: actual entry, intermediate operations, consuming
admission or execution path, runtime completion and cleanup, as applicable.
Name the integration owner and the acceptance check for that complete path.
Separate component fixtures support this check; they do not replace it.

Record the necessary interface agreements in the existing task or its execution
plan. For each crossed boundary, identify:

- The producer, consumer and responsible owners.
- The data or evidence transferred, its provenance, lifetime and ownership.
- Failure behavior, unsupported cases and what remains unresolved.
- The check showing that the real consumer uses the producer's result.

Use the smallest record sufficient for the change. This is implementation
planning, not new semantic authority, a separate interface specification, or an
additional approval requirement. Reuse retained mechanisms and evidence where
their contracts apply. A helper without its required production consumer is
partial work, even when its isolated tests pass.

For complex parallel work, have the independent reviewer challenge the boundary
map before substantial implementation. Compile interfaces early and establish
the integration acceptance check from the start. Exercise the real path at the
first coherent slice; do not accumulate independently passing components before
discovering their integration requirements. Review includes admission, runtime,
failure and cleanup consumers, not just the producing API.

When work stalls or repeated repairs reveal new dependencies, ask the same
independent reviewer to analyse the complete remaining path, challenge its
assumptions and suggest a simpler implementation plan before adding more
helpers. Keep confirmed findings, failed approaches, missing connections and
next owners in the existing delivery ledger or task so agents do not rediscover
them. Update the plan when the delivery path changes.

Estimate the whole outstanding delivery chain, including unimplemented
consumers, integration, review and required gates. Distinguish measured work
from unresolved interfaces and explain the assumptions behind the range. Do not
present time to the next local repair as time to milestone completion, or count
component checks as completed issue acceptance.

## Verification cadence

Use checkpoint gating rather than a full workspace gate for every PR. Every
delivery requires focused verification of its changed behavior and affected
callers, independent review, and verification of the actual retained result.
Include the positive, negative, regression and native evidence required by its
governing artifacts. Refresh affected checks after repairs or input movement.

PM records the next full-gate checkpoint, its completion condition and owner in
the existing assignment/task before advancing. Choose boundaries where shared
runtime mechanisms become ready for their dependents, or dependent libraries
have been integrated. A PR does not automatically create a checkpoint. These
verification boundaries do not close a product checkpoint or authorize proposal
removal or worktree retirement under AD-0011.

Run a fresh full workspace gate on the pinned integration candidate at each
agreed checkpoint and before Main integration. A final checkpoint gate can also
serve as the pre-Main gate when the inputs remain equal; do not duplicate it at
identical inputs. Verify the integrated result, transferring evidence only within
demonstrated source/configuration/tool/artifact equality and refreshing affected
checks when that equality fails. Main's merge and signing permissions remain a
separate human gate.

Between checkpoints, handoffs and PRs state the focused checks and review,
retained commit, last full-gate commit/receipt, intervening deliveries, and the
next checkpoint's owner and trigger. Mark milestone-wide regression verification
pending. A delivery may advance after its required focused verification and
review; do not describe that result as a fresh full-gate pass. If a checkpoint
fails, assign repair and required re-verification before crossing the boundary.

Criterion-specific evidence remains required. Keep a criterion unchecked when
its original scope still awaits checkpoint or final integrated verification, and
name that obligation in its acceptance record. Do not undo valid earlier full
gate receipts or infer completed acceptance from the cadence change.

## Acceptance

Check a criterion only when its entire original scope has required evidence on
its intended retaining branch. Contract-only criteria use recorded acceptance.
Partial delivery stays unchecked with:

```text
Delivered: subset; PR; retaining ref/commit; evidence link.
Remaining: missing obligations. Awaiting: review/integration/verification.
Owner: next responsible agent/person.
```

Until retained verification passes, say candidate/merged scope. The author
prepares this record, the reviewer checks it, and the author applies and reads
it back after verification,
preserving concurrent edits. If another agent integrates, it supplies the
retained commit/receipt. PM confirms the update before advancing or closing.
Uncheck disproven criteria and record the cause; partial PRs do not auto-close issues.

Role model/effort preferences are in
[ash-workflow.yaml](../../.agents/ash-workflow.yaml). Read
[dispatch rules](../../.agents/skills/ash-orchestrator/references/dispatch.md)
only when launching work or sending an authorized follow-up.

For a new milestone team, fill the
[launch template](milestone-launch-template.md).
