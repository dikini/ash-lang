# C1 bounded model source review

Verdict: **pass for frozen integration**. No actionable findings remain in v3.
This is a source-review verdict, not a completed AD-0012 gate, semantic
acceptance, product authorization, or C1 issue closure.

Reviewed checkpoint: `/tmp/ash-m3/c1-model-manifest-v3.json`.
SHA-256: `bfa3460d74c10736681b143515d809f425a797643c9fc151ec3e689f567ca95d`.
Product parent: `33af1ed1e9adfaa2efa73443a6c0709131b00ff6`.
Sources: `/tmp/ash-m3/c1-model-source-v3/`; all six manifest entries verified.
Reviewer: independent Sol 6.1, xhigh; exact model runtime unavailable.

The model proves the selected new ownership transitions under stated local
admission premises. `step_accounting` derives owner conservation from concrete
updates; `step_preserves_unique` and its finite-trace result use freshness only
for newly admitted root owners. No transition assumes a safe successor.
Slot identities, fixed capacity on normal steps, and generation bounds have
separate preservation results. Actual store, slot and generation equality
guards restoration; the spent-key fact persists through every transition and
finite trace, including slot recycling and new retention.

Fixed interpretation and current-consumer compatibility are preserved with
admission. Captured owners are disjoint from all enclosing support and outside
completion owners, including unreferenced ones. Self-capture, missing outside
completion, branch-local escape and incompatible interpretation have explicit
refusal guards. Shared access to enclosing support does not duplicate its
owner or introduce a thread-safety claim.

The examples connect the selected transitions rather than inferring behavior
from result constructors. A complete P trace retains, restores into the new
consumer, consumes the nested owner, finishes running cleanup and returns to
that consumer while Q remains retained. It applies aggregate ownership and
context preservation. Saved body result and live nested/cleanup phase survive
restoration. Another concrete trace starts the armed outer cleanup, restores
P, checkpoints and retains P again while the drain remains running and Q stays
live. The complete outer-close trace finishes both branches before the drain
finishes and the store releases.

`NoWork` is connected to absence of represented clauses, active branches and
live slots under `ContextSafe`; release is guarded by it and completed outer
cleanup. Normal completion requires finished branch cleanup and consumed
nested phases. These results do not prove a source drain returns empty:
C3 must separately establish its recursive normal-return analysis.

Failure bookkeeping preserves every represented owner in one live, completed,
disposed or unresolved-residual location. Concrete witnesses distinguish
complete teardown from disposal of Q followed by refusal that leaves P's
owners unresolved. Failure blocks source execution and release. The amended
proposal matches current fallible iterative teardown: no double release,
reported incomplete teardown and potentially unreleased residuals. It promises
neither source cleanup nor complete physical reclamation after teardown fails.

The correspondence accurately limits this proof. Capture inventories and the
exact interpretation tokens represent actual complete control under stated
assumptions; the model does not reconstruct a frame forest, action bodies,
general answer types or effect rows. The retain macro-step includes the
administrative clause return and requires its actual suffix to be clear.
Existing private-clause resume and safe inner discard remain inherited
behavior. Natural identities and ghost history do not form a globally finite
state checker or require runtime history tables. The product must derive the
premises from source and linked Core and implement the runtime correspondence.
No C3, scheduler, native-provider, migration, fairness, termination or whole
compiler theorem is claimed.

Verification performed without competing builds:

- Read the complete model, examples, proposal and correspondence, then checked
  the repaired deltas against the earlier findings.
- Verified the six source/document hashes and both local-log hashes against
  the checkpoint; rechecked the product parent.
- Matched all explicit reports against source, local logs and draft gate:
  18 model reports and 31 example reports. Logs contain no error, warning or
  `sorryAx`; reported axioms are only `propext` and `Quot.sound`.
- Inspected sources for unfinished proofs or custom axioms: none found.
- Checked 53 relative file links at their intended repository locations:
  none missing. Checked trailing whitespace: none found.
- Ran no Lean or Cargo build. The inspected compilations are developer local
  feedback and do not replace frozen integration.

Prior findings are resolved: actual key matching and slot uniqueness; fixed
store/current-consumer interpretation; non-vacuous empty-work connection;
terminal release guards; honest incomplete teardown; full external-owner
partition; saved-result preservation; and an actual running-drain yield trace.

Next owner: root verifies this review and initiates the frozen AD-0012 gate
against these exact inputs. After its receipt, independently verify retained
sources, registration and evidence before semantic acceptance or C2 authority.
