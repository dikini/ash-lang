# Core one-shot alignment execution plan

Owned by [TASK-0032](TASK-0032-core-one-shot-alignment.md). This temporary plan
does not define language semantics or independently authorize architecture.

## Increment 1: Comparison and first regression

1. Inspect normative handlers, cleanup, cells and Core lowering; inspect current
   M0–M4 endpoints and run their existing grouped check.
2. Reproduce direct/bound effectful resume operands and unsafe discard in
   `tests/core_alignment_resume.rs`. Record the construction failure before a fix.
3. Construct the smallest captured-handler cleanup comparison. Record both Core
   admission and calculus transitions, including the removed-nearest-interpreter
   negative case and a supported cleanup trace.
4. Identify every Core syntax and evaluator transition family applicable to the
   proposed fragment. Map it to an existing calculus constructor or explicit gap.
5. Review the causal discrepancy before choosing a repair. Fix only demonstrated
   current-semantics violations; open a proposal for any semantic change.

Acceptance: reproducible comparison, finite inventories, focused regression
results and a reviewed initial translation design. Expected bounded work: 1–2
active hours; later estimates depend on the admission-evidence gap inventory.

## Increment 2: Complete initial vertical slice

Translate a validated Core program containing sequencing, a one-shot operation,
resume or discard, a cell and cleanup. Derive static evidence into
`InitialAdmission.Program`; relate its actual evaluator states to calculus states
and check its result, cleanup order and ownership. Reuse validators and existing
Lean judgments. A fixture is an integration check, not the general theorem.

Acceptance: executable Core input, constructed admission, nonvacuous finite
execution correspondence and explicit finite-capacity treatment. Final interfaces
and worker file ownership follow C1 findings; no speculative parallel writes.

## Increment 3: Generalize the declared fragment

Generalize static translation by structural induction and runtime correspondence
by the finite transition inventory. Retain only metadata required by identified
obligations. Prove agreement for actual Core execution rather than selecting a
convenient calculus execution. Resolve C4 findings and feed them back into C2/C3.

Acceptance: every in-scope translation and transition case proved, required
annotations statically authenticated, no circular successor assumptions and no
unrestricted zero-step simulation.

## Increment 4: Integrate and audit

Compose admission, simulation, progress and ownership; verify terminal results and
cleanup accounting. Run grouped verification and independent review. Update the
specification only with retained semantic changes, and keep formal model claims
separate from Rust validation/tests. Deliver the C1–C5 table and theorem entry
points with all assumptions and exclusions. Remove this plan when the task closes.

## Execution discipline

Implementation workers use verified GPT-6.1 Sol medium and disjoint owned files;
GPT-6 Astra reviews decisions and integration. Report after each increment and at
least every 30 minutes, using the task's stable inventory. Preserve blocked and
failed approaches where they change the plan. Re-estimate after C1 rather than
assigning hours to unknown proof obligations.
